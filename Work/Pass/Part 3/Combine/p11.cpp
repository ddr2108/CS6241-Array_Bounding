#define DEBUG_TYPE "p11"
#include "llvm/IR/Function.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/LoopInfo.h"
#include <map>
#include <set>
#include <queue>

using namespace llvm;
using std::set;
using std::queue;

namespace {
	
	//Structure for holding information about instructions
	typedef struct _defInstruct{
		StringRef def;		//the variable modified
		int instructNum;	//the nth instruction in program
		int lineNum;		//actual line number

		//Constructor
		 _defInstruct(StringRef defIn, int instructNumIn, int lineNumIn){
			def = defIn;
			instructNum = instructNumIn;
			lineNum = lineNumIn;
		}
	} defInstruct;

	typedef struct _instTranslation{
		Instruction* oldInst;
		Instruction* newInst;
					
		//Constructor
		 _instTranslation(Instruction* oldInstIn, Instruction* newInstIn){
			oldInst = oldInstIn;
			newInst = newInstIn;
		}
	}instTranslation;

	struct p11 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p11() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){

			//Information about structure of program
			std::map<BasicBlock*, int> basicBlockIndex;
			std::map<int, BasicBlock*> basicBlockReverseIndex;
			std::map<Instruction*, int> instructionIndex;
			std::map<int, defInstruct*> instructionDefIndex;

			int *dist = NULL;						//Hold distance between any two blocks
			int* reachDef = NULL;						//Hold reaching def for each instruction
			std::map<BasicBlock*, std::set<int> > killedDef;	//Hold killed def for each block	
			std::map<BasicBlock*, std::set<int> > usedDef;		//Hold used def for each bock
			std::map<BasicBlock*, std::set<BasicBlock*> > influencedNode;		//Hold used dbock
			std::map<BasicBlock*, std::set<BasicBlock*> > ROI;		//Hold used def for each bock
			std::map<std::vector<BasicBlock*>, std::vector<BasicBlock*> > cloned;		//hold relation between original and clone
			std::map<std::vector<BasicBlock*>, BasicBlock* > headCloned;		//hold relation between original and clone
			std::map<std::vector<BasicBlock*>, std::vector<instTranslation*> > renameBlock;	//hold relation between ROI and new names

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////INITIALIZE////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int cloningFlag = 1;		
			
		while (cloningFlag == 1){

			//Reset Flag
			cloningFlag = 0;

			//Free memory
			if (dist!=NULL){
				free(dist);
			}
			if (reachDef!=NULL){
				free(reachDef);
			}

			//Clear maps
			killedDef.clear();
			usedDef.clear();
			influencedNode.clear();
			ROI.clear();
			cloned.clear();
			headCloned.clear();
			renameBlock.clear();
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////DISTANCE BETWEEN BLOCKS///////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int numBlock = 0;	//Number of blocks

			//Get list of basic blocks			
			Function::BasicBlockListType &allblocks = F.getBasicBlockList();
			//Go through basic blocks
			for (Function::iterator i = allblocks.begin(); i != allblocks.end(); i++) {
				basicBlockReverseIndex[numBlock] = i;
				basicBlockIndex[i] = numBlock++;		//hold information about where the basic block is
			}

			//Allocate array
			dist = (int*) malloc(numBlock*numBlock*sizeof(int*));
			for (int i = 0; i<numBlock; i++){
				//Init to infinite
				for(int j =0; j<numBlock; j++){
					if (i==j){
						dist[i*numBlock + j] = 0;
					}else{
						dist[i*numBlock + j] = 1000000000;
					}
				}
			}

			//Fill array will all with distance 1;
			BasicBlock* successorBlock;	//Next basic block
			//Block indexes
			int sourceBlock = 0;
			int destinationBlock;
			for (Function::iterator i = allblocks.begin(); i != allblocks.end(); i++) {
				//For each successor
				for (int j = 0; j < (i->getTerminator())->getNumSuccessors();j++){
					successorBlock = (i->getTerminator())->getSuccessor(j);	//Successor
					destinationBlock = basicBlockIndex[successorBlock];
					dist[sourceBlock*numBlock + destinationBlock] = 1;			//Set distance to 1
				}
				sourceBlock++;
			}

			//Perform the algorithm
			for (int i = 0; i<numBlock ;i++){
				for (int j = 0; j<numBlock ;j++){
					for (int k = 0; k<numBlock ;k++){
						if (j!=k){
							if (dist[j*numBlock + k] > (dist[j*numBlock + i] + dist[i*numBlock + k])){ 
								dist[j*numBlock + k] = dist[j*numBlock + i] + dist[i*numBlock + k];
							}
						}
					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////REACHING DEFINTION ANALYSIS////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int numInst = 0;		//number of instructions
			int numDef = 0;			//number of defs

			//Get loopinfo
  			LoopInfo &LI = getAnalysis<LoopInfo>();

			std::vector<Instruction*> instructionLists;	//List of instructions

			//Put each instruction into list			
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
				instructionLists.insert(instructionLists.end(), &*i);

				//Get line number
				unsigned int line;
				MDNode *N = i->getMetadata("dbg");
				if (N) {
					DILocation Loc(N);                     
					line = Loc.getLineNumber();
				}

				//Store data about variables in list - include line number, variable name, and actual instr
				if (i->getOpcode()==28 && N && i->getOperand(1)->getName()!=""){
					//Insert information about instruction
					defInstruct* curInstuction = new defInstruct(i->getOperand(1)->getName(), numInst, line);
					instructionDefIndex[numDef++] = curInstuction;
				}
				
				//Store index number of instruction
				instructionIndex[&*i] = numInst++;
   			}

			//Allocate 2d array to hold reaching def
			reachDef = (int*)calloc((numInst)*numDef,sizeof(int));
			
			//Hold defentions that are being studied
			int prevDef = 0;
			int curDef = 0;
			//go through each instruction and fix successor reaching defs
			for(int i = 0; i < numInst; i++){
				Instruction* curInst = instructionLists[i];	//Instruction being studied
				BasicBlock *curBlock = curInst->getParent();	//block with current instruction
				prevDef = curDef;				//defs being studied
				
				//Get which defs this instruction added
				for (curDef = 0; curDef < numDef; curDef++){
					//compare def to the instruction being studied
					if(instructionDefIndex[curDef]->instructNum > i){
						curDef--;
						break;
					}
				}

				//copy prev instruction if not first instr in block
				if (i > 0 && (curInst->getParent()->getFirstNonPHI()!=curInst)){
					//Copy previous reach def
					for (int j = 0; j < numDef; j++){
						//if it is marked as reaching, mark it as reaching in next
						if (reachDef[(i-1)*numDef+j] > 0){
							reachDef[i*numDef+j] = reachDef[(i-1)*numDef+j]; 
						}
					}
				}
				
				//Add new defitions reachable because of new isntruction
				for (int j = prevDef+1; j <= curDef && j < numDef; j++){
					reachDef[i*numDef+j] = basicBlockIndex[curBlock] + 1;		//mark instruction as reaching
					//Check if need to get rid of def
					for (int k = 0; k < numDef; k++){
						//if instruction  is marked as reaching and not the same instruction
						if (reachDef[i*numDef+k] > 0 && instructionDefIndex[k]->instructNum!=i){
							//if the instructions are for the same variable, mark the others so
							if(instructionDefIndex[j]->def == instructionDefIndex[k]->def){
								reachDef[i*numDef+k] = 0;
							}
						}
					}
				}

				int changedFlag = 0;	//Flag to hold whether any changes where made
				int killedFlag = 0;	//Flag to hold whether a def was killed

				//If  it is a terminating instruction and is doing a call
				if (curInst->isTerminator() && (((curBlock->getTerminator())->getNumSuccessors()>1)||curInst->getOpcode()==2)){
					for (int j = 0; j<curBlock->getTerminator()->getNumSuccessors(); j++){
						//Get the destination of the call
						BasicBlock* nextBlock = curBlock->getTerminator()->getSuccessor(j);
						Instruction* nextInst = nextBlock->getFirstNonPHI();

						//Get index of the instruction
						int nextInstIndex = instructionIndex[nextInst];

						for (int k = 0; k<numDef; k++){
							//Copy the reach definitions
							if (reachDef[i*numDef+k] > 0){
								if (reachDef[nextInstIndex*numDef+k] < 1){ 
									changedFlag = 1;	//mark  there was a change
									//Copy def
									reachDef[nextInstIndex*numDef+k] = basicBlockIndex[curBlock] + 1; 
								     
									std::set<int> newKill;	//set of defs killed

								     	//check for killed def
									for (int d = 0; d < numDef;d++){
										//if a diff def for same variable, and both reach
										if (d!=k && instructionDefIndex[d]->def==instructionDefIndex[k]->def && reachDef[nextInstIndex*numDef+d]>0){
											//if they are from diff blocks, then it is killed
											if (reachDef[nextInstIndex*numDef+d] != reachDef[nextInstIndex*numDef+k]){
												killedFlag = 1;
											}

										       	newKill.insert(d);	//insert it as newly killed
										  }
									}
								     
									//if there is a def killed, add the intial that triggered 
								     	if (killedFlag){
										killedFlag = 0;		//reset flag

								          	std::set<int> currentKill = killedDef[nextBlock];	//get set
										
										//Add newly killed
								         	currentKill.insert(k);
										currentKill.insert(newKill.begin(), newKill.end());
								          	
										killedDef[nextBlock] = currentKill;			//Add back
								     	}
								}
							}
						}

						//If there was a change restart analysis earlier - add to procset
						if (changedFlag){
							changedFlag = 0;	//reset flag

							//if modified an earlier instruction, go back
							if (i>nextInstIndex){
								i = nextInstIndex;
							}

							//Modify def analysis based on moving back
							for (curDef = 0; curDef < numDef; curDef++){
								if(instructionDefIndex[curDef]->instructNum > i){
									curDef--;
									break;
								}
							}

							//go back to new successor block if backwards
							if (i>nextInstIndex){
								break;
							}
						}

					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////USED DEF ANALYSIS//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int curInstIndex = 0;
			//Go through each instruction
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
				if (i->getOpcode()==27){		//Is a load instruction
					std::set<int> defsUsed;
					//Go throuch reaching defs
					for (int d = 0 ;d<numDef; d++){
						//if the variable used has multiple reachinf defs, insert them
						if (reachDef[curInstIndex*numDef + d] > 0 && instructionDefIndex[d]->def == i->getOperand(0)->getName()){
							defsUsed.insert(d);		//add to used
						}
					}
					//if there are mutliple reach defs, then add to used defs list
					if (defsUsed.size()>1){
						std::set<int> currentUsed = usedDef[i->getParent()];
						currentUsed.insert(defsUsed.begin(), defsUsed.end());
						usedDef[i->getParent()] = currentUsed;
					}

				}
				curInstIndex++;
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////INFLUENCED NODE//////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//Go through each block
			for (Function::iterator i = allblocks.begin(); i != allblocks.end(); i++){	
				//if it has mutliple defs that it killed
				if (killedDef[i].size() > 0){
					//Go through each block and look for a path
					for (Function::iterator j = allblocks.begin(); j != allblocks.end(); j++){
						//Get indexes for block
						int sourceBlock = basicBlockIndex[i];
						int destBlock = basicBlockIndex[j];

						if (usedDef[j].size() > 0){
							//If they are different blocks and one source reaches dest or the same block
							if ((dist[sourceBlock*numBlock + destBlock]>0 && dist[sourceBlock*numBlock + destBlock]<100000000) || sourceBlock==destBlock){
								//Go through the killed defs for source block
								for (std::set<int>::iterator k = killedDef[i].begin(); k != killedDef[i].end(); ++k){
									int killed = *k;
					
									//GO through used defs for dest blocks
									for (std::set<int>::iterator m = usedDef[j].begin(); m != usedDef[j].end(); ++m){
										int used = *m;

										//if there is an interesection between killed and used, dest is influenced
										if (used==killed){
											std::set<BasicBlock*> influencedBlocks = influencedNode[i];
											influencedBlocks.insert(j);
											influencedNode[i] = influencedBlocks;
										}
									}
								}
							}
						}		
					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////ROI//////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int maxSize = 10000000;
			//int 			
			for (std::map<BasicBlock*, std::set<BasicBlock*> >::iterator i = ROI.begin(); i != ROI.end(); ++i){
				int size = i->second.size();
			}
			
			int ROIFlag = 1;			
			//Go through all blocks
			for (Function::iterator i = allblocks.begin(); i != allblocks.end() ; i++){
				int sourceBlock = basicBlockIndex[i];	//Initial block
	
				//GO through influenced blocks for each blocks
				for (std::set<BasicBlock*>::iterator j = influencedNode[i].begin(); j != influencedNode[i].end(); ++j){ 
					int endBlock = basicBlockIndex[*j]; 	//last block

					std::set<BasicBlock*> curROI;
					//Go through all the blocks and set as an intermediate block
					for (Function::iterator k = allblocks.begin(); (k != allblocks.end()) && ROIFlag==1; k++){	
						int intermediateBlock = basicBlockIndex[k];

						//if source reaches intermediate, and intermediate reaches dest, then in ROI
						if ((dist[sourceBlock*numBlock+intermediateBlock]>0 && dist[sourceBlock*numBlock+intermediateBlock]<1000000000)|| sourceBlock==intermediateBlock){ 
							if ((dist[intermediateBlock*numBlock+endBlock]>0 && dist[intermediateBlock*numBlock+endBlock]<1000000000)|| endBlock==intermediateBlock){
								curROI.insert(k);	
							}
						}	
					}

					//Insert into list of ROI
					if (curROI.size()>0){
						ROI[i] =curROI;
						//ROIFlag = 0;
						//break;			//FIX
					}
				}
				
				//if (ROI[i].size()>1){		//FIX
				//	break;			//FIX
				//}

			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////REPLICATING//////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//Go through all the ROI sets and clone them		
			for (std::map<BasicBlock*, std::set<BasicBlock*> >::iterator i = ROI.begin(); i != ROI.end(); ++i){

				//Count number of predecessor blocks
				int sourceBlock = basicBlockIndex[i->first];	//get index of top of ROI block
				int numPred = 0;
				for (int j = 0; j<numBlock; j++){
					if (dist[j*numBlock + sourceBlock]==1){
						numPred++;	//Increment
					}
				}

				//Create 1 for each predecessor
				for (int k = 1; k<numPred; k++){

					std::vector<BasicBlock*> originalROI;				
					std::vector<BasicBlock*> clonedROI;
					std::vector<instTranslation*> newTranslations;

					//Go through a specific set of ROI blocks
					for (std::set<BasicBlock*>::iterator j=(i->second).begin(); j!=(i->second).end(); ++j){

						BasicBlock *cloneBB = BasicBlock::Create((*j)->getContext(), Twine((*j)->getName() + "clone"), &F);
						//Go through instructions for each block
						for (BasicBlock::iterator m = (*j)->begin(); m!=(*j)->end(); ++m) {
							//clone instruction     
							Instruction *cloneInst = m->clone();
							if (m->hasName()){
								cloneInst->setName(m->getName() + "clone");
							}

							//Insert name translation
							instTranslation* curInstTranlate = new instTranslation(m, cloneInst);
							newTranslations.insert(newTranslations.end(), curInstTranlate);

							cloneBB->getInstList().push_back(cloneInst);
						}
						//Add cloned BB
						clonedROI.insert(clonedROI.end(), cloneBB);
						originalROI.insert(originalROI.end(), *j);

					}
					//Map orininal to cloned
					cloned[clonedROI] = originalROI;
					headCloned[clonedROI] = i->first;
					renameBlock[clonedROI] = newTranslations;
				}
			}

			//Fix up names
			//Go throuch each clone
			for (std::map<std::vector<BasicBlock*>, std::vector<instTranslation*> >::iterator i = renameBlock.begin(); i!=renameBlock.end(); ++i){
				//Go throuch each block in clone
				for (std::vector<BasicBlock*>::const_iterator j=(i->first).begin(); j!=(i->first).end(); ++j){
					//Go throuch each instruction					
					for (BasicBlock::iterator k = (*j)->begin(); k!=(*j)->end(); ++k) {
						//Go throuch each operand in each instruction
						for (int m = 0; m<k->getNumOperands() ;m++){
							//Go through each rename
							for (int n = 0; n<i->second.size();n++){
								instTranslation* instFixing = i->second[n];
								//if refer to old, replace
								if (k->getOperand(m)==instFixing->oldInst){
									k->setOperand(m,instFixing->newInst);
								}
							}
						}
					}

				}
			}

			//Go through cloned and fix up pointers
			for (std::map<std::vector<BasicBlock*>, std::vector<BasicBlock*> >::iterator i = cloned.begin(); i!=cloned.end(); ++i){
				for (std::vector<BasicBlock*>::const_iterator j=(i->first).begin(); j!=(i->first).end(); ++j){
					//Fix up terminator pointers
					for (int k = 0; k<(*j)->getTerminator()->getNumSuccessors(); k++){
						//Get the destination of the call
						BasicBlock* nextBlock = (*j)->getTerminator()->getSuccessor(k);

						//Try to find the block within the ROI
						std::vector<BasicBlock*>::iterator it;
						it = std::find((i->second).begin(),(i->second).end(), nextBlock);

						//If it is found, we have to redirect it
						if (it!=(i->second).end()){
							//cast as branch
							BranchInst* bi = dyn_cast<BranchInst>((*j)->getTerminator());
							if (bi){
								//get next block in clone and set as successor
								BasicBlock* cloneNextBlock = i->first[it - (i->second).begin()];
								bi->setSuccessor (k, cloneNextBlock);
							}
						}
					}				
				}
			}

			//Fix up predecessor  pointers
			while(cloned.size()>0){
				//Go through each ROI
				for (std::map<std::vector<BasicBlock*>, std::vector<BasicBlock*> >::iterator i = cloned.begin(); i!=cloned.end(); ++i){
					std::vector<BasicBlock*> clonedROI = i->first;
					std::vector<BasicBlock*> originalROI = i->second;

					//Get information about head of basic block	
					BasicBlock* headBlock = headCloned[i->first];
					int headBlockIndex = basicBlockIndex[headBlock];

					//Find the predecessors of block
					int numPred = 0;
					for (int j = 0; j<numBlock; j++){
						if (dist[j*numBlock + headBlockIndex]==1){
							numPred++;	//Increment
							//First predecessor can just use the original
							if (numPred==1){
								continue;
							}

							cloningFlag = 1;

							//Get cloned head block
							BasicBlock* cloneHeadBlock;
							std::vector<BasicBlock*>::iterator it;
							it = std::find(originalROI.begin(),originalROI.end(), headBlock);
							if (it!=originalROI.end()){
								//get next block in clone and set as successor
								cloneHeadBlock = clonedROI[it - originalROI.begin()];
							}


							//Get the previous block
							BasicBlock* prevBlock = basicBlockReverseIndex[j];
							//Go through the successors for the prdedecessor block
							for (int k = 0; k<prevBlock->getTerminator()->getNumSuccessors(); k++){
								//Get the destination of the call and check if dest is head
								BasicBlock* nextBlock = prevBlock->getTerminator()->getSuccessor(k);
								if (nextBlock!=headBlock){
									continue;
								}

								//cast as branch
								BranchInst* bi = dyn_cast<BranchInst>(prevBlock->getTerminator());
								if (bi){
									//get head block in clone and set as successor
									bi->setSuccessor (k, cloneHeadBlock);
									
									//Remove from maps
									cloned.erase(clonedROI);
									headCloned.erase(clonedROI);
									break;
								}						
							}
						}

						//Go through all clones
						for (std::map<std::vector<BasicBlock*>, std::vector<BasicBlock*> >::iterator k = cloned.begin(); k!=cloned.end(); ++k){ 
							//Find another clone for same blocks
							if (k->second==originalROI){
								clonedROI = k->first;
								break; 
							}
						}


					}
				}
			}
		}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			std::map<std::vector<int>, int> hashTable;		//hold relation between expression and id
			std::map<Value*, int> valueID;		//memory location and id
			std::map<int, std::vector<Value*> > reverseValueID;		//id to memory locations
			std::map<Value*, std::set<int> > valueLookup;		//hold relation between memory and expressions
			std::map<int, std::vector<int> > reverseHashTable;		//hold relation between expression and id


			//Queue of blocks
			set<BasicBlock*> visited;
			queue<BasicBlock*> nextBlocks;
			nextBlocks.push(&F.getEntryBlock());

			int ID = 1;

			//Visit until nore more blocks left
			while(!nextBlocks.empty()){
				//Clear entries fot gvn
				hashTable.clear();
				valueID.clear();
				reverseValueID.clear();
				valueLookup.clear();
				reverseHashTable.clear();	

				//Get next block
				BasicBlock* block = nextBlocks.front();
				nextBlocks.pop();

				//If already have gone to this block, skip it
				if(visited.find(block) != visited.end()) continue;
				visited.insert(block);

				int curID;
				std::vector<int> curInstComboID;
				std::vector<Instruction*> curInstCombo;

				//Visit the instructions
				for(BasicBlock::iterator i = block->begin(), ei = block->end(); i != ei; ++i){

					//if it is a store instruction
					if ((&*i)!=NULL){
						if (StoreInst* storeInst = dyn_cast<StoreInst>(i)){
							if(storeInst->getPointerOperand()->getName()!=""){
								//If value store is a constant
								if (isa<Constant>(storeInst->getValueOperand())){

									//Insert into ValueID table
									if (valueID[storeInst->getValueOperand()]!=0){		//already in value table
										curID = valueID[storeInst->getValueOperand()];
									}else{							//not in table
										curID = ID++;	//increment ID
									}

									//List as a current instruction
									curInstComboID.clear();
									curInstCombo.clear();
									curInstComboID.insert(curInstComboID.end(), curID);

									//Update ValueID Table
									valueID[storeInst->getValueOperand()] = curID;
								}
								int deleteFlag = 0;	//flag to hold info about deletions
								int sizeFlag = 0;	//flag to hold info about size

								//Reorganize elements to ensure that similar expression get same value #
								if (curInstComboID.size()==3){
									sizeFlag = 1;
									//Smaller number first
									if (curInstComboID[0]>curInstComboID[1]){
										int tempValue = curInstComboID[1];
										curInstComboID[1] = curInstComboID[0];
										curInstComboID[0] = tempValue;
									}
								}


								//Check Hash table for 
								if (hashTable[curInstComboID]!=0){		//already in hash table
									curID = hashTable[curInstComboID];
									deleteFlag = 1;
								}else{							//not in table
									curID = ID++;	//Increment ID
								}

								if (curInstComboID.size()==1){
									curID = curInstComboID[0];
								}


								if (deleteFlag && sizeFlag && reverseValueID[curID].size()>0){
	
									//Create new instructions as replacements
									LoadInst *replacementLoad = new LoadInst(reverseValueID[curID][0], "GVN", storeInst);
									replacementLoad->setAlignment(4);
									StoreInst *replacementStore = new StoreInst(replacementLoad, storeInst->getPointerOperand(), storeInst);
									replacementStore->setAlignment(4);
									
									//Remove old instructions
									i++;
									storeInst->eraseFromParent();
									if (curInstCombo.size()==3){
										curInstCombo[2]->eraseFromParent();
									}
									curInstCombo[1]->eraseFromParent();	
									curInstCombo[0]->eraseFromParent();	

									//change pointers for ease of use
									storeInst = replacementStore;

								}

								//Kill all values effected
								for (std::set<int>::iterator j = valueLookup[storeInst->getPointerOperand()].begin(); j != valueLookup[storeInst->getPointerOperand()].end(); ++j){
									//Remove them from hash table
									hashTable.erase(reverseHashTable[*j]);

								}
								valueLookup[storeInst->getPointerOperand()].clear();
								//Fix reverse lookup
								int oldID = valueID[storeInst->getPointerOperand()];
								reverseValueID[oldID].erase(std::remove(reverseValueID[oldID].begin(), reverseValueID[oldID].end(), storeInst->getPointerOperand()), reverseValueID[oldID].end());


								//Insert into ValueID table
								valueID[storeInst->getPointerOperand()] = curID;
								//Add to reverse look up table
								reverseValueID[curID].insert(reverseValueID[curID].end(), storeInst->getPointerOperand());
								//Insert into hash table
								hashTable[curInstComboID] = curID;
								reverseHashTable[curID] = curInstComboID;
								//Reverse look up of var use
								for (int j = 0; j<(curInstCombo.size());j++){
 									if (LoadInst* loadInst = dyn_cast<LoadInst>(curInstCombo[j])){
										valueLookup[loadInst->getPointerOperand()].insert(curID);
									}
								}
			
								//Get ready for next instruction
								curInstCombo.clear();
								curInstComboID.clear();
							}
						}
						//if it is a store instruction
						else if (LoadInst* loadInst = dyn_cast<LoadInst>(i)){
							//Clear information about current instruction if something broke
							if (curInstComboID.size()>1){
								curInstComboID.clear();
								curInstCombo.clear();
							}

							//Get information about components
							Value* instValue = loadInst->getPointerOperand();
							int instID = valueID[instValue];

							//Insert info about ongoing instruction
							curInstComboID.insert(curInstComboID.end(), instID);
							curInstCombo.insert(curInstCombo.end(), &*i);
						}
						//if operation
						else if (TerminatorInst* termInst = dyn_cast<TerminatorInst>(i)){
							int numSucc = termInst->getNumSuccessors();
							for(int i = 0; i < numSucc; i++){
								nextBlocks.push(termInst->getSuccessor(i));
							}
						}else if (ICmpInst* compareInst = dyn_cast<ICmpInst>(i)){
							int valChecked = valueID[compareInst->getOperand(0)];	//get the value being checked
							int bound = valueID[compareInst->getOperand(1)];		//get the bound compared
							llvm::CmpInst::Predicate comparison = compareInst->getSignedPredicate();// equality
						
							//Try combo of values to see if a particular variation reaches
							for (std::vector<Value*>::iterator itr = reverseValueID[valChecked].begin(); itr != reverseValueID[valChecked].end(); ++itr){
								for (std::vector<Value*>::iterator it = reverseValueID[bound].begin(); it != reverseValueID[bound].end(); ++it){
									ICmpInst* testCheck =  new ICmpInst(compareInst, comparison,*itr, *it, Twine("Test"));
									if (1/*match reaching icmp*/){
										//if there is a match, remove compare instruction and branch
										testCheck->eraseFromParent();	//Erase instruction instruction

										//Go to next instruction and check if 
										i++;
										if (BranchInst* branchAfterCheck = dyn_cast<BranchInst>(i)){
											if (i->getName().find("CmpTest",0) && branchAfterCheck->getNumSuccessors()==2){

												BasicBlock *nextBlock = branchAfterCheck->getSuccessor(0);
												BasicBlock *errorBlock = branchAfterCheck->getSuccessor(1);

												int deleteBlock = 0;
												if (errorBlock->getSinglePredecessor()){
													deleteBlock = 1;		
												}

												BranchInst::Create(nextBlock, branchAfterCheck->getParent());
												branchAfterCheck->eraseFromParent(); //Remove the

												//if exit block only has 1 predecessor
												if (deleteBlock){
													errorBlock->eraseFromParent();
												}

												//Add to block to examine and go to next block
												nextBlocks.push(nextBlock);
												break;
											}

										}

										compareInst->eraseFromParent();	//Erase

									}else{
										//if there is no match, just erase the new instruction
										testCheck->eraseFromParent();
									}
								}
							}

errs()<<"asd\n";
						}else{	
							if (i->isBinaryOp()){		//binary operation - add, sub, etc.
								//Check if an operand is a constant
								for (int j = 0; j<i->getNumOperands(); j++){
									//If value used is a constant
									if (isa<Constant>(i->getOperand(j))){
										//Insert into ValueID table
										if (valueID[i->getOperand(j)]!=0){	//not in table
											curID = valueID[i->getOperand(j)];
										}else{					//in table
											curID = ID++;	//Increment ID
										}

										//List as a current instruction
										curInstComboID.insert(curInstComboID.end(), curID);

										//Update ValueID Table
										valueID[i->getOperand(j)] = curID;
									}
								}


								//Get Operand
								int instOp = i->getOpcode();

								//Insert info about ongoing instruction
								curInstComboID.insert(curInstComboID.end(), i->getOpcode());
								curInstCombo.insert(curInstCombo.end(), &*i);
							}
						}
					}
				}


			}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//Print Hash Table
			errs()<<"Hash Table\n";
			for (std::map<std::vector<int>, int>::iterator itr = hashTable.begin(); itr != hashTable.end(); ++itr){
			   	errs() << "id:" << itr->second<<" set:";
				for (std::vector<int>::const_iterator it=(itr->first).begin(); it!=(itr->first).end(); ++it){
				   	errs() << *it<<"-";
				}
				errs()<<"\n";
			}

			//Print Value Table
			errs()<<"\nValue Table\n";
			for (std::map<Value*, int>::iterator itr = valueID.begin(); itr != valueID.end(); ++itr){
			   	errs() << "id:" << itr->second<<" Value:";
				if (isa<Constant>(itr->first)){
			   		errs() <<*itr->first;
				}else{
			   		errs() <<itr->first->getName();
				}
				errs()<<"\n";
			}

			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				errs()<<*i<<'\n';
   			}


			return false;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		  	AU.addRequired<LoopInfo>();		//add request	
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


