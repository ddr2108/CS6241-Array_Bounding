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
			std::map<int, Instruction*> instructionReverseIndex;
			std::map<int, defInstruct*> instructionDefIndex;

			int* reachDef = NULL;						//Hold reaching def for each instruction
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
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
				instructionReverseIndex[numInst] = &*i;
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
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			std::map<std::vector<int>, int> hashTable;		//hold relation between expression and id
			std::map<int, std::vector<int> > reverseHashTable;		//hold relation between expression and id

			std::map<std::set<defInstruct*>, int> phiTable;		//hold relation between phi expression and phi id

			std::map<Value*, int> valueID;		//memory location and id
			std::map<int, std::vector<Value*> > reverseValueID;		//id to memory locations




			//Queue of blocks
			set<BasicBlock*> visited;
			queue<BasicBlock*> nextBlocks;
			nextBlocks.push(&F.getEntryBlock());

			int ID = 1;
			int phiID = -1;

			//Visit until nore more blocks left
			while(!nextBlocks.empty()){

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

								errs()<<curInstComboID[0]<<curInstComboID[1]<<curInstComboID[2]<<curInstComboID.size()<<"\n";
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


								//Check Hash table to see if already exists
								if (hashTable[curInstComboID]!=0){		//already in hash table
									curID = hashTable[curInstComboID];
									deleteFlag = 1;
								}else{							//not in table
									curID = ID++;	//Increment ID
								}

								//If it is an eqaulity, just give id of the other element
								if (curInstComboID.size()==1){
									curID = curInstComboID[0];
								}


								if (deleteFlag && sizeFlag && reverseValueID[curID].size()>0){
	
									//Create new instructions as replacements
									StoreInst* storeInstWithValue = dyn_cast<StoreInst>(reverseValueID[curID][0]);		
									LoadInst *replacementLoad = new LoadInst(storeInstWithValue->getPointerOperand(), "GVN", storeInst);
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

								//Insert into ValueID table
								valueID[storeInst] = curID;
								//Add to reverse look up table
								reverseValueID[curID].insert(reverseValueID[curID].end(), storeInst);

								//Insert into hash table
								hashTable[curInstComboID] = curID;
								reverseHashTable[curID] = curInstComboID;
			
								//Get ready for next instruction
								curInstCombo.clear();
								curInstComboID.clear();
							}
						}
						//if it is a load instruction
						if (LoadInst* loadInst = dyn_cast<LoadInst>(i)){
							//Clear information about current instruction if something broke
							if (curInstComboID.size()>1){
								curInstComboID.clear();
								curInstCombo.clear();
							}

							int instID;

							//Get information about components
							Value* allocValue = loadInst->getPointerOperand();

							//Check if phi instruction needed
							std::set<defInstruct*> phiSet;
							defInstruct* firstReaching;
							for (int j = 0; j< numDef;j++){
								//Find all reaching for same var
								int reachDefIndex = instructionIndex[loadInst];
								if (reachDef[reachDefIndex*numDef + j]==1 && allocValue->getName()==instructionDefIndex[j]->def){
									phiSet.insert(instructionDefIndex[j]);
									firstReaching = instructionDefIndex[j];
								}
							}
							//Check if there are multiple reaching and thus phi needed
							if (phiSet.size()>1){		//needed
								//check if arleady exists
								if (phiTable[phiSet]==0){	//not in
									phiTable[phiSet] = phiID;
									instID = phiID--;
								}else{	//int
									instID = phiTable[phiSet];
								}
							}else{		//not needed
								instID = valueID[instructionReverseIndex[firstReaching->instructNum]];
							}		

							//Insert info about ongoing instruction
							curInstComboID.insert(curInstComboID.end(), instID);
							curInstCombo.insert(curInstCombo.end(), &*i);
						}
						//if operation
						if (TerminatorInst* termInst = dyn_cast<TerminatorInst>(i)){
							int numSucc = termInst->getNumSuccessors();
							for(int i = 0; i < numSucc; i++){
								nextBlocks.push(termInst->getSuccessor(i));
							}
						}
						//Compare instruction
						if (ICmpInst* compareInst = dyn_cast<ICmpInst>(i)){
/*							int valChecked = valueID[compareInst->getOperand(0)];	//get the value being checked
							int bound = valueID[compareInst->getOperand(1)];		//get the bound compared
							llvm::CmpInst::Predicate comparison = compareInst->getSignedPredicate();// equality
						
							//Try combo of values to see if a particular variation reaches
							for (std::vector<Value*>::iterator itr = reverseValueID[valChecked].begin(); itr != reverseValueID[valChecked].end(); ++itr){
								for (std::vector<Value*>::iterator it = reverseValueID[bound].begin(); it != reverseValueID[bound].end(); ++it){
									ICmpInst* testCheck =  new ICmpInst(compareInst, comparison,*itr, *it, Twine("Test"));
									if (1){
										//if there is a match, remove compare instruction and branch
										testCheck->eraseFromParent();	//Erase instruction
										compareInst->eraseFromParent();	//Erase instruction

										//Go to next instruction and check if 
										i++;
										if (BranchInst* branchAfterCheck = dyn_cast<BranchInst>(i)){
											if (branchAfterCheck->getNumSuccessors()==2){

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

									}else{
										//if there is no match, just erase the new instruction
										testCheck->eraseFromParent();
									}
								}
							}*/
						}

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
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////DEBUG////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/**/
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
/*
			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				errs()<<*i<<'\n';
   			}

			//Print Phi Table
			for (std::map<std::set<defInstruct*>, int>::iterator itr = phiTable.begin(); itr != phiTable.end(); ++itr){
			   	errs() << "id:" << itr->second<<" set:";
				for (std::set<defInstruct*>::const_iterator it=(itr->first).begin(); it!=(itr->first).end(); ++it){
				   	errs() << (*it)->lineNum<<"-";
				}
				errs()<<"\n";
			}*/
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

			return false;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		  	AU.addRequired<LoopInfo>();		//add request	
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


