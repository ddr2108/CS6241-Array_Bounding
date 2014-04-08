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

	struct p11 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p11() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){

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
									errs()<<*j<<"\n";

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
						else{
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

/*			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				errs()<<*i<<'\n';
   			}
*/

			return false;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		  	AU.addRequired<LoopInfo>();		//add request	
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


