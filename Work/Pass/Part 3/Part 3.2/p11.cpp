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
			std::map<int, std::set<Value*> > reverseValueID;		//id to memory locations
			std::map<Value*, std::set<StringRef> > valueLookup;		//hold relation between memory and expressions

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
				std::vector<int> curInstCombo;

				//Visit the instructions
				for(BasicBlock::iterator i = block->begin(); i != block->end(); i++){

					//if it is a store instruction
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
								curInstCombo.clear();
								curInstCombo.insert(curInstCombo.end(), curID);

								//Update ValueID Table
								valueID[storeInst->getValueOperand()] = curID;
							}

							//Insert into Hash table
							if (hashTable[curInstCombo]!=0){		//already in hash table
								curID = hashTable[curInstCombo];
							}else{							//not in table
								curID = ID++;	//Increment ID
							}

							//Insert into ValueID table
							valueID[storeInst->getPointerOperand()] = curID;
							//Insert into hash table
							hashTable[curInstCombo] = curID;

							//Get ready for next instruction
							curInstCombo.clear();
						}
					}
					//if it is a store instruction
					else if (LoadInst* loadInst = dyn_cast<LoadInst>(i)){
						//Clear information about current instruction if something broke
						if (curInstCombo.size()>1){
							curInstCombo.clear();
						}

						//Get information about components
						Value* instValue = loadInst->getPointerOperand();
						int instID = valueID[instValue];

						//Insert info about ongoing instruction
						curInstCombo.insert(curInstCombo.end(), instID);
					}
					//if operation
					else{
						if (i->isBinaryOp()){		//binary operation - add, sub, etc.
							//Check if an operand is a constant
							for (int j = 1; j<i->getNumOperands(); j++){
								
								//If value used is a constant
								if (isa<Constant>(i->getOperand(j))){
									//Insert into ValueID table
									if (valueID[i->getOperand(j)]!=0){	//not in table
										curID = valueID[i->getOperand(j)];
									}else{					//in table
										curID = ID++;	//Increment ID
									}

									//List as a current instruction
									curInstCombo.insert(curInstCombo.end(), curID);

									//Update ValueID Table
									valueID[i->getOperand(j)] = curID;
								}
							}


							//Get Operand
							int instOp = i->getOpcode();

							//Insert info about ongoing instruction
							curInstCombo.insert(curInstCombo.end(), i->getOpcode());
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

			return false;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		  	AU.addRequired<LoopInfo>();		//add request	
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


