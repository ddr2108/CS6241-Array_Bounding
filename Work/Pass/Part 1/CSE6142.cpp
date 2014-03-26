#include "llvm/IR/Function.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include <map>
#include <set>
#include <queue>

using namespace llvm;
using std::map;
using std::set;
using std::queue;

namespace
{
	struct CSE6142 : public FunctionPass
	{
		static char ID;
		CSE6142() : FunctionPass(ID){}

		map<Value*, Value*> arraySizeMap;
		set<BasicBlock*> visited;

		virtual bool runOnFunction(Function &F){

			//Queue of blocks
			queue<BasicBlock*> nextBlocks;
			nextBlocks.push(&F.getEntryBlock());

			//Visit until nore more blocks left
			while(!nextBlocks.empty()){
				//Get next block
				BasicBlock* block = nextBlocks.front();
				nextBlocks.pop();

				//If already have gone to this block, skip it
				if(visited.find(block) != visited.end()) continue;
				visited.insert(block);

				//Visit the instructions
				for(BasicBlock::iterator inst = block->begin(); inst != block->end(); inst++){

					//if it is an allocate instruction
					if(AllocaInst* alloc = dyn_cast<AllocaInst>(inst)){

						PointerType *pt = alloc->getType();

						//If it is an array
						if (ArrayType *at = dyn_cast<ArrayType>(pt->getElementType())){
							//get size							
							int arraySize = at->getNumElements();
							ConstantInt* newValue = llvm::ConstantInt::get(llvm::IntegerType::get(block->getContext(), 64),arraySize,false);
							//Store size
							arraySizeMap[alloc] = newValue;
						}
					}

					//An array element is being retrieved. We need to check if it's inbounds
					if(&*inst != &block->front()){
						if(Instruction* getInst = dyn_cast<GetElementPtrInst>(inst)){
							//If the index is constant, static analysis should have caught it
							llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(getInst->getOperand(2));
							if (CI==NULL) {		//Runtime analysis

								//Get the defined size from the map
								Value *sizeArray = arraySizeMap[getInst->getOperand(0)];

								//Check to see if the index is less than the size
								ICmpInst* boundCheck = 
									new ICmpInst(getInst, CmpInst::ICMP_SLT, getInst->getOperand(2), 
									sizeArray, Twine("CmpTest"));
								BasicBlock* nextBlock = block->splitBasicBlock(inst, Twine(block->getName() + "valid"));
							
								//Create a new exit block
								BasicBlock* errorBlock = BasicBlock::Create(block->getContext(), 
									Twine(block->getName() + "exit"), &F);
								ReturnInst::Create(block->getContext(), 
									ConstantInt::get(IntegerType::get(block->getContext(), 32), 0), errorBlock);

								//Remove the temporary terminator
								block->getTerminator()->eraseFromParent();

								//Add our own terminator condition
								BranchInst::Create(nextBlock, errorBlock, boundCheck, block);

								//shouldBreak = true;
								nextBlocks.push(nextBlock);
								break;
							}else{		//Static analysis
								
								int arrayIndex = CI->getZExtValue(); 	//Pull out the array index

								//Get the defined size from the map
								Value *sizeArray = arraySizeMap[getInst->getOperand(0)];
								llvm::ConstantInt* CI2 = dyn_cast<llvm::ConstantInt>(sizeArray);
								int arraySize = CI2->getZExtValue(); 	//Pull out the array index

								//Check size of array vs index
								if (arrayIndex>=arraySize){

									//Get line number
									unsigned Line;
									if (MDNode *N = getInst->getMetadata("dbg")) {
										DILocation Loc(N);                     
										Line = Loc.getLineNumber();
									}

									//Print error
									errs()<<"Index outside of array bounds\n Line:"<<Line<<"\n Access index " <<arrayIndex<<" of array "<<getInst->getOperand(0)->getName()<<" of size "<<arraySize<<"\n\n";

								}				

							}

						}
					}

					//add new blocks to go to
					if(TerminatorInst* termInst = dyn_cast<TerminatorInst>(inst)){
						int numSucc = termInst->getNumSuccessors();
						for(int i = 0; i < numSucc; i++){
							nextBlocks.push(termInst->getSuccessor(i));
						}
					}
				}

			}

			return false;
		}
	};

	char CSE6142::ID = 0;
	static RegisterPass<CSE6142> X("CSE6142", "");
}
