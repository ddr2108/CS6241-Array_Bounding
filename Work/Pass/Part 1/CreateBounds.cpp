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
	struct CreateBounds : public FunctionPass
	{
		static char ID;
		CreateBounds() : FunctionPass(ID){}

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
						//if array
						if(alloc->isArrayAllocation()){
							arraySizeMap[alloc] = alloc->getOperand(0);
						}
						
						PointerType *pt = alloc->getType();
						//If it is an array and the previous if statement did not catch it
						if (ArrayType *at = dyn_cast<ArrayType>(pt->getElementType())){
							//get size							
							int arraySize = at->getNumElements();
							ConstantInt* newValue = llvm::ConstantInt::get(llvm::IntegerType::get(block->getContext(), 32),arraySize,false);
							//Store size
							arraySizeMap[alloc] = newValue;


						}
					}

					//An array element is being retrieved. We need to check if it's inbounds
					if(&*inst != &block->front()){
						if(GetElementPtrInst* getInst = dyn_cast<GetElementPtrInst>(inst)){
							//Get index into array
							int indexOperand = getInst->getNumIndices();
							llvm::ConstantInt* CI = dyn_cast<llvm::ConstantInt>(getInst->getOperand(indexOperand));
							
							//Get info about array
							Value *sizeArray = arraySizeMap[getInst->getOperand(0)];
							llvm::ConstantInt* CI2 = dyn_cast<llvm::ConstantInt>(sizeArray);

							if (CI==NULL || CI2==NULL) {		//Runtime analysis

								//Create a new exit block
								BasicBlock* errorBlock = BasicBlock::Create(block->getContext(), Twine(block->getName() + "exit"), &F);
								ReturnInst::Create(block->getContext(), 
									ConstantInt::get(IntegerType::get(block->getContext(), 32), 0), errorBlock);

									
								//Check to see if the index is less than the size
								ICmpInst* upperBoundCheck =  new ICmpInst(getInst, CmpInst::ICMP_SLT, getInst->getOperand(indexOperand), sizeArray, Twine("CmpTestUpper"));
								BasicBlock* followingBlock = block->splitBasicBlock(inst, Twine(block->getName() + "valid"));


								//Check to see if index is negative
								BasicBlock* secondCheckBlock = BasicBlock::Create(block->getContext(), Twine(block->getName() + "lowerBoundCheck"), &F);
								ConstantInt* zeroValue = llvm::ConstantInt::get(llvm::IntegerType::get(block->getContext(),   32),-1,false);												
								ICmpInst* lowerBoundCheck =  new ICmpInst(*secondCheckBlock, CmpInst::ICMP_SGT, getInst->getOperand(indexOperand), zeroValue, Twine("CmpTestLower"));
								BranchInst::Create(followingBlock, errorBlock, lowerBoundCheck, secondCheckBlock);



								//Modify exisiting block
								block->getTerminator()->eraseFromParent(); //Remove the temporary terminator
								//Add our own terminator condition
								BranchInst::Create(secondCheckBlock, errorBlock, upperBoundCheck, block);

								nextBlocks.push(followingBlock);
								break;
							}else{		//Static analysis - constant size and index
								
								int arrayIndex = CI->getZExtValue(); 	//Pull out the array index
								int arraySize = CI2->getZExtValue(); 	//Pull out the array index

								//Check size of array vs index
								if (arrayIndex>=arraySize || arrayIndex<0){

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

			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				//errs()<<*i<<'\n';
   			}


			return false;
		}
	};

	char CreateBounds::ID = 0;
	static RegisterPass<CreateBounds> X("CreateBounds", "");
}
