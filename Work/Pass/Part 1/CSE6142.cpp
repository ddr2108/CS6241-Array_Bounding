#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
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

		virtual bool runOnFunction(Function &F)
		{
			queue<BasicBlock*> nextBlocks;
			nextBlocks.push(&F.getEntryBlock());

			while(!nextBlocks.empty())
			{
				BasicBlock* block = nextBlocks.front();
				nextBlocks.pop();

				if(visited.find(block) != visited.end()) continue;

				visited.insert(block);

				//bool shouldBreak = false;
				for(BasicBlock::iterator inst = block->begin(); inst != block->end(); inst++)
				{
					if(AllocaInst* alloc = dyn_cast<AllocaInst>(inst))
					{
						//Only map arrays
						if(alloc->isArrayAllocation())
						{
							AllocaInst* mapInst = new AllocaInst(llvm::IntegerType::get(block->getContext(), 64)
								, Twine("SizeMap"), inst);

							//errs() << *alloc->getOperand(0) << "\n";
							StoreInst* storeInst = new StoreInst(alloc->getOperand(0), mapInst, mapInst);
							mapInst->moveBefore(storeInst);
							errs() << *inst << "\n";

							arraySizeMap[alloc] = mapInst;
						}
					}

					//An array element is being retrieved. We need to check if it's inbounds
					if(&*inst != &block->front())
					if(Instruction* getInst = dyn_cast<GetElementPtrInst>(inst))
					{
						//Get the defined size from the map
						Value* maxSize = arraySizeMap[getInst->getOperand(0)];
						//errs() << *maxSize << "\n";

						//Convert the size from a pointer to an int
						Value* matchingType = new PtrToIntInst(maxSize, getInst->getOperand(1)->getType(), 
							Twine("PTR"), getInst);

						//errs() << *getInst->getOperand(1) << "\n";

						//Check to see if the index is less than the size
						ICmpInst* boundCheck = 
							new ICmpInst(getInst, CmpInst::ICMP_SGT, getInst->getOperand(1), 
							matchingType, Twine("CmpTest"));
						BasicBlock* nextBlock = block->splitBasicBlock(inst, Twine(block->getName() + "valid"));

						//Create a new exit block
						BasicBlock* errorBlock = BasicBlock::Create(block->getContext(), 
							Twine(block->getName() + "exit"), &F);
						ReturnInst::Create(block->getContext(), 
							ConstantInt::get(IntegerType::get(block->getContext(), 32), 0), errorBlock);
						errs() << *errorBlock << "\n";

						//Remove the temporary terminator
						block->getTerminator()->eraseFromParent();

						//Add our own terminator condition
						BranchInst::Create(nextBlock, errorBlock, boundCheck, block);

						//shouldBreak = true;
						nextBlocks.push(nextBlock);
						break;

						errs() << *boundCheck << "\n";
					}

					if(TerminatorInst* termInst = dyn_cast<TerminatorInst>(inst))
					{
						int numSucc = termInst->getNumSuccessors();
						for(int i = 0; i < numSucc; i++)
						{
							nextBlocks.push(termInst->getSuccessor(i));
						}
					}
				}
				//if(shouldBreak) break;
			}

			return false;
		}
	};

	char CSE6142::ID = 0;
	static RegisterPass<CSE6142> X("CSE6142", "");
}
