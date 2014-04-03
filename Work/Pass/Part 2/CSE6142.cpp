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

		struct Output
		{
			set<Value*> outSet;
			map<Value*, BasicBlock*> outSrc;
		};

		map<Value*, Value*> arraySizeMap;
		set<BasicBlock*> visited;

		map<BasicBlock*, Output* > outputs;
		map<BasicBlock*, set<Value*>* > genSet;
		map<BasicBlock*, Output* > inSet;
		map<BasicBlock*, set<BasicBlock*> > pred;

		set<Value*>* backwards(Output* output, BasicBlock* block)
		{
			set<Value*>* S = new set<Value*>();

			set<Value*>* gen = genSet[block];
			//errs() << "backwards: " << output->outSet.size() << "\n";

			//O(n^2) loop to check for matching compares
			for(set<Value*>::iterator itr = output->outSet.begin(); itr != output->outSet.end(); itr++)
			{
				CmpInst* inst = dyn_cast<CmpInst>(*itr);

				//errs() << gen->size() << "\n";
				bool conflict = false;
				for(set<Value*>::iterator localItr = gen->begin(); localItr != gen->end(); localItr++)
				{
					CmpInst* localInst = dyn_cast<CmpInst>(*localItr);

					errs() << *localInst << " vs " << *inst << "\n";

					//Oper 0 is what the index is
					//Oper 1 is the bound we are checking

					//Are we checking the same variable
					if(localInst->getOperand(0) == inst->getOperand(0))
					{
						if(localInst->getPredicate() == inst->getPredicate())
						{
							if(localInst->getOperand(1) == inst->getOperand(1))
								errs() << "Matching = " << *localInst << "\n";
							else
							{
								errs() << "Conflict\n";
								conflict = true;
							}
						}
					}
				}

				if(!conflict) S->insert(*itr);
			}

			errs() << "S size: " << S->size() << "\n";
			return S;
		}

		void calculateSets(set<BasicBlock*>* term)
		{
			queue<BasicBlock*> toVisit;

			for(set<BasicBlock*>::iterator itr = term->begin(); itr != term->end(); itr++)
				toVisit.push(*itr);
			set<BasicBlock*> visited;

			while(!toVisit.empty())
			{
				BasicBlock* block = toVisit.front();
				toVisit.pop();

				if(visited.find(block) != visited.end()) continue;

				//Retrieve genset and pred
				set<Value*>* gen = genSet[block];
				set<BasicBlock*>* predecessors = &pred[block];
				Output* outset = outputs[block];
				Output* inset = inSet[block];


				if(inset == NULL)
				{
					//errs() << "Creating inset for block: " << block->getName() << "\n";
					inset = new Output();
					inSet[block] = inset;
				}
				if(outset == NULL)
				{
					//errs() << "Creating outset for block: " << block->getName() << "\n";
					outset = new Output();
					outputs[block] = outset;
				}

				//Get successors
				TerminatorInst* termInst = block->getTerminator();
				int numSucc = termInst->getNumSuccessors();
				set<BasicBlock*> successors;
				for(int i = 0; i < numSucc; i++) successors.insert(termInst->getSuccessor(i));

				//Clear sets
				inset->outSet.clear();
				inset->outSrc.clear();
				outset->outSet.clear();
				outset->outSrc.clear();

				//Create c_out set
				bool isReady = true;
				for(set<BasicBlock*>::iterator itr = successors.begin(); itr != successors.end(); itr++)
				{
					Output* succ = inSet[*itr];
					if(succ == NULL)
					{
						//errs() << "ERROR(" << block->getName() << "): Null inset found for block: " << (*itr)->getName() << "\n";
						//continue;
						isReady = false;
						break;
					}
					//Loop through successor values
					for(set<Value*>::iterator comp = succ->outSet.begin(); comp != succ->outSet.end(); comp++)
					{
						if(itr == successors.begin())
						{
							outset->outSet.insert(*comp);
							outset->outSrc[*comp] = succ->outSrc[*comp];
						}
						else
						{
							set<Value*> toRemove;

							//See if the comparison is in the c_in set
							for(set<Value*>::iterator outItr = outset->outSet.begin(); outItr != outset->outSet.end(); outItr++)
							{
								if(succ->outSet.find(*outItr) == succ->outSet.end())
									toRemove.insert(*outItr);
							}

							for(set<Value*>::iterator outItr = toRemove.begin(); outItr != toRemove.end(); outItr++)
							{
								outset->outSet.erase(*outItr);
								outset->outSrc.erase(*outItr);
							}
						}
					}
				}
				if(!isReady) continue;
				else visited.insert(block);

				errs() << block->getName() << "\n";

				errs() << "Gen(" << gen << "): " << gen->size() << "\n";
				errs() << "OutSet size: " << outset->outSet.size() << "\n";

				set<Value*>* S = backwards(outset, block);

				//Add genset to c_in
				for(set<Value*>::iterator itr = gen->begin(); itr != gen->end(); itr++)
				{
					inset->outSet.insert(*itr);
					inset->outSrc[*itr] = block;
				}
				//Add backward() return
				for(set<Value*>::iterator itr = S->begin(); itr != S->end(); itr++)
				{
					inset->outSet.insert(*itr);
					inset->outSrc[*itr] = block;
				}
				//errs() << "Gen size: " << gen->size() << "\n";
				errs() << "InSet size: " << inset->outSet.size() << "\n-------------------------\n";

				//if(predecessors->size() > 1)
				//errs() << "size: " << predecessors->size() << "\n";

				//Add predecessors
				for(set<BasicBlock*>::iterator itr = predecessors->begin(); itr != predecessors->end(); itr++)
				{
					//errs() << block->getName() << " -> " << (*itr)->getName() << "\n";
					toVisit.push(*itr);
				}
				
			}
		}

		virtual bool runOnFunction(Function &F){

			//Queue of blocks
			queue<BasicBlock*> nextBlocks;
			nextBlocks.push(&F.getEntryBlock());

			set<BasicBlock*> lastBlock;

			set<BasicBlock*> visited;

			//Visit until nore more blocks left
			while(!nextBlocks.empty()){
				//Get next block
				BasicBlock* block = nextBlocks.front();
				nextBlocks.pop();

				//If already have gone to this block, skip it
				if(visited.find(block) != visited.end()) continue;
				visited.insert(block);

				//Gen set
				set<Value*>* c_gen = genSet[block];

				if(c_gen == NULL)
				{
					c_gen = new set<Value*>();
					genSet[block] = c_gen;
				}

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
							ConstantInt* newValue = llvm::ConstantInt::get(llvm::IntegerType::get(block->getContext(), 64),arraySize,false);
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

								//errs() << "Runtime\n";

								//Create a new exit block
								BasicBlock* errorBlock = BasicBlock::Create(block->getContext(), Twine(block->getName() + "exit"), &F);
								ReturnInst::Create(block->getContext(), 
									ConstantInt::get(IntegerType::get(block->getContext(), 32), 0), errorBlock);

									
								//Check to see if the index is less than the size
								ICmpInst* upperBoundCheck =  new ICmpInst(getInst, CmpInst::ICMP_SLT, getInst->getOperand(indexOperand), sizeArray, Twine("CmpTestUpper"));
								c_gen->insert(upperBoundCheck);
								BasicBlock* followingBlock = block->splitBasicBlock(inst, Twine(block->getName() + "valid"));

								//Check to see if index is negative
								BasicBlock* secondCheckBlock = BasicBlock::Create(block->getContext(), Twine(block->getName() + "lowerBoundCheck"), &F);
								ConstantInt* zeroValue = llvm::ConstantInt::get(llvm::IntegerType::get(block->getContext(),   64),-1,false);
								ICmpInst* lowerBoundCheck =  new ICmpInst(*secondCheckBlock, CmpInst::ICMP_SGT, getInst->getOperand(indexOperand), zeroValue, Twine("CmpTestLower"));
								c_gen = new set<Value*>();
								genSet[secondCheckBlock] = c_gen;
								c_gen->insert(lowerBoundCheck);
								BranchInst::Create(followingBlock, errorBlock, lowerBoundCheck, secondCheckBlock);


								//Modify exisiting block
								block->getTerminator()->eraseFromParent(); //Remove the temporary terminator
								//Add our own terminator condition
								BranchInst::Create(secondCheckBlock, errorBlock, upperBoundCheck, block);

								//nextBlocks.push(followingBlock);
								nextBlocks.push(secondCheckBlock);

								//Move all the predecessor links to the head block
								TerminatorInst* splitTerm = followingBlock->getTerminator();
								int numSuccessor = splitTerm->getNumSuccessors();
								for(int i = 0; i < numSuccessor; i++)
									if(pred[splitTerm->getSuccessor(i)].erase(block) > 0) errs() << "SDFSDF\n";

								//pred[followingBlock].insert(secondCheckBlock);
								pred[secondCheckBlock].insert(block);
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
							BasicBlock* term = termInst->getSuccessor(i);
							nextBlocks.push(term);
							pred[term].insert(block);
							//errs() << block->getName() << " -> " << term->getName() << "\n";
						}

						if(numSucc == 0)
						{
							lastBlock.insert(block);
						}
					}
				}
				//errs() << genSet.size() << " : " << genSet[block]->size() << " : " << c_gen << "\n";

			}

			//Queue of blocks
			nextBlocks.push(&F.getEntryBlock());
			visited.clear();
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
					if (BranchInst* branchAfterCheck = dyn_cast<BranchInst>(inst)){
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
								lastBlock.erase(errorBlock);
								errorBlock->eraseFromParent();
							}
							
							//Add to block to examine and go to next block
							nextBlocks.push(nextBlock);
							break;
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

			calculateSets(&lastBlock);


			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				//errs()<<*i<<'\n';
   			}


			return false;
		}
	};

	char CSE6142::ID = 0;
	static RegisterPass<CSE6142> X("CSE6142", "");
}
