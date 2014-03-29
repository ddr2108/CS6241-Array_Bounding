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
			
			//Queue of blocks
			queue<BasicBlock*> blocksToOptimize;
			blocksToOptimize.push(&F.getEntryBlock());
			set<BasicBlock*> visitedOptimized;

			//Visit until nore more blocks left
			while(!blocksToOptimize.empty()){
				//Get next block
				BasicBlock* block = blocksToOptimize.front();
				blocksToOptimize.pop();

				//If already have gone to this block, skip it
				if(visitedOptimized.find(block) != visitedOptimized.end()) continue;
				visitedOptimized.insert(block);
			
				//Visit the instructions
				for(BasicBlock::iterator inst = block->begin(); inst != block->end(); inst++){

					//Check if it is comparison insturction
					if (ICmpInst* getInst = dyn_cast<ICmpInst>(inst)){
						int deleteFlag = 0;


						Value *valChecked = getInst->getOperand(0);		//get the value being checked
						Value *bound = getInst->getOperand(1);			//get the bound compared
						llvm::CmpInst::Predicate comparison = getInst->getSignedPredicate();		//get equality

						//go through reaching def		--////FIX based on reaching code
						for (int i = 0; i< numReaching ;i++){
							ICmpInst* reachingComparison = get();	//get the reaching def
						
							//Check if same comparison (ie both greater than, or both less than)
							if (reachingComparison->getSignedPredicate() != comparison){
								continue;
							}

							//Do some comparisons to see if delete if less than instructions
							if (comparison==CmpInst::ICMP_SLT){
								//if bounds are same
								if (bound==reachingComparison->getOperand(1)){
									//if the values compared are the same
									if (valChecked==reachingComparison->getOperand(0)){
										deleteFlag = 1;
										break;
									}
									//if both constants & new value is smaller
									if (ConstantInt* valNew = dyn_cast<ConstantInt>(valChecked)){
									if (ConstantInt* valOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(0))){
										if (valNew<=valOld){
											deleteFlag = 1;
											break;
										}
									}}	
								}else{
									//if bounds are same, must be both constants to compare
									if (ConstantInt* boundNew = dyn_cast<ConstantInt>(bound))
									if (ConstantInt* boundOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(1))){
										//if new bound is larger
										if (boundNew>=boundOld){
											//if the values compared are the same
											if (valChecked==reachingComparison->getOperand(0)){
												deleteFlag = 1;
												break;
											}
											//if both constants & new value is smaller
											if (ConstantInt* valNew = dyn_cast<ConstantInt>(valChecked))
											if (ConstantInt* valOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(0))){
												if (valNew<=valOld){
													deleteFlag = 1;
													break;
												}
											}	
										}
								
									}

								}

							}

							//Do some comparisons to see if delete if greater than instructions
							if (comparison==CmpInst::ICMP_SGT){
								//if bounds are same
								if (bound==reachingComparison->getOperand(1)){
									//if the values compared are the same
									if (valChecked==reachingComparison->getOperand(0)){
										deleteFlag = 1;
										break;
									}
									//if both constants & new value is smaller
									if (ConstantInt* valNew = dyn_cast<ConstantInt>(valChecked))
									if (ConstantInt* valOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(0))){
										if (valNew>=valOld){
											deleteFlag = 1;
											break;
										}
									}	
								}else{
									//if bounds are same, must be both constants to compare
									if (ConstantInt* boundNew = dyn_cast<ConstantInt>(bound))
									if (ConstantInt* boundOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(1))){
										//if new bound is larger
										if (boundNew<=boundOld){
											//if the values compared are the same
											if (valChecked==reachingComparison->getOperand(0)){
												deleteFlag = 1;
												break;
											}
											//if both constants & new value is smaller
											if (ConstantInt* valNew = dyn_cast<ConstantInt>(valChecked))
											if (ConstantInt* valOld = dyn_cast<ConstantInt>(reachingComparison->getOperand(0))){
												if (valNew>=valOld){
													deleteFlag = 1;
													break;
												}
											}	
										}
								
									}

								}
							}
						
						}
					
						if (deleteFlag){
							deleteFlag = 0;		//reset flag

							getInst->eraseFromParent();	//Erase instruction

							//Go to next instruction and check if 
							inst++;
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
										errorBlock->eraseFromParent();
									}
							
									//Add to block to examine and go to next block
									blocksToOptimize.push(nextBlock);
									break;
								}

							}
						}

					}
				
					//add new blocks to go to
					if(TerminatorInst* termInst = dyn_cast<TerminatorInst>(inst)){
						int numSucc = termInst->getNumSuccessors();
						for(int i = 0; i < numSucc; i++){
							blocksToOptimize.push(termInst->getSuccessor(i));
						}
					}
				}
			}

			return false;
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


