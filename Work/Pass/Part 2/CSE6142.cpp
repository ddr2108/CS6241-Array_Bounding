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

		enum state {UNCHANGED, UNKNOWN, INCREASED, DECREASED};

		struct Output
		{
			set<Value*> outSet;
			map<Value*, BasicBlock*> outSrc;
			map<Value*, state> outState;
		};

		map<Value*, Value*> arraySizeMap;
		set<BasicBlock*> visited;

		map<BasicBlock*, Output* > outputs;
		map<BasicBlock*, set<Value*>* > genSet;
		map<BasicBlock*, Output* > inSet;
		map<BasicBlock*, set<BasicBlock*> > pred;
		map<BasicBlock*, map<Value*, state> > stateChanges;

		state getState(StoreInst* inst)
		{
			state retn = UNCHANGED;

			Value* origInst = inst->getOperand(1);

			queue<Value*> evalList;
			evalList.push(inst->getOperand(0));

			//We will track if this variable was part of the equation, or just holds the value
			bool varModified = false;

			while(!evalList.empty())
			{
				Value* val = evalList.front();
				evalList.pop();

				if(Instruction* valInst = dyn_cast<Instruction>(val))
				{
					//Check to see how the variable is changing (Constants only)
					if(valInst->getOpcode() == Instruction::Add || valInst->getOpcode() == Instruction::Mul)
					{
						//If sub and add mix, we don't know the results
						if(retn == INCREASED || retn == UNCHANGED)
							retn = INCREASED;
					}
					if(valInst->getOpcode() == Instruction::Sub 
						|| valInst->getOpcode() == Instruction::SDiv || valInst->getOpcode() == Instruction::UDiv)
					{
						//If sub and add mix, we don't know the results
						if(retn == DECREASED || retn == UNCHANGED)
							retn = DECREASED;
					}

					//If there's a load inst, variables are involved
					if(LoadInst* load = dyn_cast<LoadInst>(valInst))
					{
						//Either the original variable was modified, or an unknown dynamic variable is involved
						if(load->getOperand(0) == origInst) varModified = true;
						else retn = UNKNOWN;
					}

					int numOp = valInst->getNumOperands();
					for(int i = 0; i < numOp; i++)
						evalList.push(valInst->getOperand(i));
				}
			}

			//We don't know what this value is in relation to the original variable
			if(!varModified) retn = UNKNOWN;

			errs() << retn << " : " << *inst << "\n";

			return retn;
		}

		Value* getBaseValue(Value* value)
		{
			Value* retn = value;
			while(Instruction* inst = dyn_cast<Instruction>(retn))
			{
				if(inst->getNumOperands() != 1)
					break;
				else if(!dyn_cast<CastInst>(inst) && !dyn_cast<LoadInst>(inst))
					break;
				else
					retn = inst->getOperand(0);
			}

			return retn;
		}

		set<Value*>* backwards(Output* output, BasicBlock* block, bool doRemove=false)
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
				map<Instruction*, Instruction*> toRemove;

				Value* op1 = getBaseValue(inst->getOperand(0));
				Value* op2 = getBaseValue(inst->getOperand(1));

				state changeStateOp1 = stateChanges[block][op1];
				state changeStateOp2 = stateChanges[block][op2];

				//See if this block killed one of the compare's operands
				if(changeStateOp1 != UNCHANGED || changeStateOp2 != UNCHANGED)
				{
					errs() << changeStateOp1 << " :: " << changeStateOp2 << "\n";
					switch(changeStateOp1)
					{
					case UNKNOWN:
						conflict = true;
						break;
					case INCREASED:
						if(inst->getPredicate() == CmpInst::ICMP_SLT)
						{
							errs() << "Killing upper\n";
							conflict = true;
						}
						break;
					case DECREASED:
						if(inst->getPredicate() == CmpInst::ICMP_SGT)
						{
							errs() << "Killing lower\n";
							conflict = true;
						}
						break;
					}
				}

				for(set<Value*>::iterator localItr = gen->begin(); localItr != gen->end(); localItr++)
				{
					CmpInst* localInst = dyn_cast<CmpInst>(*localItr);

					Value* localOp1 = getBaseValue(localInst->getOperand(0));
					Value* localOp2 = getBaseValue(localInst->getOperand(1));

					errs() << *localInst << " vs " << *inst << "\n";
					errs() << *op1 << " vs " << *localOp1 << "\n";

					//Oper 0 is what the index is
					//Oper 1 is the bound we are checking

					//Are we checking the same variable
					bool equalConst = false;
					ConstantInt* localConst = dyn_cast<ConstantInt>(localInst->getOperand(0));
					ConstantInt* prevConst = dyn_cast<ConstantInt>(inst->getOperand(0));

					//We count equivalent constants as being the same variable
					if(localConst != NULL && prevConst != NULL)
					{
						errs() << localConst->getZExtValue() << "\n";
						if(localConst->getZExtValue() == prevConst->getZExtValue()) equalConst = true;
					}

					if(localOp1 == op1 || equalConst)
					{
						if(localInst->getPredicate() == inst->getPredicate())
						{
							localConst = dyn_cast<ConstantInt>(localOp2);
							prevConst = dyn_cast<ConstantInt>(op2);


							if(localOp2 == op2)
							{
								errs() << "Matching = " << *localInst << "\n";
								toRemove[localInst] = inst;
							}
							else if(localInst->getPredicate() == CmpInst::ICMP_SLT)
							{
								errs() << "SLT\n";
								if(localConst == NULL) conflict = true;
								else if(prevConst == NULL) conflict = true;
								else if(prevConst->uge(localConst->getZExtValue()));
								else conflict = true;
							}
							else if(localInst->getPredicate() == CmpInst::ICMP_SGT)
							{
								errs() << "SGT\n";
								if(localConst == NULL) conflict = true;
								else if(prevConst == NULL) conflict = true;
								else if(localConst->uge(prevConst->getZExtValue()));
								else conflict = true;
							}
							else
							{
								errs() << "Conflict\n";
								conflict = true;
							}
						}
					}
					else if(localInst->getOperand(1) == inst->getOperand(1))
					{
						if(localInst->getPredicate() == CmpInst::ICMP_SLT)
						{
							errs() << "SLT\n";
							if(localConst == NULL) conflict = true;
							else if(prevConst == NULL) conflict = true;
							else if(prevConst->uge(localConst->getZExtValue()))
							{
								toRemove[localInst] = inst;
							}
							else conflict = true;
						}
						else if(localInst->getPredicate() == CmpInst::ICMP_SGT)
						{
							errs() << "SGT\n";
							if(localConst == NULL) conflict = true;
							else if(prevConst == NULL) conflict = true;
							else if(localConst->uge(prevConst->getZExtValue()))
							{
								toRemove[localInst] = inst;
							}
							else conflict = true;
						}
					}
				}

				for(map<Instruction*, Instruction*>::iterator remItr = toRemove.begin(); remItr != toRemove.end(); remItr++)
				{
					gen->erase(remItr->first);
					remItr->first->replaceAllUsesWith(remItr->second);
					remItr->first->eraseFromParent();
				}

				if(!conflict) S->insert(*itr);
			}

			errs() << "S size: " << S->size() << "\n";
			return S;
		}

		void calculateRedundant(BasicBlock* entry)
		{
			queue<BasicBlock*> toVisit;
			toVisit.push(entry);
			set<BasicBlock*> visited;

			while(!toVisit.empty())
			{
				BasicBlock* block = toVisit.front();
				toVisit.pop();

				if(visited.find(block) != visited.end()) continue;

				//Retrieve genset and pred
				set<Value*>* gen = genSet[block];
				Output* outset = outputs[block];
				Output* inset = inSet[block];

				//Create sets if they are null
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

				//Calculate IN
				inset->outSet.clear();
				inset->outSrc.clear();

				set<BasicBlock*>* preds = &pred[block];
				bool isReady = true;
				for(set<BasicBlock*>::iterator itr = preds->begin(); itr != preds->end(); itr++)
				{
					Output* outs = outputs[*itr];
					if(outs == NULL)
					{
						isReady = false;
						break;
					}
					for(set<Value*>::iterator valItr = outs->outSet.begin(); valItr != outs->outSet.end(); valItr++)
					{
						if(itr == preds->begin())
						{
							inset->outSet.insert(*valItr);
							inset->outSrc[*valItr] = outs->outSrc[*valItr];
						}
						else
						{
							set<Value*> toRemove;

							//See if the comparison is in the inset set
							for(set<Value*>::iterator outItr = outs->outSet.begin(); outItr != outs->outSet.end(); outItr++)
							{
								if(outs->outSet.find(*outItr) == outs->outSet.end())
									toRemove.insert(*outItr);
							}

							for(set<Value*>::iterator outItr = toRemove.begin(); outItr != toRemove.end(); outItr++)
							{
								inset->outSet.erase(*outItr);
								inset->outSrc.erase(*outItr);
							}
						}
					}
				}

				if(!isReady)
				{
					toVisit.push(block);
					continue;
				}

				visited.insert(block);

				set<Value*>* forward = backwards(inset, block);

				//Calculate OUT
				outset->outSet.clear();
				outset->outSrc.clear();

				//Add gen
				for(set<Value*>::iterator itr = gen->begin(); itr != gen->end(); itr++)
				{
					outset->outSet.insert(*itr);
					outset->outSrc[*itr] = block;
				}
				//Add forward set
				for(set<Value*>::iterator itr = forward->begin(); itr != forward->end(); itr++)
				{
					outset->outSet.insert(*itr);
					outset->outSrc[*itr] = block;
				}

				//Add Successors
				TerminatorInst* termInst = block->getTerminator();
				int numSucc = termInst->getNumSuccessors();
				for(int i = 0; i < numSucc; i++)
					toVisit.push(termInst->getSuccessor(i));
			}
			
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

					//Trace through the store instruction to see if we can determine how this value changed
					if(StoreInst* storeInst = dyn_cast<StoreInst>(inst))
					{
						state varState = getState(storeInst);
						Value* changingVar = storeInst->getOperand(1);
						stateChanges[block][changingVar] = varState;
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

			//calculateSets(&lastBlock);
			calculateRedundant(&F.getEntryBlock());


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
