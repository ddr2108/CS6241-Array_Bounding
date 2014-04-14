#define is64 false

#include "llvm/IR/Function.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DebugInfo.h"
#include "llvm/Analysis/Dominators.h"
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

		set<BasicBlock*> visited;

		map<BasicBlock*, Output* > outputs;
		map<BasicBlock*, set<Value*>* > genSet;
		map<BasicBlock*, Output* > inSet;
		map<BasicBlock*, set<BasicBlock*> > pred;
		map<BasicBlock*, map<Value*, state> > stateChanges;

		map<BasicBlock*, BasicBlock*> original;

		BasicBlock* errorBlock;

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

		//Finds the base value of an instruction. This means the method will skip passed cast instructions to find the original load.
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

		//Determines whether two values are the same, and if they are the second one is added to the "toRemove" map
		bool compareValues(Value* itr, Value* localItr, map<Instruction*, Instruction*> &toRemove, BasicBlock* block)
		{
			//Make sure they aren't the same instruction
			if(itr == localItr) return false;

			CmpInst* inst = dyn_cast<CmpInst>(itr);

			//errs() << gen->size() << "\n";
			bool conflict = false;

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

			CmpInst* localInst = dyn_cast<CmpInst>(localItr);

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
				//Makes sure the comparisons have the same predicate
				if(localInst->getPredicate() == inst->getPredicate())
				{
					localConst = dyn_cast<ConstantInt>(localOp2);
					prevConst = dyn_cast<ConstantInt>(op2);


					//Checks to see if the increase/decreases are allowable depending on the predicate
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

			return conflict;
		}

		//Despite being called "backwards" this method is actually used for both forward and backward data flow analysis
		set<Value*>* backwards(Output* output, BasicBlock* block, bool doRemove=false)
		{
			set<Value*>* S = new set<Value*>();

			set<Value*>* gen = genSet[block];
			//errs() << "backwards: " << output->outSet.size() << "\n";

			//O(n^2) loop to check for matching compares
			for(set<Value*>::iterator itr = output->outSet.begin(); itr != output->outSet.end(); itr++)
			{
				map<Instruction*, Instruction*> toRemove;
				bool conflict = false;
				for(set<Value*>::iterator localItr = gen->begin(); localItr != gen->end(); localItr++)
				{
					conflict |= compareValues(*itr, *localItr, toRemove, block);
				}

				//In the 3 step of the algorithm, we remove instructions that are redundant
				if(doRemove)
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

		//Forward analysis. Remove redundant bound checks
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

				//Check if the predecessors both have outsets available. If not, wait to try again later
				if(!isReady)
				{
					toVisit.push(block);
					continue;
				}

				visited.insert(block);

				set<Value*>* forward = backwards(inset, block, true);

				//Calculate OUT
				outset->outSet.clear();
				outset->outSrc.clear();

				map<Instruction*, Instruction*> toRemove;

				//Add gen, while removing duplicate gen vars
				for(set<Value*>::iterator itr = gen->begin(); itr != gen->end(); itr++)
				{
					bool duplicate = false;
					for(set<Value*>::iterator itr2 = gen->begin(); itr2 != itr; itr2++)
					{
						bool isDup = compareValues(*itr, *itr2, toRemove, block);
						duplicate |= isDup;
					}

					//if(!duplicate)
					{
						outset->outSet.insert(*itr);
						outset->outSrc[*itr] = block;
					}
				}
				//Remove the redundant gen statements
				for(map<Instruction*, Instruction*>::iterator itr = toRemove.begin(); itr != toRemove.end(); itr++)
				{
					errs() << "REMOVE: " << *itr->first << "\n";
					gen->erase(itr->first);
					itr->first->replaceAllUsesWith(itr->second);
					itr->first->eraseFromParent();

					outset->outSet.erase(itr->first);
					outset->outSrc.erase(itr->first);
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

		//Find busy checks and propagate the compares upward
		void calculateSets(set<BasicBlock*>* term)
		{
			queue<BasicBlock*> toVisit;

			for(set<BasicBlock*>::iterator itr = term->begin(); itr != term->end(); itr++)
				toVisit.push(*itr);
			set<BasicBlock*> visited;

			//Note: This dominator tree is not current, as we have added blocks/instructions
			DominatorTree &domTree = getAnalysis<DominatorTree>();

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

					//Create an extra redundant check in this block
					ICmpInst* cmp = dyn_cast<ICmpInst>(*itr);
					TerminatorInst* term = block->getTerminator();

					Instruction* cmpOp1 = dyn_cast<Instruction>(cmp->getOperand(0));
					Instruction* cmpOp2 = dyn_cast<Instruction>(cmp->getOperand(1));

					if((cmpOp1 == NULL || domTree.dominates( cmpOp1, original[block])) && ( cmpOp2 == NULL || domTree.dominates(cmpOp2, original[block])))
					{
						errs() << *cmpOp1 << " -> " << original[block]->getName() << "\n";
						ICmpInst* boundCheck =  new ICmpInst(term, cmp->getPredicate(), cmp->getOperand(0), cmp->getOperand(1), Twine("CmpBusy"));
						gen->insert(boundCheck);
					}
				}

				//errs() << "Gen size: " << gen->size() << "\n";
				errs() << "InSet size: " << inset->outSet.size() << "\n-------------------------\n";

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

			errorBlock = NULL;

			//Visit until nore more blocks left
			while(!nextBlocks.empty()){
				//Get next block
				BasicBlock* block = nextBlocks.front();
				nextBlocks.pop();

				if(original[block] == NULL)
					original[block] = block;

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

					if(ICmpInst* cmp = dyn_cast<ICmpInst>(inst))
					{
						c_gen->insert(inst);
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

			//Optimize bounds checks
			calculateSets(&lastBlock);
			calculateRedundant(&F.getEntryBlock());

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
					//add new blocks to go to
					if(TerminatorInst* termInst = dyn_cast<TerminatorInst>(inst)){
						int numSucc = termInst->getNumSuccessors();
						for(int i = 0; i < numSucc; i++)
						{
							BasicBlock* succ = termInst->getSuccessor(i);
							int size = succ->getInstList().size();
							TerminatorInst* succTerm = succ->getTerminator();

							BasicBlock* succFollow = NULL;
							if(succTerm->getNumSuccessors() > 0)
								succFollow = succTerm->getSuccessor(0);

							if(size == 1 && succTerm->getNumSuccessors() == 1 && succFollow->getSinglePredecessor())
							{
								termInst->setSuccessor(i, succFollow);
								succFollow->eraseFromParent();
								
								nextBlocks.push(succFollow);
							}
							else
								nextBlocks.push(succ);
						}
					}
				}
			
			}//*/

			//Print out resulting assembly
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				//errs()<<*i<<'\n';
   			}


			return false;
		}

		void getAnalysisUsage(AnalysisUsage &AU) const
		{
			AU.addRequired<DominatorTree>();
			//AU.addPreserved<DominatorTree>();
		}
	};

	char CSE6142::ID = 0;
	static RegisterPass<CSE6142> X("CSE6142", "");
}
