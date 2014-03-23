#define DEBUG_TYPE "arrayBound"
#include "llvm/ADT/Statistic.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Transforms/Scalar.h"
#include <set>

using namespace llvm;

namespace {
	
	struct arrayBound : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		arrayBound() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){

   			std::set<Instruction*> instructionList;		//List of instructions
			//Put each instruction into list			
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				instructionList.insert(&*i);
   			}

			//While still analyzing instructions
			while (!instructionList.empty()) {

				//Pull top most instruction
				Instruction *I1 = *instructionList.begin();
			     	instructionList.erase(instructionList.begin());
			 
				//If there is an array instruction - find declartion of all variables
			     	if (I1->getOpcode()==29){	


					
					//Find the element that is being indexed
					Value* indexValue = I1->getOperand(2);
					ConstantInt* indexConstant = dyn_cast<ConstantInt>(indexValue);	
					//If it isn't a constant, go to next instruction
					if(!indexConstant) {
						continue;
					}
					int arrayIndex = indexConstant->getZExtValue(); 	//Pull out the array index

					//Pull out instruction where array is allocated
					Value* allocValue = I1->getOperand(0);
					AllocaInst* allocInstr;					
					if (isa<AllocaInst>(allocValue)){
						allocInstr = cast<AllocaInst>(allocValue);
					}else{
						continue;
					}
ICmpInst* test = new ICmpInst(CmpInst::ICMP_EQ, indexValue, indexValue,"foo");				
//AllocaInst* pa = new AllocaInst(allocInstr->getType() , 0, "indexLoc");
I1->getParent()->getInstList().insert(I1, test);

					//Get number of elements in array
					PointerType *pt = allocInstr->getType();
					ArrayType *at = cast<ArrayType>(pt->getElementType());
					int arraySize = at->getNumElements();		//Pull out array size
					
					//Check size of array vs index
					if (arrayIndex>=arraySize){
						
						//Get line number
						unsigned Line;
						if (MDNode *N = I1->getMetadata("dbg")) {
							DILocation Loc(N);                     
							Line = Loc.getLineNumber();
						}

						//Print error
						errs()<<"Index outside of array bounds\n Line:"<<Line<<"\n Access index " <<arrayIndex<<" of array "<<allocInstr->getName()<<" of size "<<arraySize<<"\n\n";

					}				

				}
				


			}


/*
BasicBlock*
MyCompiler::handle_if( BasicBlock* bb, SetCondInst* condition )
{
    // Create the blocks to contain code in the structure of if/then/else
    BasicBlock* then = new BasicBlock(); 
    BasicBlock* else = new BasicBlock();
    BasicBlock* exit = new BasicBlock();

    // Insert the branch instruction for the "if"
    bb->getInstList().push_back( new BranchInst( then, else, condition ) );

    // Set up the terminating instructions
    then->getInstList().push_back( new BranchInst( exit ) );
    else->getInstList().push_back( new BranchInst( exit ) );

    // Fill in the then part .. details excised for brevity
    this->fill_in( then );

    // Fill in the else part .. details excised for brevity
    this->fill_in( else );

    // Return a block to the caller that can be filled in with the code
    // that follows the if/then/else construct.
    return exit;
}*/




			//Print out a list of instructions
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				errs()<<*i<<'\n'<<i->getOpcode()<<'\n';
   			}
			
			return 1;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		}

	};
}
char arrayBound::ID = 0;
static RegisterPass<arrayBound> X("arrayBound", "Project 1: Array Bounds", true, true);

