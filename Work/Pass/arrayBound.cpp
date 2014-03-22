#define DEBUG_TYPE "arrayBound"
#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Support/raw_ostream.h"
#include <set>

using namespace llvm;

namespace {
	
	struct arrayBound : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		arrayBound() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){
			int refer = 0;			

   			std::set<Instruction*> instructionList;	//List of instructions
			//Put each instruction into list			
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				instructionList.insert(&*i);
   			}

			//While still analyzing instructions
			while (!instructionList.empty()) {
				//Pull top most instruction
				Instruction *I1 = *instructionList.begin();
			     	instructionList.erase(instructionList.begin());
			 
				//If there is an allocate instruction - find declartion of all variables
			     	if (I1->getOpcode()==26){						

					//Get all instructions that refer to this value
					for (Value::use_iterator UI = I1->use_begin(), UE = I1->use_end(); UI != UE; ++UI){
						if (Instruction *I2 = dyn_cast<Instruction>(*UI)) {
							
							//Check if store insruction that is storing t this variable
							if (!(I2->getOpcode() == 28 && I2->getOperand(1) == I1)){
								refer++;
								break;
							}
						}

					}
					
					//if no real use, remove all references
					if (refer==0){
						errs()<<I1->getName()<<'\n';
						//Remove all instructions refering to it 			
						for (Value::use_iterator UI = I1->use_begin(), UE = I1->use_end(); UI != UE; ++UI){
							if (Instruction *I2 = dyn_cast<Instruction>(*UI)){
								I2->eraseFromParent();
							}
						}						


						//Remove instruction					 	
						I1->eraseFromParent();
					}
				}
				

				refer = 0;
			}

			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
       				errs()<<*i<<'\n';
   			}
			
			return 1;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
			//AU.setPreservesCFG();
		}

	};
}
char arrayBound::ID = 0;
static RegisterPass<arrayBound> X("arrayBound", "Project 1: Array Bounds", true, true);

