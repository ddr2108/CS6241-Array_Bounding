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
	
	//Structure for holding information about instructions
	typedef struct _defInstruct{
		StringRef def;		//the variable modified
		int instructNum;	//the nth instruction in program
		int lineNum;		//actual line number

		//Constructor
		 _defInstruct(StringRef defIn, int instructNumIn, int lineNumIn){
			def = defIn;
			instructNum = instructNumIn;
			lineNum = lineNumIn;
		}
	} defInstruct;

	struct p11 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p11() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){
			
			//Information about structure of program
			std::map<BasicBlock*, int> basicBlockIndex;
			std::map<Instruction*, int> instructionIndex;
			std::map<int, defInstruct*> instructionDefIndex;

			int *dist;						//Hold distance between any two blocks
			int* reachDef;						//Hold reaching def for each instruction
			std::map<BasicBlock*, std::set<int> > killedDef;	//Hold killed def for each block	
			std::map<BasicBlock*, std::set<int> > usedDef;		//Hold used def for each bock
			std::map<BasicBlock*, std::set<BasicBlock*> > influencedNode;		//Hold used dbock
			std::set<std::set<BasicBlock*> > ROI;		//Hold used def for each bock
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////DISTANCE BETWEEN BLOCKS///////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int numBlock = 0;	//Number of blocks

			//Get list of basic blocks			
			Function::BasicBlockListType &allblocks = F.getBasicBlockList();
			//Go through basic blocks
			for (Function::iterator i = allblocks.begin(); i != allblocks.end(); i++) {
				basicBlockIndex[i] = numBlock++;		//hold information about where the basic block is
			}

			//Allocate array
			dist = (int*) malloc(numBlock*numBlock*sizeof(int*));
			for (int i = 0; i<numBlock; i++){
				//Init to infinite
				for(int j =0; j<numBlock; j++){
					if (i==j){
						dist[i*numBlock + j] = 0;
					}else{
						dist[i*numBlock + j] = 1000000000;
					}
				}
			}

			//Fill array will all with distance 1;
			BasicBlock* successorBlock;	//Next basic block
			//Block indexes
			int sourceBlock = 0;
			int destinationBlock;
			for (Function::const_iterator i = allblocks.begin(); i != allblocks.end(); i++) {
				//For each successor
				for (int j = 0; j < (i->getTerminator())->getNumSuccessors();j++){
					successorBlock = (i->getTerminator())->getSuccessor(j);	//Successor
					destinationBlock = basicBlockIndex[successorBlock];
					dist[sourceBlock*numBlock + destinationBlock] = 1;			//Set distance to 1
				}
				sourceBlock++;
			}

			//Perform the algorithm
			for (int i = 0; i<numBlock ;i++){
				for (int j = 0; j<numBlock ;j++){
					for (int k = 0; k<numBlock ;k++){
						if (j!=k){
							if (dist[j*numBlock + k] > (dist[j*numBlock + i] + dist[i*numBlock + k])){ 
								dist[j*numBlock + k] = dist[j*numBlock + i] + dist[i*numBlock + k];
							}
						}
					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////REACHING DEFINTION ANALYSIS////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int numInst = 0;		//number of instructions
			int numDef = 0;			//number of defs

			//Get loopinfo
  			LoopInfo &LI = getAnalysis<LoopInfo>();

			std::vector<Instruction*> instructionLists;	//List of instructions

			//Put each instruction into list			
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
				instructionLists.insert(instructionLists.end(), &*i);

				//Get line number
				unsigned int line;
				MDNode *N = i->getMetadata("dbg");
				if (N) {
					DILocation Loc(N);                     
					line = Loc.getLineNumber();
				}

				//Store data about variables in list - include line number, variable name, and actual instr
				if (i->getOpcode()==28 && N && i->getOperand(1)->getName()!=""){
					//Insert information about instruction
					defInstruct* newInstruction = new defInstruct(i->getOperand(1)->getName(), numInst, line);
					instructionDefIndex[numDef++] = newInstruction;
				}
				
				//Store index number of instruction
				instructionIndex[&*i] = numInst++;
   			}

			//Allocate 2d array to hold reaching def
			reachDef = (int*)calloc((numInst)*numDef,sizeof(int));
			
			//Hold defentions that are being studied
			int prevDef = 0;
			int curDef = 0;
			//go through each instruction and fix successor reaching defs
			for(int i = 0; i < numInst; i++){
				//Instruction being studied
				Instruction* curInst = instructionLists[i];
				prevDef = curDef;
				
				//Get which defs this instruction added
				for (curDef = 0; curDef < numDef; curDef++){
					//compare def to the instruction being studied
					if(instructionDefIndex[curDef]->instructNum > i){
						curDef--;
						break;
					}
				}

				//copy prev instruction if not first instr in block
				if (i > 0 && (curInst->getParent()->getFirstNonPHI()!=curInst)){
					//Copy previous reach def
					for (int j = 0; j < numDef; j++){
						//if it is marked as reaching, mark it as reaching in next
						if (reachDef[(i-1)*numDef+j] > 0){
							reachDef[i*numDef+j] = reachDef[(i-1)*numDef+j]; 
						}
					}
				}
				
				//Add new defitions reachable because of new isntruction
				for (int j = prevDef+1; j <= curDef && j < numDef; j++){
					reachDef[i*numDef+j] = 1;		//mark instruction as reaching
					//Check if need to get rid of def
					for (int k = 0; k < numDef; k++){
						//if instruction  is marked as reaching and not the same instruction
						if (reachDef[i*numDef+k]==1 && instructionDefIndex[k]->instructNum!=i){
							//if the instructions are for the same variable, mark the others so
							if(instructionDefIndex[j]->def == instructionDefIndex[k]->def){
								reachDef[i*numDef+k]=0;
							}
						}
					}
				}

				int changedFlag = 0;	//Flag to hold whether any changes where made
				int killedFlag = 0;	//Flag to hold whether a def was killed

				//Call Test
				Instruction* newInstr = instructionLists[i];
				BasicBlock *newBlock = newInstr->getParent();
				//If  it is a terminating instruction and is doing a call
				if (newInstr->isTerminator() && (((newBlock->getTerminator())->getNumSuccessors()>1)||newInstr->getOpcode()==2)){
					for (int x = 0; x<newBlock->getTerminator()->getNumSuccessors(); x++){
						//Get the destination of the call
						BasicBlock* newBlock2 = newBlock->getTerminator()->getSuccessor(x);
						Instruction* newInstr2 = newBlock2->getFirstNonPHI();

						//Get index of the instruction
						int y = instructionIndex[newInstr2];

						for (int j = 0; j<numDef;j++){
							//Copy the reach definitions
							if (reachDef[i*numDef+j] > 0){
								if (reachDef[y*numDef+j] < 1){ 
									changedFlag = 1;	//mark  there was a change
									//Copy def
									reachDef[y*numDef+j] = reachDef[i*numDef+j]; 
								     
								     	//check for killed def
									for (int d = 0; d < numDef;d++){
										//if a diff def for same variable, and both reach
										if (d!=j && instructionDefIndex[d]->def==instructionDefIndex[j]->def && reachDef[y*numDef+d]>0){
											killedFlag = 1;		//mark as killed

											//add the existing to killed set
										       	std::set<int> currentKill = killedDef[newBlock2];
										       	currentKill.insert(d);
										      	killedDef[newBlock2] = currentKill;
										  }
									}
								     
									//if there is a def killed, add the intial that triggered 
								     	if (killedFlag){
								          	std::set<int> currentKill = killedDef[newBlock2];
								         	currentKill.insert(j);
								          	killedDef[newBlock2] = currentKill;
								     	}
								}
							}
						}

						//If there was a change restart analysis earlier - add to procset
						if (changedFlag){
							//if modified an earlier instruction, go back
							if (i>y){
								i = y;
							}

							//Modify def analysis based on moving back
							for (curDef = 0; curDef < numDef; curDef++){
								if(instructionDefIndex[curDef]->instructNum > i){
									curDef--;
									break;
								}
							}

							//go back to new successor block
							break;
						}

					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////USED DEF ANALYSIS//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

			int curInst = 0;
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
				if (i->getOpcode()==27){		//Is a load instruction
					std::set<int> defsUsed;
					for (int d = 0 ;d<numDef; d++){	//compare to all the other defs
						if (reachDef[curInst*numDef + d] == 1 && instructionDefIndex[d]->def == i->getOperand(0)->getName()){
							defsUsed.insert(d);		//add to used
						}
					}
					if (defsUsed.size()>1){
						std::set<int> currentUsed = usedDef[i->getParent()];
						currentUsed.insert(defsUsed.begin(), defsUsed.end());
						usedDef[i->getParent()] = currentUsed;
					}

				}
				curInst++;
			}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////DEBUG////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			
			//Print results
			for (int z = 0; z<numInst;z++){
				errs()<<*instructionLists[z]<<"\n";
				for (int y = 0; y<numDef; y++){
					if (reachDef[z*numDef+y]==1){
						errs()<<"-------"<<instructionDefIndex[y]->lineNum<<"-"<<instructionDefIndex[y]->def<<"\n";
					}
				}
			}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			free(dist);
			return true;

		}

		virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		  	AU.addRequired<LoopInfo>();		//add request	
		}

	};

	char p11::ID = 0;
	static RegisterPass<p11> X("p11", "Part 1.1", true, true);
}


