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
	
	struct p11 : public FunctionPass {
		// Pass identification, replacement for typeid
		static char ID; 
		p11() : FunctionPass(ID) {}

		//Run for each function
		virtual bool runOnFunction(Function &F){
			
			//Information about structure of program
			std::map<BasicBlock*, int> basicBlockIndex;
			std::map<Instruction*, int> instructionIndex;
			std::map<Instruction*, int> instructionDefIndex;

			int *dist;						//Hold distance between any two blocks	
			std::map<BasicBlock*, std::set<int> > killedDef;	//Hold killed def for each block	
			std::map<BasicBlock*, std::set<int> > usedDef;		//Hold used def for each bock

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////DISTANCE BETWEEN BLOCKS///////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int ind;			
			int i,j;

			BasicBlock* successorBlock;

			//Get list of basic blocks			
			Function::BasicBlockListType &allblocks = F.getBasicBlockList();
			//Go through basic blocks
			ind = 0;			
			for (Function::iterator newBlock = allblocks.begin(); newBlock != allblocks.end(); newBlock++) {
				basicBlockIndex[newBlock] = ind;		//hold information about where the basic block is
				ind++;
			}

			//Allocate array
			dist = (int*) malloc(ind*ind*sizeof(int*));
			for (i = 0; i<ind; i++){
				//Init to infinite
				for(j =0; j<ind; j++){
					if (i==j){
						dist[i*ind + j] = 0;
					}else{
						dist[i*ind + j] = 1000000000;
					}
				}
			}

			//Fill array will all with distance 1;
			i = 0;
			for (Function::const_iterator firstBlock = allblocks.begin(); firstBlock != allblocks.end(); firstBlock++) {
				for (int k = 0; k < (firstBlock->getTerminator())->getNumSuccessors();k++){
					successorBlock = (firstBlock->getTerminator())->getSuccessor(k);	//Successor
					j = basicBlockIndex[successorBlock];
					dist[i*ind + j] = 1;
				}
				i++;
			}

			//Perform the algorithm
			for (int x = 0; x<ind ;x++){
				for (int y = 0; y<ind ;y++){
					for (int z = 0; z<ind ;z++){
						if (y!=z){
							if (dist[y*ind + z] > (dist[y*ind + x] + dist[x*ind + z])){ 
								dist[y*ind + z] = dist[y*ind + x] + dist[x*ind + z];
							}
						}
					}
				}
			}
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////REACHING DEFINTION ANALYSIS////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			int changed;			
			int count= -1;
			int count2 = 0;
//struct _
			//Get loopinfo
  			LoopInfo &LI = getAnalysis<LoopInfo>();

			std::vector<Instruction*> instructionLists;
			std::vector<StringRef> bbList;
			std::vector<StringRef> def;
			std::vector<unsigned> lineNum;
			std::vector<unsigned> realLineNum;

			//Put each instruction into list			
			for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
				count++;
				instructionLists.insert(instructionLists.end(), &*i);
				bbList.insert(bbList.end(), "asd");
				//instructionIndex[&*i] = 1;

				//Get line number
				unsigned int line;
				MDNode *N = i->getMetadata("dbg");
				if (N) {
					DILocation Loc(N);                     
					line = Loc.getLineNumber();
				}

				//Store data about variables in list - include line number, variable name, and actual instruction
				if (i->getOpcode()==28 && N && i->getOperand(1)->getName()!=""){
					def.insert(def.end(), i->getOperand(1)->getName());
					lineNum.insert(lineNum.end(), count);
					realLineNum.insert(realLineNum.end(), line);
					count2++;
				}
   			}
			
			//2d array to hold reaching def
			int* reachDef = (int*)calloc((count+1)*count2,sizeof(int));
			
			int prevK = 0;
			int k=0;
			int p = 0;
			//go through each instruction
			for(p = 0;p<=count;p++){
				Instruction* i = instructionLists[p];
				prevK = k;
				
				//Get Line num
				for (k = 0; k<count2;k++){
					if(lineNum[k]>p){
						k--;
						break;
					}
				}

				//copy prev instruction if not first instr in block
				if (p>0 && (i->getParent()->getFirstNonPHI()!=i)){
					//Copy previous reach def
					for (int j = 0; j<count2;j++){
						if (reachDef[(p-1)*count2+j] == 1){
							reachDef[p*count2+j] = reachDef[(p-1)*count2+j]; 
						}
					}
				}

				
				//Add new defitions reachable because of new isntruction
				for (int m = prevK+1; m<=k;m++){

					//if(reachDef[p*count2+m]==0){
						reachDef[p*count2+m]=1;
						//Check if need to get rid of def
						for (int z = count2; z>=0;z--){
							if (reachDef[p*count2+z]==1 && lineNum[z]!=p){

								if(def[m].equals_lower(def[z])){
									reachDef[p*count2+z]=0;
								}
							}
						}
					//}
				}

				int change = 0;

				//Call Test
				Instruction* newInstr = instructionLists[p];
				BasicBlock *newBlock = newInstr->getParent();
				//If  it is a terminating instruction and is doing a call
				if (newInstr->isTerminator() && (((newBlock->getTerminator())->getNumSuccessors()>1)||newInstr->getOpcode()==2)){
					for (int x = 0; x<newBlock->getTerminator()->getNumSuccessors(); x++){
						//Get the destination of the call
						BasicBlock* newBlock2 = newBlock->getTerminator()->getSuccessor(x);
						Instruction* newInstr2 = newBlock2->getFirstNonPHI();
						for (int y = 0; y<=count;y++){
							//Find the instruction
							if(instructionLists[y]==newInstr2){
								for (int j = 0; j<count2;j++){
									//Copy the reach definitions
									if (reachDef[p*count2+j] == 1){
										if (reachDef[y*count2+j]!=1){ 
											reachDef[y*count2+j]= reachDef[p*count2+j]; 
											change = 1;		//mark if there was a change
										     //Find the def
										     int killedFlag = 0;
										     //check for killed def
										     for (int d = 0;d<count2;d++){
//errs()<<"asd\n";
										          if (d!=j && def[d]==def[j] && reachDef[y*count2+d]==1){

										               killedFlag = 1;
										               std::set<int> currentKill = killedDef[newBlock2];
										               currentKill.insert(d);
										               killedDef[newBlock2] = currentKill;
										          }
										     }
										     //if there is a def killed, add initial
										     if (killedFlag){
										          std::set<int> currentKill = killedDef[newBlock2];
										          currentKill.insert(j);
										          killedDef[newBlock2] = currentKill;
										     }

											}
									}
								}
								//If there was a change restart analysis earlier - add to procset
								if (change==1){
									if (p>y){
										p = y;
									}

									//Get Line num
									for (k = 0; k<count2;k++){
										if(lineNum[k]>p){
											k--;
											break;
										}
									}
									break;
								}
							}
						}
					}
				}
				
			}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////USED DEF ANALYSIS//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	int l = 0;
	for(inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i){
		if (i->getOpcode()==27){		//Is a load instruction
			std::set<int> defsUsed;
			for (int d = 0 ;d<count2; d++){	//compare to all the other defs
				if (reachDef[l*count2 + d] == 1 && def[d]==i->getOperand(0)->getName()){
					defsUsed.insert(d);		//add to used
				}
			}
			if (defsUsed.size()>1){
				std::set<int> currentUsed = usedDef[i->getParent()];
				currentUsed.insert(defsUsed.begin(), defsUsed.end());
				usedDef[i->getParent()] = currentUsed;
			}

		}
		l++;
	}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////DEBUG////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			
			//Print results
			for (int z = 0; z<=count;z++){
				errs()<<*instructionLists[z]<<"\n";
				for (int y = 0; y<count2; y++){
					if (reachDef[z*count2+y]==1){
						errs()<<"-------"<<realLineNum[y]<<"-"<<def[y]<<"\n";
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


