//===- svf-ex.cpp -- A driver example of SVF-------------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//

/*
 // A driver program of SVF including usages of SVF APIs
 //
 // Author: Yulei Sui,
 */

#include "SVF-LLVM/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/Options.h"

#include "Util/PTAStat.h"
#include "Graphs/ICFGStat.h"

using namespace llvm;
using namespace std;
using namespace SVF;

static llvm::cl::opt<std::string> InputFilename(cl::Positional,
        llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));

/*!
 * An example to query alias results of two LLVM values
 */
SVF::AliasResult aliasQuery(PointerAnalysis* pta, Value* v1, Value* v2)
{
    SVFValue* val1 = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(v1);
    SVFValue* val2 = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(v2);

    return pta->alias(val1,val2);
}

/*!
 * An example to print points-to set of an LLVM value
 */
std::string printPts(PointerAnalysis* pta, Value* val)
{

    std::string str;
    raw_string_ostream rawstr(str);
    SVFValue* svfval = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);

    NodeID pNodeId = pta->getPAG()->getValueNode(svfval);
    const PointsTo& pts = pta->getPts(pNodeId);
    for (PointsTo::iterator ii = pts.begin(), ie = pts.end();
            ii != ie; ii++)
    {
        rawstr << " " << *ii << " ";
        PAGNode* targetObj = pta->getPAG()->getGNode(*ii);
        if(targetObj->hasValue())
        {
            rawstr << "(" << targetObj->getValue()->toString() << ")\t ";
        }
    }

    return rawstr.str();

}

std::string instrToString(const llvm::Instruction *inst)
{
    std::string str;
    llvm::raw_string_ostream ss(str);
    ss<<*inst;
    return ss.str();
}

inline const llvm::Function* getCallee(const llvm::CallBase *cs) {
    // FIXME: do we need to strip-off the casts here to discover more library functions
    //llvm::Function *callee = llvm::dyn_cast<llvm::Function>(cs.getCalledValue()->stripPointerCasts());
    return cs->getCalledFunction();
}

inline const llvm::Function* getCallee(const llvm::Instruction *inst) {
	if(const llvm::CallInst *cInst=dyn_cast<llvm::CallInst>(inst))
    	{
		CallBase *shit=(CallBase *)cInst;
		return getCallee(shit);
    	}
    	else if(const llvm::InvokeInst *cInst=dyn_cast<llvm::InvokeInst>(inst))
    	{
		CallBase *shit=(CallBase *)cInst;
		return getCallee(shit);
    	}
	else
	{
		cout<<"fxxk in getCallee"<<instrToString(inst)<<"!!!!\n";
		return NULL;
	}
}

//doesn't handle argument and function?? can get the function for those?
const llvm::Instruction *getInstr(PAGNode *node, std::map<NodeID, const llvm::Instruction *>cache)
{
    if(cache.find(node->getId()) != cache.end())
	return cache[node->getId()];

    //cout<<"getInstr1\n";
    if(node->getNodeKind() == SVFVar::DummyValNode || node->getNodeKind() == SVFVar::DummyObjNode)
	return NULL;
    //cout<<"getInstr2\n";

    if(node->getValue())
    {
	/*if(const llvm::Function* fun = SVFUtil::dyn_cast<Function>(node->getValue()))
	{
		std::cout<<"hi hi\n";
                return NULL;
	}*/
	const SVFValue *shit=node->getValue();
	const Value *shit2=LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(shit);

        if(const llvm::Instruction* inst = SVFUtil::dyn_cast<Instruction>(shit2))
        //if(llvm::isa<llvm::Instruction>(node->getValue()))
        {
	    cache[node->getId()]=inst;
            return inst;
            //return llvm::cast<llvm::Instruction>(node->getValue());
        }
        else
      	{
	    cache[node->getId()]=NULL;
	    //cout<<"not instr?\n";
	    //cout<<node->toString()<<"\n";
            return NULL;
	}
    }
    else
    {
	cache[node->getId()]=NULL;
	cout<<"no value?\n";
        return NULL;
    }
}

std::set<NodeID> findAlias(const PAGNode *freeNode, PointerAnalysis* pta, PAG* G, std::map<NodeID, const llvm::Instruction *>cache, ICFG* icfg)
{
	//bool check=true;
	std::set<NodeID> result;
  	std::set<NodeID> result2;
	//cout<<"alias start time "<<time(NULL)<<"\n";

	const PointsTo& freePts=pta->getPts(freeNode->getId());
        if(!freePts.empty())
        {
		for(PointsTo::iterator it=freePts.begin(), eit=freePts.end(); it!=eit; ++it)
               	{ 
			const NodeSet& revPts=pta->getRevPts(*it);
			//int size=0;
        		//cout<<"rev size? "<< revPts.count()<<"\n";
			//cout.flush();
        		//for(Set<NodeID>::iterator it2=revPts.begin(), eit2=*revPts.end(); it2!=eit2; ++it2)
			for (const NodeID o : revPts)
        		{
				result.insert(o);
				//size++;
				/*if(!G->hasGNode(o))
				{
					cout<<"\tuse:fxxk, no such node\n";
					continue;
				}*/

                        	//cout<<"\tuse: " << o << "\n";
				//<<freeNode->getValueName()<<"\n";

				/*PAGNode* aliasNode=G->getGNode(o);

				const llvm::Instruction *inst=getInstr(aliasNode, cache);
				//SVFInstruction* svfinst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst);

                    		if(!inst)	// || loggedInstr.find(inst)!=loggedInstr.end())
				{
					cout<<"\tuse:fxxk\n";
                        		continue;
				}
				else
                        	{
					//ICFGNode* iNode = icfg->getICFGNode(svfinst);
					//cout<<"\tuse_icfg: "<<iNode->getId()<<"\n";

                        		const DebugLoc &dbg=inst->getDebugLoc();
					if(!dbg)
					{
						cout<<"\tuse:fxxk\n";
						continue;
					}
                        		unsigned line=dbg->getLine();
					auto *Scope=cast<DIScope>(dbg->getScope());
					StringRef shit=Scope->getFilename();
					std::string shit2=shit.str();
					cout<<"\tuse_line: "<<shit2<<"-"<<line<<"\n";
				}*/
        		}
			//cout<<"revPts size "<<size<<"\n";
		}
        }


	cout.flush();
	return result;
}


void dumpFuck(SVFG *vfg, std::set<NodeID> allUse, PAG* G)
{
	cout<<"======printing SVFG======\n";

	SVFG::SVFGNodeIDToNodeMapTy::iterator it = vfg->begin();
	SVFG::SVFGNodeIDToNodeMapTy::iterator eit = vfg->end();
	for (; it != eit; ++it)
	{
		SVFGNode* vNode = it->second;
		NodeID id=it->first;
		cout<<"nodeId: "<<id<<"\n";
		cout<<"children: ";
		for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit = vNode->OutEdgeEnd(); it != eit; ++it)
		{
			VFGEdge* edge = *it;
			VFGNode* dstNode = edge->getDstNode();
			cout<<dstNode->getId()<<" ";
		}
		cout<<"\n";
	}

	cout<<"======printing ICFG to SVFG map=====\n";
	for (const NodeID o: allUse)
	{
		PAGNode* pNode=G->getGNode(o);

		if(!vfg->hasDefSVFGNode(pNode))
			return;

		const VFGNode* rootNode = vfg->getDefSVFGNode(pNode);
        	cout<<"pagNode: "<<o<<" vfgNode: "<<rootNode<<"\n";
	}
}

void printAllUse(std::set<NodeID> allUse, PAG* G, ICFG* icfg)
{
	std::map<NodeID, const llvm::Instruction *> pagCache;
	int count=0;
	int fxxkCount=0;
	int fxxkCount2=0;
	for (const NodeID o : allUse)
	{
		cout<<count<<"/"<<allUse.size()<<"\n";
		cout<<"useId: "<<o<<"\n";
		count++;
		if(!G->hasGNode(o))
		{
			cout<<"\tuse:fxxk, no such node\n";
			fxxkCount2++;
			continue;
		}
		//cout<<"\tuse: " << o << "\n";
		//<<freeNode->getValueName()<<"\n";

		PAGNode* aliasNode=G->getGNode(o);

		const llvm::Instruction *inst=getInstr(aliasNode, pagCache);
		//SVFInstruction* svfinst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst);
		if(!inst)       // || loggedInstr.find(inst)!=loggedInstr.end())
		{
			cout<<"\tuse:fxxk\n";
			fxxkCount++;
			continue;
		}
		else
		{
			SVFInstruction* svfinst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst);
			ICFGNode* iNode = icfg->getICFGNode(svfinst);
			cout<<"\tuse_icfg: "<<iNode->getId()<<"\n";

			/*const DebugLoc &dbg=inst->getDebugLoc();
			if(!dbg)
			{
				cout<<"\tuse:fxxk\n";
				continue;
			}
			unsigned line=dbg->getLine();
			auto *Scope=cast<DIScope>(dbg->getScope());
			StringRef shit=Scope->getFilename();
			std::string shit2=shit.str();
			cout<<"\tuse_line: "<<shit2<<"-"<<line<<"\n";*/
		}
	}

	cout<<"fxxkCount: " <<fxxkCount<<"\n";
	cout<<"fxxkCount2: " <<fxxkCount2<<"\n";
}
void printAllFreePts(PointerAnalysis* pta, ICFG* icfg, Module *mod, PTACallGraph* callgraph, const SVFG* vfg)
{
    //std::cout<<"yoohoo!!!!..........................\n";
    PAG* G = pta->getPAG();
    std::map<NodeID, const llvm::Instruction *> pagCache;
    std::set<NodeID> allUse;
    
    //cout<<"start seeking free, time "<<time(NULL)<<"\n";


    int freeCount=0;

    for(PAG::CSToArgsListMap::iterator It = G->getCallSiteArgsMap().begin(), E = G->getCallSiteArgsMap().end(); It != E; ++It)
    {
	const CallICFGNode* callBlock = It->first;
	const Instruction* fuckInstr = SVFUtil::cast<Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(callBlock->getCallSite()));
	const Function* F = getCallee(fuckInstr);
	if(!F || F->getName().empty())
	  continue;

	if((F->getName().str().compare("free")==0 && F->empty()) || F->getName().str().compare("MagickFree")==0)
	{
		//cout<<"freeCount: " << freeCount<<"\n";
		freeCount++;
		const CallICFGNode* callBlock = It->first;
		//const Instruction* freeInst = SVFUtil::cast<Instruction>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(callBlock->getCallSite()));
		//const llvm::Instruction *freeInst=It->first->getCallSite();
		ICFGNode *sourceNode=(ICFGNode *)callBlock;
		//icfg->getICFGNode(fuckInstr);
		PAG::SVFVarList& Arglist = It->second;
		assert(!Arglist.empty() && "no actual parameter at deallocation site?");
		const PAGNode* freeNode=Arglist.front();
		if(!freeNode->hasValue())
		{
			//continue;
			//cout<< "fxxk, no value? " << freeNode<<"\n";
			//cout<< "instr? "<<instrToString(freeInst)<<"\n";
			//cout<<"source node id? "<<sourceNode->getId()<<"\n";
		}
		else //if(cheat2(sourceNode))
		{
			//std::cout<<printPts(pta, freeNode->getValue());
			//cout<<"****************new item?********************\n";
			//cout<<"freeNode: " << freeNode->getId() << " "<<freeNode->getValueName()<<"\n";
			cout<<"icfg: "<<sourceNode->getId()<<"\n";

			/*const DebugLoc &dbg=freeInst->getDebugLoc();
			unsigned line=dbg->getLine();
			auto *Scope=cast<DIScope>(dbg->getScope());
			StringRef shit=Scope->getFilename();
			std::string shit2=shit.str();
			cout<<"line: "<<shit2<<"-"<<line<<"\n";*/

			//cout<<"free instr? "<<instrToString(freeInst)<<"\n";
			//cout<<"instr in func? ";
			//printICFGNodeFunc(sourceNode);

			//const SVFFunction *freeFunc=sourceNode->getFun();

			//cout<<"\n";
			//cout<<"found free, start time "<<time(NULL)<<"\n";
			//std::set<const ICFGNode*> aliasICFGNodes;
			std::map<const ICFGNode *, const llvm::Instruction *> aliasICFGNodesMap;
			std::map<const SVFFunction *, std::set<const llvm::Instruction *>> funcToInstrMap;
			//const Value* freeVal=freeNode->getValue();
			//cout<<"dbg1\n";
			std::set<NodeID> aliasSet=findAlias(freeNode, pta, G, pagCache, icfg);
			cout<<"use: ";
			for (const NodeID o : aliasSet)
			{
				allUse.insert(o);
				cout<<o<<" ";
			}
			cout<<"\n";
			//cout<<"alias size "<<aliasSet.size()<<"\n";
			//cout<<"allUse size "<<allUse.size()<<"\n";
		}
	}
    }

    cout<<"====printAllUse====\n";
    printAllUse(allUse, G, icfg);

    //cout<<"dbg3\n";
}

/*!
 * An example to query/collect all successor nodes from a ICFGNode (iNode) along control-flow graph (ICFG)
 */
int traverseOnICFG(ICFG* icfg, ICFGNode *root, PTACallGraphNode* ptaNode)
{
    //SVFInstruction* svfinst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst);

    ICFGNode* iNode = root;
    FIFOWorkList<const ICFGNode*> worklist;
    Set<const ICFGNode*> visited;
    worklist.push(iNode);

    int totalNodes=0;

    //cout<<"ptaID: "<<ptaNode->getId()<<"\n";

    /// Traverse along VFG
    while (!worklist.empty())
    {
	totalNodes++;
        const ICFGNode* iNode = worklist.pop();
	bool expand=true;
	cout<<"ICFGID: "<<iNode->getId()<<"\n";
	cout<<"type: ";
	if(iNode==root)
		cout<<"start";
	else if(SVFUtil::isa<IntraICFGNode>(iNode))
		cout<<"intra";
	else
	{
		if(SVFUtil::isa<FunEntryICFGNode>(iNode))
		{
			cout<<"wtf:funEntry";
			expand=false;
		}
		else if(SVFUtil::isa<FunExitICFGNode>(iNode))
		{
			cout<<"funExit";
			//expand=false;
		}
		else if(SVFUtil::isa<CallICFGNode>(iNode))
			cout<<"funCall";
		else if(SVFUtil::isa<RetICFGNode>(iNode))
			cout<<"funRet";
		else if(SVFUtil::isa<GlobalICFGNode>(iNode))
		{
			cout<<"global?";
			expand=false;
		}
		else { 
			cout<<"wtf:unknown kind"; 
			expand=false;
		}
	}

	cout<<"\n";
	//cout<<"outEdges: "<<iNode->getOutEdges().size()<<"\n";

	if(!expand)
	{
		//cout<<"\n";
		continue;
	}

	cout<<"children: ";
	//cout<<"expanding...\n";

	int numChildren=0;
        for (ICFGNode::const_iterator it = iNode->OutEdgeBegin(), eit =
                    iNode->OutEdgeEnd(); it != eit; ++it)
        {
            ICFGEdge* edge = *it;
            ICFGNode* succNode = edge->getDstNode();

	    cout<<" "<<succNode->getId();

	    bool skip=false;
	    //don't expand new function...
	    if(SVFUtil::isa<FunEntryICFGNode>(succNode))
		skip=true;
	    if(SVFUtil::isa<GlobalICFGNode>(succNode))
		skip=true;
	    if(SVFUtil::isa<FunExitICFGNode>(iNode))
		skip=true;

            if (visited.find(succNode) == visited.end())
            {
                //visited.insert(succNode);
		if(!skip) { 
			visited.insert(succNode);
			worklist.push(succNode); 
			numChildren++;
		}
            }
        }
	cout<<"\n";
	if(SVFUtil::isa<CallICFGNode>(iNode))
	{
		const CallICFGNode *callNode=dyn_cast<CallICFGNode>(iNode);
		const RetICFGNode *retNode=callNode->getRetICFGNode();
		cout<<"retNode: "<<retNode->getId()<<"\n";
		if(visited.find(retNode)==visited.end())
		{
			//cout<<"retNode pushed\n";
			visited.insert(retNode);
			worklist.push(retNode);
			numChildren++;
		}
		//else { cout<<"retNode already there??\n"; }
	}

	//cout<<"\nnumChildren: "<<numChildren<<"\n";

    }
    //cout<<"totalNodes: "<<totalNodes<<"\n";

    return totalNodes;
}

std::string dumpFunc(const Function* F)
{
	std::string str;
	raw_string_ostream rawstr(str);

	//return SVFUtil::getSourceLocOfFunction(F).c_str();
	/*
     	* https://reviews.llvm.org/D18074?id=50385
     	* looks like the relevant
     	*/
	if (llvm::DISubprogram *SP =  F->getSubprogram())
	{
		if (SP->describes(F))
			rawstr << SP->getName()<<";"<<SP->getFilename()<<";"<< SP->getLine();
	}
	return rawstr.str();
}

void dumpICFG(SVFModule *mod, ICFG *icfg, PTACallGraph* callgraph)
{
	cout<<"===start dumpICFG\n";
	int totalFound=0;
        for (const SVFFunction* fun : mod->getFunctionSet())
        {
                ICFGNode* root=icfg->getFunEntryICFGNode(fun);
                PTACallGraphNode* ptaNode=callgraph->getCallGraphNode(fun);
		//SVFValue *fxxkValue=(SVFValue *)fun;
		//const Function* func =
		//SVFUtil::cast<Function>(LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(fxxkValue));
		//printf("====func name: %s====\n", dumpFunc(func).c_str());
		cout<<"funcRec: "<<root->getId()<<"\n";
                totalFound+=traverseOnICFG(icfg, root, ptaNode);
		cout<<"======="<<"\n";
        }

	cout<<"totalFound "<<totalFound<<"\n";
}

/*!
 * An example to query/collect all the uses of a definition of a value along value-flow graph (VFG)
 */

void traverseOnVFG(const SVFG* vfg, Value* val)
{
    SVFIR* pag = SVFIR::getPAG();
    SVFValue* svfval = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);

    PAGNode* pNode = pag->getGNode(pag->getValueNode(svfval));
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    FIFOWorkList<const VFGNode*> worklist;
    Set<const VFGNode*> visited;
    worklist.push(vNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            VFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }

    /// Collect all LLVM Values
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        //const VFGNode* node = *it;
        /// can only query VFGNode involving top-level pointers (starting with % or @ in LLVM IR)
        /// PAGNode* pNode = vfg->getLHSTopLevPtr(node);
        /// Value* val = pNode->getValue();
    }
}

int main(int argc, char ** argv)
{

    int arg_num = 0;
    char **arg_value = new char*[argc];
    std::vector<std::string> moduleNameVec;
    LLVMUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    cl::ParseCommandLineOptions(arg_num, arg_value,
                                "Whole Program Points-to Analysis\n");
    
    if (Options::WriteAnder() == "ir_annotator")
    {
        LLVMModuleSet::getLLVMModuleSet()->preProcessBCs(moduleNameVec);
    }

    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);

    int modNum=LLVMModuleSet::getLLVMModuleSet()->getModuleNum();
    cout<<"modNum? "<<modNum<<"\n";
    
    Module *mod=LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule();
    cout<<"modName? "<<mod->getName().str()<<"\n";

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    /// Query aliases
    /// aliasQuery(ander,value1,value2);

    /// Print points-to information
    /// printPts(ander, value1);

    /// Call Graph
    PTACallGraph* callgraph = ander->getPTACallGraph();

    cout<<"total callsite number " <<callgraph->getTotalCallSiteNumber()<<"\n";
    callgraph->dump("xyz.callgraph");
    /// ICFG
    ICFG* icfg = pag->getICFG();

    //ICFGStat stat(icfg);
    //stat.performStat();
 
    dumpICFG(svfModule, icfg, callgraph);

    //icfg->dump("xyz.icfg", true);

    /// Value-Flow Graph (VFG)
    VFG* vfg = new VFG(callgraph);

    /// Sparse value-flow graph (SVFG)
    SVFGBuilder svfBuilder;
    SVFG* svfg = svfBuilder.buildFullSVFG(ander);

    cout<<"====printAllFree===\n";

    printAllFreePts(ander, icfg, mod, callgraph, svfg);

    /// Collect uses of an LLVM Value
    /// traverseOnVFG(svfg, value);

    /// Collect all successor nodes on ICFG
    /// traverseOnICFG(icfg, value);

    // clean up memory
    delete vfg;

    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();

    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".svf.bc");
    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    llvm::llvm_shutdown();
    return 0;
}

