import sys
import os
import shutil

from graph_tool.all import *

import numpy
allRetNodes=set()
allExitNodes=set()

def procBB(inFile):
	line=inFile.readline()
	if not line:
		return None
	if not line.startswith("ICFGID"):
		return None

	temp1=line.split()
	id=int(temp1[1])
	line=inFile.readline()
	temp2=line.split()
	type=temp2[1]
	line=inFile.readline()
	temp3=line.split()
	del temp3[0]
	children=[]
	for child in temp3:
		children.append(int(child))
	if type=="funCall":
		line=inFile.readline()
		temp4=line.split()
		retId=int(temp4[1])
	else:
		retId=-1;

	return(id, type, children, retId)

def addEdge(g, idMap, id, children):
	if id in idMap:
		src=idMap[id]
	else:
		src=g.add_vertex()
		idMap[id]=src
	for child in children:
		if child in idMap:
			dst=idMap[child]
		else:
			dst=g.add_vertex()
			idMap[child]=dst

		g.add_edge(src, dst)

def procFunc(inFile, allFuncs):
	callNodes=dict()
	callRetMap=dict()
	retNodes=set()
	exitNodes=dict()
	g=Graph()

	#BBs=dict()

	idMap=dict()

	line=inFile.readline()
	if line and line.strip().startswith("funcRec"):	
		temp=line.split()
		entryID=int(temp[1])
	else:
		return None
	while True:
		tup=procBB(inFile)
		
		if not tup:
			break

		id=tup[0]
		type=tup[1]
		children=tup[2]
		retId=tup[3]

		#BBs[id]=children
		#only put in BBs intra nodes? record children of calls and exits in their own dict

		if type=="funCall":
			callNodes[id]=children
			callRetMap[id]=retId
			addEdge(g, idMap, id, [retId])
		elif type=="funRet":
			allRetNodes.add(id)
			retNodes.add(id)
			#BBs[id]=children

			#for child in children:
			addEdge(g, idMap, id, children)

		elif type=="funExit":
			allExitNodes.add(id)
			exitNodes[id]=children
		else:
			#BBs[id]=children
			addEdge(g, idMap, id, children)
			

	#line=inFile.readline()	#eat up junk....

	idMap2=g.new_vertex_property("int64_t")
	for id in idMap:
		v=idMap[id]
		idMap2[v]=id

	return (entryID, callNodes, retNodes, callRetMap, g, idMap, idMap2, exitNodes)

def dumpFunc(func):
	entryId=func[0]
	#BBs=func[1]
	callNodes=func[1]
	print("entryId " + (str(entryId)))
	temp=""
	temp2=""
	for shit in callNodes:
		#temp=temp+str(callNodes)+" "
		temp2=""
		for shit2 in callNodes[shit]:
			temp2=temp2+str(shit2) + " "
		print("callNodeID: " + str(shit))
		print("targets: " + temp2)
	#print("callNodes " + temp)

def genRevMap1(allFuncs):
	revMap=dict()
	for entryId in allFuncs:
		tup=allFuncs[entryId]
		idMap=tup[5]

		for id in idMap:
			revMap[id]=entryId

	return revMap;

def genRevMap2(allFuncs):
	revMap=dict()
	for entryId in allFuncs:
		tup=allFuncs[entryId]

		retNodes=tup[2]
		g=tup[4]
		idMap=tup[5]
		idMap2=tup[6]

		for retNode in retNodes:
			#callout=set()

			retVex=idMap[retNode]
			for e in dfs_iterator(g, retVex):
				vex=e.target()
				vexId=idMap2[vex]
				if vexId in revMap:
					temp=revMap[vexId]
					temp.add(retNode)
				else:
					temp=set()
					temp.add(retNode)
					revMap[vexId]=temp

	return revMap

def genCallgraph2(allFuncs, g, g_idMap):
	#connect func ret to retNodes...
	for entryId in allFuncs:
		tup=allFuncs[entryId]
		# (entryID, callNodes, retNodes, callRetMap, g, idMap, idMap2, exitNodes)
		exitNodes=tup[7]
		if len(exitNodes)>1:
			print("fxxk, more than one exit for func " + str(entryId))
			return

		for exitId in exitNodes:
			children=exitNodes[exitId]
			for c in children:
				if not c in allRetNodes:
					print("fxxk, exit to non ret node: exit " + str(exitId) + " target: " + str(c))

			addEdge(g, g_idMap, entryId, children)

	#UAF will happen in calling the function, so no need to check for it inside the func...
	#need to handle globals..
	#(entryID, callNodes, retNodes, callRetMap, g, idMap, idMap2, exitNodes)
	#find callsites reachable from retNodes and connect retNodes to funcs
	for entryId2 in allFuncs:
		tup2=allFuncs[entryId2]
		retNodes=tup2[2]
		funcCfg=tup2[4]
		callNodes=tup2[1]
		idMap=tup2[5]
		idMap2=tup2[6]

		for r in retNodes:
			retVex=idMap[r]
			for e in dfs_iterator(funcCfg, retVex):
				vex=e.target()
				vexId=idMap2[vex]
				if vexId in callNodes:
					children=callNodes[vexId]
					children2=set()
					for c in children:
						if not c in allFuncs:
							print("fxxk calling non fun entry? caller " + str(vexId) + " callee " + str(c))
							if (not c in allRetNodes) and (not c in allExitNodes):
								print("not even ret/exit")
						else:
							children2.add(c)
					addEdge(g, g_idMap, r, children)

def genCallgraph(allFuncs):
	g=Graph()
	idMap=dict()
	for entryId in allFuncs:
		tup=allFuncs[entryId]
		callNodes=tup[1]
		children=set()
		for child in callNodes:
			temp=callNodes[child]
			for c in temp:
				if c in allFuncs:
					children.add(c)
				else:
					print("fxxk calling non func entry?  caller " + str(entryId) + " callee " + str(c))
					if (not c in allRetNodes) and (not c in allExitNodes):
						print("not even ret/exit")
			#children.update(temp)
		#print("gen callgraph " + str(entryId))
		#print("edges " + str(children))
		addEdge(g, idMap, entryId, children)

	return (g, idMap)

def checkGraph(callgraphTup, allFuncs):
	callgraph=callgraphTup[0]
	callgraphMap=callgraphTup[1]

	for entryId in allFuncs:
		if not entryId in callgraphMap:
			print("fxxk, no src id " + str(entryId) + " in map")
			return
		#print("found entryID " + str(entryId))

		srcV=callgraphMap[entryId]
		temp=srcV.out_neighbors()
		neighbors=list(temp)
		tup=allFuncs[entryId]
		callNodes=tup[1]
		for caller in callNodes:
			temp=callNodes[caller]
			#print("testing caller " + str(caller))
			for target in temp:

				#neighbors2=srcV.out_neighbors()

				if not target in callgraphMap:
					print("fxxk, no target id " + str(target) + " in map")
					return
				targetV=callgraphMap[target]

				#nStr=""

				#for n in neighbors2:
				#	nStr=nStr+str(n)+" "
				#print("neighbors? " + nStr)

				#neighbors=srcV.out_neighbors()

				if targetV not in neighbors:
					print("fxxk, target id " + str(target) + " not in neighbor?")
					return
				
				#print("found target id " + str(target))

def readOneUse(inFile, result):
	line=inFile.readline()
	if not line:
		return None
	line=inFile.readline()
	if not line.strip().startswith("useId:"):
		return None
	temp=line.strip().split()
	useId=int(temp[1])
	line=inFile.readline()
	if line.strip().startswith("use:fxxk"):
		return 1
	temp2=line.strip().split()
	icfgId=int(temp2[1])
	result[useId]=icfgId
	return 1

def readUseMap(inFile):
	result=dict()
	line=inFile.readline()
	while not line.startswith("====printAllUs"):
		line=inFile.readline()
	while True:
		if not readOneUse(inFile, result):
			break

	return result

def readFreeUse(inFile, useMap):
	result=dict()
	line=inFile.readline()
	while not line.startswith("====printAllFree==="):
		line=inFile.readline()
	while True:
		line=inFile.readline()
		if not line:
			break
		if not line.startswith("icfg:"):
			print("end line " + line)
			break
		temp=line.strip().split()
		freeId=int(temp[1])
	
		line=inFile.readline()
		useSet=set()
		if not line.strip().startswith("use:"):
			print("fxxk, wrong use line? " + line)
			break


		temp2=line.strip().split()
		del(temp2[0])

		print("freeId " + str(freeId) + " use len " + str(len(temp2)))
		for u in temp2:
			useId=int(u)
			if useId in useMap:
				useCFG=useMap[useId]
				useSet.add(useCFG)
		result[freeId]=useSet

	return result

def readAllRoots(inFile):
	rootMap=dict()
	line=inFile.readline()
	while not line.startswith("====printing roots===="):
		line=inFile.readline()
	line=inFile.readline()
	while line:
		if line.startswith("rootID"):
			temp=line.split()
			rootId=int(temp[1])
			line1=inFile.readline()
			#ActualRetVFGNode
			#FormalParmVFGNode
			#IntraPHIVFGNode
			#ActualOUTVFGNode
			#AddrVFGNode
			#NullPtrVFGNode
			if line1.startswith("NullPtrVFGNode"):
				line2=inFile.readline()
				line=inFile.readline()
				rootMap[rootId]=0
			elif line1.startswith("IntraPHIVFGNode") or line1.startswith("BinaryOPVFGNode"):
				line=inFile.readline()
				rootMap[rootId]=0
			elif line1.startswith("AddrVFGNode"):
				line2=inFile.readline()
				line=inFile.readline()
				if line2.strip().startswith("@"):
					rootMap[rootId]=2
				else:
					rootMap[rootId]=0
			elif line1.startswith("ActualRetVFGNode") or line1.startswith("FormalParmVFGNode"):
				line2=inFile.readline()
				line=inFile.readline()
				rootMap[rootId]=0
			elif line1.startswith("ActualOUTSVFGNode"):
				line2=inFile.readline()
				line3=inFile.readline()
				line=inFile.readline()
				rootMap[rootId]=0
			else:
				print("wtf? none of the above? " + line1)
				return
		else:
			print("fxxk, unexpected start of root rec?" + line)
			break

	return rootMap

def readUseClassification(inFile, rootMap):
	useClassMap=dict()
	line=inFile.readline()
	while not line.startswith("=====classifyAllUse===="):
		line=inFile.readline()
	while True:
		line=inFile.readline()
		if not line:
			break
		if not line.startswith("classifying useId"):
			print("fxxk, wrong header in readUseClassification? " + line)
			break
		temp=line.split()
		useId=int(temp[2])
		useClass=0

		line=inFile.readline()
		if not line.startswith("found vfgNode"):
			useClassMap[useId]=-1
		else:
			line=inFile.readline()
			print("root? " + line)
			temp2=line.split()
			del temp2[0]
			for r in temp2:
				root=int(r)
				if root in rootMap:
					rootClass=rootMap[root]
					useClass=useClass|rootClass

			line=inFile.readline()
			temp3=line.split()
			print(line)
			useClass2=int(temp3[3])
			useClass=useClass|useClass2
			useClassMap[useId]=useClass

	return useClassMap

def getSources(src, funcTup):
	#(entryID, callNodes, retNodes, callRetMap, g, idMap, idMap2, exitNodes)
	callNodes=funcTup[1]
	exitNodes=funcTup[7]
	callRetMap=funcTup[3]
	g=funcTup[4]

	idMap=funcTup[5]
	idMap2=funcTup[6]

	if src in callRetMap:
		print("hit callRetMap in getSource")
		result=set()
		result.add(callRetMap[src])
		return result

	if not src in idMap:
		print("fxxk, no src vex?")

	rootVex=idMap[src]
	tempSet=set(g.vertices())
	print("getsources src " + str(src) + " graph size " + str( len(tempSet) ))
	#nStr=""
	#for e in rootVex.out_neighbors():
	#	nStr=nStr+" "+idMap2[e]
	#print("neighbors " + nStr)

	result=set()
	for e in dfs_iterator(g, rootVex):
		targetVex=e.target()
		vexId=idMap2[targetVex]

		#any use of the freed item in a called function will also happen in parameter pass?
		#unless it's global....

		#print("target id " + str(vexId))
		if vexId in callNodes:
			#print("ding")
			children=callNodes[vexId]
			result.update(children)

		if vexId in exitNodes:
			#print("ding2")
			children=exitNodes[vexId]
			result.update(children)

	return result

def getTargets(rawTargets, revMap, revMap2):
	result=set()
	fxxkCount=0
	for r in rawTargets:
		#UAF will happen in calling the function, so no need to look for it inside the func?
		#globals....??

		#if r in useClassMap:
		#	useClass=useClassMap[r]
		#else:
		#	print("fxxk, no use class for " + str(r))
		#	useClass=0

		if r in revMap: 	#and useClass!=-1 and useClass!=1:
			result.add(revMap[r])
		if r in revMap2:
			result.update(revMap2[r])
		if (not r in revMap) and (not r in revMap2):
			fxxkCount=fxxkCount+1
	if fxxkCount!=0:
		print("fxxkCount: " + str(fxxkCount))
	return result

def reachable(distMap, idMap, src, dst):
	if src in idMap and dst in idMap:
		#print("src " + str(src) + " dst " + str(dst))
		srcVex=idMap[src]
		dstVex=idMap[dst]
		vec1=distMap[srcVex]
		dist=vec1[dstVex]
		#print("dist? " + str(dist))
		if dist==numpy.iinfo(numpy.int32).max:
			return False
		else:
			return True
	#print("fxxk, no such nodes? src")
	return False

def main():
	allFuncs=dict()
	inFile=open(sys.argv[1], 'r')
	#search for dumpICFG
	line=inFile.readline()
	while not line.strip().startswith("===start dumpICFG"):
		line=inFile.readline()
	#func=procFunc(inFile, allFuncs)
	count=0
	while True:
		func=procFunc(inFile, allFuncs)
		if not func:
			break
		entryId=func[0]
		allFuncs[entryId]=func

		dumpFunc(func)
		#count=count+1
		#if count>10:
		#	break

	callgraphTup=genCallgraph(allFuncs)
	callgraph=callgraphTup[0]
	callgraphMap=callgraphTup[1]

	print("====checkgraph====")
	checkGraph(callgraphTup, allFuncs)

	print("====genRevMpa1====")
	revMap=genRevMap1(allFuncs)
	print("genRevMap2=====")
	revMap2=genRevMap2(allFuncs)

	print("====genCallgraph2====")
	genCallgraph2(allFuncs, callgraph, callgraphMap)

	nodeSet=set(callgraph.vertices())
	print("num vertices in callgraph " + str( len(nodeSet) ))
	print("====readUsseMap===")
	inFile2=open(sys.argv[1], 'r')
	useMap=readUseMap(inFile2)
	print("useMap size: " + str(len(useMap)))

	print("====useOfFree===")
	inFile3=open(sys.argv[1], 'r')
	freeMap=readFreeUse(inFile3, useMap)

	print("=====readAllRoots====")
	inFile4=open(sys.argv[1], 'r')
	rootMap=readAllRoots(inFile4)

	#print("=====readUseClassify====")
	#inFile5=open(sys.argv[1], 'r')
	#useClassMap=readUseClassification(inFile5, rootMap)

	#print("yoohoo")
	#zeroCount=0
	#oneCount=0
	#twoCount=0
	#threeCount=0
	#wrongCount=0
	
	#for u in useClassMap:
	#	if useClassMap[u]==1:
	#		oneCount=oneCount+1
	#	if useClassMap[u]==-1:
	#		wrongCount=wrongCount+1
	#	if useClassMap[u]==2:
	#		twoCount=twoCount+1
	#	if useClassMap[u]==3:
	#		threeCount=threeCount+1

	#print("total " + str(len(useClassMap)))
	#print("ones " + str(oneCount))
	#print("twos " + str(twoCount))
	#print("threes " + str(threeCount))
	#print("wrong " + str(wrongCount))
	#sys.exit()
	#for f in freeMap:
	#	targetSet=getTargets(freeMap[f], revMap, revMap2)
	#	print("freeId: " + str(f) + " use size " + str(len(freeMap[f])) )
	#	print("\ttargetSet size " + str( len(targetSet) ))

	print("num frees " + str(len(freeMap)) )

	print("num funcs " + str( len(allFuncs) ))
	print("num retNodes " + str( len(allRetNodes) ))
	#for v in callgraph.vertices():
	#	print("funcId " + str(v))
	#	temp=""
	#	for w in v.out_neighbors():
	#		temp=temp+str(w) + " "
	#	print("children: " + temp)

	print("start shortest distance...")
	dist_map=callgraph.new_vp("int32_t", numpy.iinfo(numpy.int32).max)
	dist_map=shortest_distance(callgraph)

	#print("====callgraph map=====")
	#for id in callgraphMap:
	#	print(str(id))

	numPass=0
	numHit=0
	print("start reachability...")

	hitMap=dict()
	for f in freeMap:
		targetSet=getTargets(freeMap[f], revMap, revMap2)
		srcFuncId=revMap[f]
		srcFuncTup=allFuncs[srcFuncId]
		srcSet=getSources(f, srcFuncTup)
		hitCount=0

		hitSet=set()
		for s in srcSet:

			for t in targetSet:
				if reachable(dist_map, callgraphMap, s, t):
					hitCount=hitCount+1
					hitSet.add(t)

		hitFunc=set()
		for h in hitSet:
			f=revMap[h]
			hitFunc.add(f)



		#	for t0 in freeMap[f]:
		#		print(".")
		#		targetSet=getTargets([t0], revMap, revMap2)
		#		for t in targetSet:
		#		#print("src " + str(f) + " dst " + str(t))
		#			if reachable(dist_map, callgraphMap, s, t):
		#				hitCount=hitCount+1
		#				break

		if hitCount!=0:
			numHit=numHit+1
			print("freeId " + str(f) + "targetSize " + str( len(targetSet) ) + " hitCount " + str(hitCount))
			print("num hit func " + str( len(hitFunc) ))
		else:
			numPass=numPass+1
			print("pass..")

		print(str(numHit) + " / " + str(numPass))
		print("total done " + str(numHit+numPass))
if __name__ == "__main__":
	main()
