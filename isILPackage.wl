(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["isILPackage`"]
isIL::usage="isIL returns True if G is intrinsically linked; false if G is nIL";

Begin["`Private`"]

isIL[g_Graph]:=isIL[getVtxPairsFromGraph[g],{}];


(* returns True if the graph is IL *)
isIL[edgeListInput_List]:=isIL[edgeListInput ,{}];

isIL[edgeListInput_List, crossingsInput_List]:=Module[
{},
(* edgeList and crossings are global, used in doSetUp, doMainLoop, etc. *)
edgeList=pushDownVertices[Sort[Map[Sort,edgeListInput]]];
edgeList=Sort[Map[Sort,edgeList]];
edgeList=removeVtxsDeg2orLess[edgeList];
If[edgeList=={},Return[False]];
If[hasTooManyEdgesToBeNIL[edgeList],Return[True]];
If[hasApexDescendant[edgeList],Return[False]];
crossings=crossingsInput;
If[doSetUp[]==0,Return[False]];
If[doMainLoop[]==1, Return[True],Return[False]];
];



getVtxPairsFromGraph[g_Graph]:=Apply[List,EdgeList[g],{1}]; 
getGraphFromVtxPairs[vtxPairs_List]:=Graph[Map[Apply[UndirectedEdge,#]&,vtxPairs,{1}]];
graphWithVtxLabels[g_Graph]:=Graph[EdgeList[g],VertexLabels->All];






(* ============================ *)

hasTooManyEdgesToBeNIL[vtxPairs_List]:=(EdgeCount[getGraphFromVtxPairs[vtxPairs]]>4VertexCount[getGraphFromVtxPairs[vtxPairs]]-10);




hasApexDescendant[vtxPairs_List]:=hasApexDescendant[getGraphFromVtxPairs[vtxPairs]];
hasApexDescendant[g_Graph]:=Module[
{vtxs,vtxPairs,triangles,trianglePairs,result,h},
(* Return True if g is 1-apex or has a 1-apex descendant*)
result=False;
vtxs=VertexList[g];
Do[(*first check if g is 1-apex*)
If[PlanarGraphQ[VertexDelete[g,v]],result=True;Break[]]
,{v,vtxs}
];(*Do*)
If[result==True, Return[True]];
triangles=FindCycle[g,{3},All];
Do[(*check if removing one triangle gives planar graph*)
If[PlanarGraphQ[EdgeDelete[g,t]],result=True;Break[]];
,{t,triangles}
];(*Do*)
Return[result];
](*Module hasApexDescendant*)









getChordless2Links[edgeListInput_List]:=Module[
{allCycles},
numVtxs=edgeListInput//Flatten//Union//Length;

allCycles=First@getChordlessCycsAndPaths[getGraphFromVtxPairs[edgeListInput]];
allCycles=Map[Append[#,#[[1]]]&,allCycles];(*append the 1st element of each cycle to the end of that cycle*)
allCycles=Map[If[Length@#<=numVtxs-2,#,Nothing]&,allCycles];
(*why it says numVtxs-2 :
In a 2-component link, each cycle has at most numVtxs-3 vtxs;
here we have numVtxs-2 because the first vertex is repeated at the end of each cycle.
 *)




(* the line below used to be in the older version of isIL *)
(* allCycles=getChordlessCycsFromCycs[getCycsOfLenL[edgeListInput,numVtxs-3],edgeListInput];
*)
doCycleIntersections[allCycles];
Return[getLinksFullFormat[allCycles]];

](*Module*)






getChordlessCycsAndPaths[g_Graph]:=Module[
{chordlessPaths, chordlessCycs,nbrsLists, pIndex,p,initialVtx,terminalVtx,newCycOrPath},
nbrsLists=getNbrsOfEachVtx[g]; (*nbrsLists\[LeftDoubleBracket]v\[RightDoubleBracket] is a list of nbrs of v*)
chordlessPaths=Apply[List,EdgeList[g],{1}](*list of edges of g, as vtx pairs*);
chordlessCycs={};
For[pIndex=1, pIndex <= Length@chordlessPaths, pIndex++,
p=chordlessPaths[[pIndex]];
Do[(*for i in {1,-1}*)
initialVtx=p[[i]]; terminalVtx=p[[-i]];
Do[(*for each nbr w of initialVtx not in p*)
If[Length[p]>2 && 
!(SelectFirst[p[[2;;-2]],MemberQ[nbrsLists[[w]],#]&]===Missing["NotFound"])(* an interior vtx of p is a nbr of w*)
,Continue[](*adding w won't yield chordless path or cyc*)];
newCycOrPath=If[i==1,Join[{w},p],Reverse[Join[p,{w}]]];
If[!MemberQ[nbrsLists[[terminalVtx]],w],(*newCycOrPath is a path, not a cycle*) 
If[w<terminalVtx,(*to avoid duplicates*)
AppendTo[chordlessPaths,newCycOrPath]
](*If w < terminalVtx*);
,(*else*)
If[w<Min[p]&&initialVtx<terminalVtx,(*add only cycs in normal form*)
AppendTo[chordlessCycs,newCycOrPath];
](*If w<Min*);
](*If !MemberQ*);
,{w,Complement[nbrsLists[[initialVtx]],p]}
](*Do*);
,{i,{1,-1}}
](*Do*);
](*For pIndex*);
Return[{chordlessCycs,chordlessPaths}];
](*Module getChordlessCycsAndPaths *)





getNbrsOfEachVtx[g_Graph]:=Module[
{result},
(* for each vtx v (labeled as a natural number), result\[LeftDoubleBracket]v\[RightDoubleBracket]= list of nbrs of v *)
result=Table[{},{i,Max[VertexList[g]]}];
Do[result[[v]]=AdjacencyList[g,v],{v,VertexList[g]}](*Do*);
Return[result];
](*Module getNbrsOfEachVtx*)


getGraphFromVtxPairs[vtxPairs_List]:=Graph[Map[Apply[UndirectedEdge,#]&,vtxPairs,{1}]];
(*Function defined to get list of edges from list of vertex pairs*)




















removeVtxsDeg2orLess[edgeList_List]:=Module[
{degs,i,eList=edgeList,pos},
(* get rid of all vtxs v of deg 2 or less:;
"remove" vtx v from edgeList by merging it with any adjacent vtx u; i.e., contract the edge {u,v},  *)
While[True,(* keep removing vtx of deg 2 until there are none *)
degs=getDegs[eList];
If[{}!=(pos=Position[degs,1]),eList=removeVtx[pos[[1,1]],eList];Continue[]];
If[{}!=(pos=Position[degs,2]),eList=removeVtx[pos[[1,1]],eList];Continue[]];
Break[];
];(* While True *)
Return[eList];
];

removeVtx[v_Integer,edgeList_List]:=Module[
{eList,u, pos},
(* 
"remove" vtx v from edgeList by merging it with any adjacent vtx u; i.e., contract the edge {u,v}, and call the new vertex u;
find the first edge e containing v; say e={u,v} or {v,u};
remove edge e;
in the remaining edges, replace all v's with u's;
*)
eList=edgeList;
pos=Position[eList,v];
u=eList[[pos[[1,1]],3-pos[[1,2]]]];
eList=Delete[eList,pos[[1,1]]];
eList=eList/.v->u;
Return[pushDownVertices[Union[Map[Sort,eList]]]];
];



getDegs[edgeListInput_List]:=Module[
{nVertices,flatEL},
flatEL=Flatten[edgeListInput];
nVertices=Length@Union[flatEL];
Return[Map[Count[flatEL,#]&,Range[nVertices]]];
]




(***************************)

















(*--------------------------------------------------------*)


(* global variables:
dcm, bicm, dcmCompact,  nVertices,
 

*)




(*
Create the following two tables: ;
disjoint cycles matrix: dcm[[i,j]]=1 iff cycle i and cycle j are disjoint;
bad intersections cycles matrix: bicm[[i,j]]=1 iff cycle i and cycle j have bad intersection;

Note: each cyc in cycles is assumed to be in standard position: e.g., standard position for {3,5,4,2,8,3} is {2,4,5,3,8,2} (and not {2,8,...});
cycles is assumed to be pre-sorted;
*)
doCycleIntersections[cycles_List]:=Module[
{len, i, j},
len=Length[cycles];
dcm= bicm =Table[0,{i,len},{j,len}];
dcmCompact=Table[{},{i,len}];
For[i=1,i<=len,i++,
For[j=i+1,j<=len,j++,
Switch[cycleIntersection[cycles[[i]],cycles[[j]]],
0,dcm[[i,j]]= dcm[[j,i]]=1; AppendTo[dcmCompact[[i]],j];AppendTo[dcmCompact[[j]],i]; , 
-1,bicm[[i,j]]=bicm[[j,i]]=1;
]
]
]
]





(* determine whether intersection of cycles c1 and c2 is connected:
return 0 if the intersection is empty, 1 if the intersection is connected, -1 if the intersection is not connected.*)
cycleIntersection[c1_List,c2_List]:=
Module[
{v},
Switch[(v=Length[Intersection[c1,c2]]),0,Return[0],1,Return[1]];
If[v==1+Length[Intersection[Map[Sort,Thread[List[Drop[c1,-1],Drop[c1,1]]]],Map[Sort,Thread[List[Drop[c2,-1],Drop[c2,1]]]]]],1,-1]
]





(* create a list of links from dcm *)
getLinks[]:=Module[
{links,doOneRow},
doOneRow[i_Integer,row_List]:=Table[{i,row[[j]]},{j,Length[row]}];
links=Table[doOneRow[i,dcmCompact[[i]]],{i,Length[dcmCompact]}];
Return[Apply[Union,Map[Sort,links,2]]];
]


getLinksFullFormat[cycles_List]:=Module[
{links,f},
links=getLinks[];
f[{a_,b_}]:={cycles[[a]],cycles[[b]]};
Return[Map[f,links]];
]















(***************************************)






(* put cycle in "normal" or "standard" form, i.e., start with smallest vertex, go in the direction of smallest neigbor, and repeat first vtx at the end; e.g.:
{5,8,3,1,4} \[Rule] {1,3,8,5,4,1}
*)
normalizeCycle[cycle_List]:=Module[
{pm,cyc},
cyc=cycle;
pm=Position[cyc,Min[cyc]][[1,1]];
cyc=Join[Take[cyc,{pm,-1}],Take[cyc,{1,pm-1}]];
If[cyc[[2]]>cyc[[-1]],cyc=Join[{cyc[[1]]},Reverse[Take[cyc,{2,-1}]]]];
Append[cyc,cyc[[1]]]
]








pushDownVertices[edgeList_List]:=Module[
{edgeListNew,vtxsOld,vtxsNew,lowestMissingVtx},
(*
Relabel the vertices (and edges) so that there are no missing vtxs;
If the highest vertex label is larger than the number of vtxs, there is a missing vtx, so relabel this highest vtx to be the smallest missing vtx;
keep repeating until there are no missing vtxs.
*)
If[edgeList=={},Return[{}]];
vtxsNew=Union[Flatten[edgeList]];
edgeListNew=Map[Sort,edgeList];
While[vtxsNew[[-1]]>Length[vtxsNew],
lowestMissingVtx=getLowestMissingVtx[vtxsNew];
edgeListNew=ReplaceAll[edgeListNew,vtxsNew[[-1]]->lowestMissingVtx];
vtxsNew[[-1]]=lowestMissingVtx;
vtxsNew=Sort[vtxsNew];
];(*While*)
Return[Sort[Map[Sort,edgeListNew]]]
]
(*Module*)


getLowestMissingVtx[vtxs_List]:=
For[i=1, i<=Length[vtxs],i++,
If[vtxs[[i]]>i,Return[i]]
](*For*)



















(* ============================ *)







makeAllEdgePairs[edgeList_List]:=Module[
{allEdgePairs,i,j},
(* Create list of all pairs of disjoint edges *)
allEdgePairs={};
For[i=1,i<= Length[edgeList],i++,
For[j=i+1, j<= Length[edgeList],j++,
If[edgeList[[i]] \[Intersection] edgeList[[j]] =={},
allEdgePairs=Append[allEdgePairs,{edgeList[[i]],edgeList[[j]]}];
]
]
];
Return[allEdgePairs];
]



makeCrossings[edgeList_List]:=Module[
{xings={},e, i, j},
e=Sort[Map[Sort,edgeList]];
For[i=1,i<=Length[e],i++,
For[j=i+1,j<=Length[e],j++,
If[e[[i,1]]<e[[j,1]]<e[[i,2]]<e[[j,2]] ,AppendTo[xings,{e[[i,1]],e[[i,2]],e[[j,1]],e[[j,2]]}];AppendTo[xings,1];Continue[]];
If[e[[j,1]]<e[[i,1]]<e[[j,2]]<e[[i,2]],AppendTo[xings,{e[[j,1]],e[[j,2]],e[[i,1]],e[[i,2]]}];AppendTo[xings,1]]]];
Return[xings];
]


swap[L_,i_,j_]:=Module[
{lis:=L},
lis[[i]]:=L[[j]];
lis[[j]]:=L[[i]];
lis
]




edgePairSort[{{a_,b_},{c_,d_}}]:=Module[
{min1,max1,min2,max2},
(* Sorts a pair of edges with respect to each other, without taking into effect or changing the order of vertices in each edge. *)
min1=Min[a,b];
max1=Max[a,b];
min2=Min[c,d];
max2=Max[c,d];
If[min1<min2,Return[{{a,b},{c,d}}]];
If[min2<min1,Return[{{c,d},{a,b}}]];
If[max1<max2,Return[{{a,b},{c,d}}]];
Return[{{c,d},{a,b}}];
]


cycsToEdgePairs[cyc1_, cyc2_]:=Module[
{consecPairs, cyc1edges, cyc2edges},
(* cyc1 & cyc2 are lists representing cycles;
Output: list of all edge-pairs with one edge from each cycle;
each pair is sorted.
*)

consecPairs[lis_]:= Thread[List[Delete[lis,-1],Delete[lis,1]]];
cyc1edges=consecPairs[cyc1];
cyc2edges=consecPairs[cyc2];
Flatten[Outer[List,cyc1edges,cyc2edges,1],1]
]



getXingNum[ep_List]:=Module[
{edgePair,pos,s=1},
(* Finds the crossing number between two edges in ep (edge pair) according to their listing in the global variable crossings;
returns 0 if ep is not in the crossings list.
Format for ep: {{a,b},{c,d}};
*)
edgePair=edgePairSort[ep];
edgePair=Flatten[edgePair]; (* need to change format to {a,b,c,d} since that's the format used in crossings *)
If[edgePair[[1]]>edgePair[[2]],(edgePair=swap[edgePair,1,2];s=-1)];
If[edgePair[[3]]>edgePair[[4]],(edgePair=swap[edgePair,3,4];s=-1*s)];
pos:=Flatten[Position[crossings,edgePair]];
If[pos!={},Return[s*Extract[crossings,pos+1]]];
Return[0] (* 0 crossing for this pair *)
]






linkNum[epList_]:=Module[
{},
(1/2)*Apply[Plus,Map[getXingNum,epList]]
]





edgePairSign[{{a_,b_},{c_,d_}}]:=Module[
{},
(* Returns +1 or -1 according to the edges' orientations and edge pair *)
Sign[(b-a)(d-c)]
]












(* A matrix representing a system of linear equations, one equation for each link from the input, saying the link has linking number zero. ;
There is one variable for each pair of disjoint edges; the variable represents the number of crossings in an arbitrary embedding of the graph (not necessarily the given embedding). ;
The equation is constructed by adding the coefficients of the relavent variables for each link, with appropriate +-1 multipliers, plus the "current" linking number (for the given embedding), and setting the sum equal to zero;
so, 
sum of (+-1)vars = - current linking number  ;
the coefficients become one row of the matrix. *)
makeFullAugmentedMatrix[cycPairs_List,allEdgePairs_List]:=Module[
{result,i,epList,maxV,newEqn,temp,pos,ZEROeqn,epPositionsInZEROEQN},
(* allEdgePairs is a list of all pairs of disjoint edges in the graph;
ZEROeqn is a list with a 0 (as coeff) for each edgepair, 
which serves as a template/blank eqn, where some of the coeffs will
later be set from 0 to nonzero *)
(*
Let newEqn = ZEROeqn;
For each pair of cycles, get all pairs of edges w/ one in each cycle, call this list eplist;
For each ep in eplist, insert sign(ep) into newEqn;
To find where to insert it, use the look up table epPositionsInZEROeqn
*)
result={};
maxV=Max[Flatten[edgeList]];
epPositionsInZEROEQN=ConstantArray[Null,{maxV,maxV,maxV,maxV}];
For[i=1,i<=Length@allEdgePairs,i++,
epPositionsInZEROEQN[[allEdgePairs[[i,1,1]],allEdgePairs[[i,1,2]],allEdgePairs[[i,2,1]],allEdgePairs[[i,2,2]]]]=i;
(*e.g. if {{1,4},{2,3}} is the 6th element in allEdgePairs,
then epPositionsInZEROEQN\[LeftDoubleBracket]1,4,2,3\[RightDoubleBracket] is set to 6*)
](*For*);
ZEROeqn=Table[0,{i,Length@allEdgePairs}];
Do[
epList=cycsToEdgePairs[cp[[1]],cp[[2]]];
newEqn=ZEROeqn;
Do[
temp=Flatten[Sort[Map[Sort,ep]]];(* e.g., Sort[Map[Sort,{{3,2},{4,1}}]] gives {{1,4},{2,3}}*)
pos=epPositionsInZEROEQN[[temp[[1]],temp[[2]],temp[[3]],temp[[4]]]];(*position of ep*)
newEqn[[pos]]=edgePairSign[ep];
,{ep,epList}
](*Do*);
AppendTo[newEqn,-linkNum[epList]] ;
AppendTo[result,newEqn];
,{cp,cycPairs}
](*Do*);
Return[result];
](*Module makeFullAugmentedMatrix*)


















 
doSetUp[]:=Module[
{},
edgeList=Sort[Map[Sort,edgeList]];
allEdgePairs=makeAllEdgePairs[edgeList];(*all disjoint pairs of edges in the graph*)
If[crossings=={},crossings=makeCrossings[edgeList]];
allLinks=getChordless2Links[edgeList];
If[allLinks=={},Return[0]];
fullAugmentedMatrix=makeFullAugmentedMatrix[allLinks,allEdgePairs];
]






(************* MAIN LOOP ************)


doMainLoop[]:=Module[
{subAugMtx,soln,tr,indexer,A,b,j,
foundSolnMod2,integerSolsCounter=0,previousSoln={}},
(* return 1 if the graph is IK, 0 if  can't decide *)
foundSolnMod2=False;

subAugMtx=fullAugmentedMatrix;
tr=Transpose[subAugMtx];
A=Transpose[Drop[tr,-1]];
b=Last[tr];
soln=LinearSolve[A,b,Modulus->2];
If[SameQ[Head[soln],List],
foundSolnMod2=True;
soln=LinearSolve[A,b];
If[SameQ[Head[soln],List],
If[!MemberQ[Map[IntegerQ,soln],False],
If[previousSoln!=soln,
previousSoln=soln;
(* Print["\n \n \n \n \n Found integer solution: ",soln, "\n \n"]; *)
integerSolsCounter++;
];
]; 
];
];


(*Unprotect[edgeList,crossings,dcm,bicm,dcmCompact,allEdgePairs,allLinks,fullAugmentedMatrix];
Remove[edgeList,crossings,dcm,bicm,dcmCompact,allEdgePairs,allLinks,fullAugmentedMatrix];*)(*To free up memory*)

 If[foundSolnMod2,
 (* Print["There exist mod 2 link-less embeddings, so the graph is not IL."]; *) 
(*If[integerSolsCounter==0,Print["Mod 2 solutions were found; and no integer solutions were found. But there may still exist an integer solution: LinearSolve[] doesn't look for all solutions; it only tries to find one (real) solution, which may or may not happen to be an integer soln."]]; *)
Return[0],
(* Print["No mod 2 link-less embeddings exist. So this graph is IL."]; *)
Return[1]
]; 
]


(* ======================  *)
End[]
EndPackage[]
