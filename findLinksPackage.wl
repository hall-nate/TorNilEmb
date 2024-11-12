(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["findLinksPackage`"]
findLinks::usage="Returns a full list of all nontrivial links in the specified embedding"
Begin["`Private`"]

(*
Output:
all pairs of disjoint cycles with nonzero linking number in a given torus embedding of a graph g;

Input:
a graph g, a list of edges that cross the upper edge in a "square" representation of a torus embedding of g, and a list of edges that cross the right-hand side edge of the square;

Note: the order of vertices in each edge matters; e.g., if edge {5,2} crosses the upper edge, it means as we go from vtx 5 to vtx 2 (not from 2 to 5), we go through the upper edge (and then reappear at the bottom edge)
*)



findLinks[g_Graph,upEdges_List,rightEdges_List]:=Module[
{cycs,foundLink},
makeEdgeSlopesTable[g,upEdges,rightEdges];
cycs=FindCycle[g,{3,VertexCount[g]-3},All];(*find all cycles of length <= order(g)-3 ;
reason for the "-3": given a cycle, the other cycle in a link must have at least 3 vtxs 
*)
cycs = getSlopes[cycs];(* each element is a pair {slope, cyc} *)
cycs=Sort[cycs];(*sorted by slope*)
cycsBySlope=Split[cycs,#1[[1]]==#2[[1]]&];
(*Split cycles into lists by their slope, and search only within each list*)
cycsBySlope=Select[cycsBySlope,(#[[1,1]]!=0&&#[[1,1]]!=\[Infinity]) &];
(*ignore lists with slope 0 or infinity*)
(*note that the definition of div below marks inessential knots as having slope infinity; this is not strictly true but works for filtering out inessential knots*)
foundLink=False;
If[printAllSlopes,Print[cycs]];
Do[
Do[
Do[
If[IntersectingQ[VertexList[cycsBySlope[[i]][[j]][[2]]],VertexList[cycsBySlope[[i]][[k]][[2]]]],Continue[]];
(*nondisjoint cycles*)
If[printAllSlopes,Print[{cycsBySlope[[i,j]],cycsBySlope[[i,k]]}]];
Print["Found link: ",{cycsBySlope[[i,j]],cycsBySlope[[i,k]]}];
foundLink=True;
,{k,j+1,Length[cycsBySlope[[i]]]}]
,{j,Length[cycsBySlope[[i]]]-1}]
,{i,Length[cycsBySlope]}];
If[!foundLink,Print["No links found."]];
](*Module getLinkingNumsOfTorusEmbedding *)


makeEdgeSlopesTable[g_Graph,upEdges_List,rightEdges_List]:=Module[
{},
(*make an n by n table, where n = ord(g), with the ij-entry as: ;
{1,0} if i\[UndirectedEdge]j is in upEdges;
{-1,0} if j\[UndirectedEdge]i is in upEdges;
{0,1} if i\[UndirectedEdge]j is in rightEdges;
{0,-1} if j\[UndirectedEdge]i is in rightEdges;
{0,0} otherwise;
--------;
edgeSlopesTable is a GLOBAL variable; 
no Return value;
*)
edgeSlopesTable=Table[{0,0},{i,VertexCount[g]},{j,VertexCount[g]}];
Map[(edgeSlopesTable[[#[[1]],#[[2]]]]+={1,0};edgeSlopesTable[[#[[2]],#[[1]]]]+={-1,0})&,
upEdges];
Map[(edgeSlopesTable[[#[[1]],#[[2]]]]+={0,1};edgeSlopesTable[[#[[2]],#[[1]]]]+={0,-1})&,
rightEdges];
](*makeEdgeSlopesTable*)


getSlopes[cycs_List]:=Map[({getSlopeOfOneCyc[#],#})&,cycs];

getSlopeOfOneCyc[cyc_List]:=div[Fold[Plus,Map[(edgeSlopesTable[[#[[1]],#[[2]]]])&,cyc]]];

(*make a distinction when a is also 0*)
div[{a_,b_}]:=If[b==0,Infinity,a/b]

End[]
EndPackage[]
