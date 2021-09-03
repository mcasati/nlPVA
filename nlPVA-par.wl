(* ::Package:: *)

BeginPackage["nlPVA`"];

Print["NonlocalPVA: a Mathematica package for working with weakly non local Poisson Vertex Algebras"];
Print["Parallel version (2021). M. Casati, P. Lorenzoni, D. Valeri & R. Vitolo"];

Clear["nlPVA`*"];
Clear["nlPVA`Private`*"];



(*Explain meaning of the functions*)
SetN::usage="It sets the number of generators of the PVA. Default=1";
GetN::usage="It gives the number of generators of the PVA. Default=1";
SetTail::usage="It sets the lenght of the nonlocal tail. Observe that for compatibility of operators, the tail must be set as the longest of the two.Default=1";
GetTail::usage="It gives the lenght of the nonlocal tail";
SetMaxO::usage="It sets the max order of derivatives to which to compute the bracket. Default=5";
GetMaxO::usage="It gives the max order of derivatives to which to compute the bracket. Default=5";
gen::usage="gen is the array of the generators";
TD::usage="it replaces the total derivative operator";
SetGenName::usage="It sets the standard name for the generators of PVA. Default=u";
GetGenName::usage="It gives the name for the generators of PVA. Default=u";
SetVarName::usage="It sets the name for the independent variable. Default=x";
GetVarName::usage="It gives the name for the independent variable. Default=x";
BuildBracket::usage="It constructs the lambda bracket object, starting from the local part and the elements in the definition of the weakly nonlocal tail";
GetBracket::usage="It gives a matrix containing the full expression of the lambda bracket between generators, in an explicit form";
CompB::usage="It computes the compatibility condition between two lambda brackets evaluated on a triple of generators (equivalent to the Schouten bracket between the corresponding bivectors)";
SetFormalParameter::usage="It sets the formal variable used in the definition of the bracket. Default=\[Beta]";
GetFormalParameter::usage="It gives the formal variable used in the definition of the bracket. Default=\[Beta]";
PVASkew::usage="PVASkew computes the condition of skewsymmetry for a lambda bracket and returns a matrix";
CompatCheck::usage="Computes the compatibility condition between two brackets and gives the list of its independent entries. It is equivalent to the PVA-Jacobi identity if computed between two copies on the same bracket";



gen:=If[$d==1,{$genname[$varname]},Array[Subscript[$genname, #][$varname]&,$d]];
TD[a_]:=D[a,$varname];


Begin["`Private`"];
$d=1;
$ltail=1;
$maxO=5;
$genname=u;
$varname=x;
$parname=\[Beta];
SetN[newd_Integer]:=Module[{},$d=newd;DistributeDefinitions["nlPVA`"]];
GetMaxO[]:=$maxO;
SetGenName[newname_]:=Module[{},$genname=newname;DistributeDefinitions["nlPVA`"]];
GetGenName[]:=$genname;
SetVarName[newname_]:=Module[{},$varname=newname;DistributeDefinitions["nlPVA`"]];
GetVarName[]:=$varname;
SetFormalParameter[newname_]:=Module[{},$parname=newname;DistributeDefinitions["nlPVA`"]];
GetFormalParameter[]:=$parname;
SetTail[newl_Integer]:=Module[{},$ltail=newl;DistributeDefinitions["nlPVA`"]];
GetTail[]:=$ltail;


Term3D[f_,m_,i_,\[Alpha]_]:=Nest[-\[Alpha]*#-D[#,$varname]&,D[f,D[gen[[i]],{$varname,m}]],m];
Term2D[f_,P_,i_,j_,\[Alpha]_,\[Lambda]_]:=(P[[j,i]]/.{Times[\[Lambda]^n_, e_] :>Times[e,Nest[\[Alpha]*#+D[#,$varname]&,f,n]],Times[\[Lambda],e_]:>Times[e,Times[\[Alpha],f]+D[f,$varname]],\[Lambda]:>Times[\[Alpha],f]+D[f,$varname]})+Times[Coefficient[P[[j,i]],\[Lambda],0],f-1];
Term1D[f_,m_,g_,j_,\[Alpha]_]:=D[g,D[gen[[j]],{$varname,m}]]*Nest[\[Alpha]*#+D[#,$varname]&,f,m];
Lambdamnij[f_,g_,m_,n_,i_,j_,P_,\[Alpha]_]:=Term1D[Term2D[Term3D[f,m,i,\[Alpha]],P,i,j,\[Alpha],$parname],n,g,j,\[Alpha]];
LambdaBLoc[f_,g_,P_,\[Alpha]_]:=Module[{p=\[Alpha]},Sum[Lambdamnij[f,g,m,n,i,j,P,p],{m,0,$maxO},{n,0,$maxO},{i,1,$d},{j,1,$d}]];
IntegrLoc[expr_,param_List]:=Module[{lastpar=Last[param],l=Length[param]-1,dummy},dummy=Collect[expr,lastpar];dummy=Collect[dummy/.{Times[lastpar^n_, e_] :>Nest[Sum[-param[[i]]*#,{i,l}]-D[#,$varname]&,e,n],Times[lastpar,e_]:>Sum[Times[-param[[i]],e],{i,l}]-D[e,$varname],lastpar:>Sum[-param[[i]],{i,l}]},lastpar];dummy];


GetNLoc[PNlocEl_,\[Lambda]_]:=Table[Sum[PNlocEl[[1]][[a,b]]*PNlocEl[[2]][[a,r]]*Subsuperscript[PNlocEl[[3]],b,s][\[Lambda]],{a,$ltail},{b,$ltail}],{r,$d},{s,$d}];
GetBracket[PFull_,\[Lambda]_]:=Table[PFull[[1,j,i]]+Sum[PFull[[2,1,a,b]]*PFull[[2,2,a,j]]*Subsuperscript[PFull[[2,3]],b,i][\[Lambda]],{a,$ltail},{b,$ltail}],{i,$d},{j,$d}]/.$parname->\[Lambda];
BuildBracket[Ploc_,c_,w_,nlname_]:=If[Dimensions[c]!={$ltail,$ltail}||Dimensions[w]!={$ltail,$d}||Dimensions[Ploc]!={$d,$d},Print["Error: inconsistent dimension for the generators. Bracket not inizialized"];Return[{}],Return[{Ploc,{c,w,nlname}}]];


(*The function ND[arg,\[Lambda]] computes (\[Lambda]+\[PartialD])arg, in particular if arg contains nonlocal objects*)
ND[arg1_+arg2_,\[Lambda]_]:=ND[arg1,\[Lambda]]+ND[arg2,\[Lambda]];
ND[arg_,\[Lambda]_]/;FreeQ[arg,Subsuperscript[$NW,s_,i_][\[Mu]_]|Subsuperscript[$NZ,s_,i_][\[Mu]_]]:=\[Lambda]*arg+TD[arg];
ND[arg_*Subsuperscript[$NW,s_,i_][\[Lambda]_],\[Lambda]_]:=TD[arg]*Subsuperscript[$NW,s,i][\[Lambda]]+arg*$nl1[[s,i]];
ND[arg_*Subsuperscript[$NZ,s_,i_][\[Lambda]_],\[Lambda]_]:=TD[arg]*Subsuperscript[$NZ,s,i][\[Lambda]]+arg*$nl2[[s,i]];
ND[Subsuperscript[$NW,s_,i_][\[Lambda]_],\[Lambda]_]:=$nl1[[s,i]];
ND[Subsuperscript[$NZ,s_,i_][\[Lambda]_],\[Lambda]_]:=$nl2[[s,i]];


(*Skewsymmetry*)
SkewLoc[Ploc_,i_,j_,\[Lambda]_]:=Simplify[Ploc[[i,j]]/.{Times[\[Lambda]^n_, e_] :>Nest[(-\[Lambda]*#-D[#,$varname])&,e,n],Times[\[Lambda],e_]:>-\[Lambda]*e-D[e,$varname],\[Lambda]:>-\[Lambda]}];
SkewNLoc[PNlocEl_,i_,j_,\[Lambda]_]:=-GetNLoc[{Transpose[PNlocEl[[1]]],PNlocEl[[2]],PNlocEl[[3]]},\[Lambda]][[j,i]];
PVASkew[PFull_,par_]:=Module[{Ploc=PFull[[1]]/.$parname->par,Pnl=PFull[[2]]/.$parname->par},Simplify[Table[Ploc[[i,j]]+SkewLoc[Ploc,j,i,par]+GetNLoc[Pnl,par][[i,j]]+SkewNLoc[Pnl,j,i,par],{i,$d},{j,$d}]]];


(*Schouten bracket auxiliary*)
SchLL[Ploc_,Qloc_,i_,j_,k_,\[Lambda]_,\[Mu]_]:=Module[{dummy},dummy=Qloc//.$parname->\[Mu];LambdaBLoc[gen[[i]],dummy[[k,j]],Ploc,\[Lambda]]];
SchNL[PNlocEl_,Qloc_,i_,j_,k_,\[Lambda]_,\[Mu]_]:=Module[{dummy1,dummy2},dummy1=Qloc[[k,j]]//.$parname->\[Mu];dummy2=Table[Sum[PNlocEl[[1]][[a,b]]*PNlocEl[[2]][[a,r]]*Subsuperscript[PNlocEl[[3]],b,s][\[Lambda]],{a,$ltail},{b,$ltail}],{r,$d},{s,$d}];Sum[D[dummy1,D[gen[[l]],{$varname,s}]]*Nest[ND[#,\[Lambda]]&,dummy2[[l,i]],s],{l,$d},{s,0,$maxO}]];
SchLN[Ploc_,QNlocEl_,i_,j_,k_,\[Lambda]_,\[Mu]_,\[Nu]_]:=Module[{dummy2},dummy2=Ploc//.$parname->\[Lambda];Sum[QNlocEl[[1]][[a,b]](Subsuperscript[QNlocEl[[3]],b,j][\[Mu]]*LambdaBLoc[gen[[i]],QNlocEl[[2]][[a,k]],Ploc,\[Lambda]]-Subsuperscript[QNlocEl[[3]],a,k][\[Nu]]*LambdaBLoc[gen[[i]],QNlocEl[[2]][[b,j]],Ploc,\[Lambda]]),{a,$ltail},{b,$ltail}]];
SchNN[PNlocEl_,QNlocEl_,i_,j_,k_,\[Lambda]_,\[Mu]_,\[Nu]_]:=Module[{dummy=Table[Sum[PNlocEl[[1]][[a,b]]PNlocEl[[2]][[a,r]]Subsuperscript[PNlocEl[[3]],b,s][\[Lambda]],{a,$ltail},{b,$ltail}],{r,$d},{s,$d}]},Sum[QNlocEl[[1]][[a,b]](Subsuperscript[QNlocEl[[3]],b,j][\[Mu]]*Sum[D[QNlocEl[[2]][[a,k]],D[gen[[l]],{$varname,s}]]*Nest[ND[#,\[Lambda]]&,dummy[[l,i]],s],{l,$d},{s,0,$maxO}]-Subsuperscript[QNlocEl[[3]],a,k][\[Nu]]*Sum[D[QNlocEl[[2]][[b,j]],D[gen[[l]],{$varname,s}]]*Nest[ND[#,\[Lambda]]&,dummy[[l,i]],s],{l,$d},{s,0,$maxO}]),{a,$ltail},{b,$ltail}]];
SchBracket[P_,Q_,i_,j_,k_,\[Lambda]_,\[Mu]_,\[Nu]_]:=SchLL[P[[1]],Q[[1]],i,j,k,\[Lambda],\[Mu]]+SchLL[Q[[1]],P[[1]],i,j,k,\[Lambda],\[Mu]]-(SchLL[P[[1]],Q[[1]],j,i,k,\[Mu],\[Lambda]]+SchLL[Q[[1]],P[[1]],j,i,k,\[Mu],\[Lambda]])+SchLL[P[[1]],Q[[1]],k,i,j,\[Nu],\[Lambda]]+SchLL[Q[[1]],P[[1]],k,i,j,\[Nu],\[Lambda]]+SchNL[P[[2]],Q[[1]],i,j,k,\[Lambda],\[Mu]]+SchNL[Q[[2]],P[[1]],i,j,k,\[Lambda],\[Mu]]-(SchNL[P[[2]],Q[[1]],j,i,k,\[Mu],\[Lambda]]+SchNL[Q[[2]],P[[1]],j,i,k,\[Mu],\[Lambda]])+SchNL[P[[2]],Q[[1]],k,i,j,\[Nu],\[Lambda]]+SchNL[Q[[2]],P[[1]],k,i,j,\[Nu],\[Lambda]]+SchLN[P[[1]],Q[[2]],i,j,k,\[Lambda],\[Mu],\[Nu]]+SchLN[Q[[1]],P[[2]],i,j,k,\[Lambda],\[Mu],\[Nu]]-(SchLN[P[[1]],Q[[2]],j,i,k,\[Mu],\[Lambda],\[Nu]]+SchLN[Q[[1]],P[[2]],j,i,k,\[Mu],\[Lambda],\[Nu]])+SchLN[P[[1]],Q[[2]],k,i,j,\[Nu],\[Lambda],\[Mu]]+SchLN[Q[[1]],P[[2]],k,i,j,\[Nu],\[Lambda],\[Mu]]+SchNN[P[[2]],Q[[2]],i,j,k,\[Lambda],\[Mu],\[Nu]]+SchNN[Q[[2]],P[[2]],i,j,k,\[Lambda],\[Mu],\[Nu]]-(SchNN[P[[2]],Q[[2]],j,i,k,\[Mu],\[Lambda],\[Nu]]+SchNN[Q[[2]],P[[2]],j,i,k,\[Mu],\[Lambda],\[Nu]])+SchNN[P[[2]],Q[[2]],k,i,j,\[Nu],\[Lambda],\[Mu]]+SchNN[Q[[2]],P[[2]],k,i,j,\[Nu],\[Lambda],\[Mu]];


(*Normalisation*)
(*intND[arg,{\[Lambda],\[Mu],\[Nu]]] computes (-\[Lambda]-\[Mu]-\[PartialD])arg, where arg may contain terms (\[Lambda]+\[PartialD])^{-1},(\[Mu]+\[PartialD])^{-1}*)
intND[arg1_+arg2_,list\[Nu]_]:=intND[arg1,list\[Nu]]+intND[arg2,list\[Nu]];
intND[arg_,list\[Nu]_]/;FreeQ[arg,Subsuperscript[$NW,s_,i_][\[Mu]_]|Subsuperscript[$NZ,s_,i_][\[Mu]_]]:=IntegrLoc[Last[list\[Nu]]*arg,list\[Nu]];
intND[arg_*Subsuperscript[$NW,s_,i_][\[Lambda]_],list\[Nu]_]:=Module[{sumparam=Cases[Take[list\[Nu],{1,-2}],Except[\[Lambda]]]},-Sum[sumparam[[a]]*arg*Subsuperscript[$NW,s,i][\[Lambda]],{a,Length[sumparam]}]-ND[arg*Subsuperscript[$NW,s,i][\[Lambda]],\[Lambda]]];
intND[arg_*Subsuperscript[$NZ,s_,i_][\[Lambda]_],list\[Nu]_]:=Module[{sumparam=Cases[Take[list\[Nu],{1,-2}],Except[\[Lambda]]]},-Sum[sumparam[[a]]*arg*Subsuperscript[$NZ,s,i][\[Lambda]],{a,Length[sumparam]}]-ND[arg*Subsuperscript[$NZ,s,i][\[Lambda]],\[Lambda]]];
(*IntegrNL[expr,{\[Lambda],\[Mu],\[Nu]}] replaces all the positive powers of \[Nu] with powers of the operator (-\[Lambda]-\[Mu]-\[PartialD]) in expr*)
IntegrNL[expr_,param_List]:=Module[{lastpar=Last[param],l=Length[param]-1,dummy},dummy=Collect[expr,lastpar];dummy=Collect[dummy/.{Times[lastpar^n_, e_] :>Nest[intND[Expand[#],param]&,e,n],Times[lastpar,e_]:>intND[Expand[e],param],lastpar:>Sum[-param[[i]],{i,l}]},lastpar];dummy/.{Subsuperscript[$NW,s_,i_][Sum[-param[[i]],{i,l}]]:>Subsuperscript[$NW,s,i][lastpar],Subsuperscript[$NZ,s_,i_][Sum[-param[[i]],{i,l}]]:>Subsuperscript[$NZ,s,i][lastpar]}];
(*NormalN\[Mu][expr,{\[Lambda],\[Mu],\[Nu]}] projects expr on the basis of Subscript[V, \[Lambda],\[Mu]] which does not include terms of the form Nw[\[Nu]]\[Mu]^d*)
NormalN\[Mu][expr_,param_List]:=Module[{dummy,maxRec,\[Nu]=param[[3]],\[Mu]=param[[2]],\[Lambda]=param[[1]]},dummy=Expand[Collect[expr,\[Mu]]];maxRec=Exponent[dummy,\[Mu]];If[maxRec>0,Do[dummy=Expand[Collect[dummy,\[Mu]]]//.{Times[Power[\[Mu],k_]*Subsuperscript[$NW,s_,i_][\[Nu]],arg_]:>-Power[\[Mu],k-1](Subsuperscript[$NW,s,i][\[Nu]]\[Lambda]*arg+Subsuperscript[$NW,s,i][\[Nu]]*TD[arg]+$nl1[[s,i]]*arg) ,Times[\[Mu]*Subsuperscript[$NW,s_,i_][\[Nu]],arg_]:>-(Subsuperscript[$NW,s,i][\[Nu]]\[Lambda]*arg+Subsuperscript[$NW,s,i][\[Nu]]*TD[arg]+$nl1[[s,i]]*arg),Power[\[Mu],k_]*Subsuperscript[$NW,s_,i_][\[Nu]]:>-Power[\[Mu],k-1](Subsuperscript[$NW,s,i][\[Nu]]\[Lambda]+$nl1[[s,i]]) ,\[Mu]*Subsuperscript[$NW,s_,i_][\[Nu]]:>-(Subsuperscript[$NW,s,i][\[Nu]]\[Lambda]+$nl1[[s,i]]),Times[Power[\[Mu],k_]*Subsuperscript[$NZ,s_,i_][\[Nu]],arg_]:>-Power[\[Mu],k-1](Subsuperscript[$NZ,s,i][\[Nu]]\[Lambda]*arg+Subsuperscript[$NZ,s,i][\[Nu]]*TD[arg]+$nl2[[s,i]]*arg) ,Times[\[Mu]*Subsuperscript[$NZ,s_,i_][\[Nu]],arg_]:>-(Subsuperscript[$NZ,s,i][\[Nu]]\[Lambda]*arg+Subsuperscript[$NZ,s,i][\[Nu]]*TD[arg]+$nl2[[s,i]]*arg),Power[\[Mu],k_]*Subsuperscript[$NZ,s_,i_][\[Nu]]:>-Power[\[Mu],k-1](Subsuperscript[$NZ,s,i][\[Nu]]\[Lambda]+$nl2[[s,i]]) ,\[Mu]*Subsuperscript[$NZ,s_,i_][\[Nu]]:>-(Subsuperscript[$NZ,s,i][\[Nu]]\[Lambda]+$nl2[[s,i]])},maxRec]];Return[dummy]];


CompB[PFull_,QFull_,i_,j_,k_,param_List]:=Module[{dummy},$nl1=PFull[[2,2]];$nl2=QFull[[2,2]];dummy=SchBracket[{PFull[[1]],{PFull[[2,1]],PFull[[2,2]],$NW}},{QFull[[1]],{QFull[[2,1]],QFull[[2,2]],$NW}},i,j,k,param[[1]],param[[2]],param[[3]]];dummy=IntegrNL[dummy,param];dummy=NormalN\[Mu][dummy,param];Simplify[dummy//.{$NW->PFull[[2,3]],$NZ->QFull[[2,3]]}]];
CompatCheck[PFull_,QFull_,param_List]:=Module[{listJacobi,dummyentr},listJacobi=Parallelize[Table[If[i<=j && j<=k,Simplify[CompB[PFull,QFull,i,j,k,param]], Null],{i,1,$d},{j,1,$d},{k,1,$d}],Method->"FinestGrained"];Return[DeleteCases[Flatten[listJacobi],Null]]];


End[ ];
EndPackage[];
