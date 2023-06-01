(* ::Package:: *)

BeginPackage["EllipticSystems`"]

Begin["`Series`"]

SeriesFactor[HoldPattern[SeriesData[p_,0,coefftab_,pdeglow_,pdeghigh_,1]]]:=Module[
	{newcoefftab,newpdeglow}
,
	newpdeglow=pdeglow;
	newcoefftab=Map[Factor,coefftab,1];
	While[If[Length[newcoefftab]==0,False,newcoefftab[[1]]===0],
		newcoefftab=Drop[newcoefftab,1];
		pdeglow++;
	];
	Return[SeriesData[p,0,newcoefftab,pdeglow,pdeghigh,1]];
];

SeriesLaurentCollect[HoldPattern[SeriesData[p_,0,coefftab_,pdeglow_,pdeghigh_,1]],x__]:=Module[
	{newcoefftab,newpdeglow}
,
	newpdeglow=pdeglow;
	newcoefftab=Map[CommonDefinitions`Rational`LaurentCollect[#,{x},Factor]&,coefftab,1];
	While[If[Length[newcoefftab]==0,False,newcoefftab[[1]]===0],
		newcoefftab=Drop[newcoefftab,1];
		pdeglow++;
	];
	Return[SeriesData[p,0,newcoefftab,pdeglow,pdeghigh,1]];
];

SeriesLimit[HoldPattern[SeriesData[p_,0,coefftab_,pdeglow_,pdeghigh_,1]],lim_]:=Module[
	{newcoefftab}
,
	newcoefftab=Map[Limit[#,lim]&,coefftab,1];
	Return[SeriesFactor[SeriesData[p,0,newcoefftab,pdeglow,pdeghigh,1]]];
];

End[]

Begin["`InfiniteProducts`"]

Define\[CapitalEpsilon][ring_]:=With[
	{\[CapitalEpsilon]=ring["\[CapitalEpsilon]"]}
,
	(*\[CapitalEpsilon] exponential rules*)
	\[CapitalEpsilon][m_Integer]=1;
	\[CapitalEpsilon]/:Times[\[CapitalEpsilon][expr1_],\[CapitalEpsilon][expr2_]]:=\[CapitalEpsilon][Expand[Factor[expr1+expr2]]];
	\[CapitalEpsilon]/:Power[\[CapitalEpsilon][expr_],n_Integer]:=\[CapitalEpsilon][n expr];
	\[CapitalEpsilon][Plus[m_Integer,x___]]:=\[CapitalEpsilon][Plus[x]];
	(*Defining Simplification function*)
	If[!ValueQ[ring["Simplify"],Method->"TrialEvaluation"],
		ring["Simplify"][expr_]:=Collect[Factor[expr/.{\[CapitalEpsilon]->(\[CapitalEpsilon][Expand[Factor[#]]]&)}],\[CapitalEpsilon][__],Factor];
	];
	(*Complex values*)
	ring["N"][expr_]:=expr/.{\[CapitalEpsilon]->(Exp[2 \[Pi] I #]&)};
	ring["NumericQ"][expr_]:=NumericQ[ring["N"][expr]];
];

DefinePochhammerNumericParameters[ring_]:=With[
	{qPochhammer=ring["qPochhammer"]}
,
	If[!ValueQ[ring["N"][1],Method->"TrialEvaluation"],
		ring["N"][expr_]:=expr;
	];
	(*Disk test function*)
	ring["DiskMembersQ"][p___]:=And@@Map[Abs[ring["N"][#]]<1&,List[p]];
	(*Empty set of parameters*)
	qPochhammer[z_]:=1/(1-z);
	(*Complete Numeric evaluation when all arguments are numeric*)
	qPochhammer[z0_,p___]:=Module[
		{precision,i,ptab,maxntab,j,m,indeces,z}
	,
		z=ring["N"][z0];
		ptab=Map[ring["N"],List[p]];
		Print["ptab=",ptab];
		precision=Min@@Map[Precision,Append[ptab,z]];
		Print["precision=",precision];
		(*Removing z=0 case*)
		If[Chop[z,10^-precision]==0,Return[1]];
		(*Removing p_i=0 case*)
		For[i=1,i<=Length[ptab],i++,
			If[Chop[z,10^-precision]==0,
				ptab=Delete[ptab,i];
				Return[qPochhammer[z,Sequence[ptab]]];
			];
		];
		(*Dealing with ptab=={}*)
		If[ptab=={},
			If[Chop[z-1,10^-precision]==0,
				Return[+\[Infinity]]
			,
				1/1-z
			];
		];
		maxntab=Map[Ceiling[(-Log[10,Abs[z]]-precision)/Log[10,Abs[#]]]&,ptab];
		Print["maxntab=",maxntab];
		indeces=Sequence@@Table[{Subscript[j, m],0,maxntab[[m]]},{m,1,Length[ptab]}];
		Print["indeces=",indeces];
		Return[Product[1-z \!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(Length[ptab]\)]
\*SuperscriptBox[\(ptab[\([i]\)]\), 
SubscriptBox[\(j\), \(i\)]]\),Evaluate[indeces]]];
	]/;ring["NumericQ"][z0]&&ring["DiskMembersQ"][p];
	(*Inversion rule for numeric parameters*)
	qPochhammer[z_,p1___,p2_?(ring["NumericQ"]),p3___]:=1/qPochhammer[z/p2,p1,1/p2,p3]/;Abs[ring["N"][p2]]>1;
];

DefinepExpPochhammerConversion[ring_]:=(
	(*pExp to Pochhammer*)
	ring["MonomialQ"][expr_]:=Module[
		{factorstab,a,b}
	,
		Switch[expr,
		_?(Position[Variables[#],#]!={}&),
			True,
		_Times,
			factorstab=expr;
			factorstab[[0]]=List;
			And@@Map[ring["MonomialQ"],factorstab],
		_Power,
			AtomQ[expr[[1]]]&&IntegerQ[expr[[2]]],
		_,
			False
		]
	];
	ring["SimpleDenominatorQ"][expr_]:=ring["MonomialQ"][Factor[1-expr]];
	ring["pExpFormal"][expr_?(ring["MonomialQ"]),denominators___]:=Module[
		{z,ptab}
	,
		z=expr;
		ptab=Map[Factor[1-#]&,List[denominators]];
		Return[qPochhammer[z,Sequence@@ptab]];
	]/;And@@Map[ring["SimpleDenominatorQ"],List[denominators]];
	ring["pExpFormal"][expr_?(ring["MonomialQ"][-#]&),denominators___]:=1/ring["pExpFormal"][-expr,denominators]/;And@@Map[ring["SimpleDenominatorQ"],List[denominators]];
	ring["pExpFormal"][expr_Plus,denominators___]:=Module[
		{numlist=expr}
	,
		numlist[[0]]=List;
		Return[Times@@Map[ring["pExpFormal"][#,denominators]&,numlist]];
	];
	(*Converting to simple denominators, output={cofactor,simple_denominator}*)
	ring["SignedMonomialQ"][expr_]:=ring["MonomialQ"][expr]||ring["MonomialQ"][-expr];
	ring["GetSimpleDenominator"][Plus[1,Times[-1,X_?(ring["MonomialQ"])]]]:={1,1-X};
	ring["GetSimpleDenominator"][Plus[-1,X_?(ring["MonomialQ"])]]:={-1,1-X};
	ring["GetSimpleDenominator"][Plus[1,X_?(ring["MonomialQ"])]]:={1-X,1-X^2};
	ring["GetSimpleDenominator"][Plus[c1_?IntegerQ,Times[c2_?IntegerQ,X_?(ring["MonomialQ"])]]]:=Module[
		{ans}
	,
		ans=ring["GetSimpleDenominator"][1+c2/c1 X];
		ans[[1]]/=c1;
		ans
	]/;Abs[c1]==Abs[c2];
	ring["GetSimpleDenominator"][Plus[X1_?(ring["SignedMonomialQ"]),X2__]]:={1/X1,Expand[Plus[X1,X2]/X1]}/;Or@@Map[NumericQ,List[X1,X2]]==False;
	ring["pExpPochhammer"][expr_]:=Module[
		{factorlist,simpledenominators={},i,poly,numerator=1,pow,cofactor,decomposition,simpledenominator}
	,
		(*Suboptimal, because will factor 1-p^2 e.t.c.*)
		factorlist=FactorList[expr];
		For[i=1,i<=Length[factorlist],i++,
			{poly,pow}=factorlist[[i]];
			If[pow>0||ring["MonomialQ"][poly],
				numerator*=Power[poly,pow]
			,
				decomposition=ring["GetSimpleDenominator"][Expand[poly]];
				If[Length[decomposition]!=2,
					Print["Unexpected type of factor, ",poly];
					Return[Indeterminate];
				];
				{cofactor,simpledenominator}=decomposition;
				numerator*=Power[cofactor,-pow];
				If[simpledenominator=!=1,
					simpledenominators=Join[simpledenominators,Table[simpledenominator,-pow]];
				];
			];
		];
		Return[ring["pExpFormal"][Expand[numerator],Sequence@@simpledenominators]];
	];
	(*qPochhammer to pExp*)
	ring["qPochhammerpExp"][z_,p___]:=pExp[z/Times@@Map[1-#&,List[p]]];
);

DefineZeros[ring_]:=With[
	{qPochhammer=ring["qPochhammer"],\[CapitalEpsilon]=ring["\[CapitalEpsilon]"]}
,
	(*Reconstructing Semi-lattice of zeros*)
	ring["GetSemiLatticeOfZeros"][qPochhammer[\[CapitalEpsilon][z_],p__\[CapitalEpsilon]],\[Zeta]_]:=Module[
		{logvars,eq,m,n,i,sol}
	,
		logvars=Map[#[[1]]&,List[\[CapitalEpsilon][z],p]];
		eq=logvars[[1]]+Sum[Subscript[n, i]logvars[[i+1]],{i,1,Length[logvars]-1}]+m==0;
		sol=Solve[eq,\[Zeta]];
		If[Length[sol]!=1,
			Print["Unexpected number of solutions in GetSemilatticeOfZeros, sol=",sol];
			Return[Indeterminate];
		];
		{Join[{1,sol[[1,1,2]]/.Append[Table[Subscript[n, i]->0,{i,1,Length[logvars]}],m->0],Coefficient[sol[[1,1,2]],m]},Table[Coefficient[sol[[1,1,2]],Subscript[n, i]],{i,1,Length[logvars]-1}]]}
	]/;ring["DiskMembersQ"][p]&&Position[z,\[Zeta]]!={};
	ring["GetSemiLatticeOfZeros"][Power[qPochhammer[\[CapitalEpsilon][z_],p__\[CapitalEpsilon]],pow_],\[Zeta]_]:=Module[
		{ans}
	,
		ans=ring["GetSemiLatticeOfZeros"][qPochhammer[\[CapitalEpsilon][z],p],\[Zeta]];
		ans[[1,1]]=pow;
		ans
	]/;ring["DiskMembersQ"][p]&&Position[z,\[Zeta]]!={};
	ring["GetSemiLatticeOfZeros"][Times[X_,Y__],\[Zeta]_]:=Join[ring["GetSemiLatticeOfZeros"][X,\[Zeta]],ring["GetSemiLatticeOfZeros"][Times[Y],\[Zeta]]];
	(*Functions to plot zeros*)
	ring["accuracy"]=10^-3;
	ring["maxm"]=ring["maxntot"]=10;(*code should be optimized later to scan only through necessary values*)
	If[!ValueQ[ring["showsemilatticedata"],Method->"TrialEvaluation"],
		ring["showsemilatticedata"]=True;
	];
	ring["GetExtremeParameters"][c0_,c1_,\[Zeta]low_,\[Zeta]high_]:=Module[
		{t,condition}
	,
		condition=Reduce[Re[\[Zeta]low]<=Re[c0]+Re[c1] t<=Re[\[Zeta]high]&&Im[\[Zeta]low]<=Im[c0]+Im[c1] t<=Im[\[Zeta]high]];
		If[ring["debug"]["GetExtremeParameters"],
			Print["c0=",c0,", c1=",c1,", \[Zeta]low=",\[Zeta]low,", \[Zeta]high=",\[Zeta]high];
			Print["condition=",condition];
		];
		Switch[condition,
		Inequality[_,LessEqual,t,LessEqual,_],
			Return[{condition[[1]],condition[[5]]}],
		_,
			Print["Unexpected reduced inequality in GetExtremeParameters, ",condition];
			Return[Indeterminate];
		];
	];
	ring["WeightedInc"][indtab_,weighttab_,low_,high_]:=Module[
		{ansind,i}
	,
		ansind=indtab;
		ansind[[-1]]+=1;
		For[i=Length[ansind],i>0,i--,
			If[ansind . weighttab<=high,Break[]];
			If[i==1,Return[Indeterminate]];
			ansind[[i]]=0;
			ansind[[i-1]]+=1;
		];
		If[ansind . weighttab<low,
			ansind[[-1]]=Ceiling[(low-ansind . weighttab)/weighttab[[-1]]];
		];
		If[ring["debug"]["WeightedInc"],
			Print["ansind=",ansind];
		];
		ansind
	];
	ring["GetListOfZerosAux"][piece_,\[Zeta]low_,\[Zeta]high_,maxpoints_]:=Module[
		{m,n,ntot,ans={},c0,cm,cn,BelongQ,\[Zeta],deg,AddPoint,cmnormal,lowD,highD,normalcorners,weights,indtab,lowt,hight,point,tinterval}
	,
		(*Degree of a zero*)
		deg=piece[[1]];
		(*Base point of a semilattice*)
		c0=piece[[2]];
		(*Directional and normal vectors of the baseine*)
		cm=piece[[3]];
		cmnormal={Im[cm],-Re[cm]}/Abs[cm];
		(*Directional vectors of a semilattice*)
		cn=Drop[piece,3];
		weights=Map[{Re[#],Im[#]} . cmnormal&,cn,1];
		If[And@@Map[#<0&,weights],
			cmnormal=-cmnormal;
			weights=-weights;
		];
		(*Ranges for the normal coordinate*)
		normalcorners={{Re[\[Zeta]low],Im[\[Zeta]low]} . cmnormal,{Re[\[Zeta]low],Im[\[Zeta]high]} . cmnormal,{Re[\[Zeta]high],Im[\[Zeta]low]} . cmnormal,{Re[\[Zeta]high],Im[\[Zeta]high]} . cmnormal}-{Re[c0],Im[c0]} . cmnormal;
		lowD=Min[normalcorners];
		highD=Max[normalcorners];
		If[ring["debug"]["GetListOfZerosAux"],
			Print["cmnormal=",cmnormal];
			Print["cn=",cn];
			Print["weights=",weights];
			Print["{lowD,highD}=",{lowD,highD}];
		];
		(*Searching for all zeros and poles within the given range*)
		BelongQ[\[Zeta]_]:=(Re[\[Zeta]low]<=Re[\[Zeta]]<=Re[\[Zeta]high])&&(Im[\[Zeta]low]<=Im[\[Zeta]]<=Im[\[Zeta]high]);
		indtab=Map[0&,cn];
		indtab[[-1]]=-1;
		While[(indtab=ring["WeightedInc"][indtab,weights,lowD,highD])=!=Indeterminate,
			If[(tinterval=ring["GetExtremeParameters"][c0+indtab . cn,cm,\[Zeta]low,\[Zeta]high])===Indeterminate,
				Return[Indeterminate];
			];
			{lowt,hight}=tinterval;
			If[!(NumberQ[lowt]&&NumberQ[hight]),
				Print["Unexpected range of line parameters, indtab=",indtab,", weights=",weights,", lowD=",lowD,", highD=",highD];
				Return[Indeterminate];
			];
			lowt=Ceiling[lowt];
			hight=Floor[hight];
			If[ring["debug"]["GetListOfZerosAux"],
				Print["indtab=",indtab];
				Print["{lowt,hight}=",{lowt,hight}];
			];
			For[m=lowt,m<=hight,m++,
				point=c0+cm m+indtab . cn;
				If[BelongQ[point],
					AppendTo[ans,point->deg];
					If[Length[ans]>=maxpoints,Return[ans]]
				,
					Print["Self-test error in GetListOfZeros, point=",point];
					Print["\[Zeta]low=",\[Zeta]low,", \[Zeta]high=",\[Zeta]high];
					Print["c0=",c0,", cm=",cm,", m=",m];
					Print["indtab=",indtab,", cn=",cn];
					Print["weights=",weights];
					Print["{lowt,hight}=",{lowt,hight}];
					Return[Indeterminate];
				];
			];
		];
		ans
	]/;And@@Map[NumericQ,piece];
	ring["GetListOfZeros"][semilattices_List,\[Zeta]low_,\[Zeta]high_,maxpointsperlattice_]:=Module[
		{rawlist,ans={},AddPoint,i}
	,
		AddPoint[\[Zeta]_->deg_]:=Module[
			{j}
		,
			For[j=1,j<=Length[ans],j++,
				If[Abs[\[Zeta]-ans[[j,1]]]<ring["accuracy"],
					ans[[j,2]]+=deg;
					Return[];
				];
			];
			AppendTo[ans,\[Zeta]->deg];
		];
		rawlist=Flatten[Map[ring["GetListOfZerosAux"][#,\[Zeta]low,\[Zeta]high,maxpointsperlattice]&,semilattices,1]];
		For[i=1,i<=Length[rawlist],i++,
			AddPoint[rawlist[[i]]];
		];
		(*Excluding removable singularities*)
		ans=DeleteCases[ans,\[Zeta]_->0];
		ans
	]/;And@@Map[NumericQ,Flatten[semilattices]];
	ring["GetListOfZeros"][semilattices_List,\[Zeta]low_,\[Zeta]high_]:=ring["GetListOfZeros"][semilattices,\[Zeta]low,\[Zeta]high,\[Infinity]];
];

DefineInfintieProducts[ring_]:=With[
	{qPochhammer=ring["qPochhammer"],\[CapitalEpsilon]=ring["\[CapitalEpsilon]"]}
,
	Define\[CapitalEpsilon][ring];
	DefinePochhammerNumericParameters[ring];
	DefinepExpPochhamerConversion[ring];
	DefineZeros[ring];
];

(*Computing series of pExp*)
pShifted[expr_,x__,m_]:=Module[
	{xtab,subst}
,
	xtab=List[x];
	subst=Map[#->#^m&,xtab];
	Return[expr/.subst];
];

pExpSeries[expr_,x__,{var_,0,deg_}]:=Module[
	{argser,sum,m,l,ans}
,
	If[Position[List[x],var,1]=={},
		Print["Expression pExpSeries",expr,",",x," is not plethystic in series variable ",var];
		Return[Indeterminate];
	];
	argser=Series[expr,{var,0,deg}];
	Switch[argser,
	_SeriesData,
		If[argser[[4]]<=0,
			Print["Cannot take Plethystyic series of ",expr," w.r.t. ",var];
			Return[Indeterminate];
		],
	_,
		Print["Unexpected series ",argser];
		Return[Indeterminate];
	];
	sum=Sum[Series[pShifted[expr,x,m]/m,{var,0,deg}],{m,1,Floor[deg/argser[[4]]]}];
	ans=Sum[sum^l/l!,{l,0,deg}];
	Return[ans];
];

DefinePlethysticExponentRing[pring_]:=With[
	{pExp=pring["pExp"]}
,
	(*pExp exponential rules*)
	pExp[0]=1;
	pExp/:Times[pExp[expr1_],pExp[expr2_]]:=pExp[Factor[expr1+expr2]];
	pExp/:Power[pExp[expr_],n_Integer]:=pExp[n expr];
	(*Defining Simplification function*)
	If[!ValueQ[pring["Simplify"],Method->"TrialEvaluation"],
		pring["Simplify"][expr_]:=Collect[Factor[expr/.{pExp->(pExp[Factor[#]]&)}],pExp[__],Factor];
	];
	(*Defining Series*)
	pring["SeriesSimplify"][expr_]:=Switch[expr,
	_SeriesData,
		SeriesFactor[expr],
	_,
		Factor[expr]
	];
	pring["SeriesPoly"][coeff_,{var_,0,deg_}]:=Series[coeff,{var,0,deg}]/;Position[coeff,pExp]=={};
	pring["SeriesPoly"][pExp[expr_],{var_,0,deg_}]:=pExpSeries[expr,Sequence@@pring["plethysticvariables"],{var,0,deg}];
	pring["SeriesPoly"][coeff_ pExp[expr_],{var_,0,deg_}]:=Module[
		{coeffser,lowpow,numdeg}
	,
		coeffser=Series[coeff,{var,0,deg}];
		Switch[coeffser,
		_SeriesData,
			lowpow=coeffser[[4]];
			numdeg=deg-lowpow,
		_,
			numdeg=deg
		];
		coeffser pring["SeriesPoly"][pExp[expr],{var,0,numdeg}]
	];
	pring["SeriesPoly"][Times[X___,Plus[Y_,Z__],W___],{var_,0,deg_}]:=
		pring["SeriesPoly"][Times[X,Y,W],{var,0,deg}]+pring["SeriesPoly"][Times[X,Plus[Z],W],{var,0,deg}]
	/;Length[List[X,Z]]>0&&Position[Plus[Y],pExp]!={};
	pring["SeriesPoly"][Plus[X_,Y__],{var_,0,deg_}]:=pring["SeriesPoly"][X,{var,0,deg}]+pring["SeriesPoly"][Plus@@Y,{var,0,deg}];
	pring["Series"][expr_,{var_,0,deg_}]:=Module[
		{num,den,seriesdataden,numdeg,dendeg,deglow,deghigh}
	,
		{num,den}=NumeratorDenominator[Factor[expr]];
		seriesdataden=pring["SeriesSimplify"][pring["SeriesPoly"][den,{var,0,deg}]];
		Switch[seriesdataden,
		_SeriesData,
			deglow=seriesdataden[[4]];
			deghigh=seriesdataden[[5]];
			If[deghigh-2deglow<=deg,
				dendeg=deg+2deglow;
				seriesdataden=pring["SeriesSimplify"][pring["SeriesPoly"][den,{var,0,dendeg}]];
			];
			numdeg=deg+seriesdataden[[4]],
		_,
			numdeg=deg
		];
		pring["SeriesSimplify"][pring["SeriesPoly"][num,{var,0,numdeg}]/seriesdataden]
	];
];

End[]

Begin["`Shiraishi`"]

debugAll=True;
silent=False;

SeriesFactor:=EllipticSystems`Series`SeriesFactor;
SeriesLaurentCollect:=EllipticSystems`Series`SeriesLaurentCollect;
SeriesLimit:=EllipticSystems`Series`SeriesLimit;

ClearAll[timeF];
timelist={"lrulesSimplify","Series0","Limit0","\[Psi]valCollect0","valtab0","eqs0","coeff0","diffdec0","Series1","SeriesLaurentCollect1","Series2","Limit2","\[Psi]valSeriesFactor","valtab","eqs1","sol1","coeff","diffdec","dFactornum","dFactorden","SMatrixElement"};
timeF["Total"]=0;
For[i=1,i<=Length[timelist],i++,
	timeF[timelist[[i]]]=0;
];

ShowAllTimes[]:=(
	StartTimer["Total"];
	Print[Dynamic[Map[#->timeF[#]&,timelist]]]
);

StartTimer[name_]:=Module[
	{timeoffset}
,
	timeoffset=TimeUsed[]-timeF[name];
	timeF[name]:=TimeUsed[]-timeoffset;
];

StopTimer[name_]:=Module[
	{freezevalue}
,
	freezevalue=timeF[name];
	timeF[name]=freezevalue;
];

PValue[\[Lambda]_,i_]:=If[i>Length[\[Lambda]],0,\[Lambda][[i]]];
QPochhammerN[a_,q_,k_Integer]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 0\), \(k - 1\)]\((1 - a\ 
\*SuperscriptBox[\(q\), \(j\)])\)\)/;k>=0;
ClearAll[\[CapitalNu],\[CapitalNu]Aux]
\[CapitalNu][\[Lambda]_List,\[Mu]_List,k_Integer,n_Integer]:=\[CapitalNu][\[Lambda],\[Mu],k,n]=Module[
	{i,j,\[CapitalLambda],\[CapitalMu]}
,
	\[CapitalLambda][i_Integer]:=If[1<=i<=Length[\[Lambda]],\[Lambda][[i]],0];
	\[CapitalMu][i_Integer]:=If[1<=i<=Length[\[Mu]],\[Mu][[i]],0];
	\[CapitalNu]Aux[\[Lambda],\[Mu],k,n][u_,q_,s_]:=(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(Length[\[Lambda]]\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(j\)]If[Mod[j - i - k, n] == 0, QPochhammerN[u\ 
\*SuperscriptBox[\(q\), \(\(-\[CapitalMu][i]\) + \[CapitalLambda][j + 1]\)] 
\*SuperscriptBox[\(s\), \(\(-i\) + j\)], q, \[CapitalLambda][j] - \[CapitalLambda][j + 1]], 1]\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(\[Beta] = 1\), \(Length[\[Mu]]\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(\[Alpha] = 1\), \(\[Beta]\)]If[Mod[\[Beta] - \[Alpha] + k + 1, n] == 0, QPochhammerN[u\ 
\*SuperscriptBox[\(q\), \(\[CapitalLambda][\[Alpha]] - \[CapitalMu][\[Beta]]\)] 
\*SuperscriptBox[\(s\), \(\[Alpha] - \[Beta] - 1\)], q, \[CapitalMu][\[Beta]] - \[CapitalMu][\[Beta] + 1]], 1]\)\));
	Return[\[CapitalNu]Aux[\[Lambda],\[Mu],k,n]];
];

(*Defining Partition Pairs*)
ClearAll[PartitionsMaxOddDeg];
PartitionsMaxOddDeg[maxdeg_Integer,maxa_Integer]:=PartitionsMaxOddDeg[maxdeg,maxa]=Module[
	{a,partitions,ans}
,
	If[debugAll,
		Print["Starting with {maxdeg,maxa} = ",{maxdeg,maxa}];
		Pause[0.1];
	];
	If[maxdeg<0,Return[{}]];
	If[maxdeg==0,Return[{{}}]];
	If[maxa==0,Return[{}]];
	(*First calculating partitions with smaller number of boxes in the first row*)
	ans=PartitionsMaxOddDeg[maxdeg,maxa-1];
	If[maxa>maxdeg,Return[ans]];
	(*Next, adding the ones with exactly maxa elements in the first row and nonzero elements in the second row*)
	For[a=maxa,a>0,a--,
		partitions=PartitionsMaxOddDeg[maxdeg-maxa,a];
		ans=Join[ans,Map[Join[{maxa,a},#]&,partitions,1]];
	];
	(*If allowed, adding partition with exactly one row and maxa elements*)
	If[maxa==maxdeg,
		AppendTo[ans,{maxa}];
	];
	Return[ans];
];

PartitionPairs[maxdeg_]:=Module[
	{deg1,ans}
,
	ans=Table[Outer[{#1,#2}&,PartitionsMaxOddDeg[deg1,deg1],PartitionsMaxOddDeg[maxdeg-deg1,maxdeg-deg1],1],{deg1,0,maxdeg}];
	Return[Flatten[ans,2]];
];

(*Defining sl_2 specialization*)
ClearAll[X,SPoint,q,t]
SPoint[l_,1][s_,q_,t_]:=t^-1 q^-l s^-1;
SPoint[l_,2][s_,q_,t_]:=1;
XVal[n_,m_]:=XAux[n,Mod[m-1,n]+1];
XAux[2,1][x_,p_]:=x/p;
XAux[2,2][x_,p_]:=x^-1;
ClearAll[Prefactor,PrefactorAux]
Prefactor[tuple_List,n_Integer,l_Integer]:=Prefactor[tuple,n,l]=(
	PrefactorAux[tuple,n,l][s_,q_,t_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(n\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(n\)]\(\[CapitalNu][tuple[\([i]\)], tuple[\([j]\)], j - i, n]\)[q\ \(SPoint[l, j]\)[s, q, t]/\((t\ \(SPoint[l, i]\)[s, q, t])\), q, s]/\(\[CapitalNu][tuple[\([i]\)], tuple[\([j]\)], j - i, n]\)[\(SPoint[l, j]\)[s, q, t]/\(SPoint[l, i]\)[s, q, t], q, s]\)\);
	PrefactorAux[tuple,n,l]
);
XMonomial[tuple_,n_][x_,p_,s_,q_,t_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(\[Beta] = 1\), \(n\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(\[Alpha] = 1\), \(Length[tuple[\([\[Beta]]\)]]\)]
\*SuperscriptBox[\((\ \((p\ t\ \(XVal[n, \[Alpha] + \[Beta]]\)[x, p])\)/\((q\ \(XVal[n, \[Alpha] + \[Beta] - 1]\)[x, p])\))\), \(tuple[\([\[Beta], \[Alpha]]\)]\)]\)\);
extraterms=0;
ClearAll[\[Psi]];
\[Psi][l_Integer,pdeg_Integer][x_,p_,s_,q_,t_]:=\[Psi][l,pdeg][x,p,s,q,t]=Module[
	{ans=0,degodd,pairs,i,\[Mu]1,\[CapitalLambda],\[CapitalMu],pair,allpairs,expr}
,
	(*PrintTemporary[Dynamic[{2degodd,Length[pairs],i,\[Mu]1}]];*)
	For[degodd=0,2degodd<=pdeg,degodd++,
		pairs=PartitionPairs[degodd];
		For[i=1,i<=Length[pairs],i++,
			For[\[Mu]1=PValue[pairs[[i,2]],1],\[Mu]1<=l+1+PValue[pairs[[i,1]],1]+extraterms,\[Mu]1++,
				pair=pairs[[i]];
				If[\[Mu]1>0,
					pair[[2]]=PrependTo[pair[[2]],\[Mu]1];
				];
				ans+=x^-l Prefactor[pair,2,l][s,q,t]XMonomial[pair,2][x,p,s,q,t];
			];
		];
	];
	Return[ans]
];

(*Auxiliary function for decomposition of expression in Subscript[\[Psi], l]*)

DefinePsiDecomposition[algebra_]:=With[
	{p=algebra["p"],x=algebra["x"]}
,
	algebra["SeriesSimplify"][expr_]:=SeriesLaurentCollect[expr,x];
	algebra["\[Psi]Leading"][l_]:=algebra["\[Psi]Leading"][l]=Factor[{l}/.CommonDefinitions`Rational`LaurentCoefficientRules[Normal[algebra[0]["\[Psi]"][l]],{x}]];
	algebra["Decompose"][HoldPattern[SeriesData[p,0,coefftab_,pdeglow_,pdeghigh_,1]]]:=Module[
			{ctop,ans,lrules,maxl,newseries,pos,expr}
		,
			If[pdeglow==pdeghigh,
				Return[{{_}->O[p]^pdeghigh}]
			];
			lrules=SortBy[CommonDefinitions`Rational`LaurentCoefficientRules[coefftab[[1]],{x}],First];
			StartTimer["lrulesSimplify"];
			lrules=Simplify[lrules];
			StopTimer["lrulesSimplify"];
			If[Length[lrules]==0,
				Return[{{_}->O[p]^pdeghigh}]
			];
			(*Computing new series to cancel the leading term*)
			maxl=-lrules[[1,1,1]];
			ctop=lrules[[1,2]]/algebra["\[Psi]Leading"][maxl];
			newseries=algebra["SeriesSimplify"][SeriesData[p,0,coefftab,pdeglow,pdeghigh,1]-ctop p^pdeglow algebra[pdeghigh-pdeglow-1]["\[Psi]"][maxl]];
			(*Obtaining the answer for the subleading part recursively*)
			ans=algebra["Decompose"][newseries];
			pos=Position[ans,{maxl}];
			If[pos=={},
				Return[SortBy[Prepend[ans,{maxl}->ctop p^pdeglow+O[p]^pdeghigh],First]];
			];
			If[Length[pos]==1,
				ans[[pos[[1,1]],2]]+=ctop p^pdeglow;
				Return[ans];
			];
			Print["Unexpected number of positions of maxl=",maxl];
			Print["pos=",pos];
			Print["subleading ans=",ans];
			Return[Indeterminate];
		];
];

(*Defining algebra of difference operators at particular s*)

Xval[j_Integer,Q_,T_]:=T Q^(2j);

\[Theta]1[z_,p_,pdeg_]:=Normal[Series[Product[(1-p^(2(n+1)) z^-1)(1-p^(2n) z),{n,0,Floor[pdeg/2]}],{p,0,pdeg}]];

DefineS1[algebra_]:=(
	If[!ValueQ[algebra["checkdecomposition"],Method->"TrialEvaluation"],
		algebra["checkdecomposition"]=True;
	];
	If[!ValueQ[algebra["Oa"],Method->"TrialEvaluation"],
		algebra["Oa"]=Global`Oa;
	];
	If[!ValueQ[algebra["Ob"],Method->"TrialEvaluation"],
		algebra["Ob"]=Global`Ob;
	];
	If[!ValueQ[algebra["Oc"],Method->"TrialEvaluation"],
		algebra["Oc"]=Global`Oc;
	];
	If[!ValueQ[algebra["x"],Method->"TrialEvaluation"],
		algebra["x"]=Global`x;
	];
	If[!ValueQ[algebra["Q"],Method->"TrialEvaluation"],
		algebra["Q"]=Global`Q;
	];
	If[!ValueQ[algebra["T"],Method->"TrialEvaluation"],
		algebra["T"]=Global`T;
	];
	If[!ValueQ[algebra["p"],Method->"TrialEvaluation"],
		algebra["p"]=Global`p;
	];
	With[
		{Q=algebra["Q"],T=algebra["T"],t=algebra["T"]^2,p=algebra["p"],x=algebra["x"],
		Oa=algebra["Oa"],Ob=algebra["Ob"],Oc=algebra["Oc"]}
	,
		If[!ListQ[algebra["groundfield"]["generators"]],
			algebra["groundfield"]["generators"]={algebra["x"],algebra["Q"],algebra["T"],algebra["p"],Subscript[algebra["c"], ___]}
		];
		If[!ValueQ[algebra["Id"],Method->"TrialEvaluation"],
			algebra["Id"]=Global`Id
		];
		algebra[pdeg_]["generators"]=algebra["generators"]={algebra["Oa"],algebra["Ob"],algebra["Oc"]};
		AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[algebra];
		AbstractAlgebra`CompositionAlgebra`DefineCompositionAlgebra[algebra];
		algebra["MonomialBasis"][deg_]:=algebra["MonomialBasis"][deg]=Module[
			{i}
		,
			If[deg<0,Return[{}]];
			If[deg==0,Return[{algebra["Id"]}]];
			Return[
				Join[
					Table[algebra["NonCommutativeMultiply"]@@Join[Table[Oa,i],Table[Ob,deg-i]],{i,1,deg}]
				,
					Table[algebra["NonCommutativeMultiply"]@@Join[Table[Ob,i],Table[Oc,deg-i]],{i,1,deg}]
				,
					Table[algebra["NonCommutativeMultiply"]@@Join[Table[Oa,i],Table[Oc,deg-i]],{i,0,deg-1}]
				]
			];
		];
		(*Defining q-shift operators*)
		algebra["\[Delta]"][k_][poly_?(algebra["FieldElementQ"])]:=poly/.{x->Q^(2k) x};
		algebra["\[Delta]"][k_][tab_List]:=Map[algebra["\[Delta]"][k],tab];
		algebra["NonCommutativeMultiply"][algebra["\[Delta]"][k1_],algebra["\[Delta]"][k2_]]:=algebra["\[Delta]"][k1+k2];
		(*Defining operators Oa, Ob*)
		algebra["qComm"][X_,Y_]:=(Q X**Y-Q^-1 Y**X)/(Q-Q^-1);
		algebra["Oac1Series"][pdeg_]:=algebra["Oac1Series"][pdeg]=Series[\[Theta]1[t x^-2,p,pdeg]/\[Theta]1[x^-2,p,pdeg]/T,{p,0,pdeg}];
		algebra["Oac2Series"][pdeg_]:=algebra["Oac2Series"][pdeg]=Series[\[Theta]1[t x^2,p,pdeg]/\[Theta]1[x^2,p,pdeg]/T,{p,0,pdeg}];
		Oa[HoldPattern[SeriesData[p,0,coefftab_,pdeglow_,pdeghigh_,1]]]:=algebra["Oac1Series"][pdeghigh-1] SeriesData[p,0,algebra["\[Delta]"][-1][coefftab],pdeglow,pdeghigh,1]+algebra["Oac2Series"][pdeghigh-1]SeriesData[p,0,algebra["\[Delta]"][1][coefftab],pdeglow,pdeghigh,1];
		Ob[poly_]:=(x+x^-1)poly;
		Oc[poly_]:=(Q Oa[Ob[poly]]-Q^-1 Ob[Oa[poly]])/(Q-Q^-1);
		(*Defining \[Psi]-functions*)
		algebra[pdeg_]["\[Psi]"][l_]:=algebra[pdeg]["\[Psi]"][l]=Module[
			{ans,s1}
		,
			StartTimer["Series0"];
			ans=Series[EllipticSystems`Shiraishi`\[Psi][l,pdeg][x,p,s1,Q^4,t],{p,0,pdeg}]/Series[EllipticSystems`Shiraishi`\[Psi][l,pdeg][Xval[0,Q,T],p,s1,Q^4,t],{p,0,pdeg}];
			StopTimer["Series0"];
			StartTimer["Limit0"];
			Switch[ans,
			_SeriesData,
				ans[[3]]=Map[CommonDefinitions`Rational`LaurentCollect[#,{x},Factor[Limit[Together[#],s1->1]]&]&,ans[[3]]],
			_,
				ans=CommonDefinitions`Rational`LaurentCollect[ans,{x},Factor[Limit[Together[#],s1->1]]&]
			];
			StopTimer["Limit0"];
			Return[ans+O[p]^(pdeg+1)];
		];
		DefinePsiDecomposition[algebra];
		(*Reconstructing word for endomorphism*)
		algebra["GetConstantEqs"][expr_]:=Module[
			{rules}
		,
			rules=CoefficientRules[Numerator[Factor[expr]],x];
			Return[Map[#[[2]]==0&,rules]];
		];
		If[!ValueQ[algebra["extral"],Method->"TrialEvaluation"],
			algebra["extral"]=1;
		];
		algebra["GetWordAux"][degtab_,pdeg_][Op_]:=Module[
			{basis,c=algebra["c"],genericexpr,i,eqs={},l,sol={{}},cnum,cnumprev,j,diff}
		,
			basis=Join@@Map[algebra["MonomialBasis"],degtab];
			Print[basis];
			genericexpr=Sum[Subscript[c, i]basis[[i]],{i,1,Length[basis]}];
			cnumprev=Length[basis];
			(*Acting on enough \[Psi]-functions to get unique solution*)
			For[l=0,l<$RecursionLimit,l++,
				Print["l=",l,", cnumprev=",cnumprev];
				eqs=algebra["GetConstantEqs"][SeriesCoefficient[(Op-p^pdeg genericexpr)[algebra[pdeg]["\[Psi]"][l]],{p,0,pdeg}]]/.sol[[1]];
				Print["ByteCount[eqs]=",ByteCount[eqs]];
				sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[basis]}]];
				If[Length[sol]!=1,Return[Indeterminate]];
				genericexpr=algebra["Collect"][genericexpr/.sol[[1]],Factor];
				Print["ByteCount[genericexpr]=",ByteCount[genericexpr]];
				cnum=Length[Select[Variables[genericexpr],MatchQ[#,Subscript[c, _]]&]];
				If[cnum>=cnumprev,
					Print["Warning: Free parameters were not reduced in GetWordAux[",degtab,"] at l=",l];
					Return[Indeterminate];
				];
				If[cnum==0,Break[]];
				cnumprev=cnum;
			];
			(*Validating the answer*)
			For[j=1,j<=algebra["extral"],j++,
				Print["j=",j];
				diff=SeriesCoefficient[(Op-p^pdeg genericexpr)[algebra[pdeg]["\[Psi]"][l+j]],{p,0,pdeg}];
				If[CommonDefinitions`Rational`LaurentCollect[diff,{x},Factor]=!=0,
					Print["Validation failed in GetWordAux, pdeg=",pdeg,", degtab=",degtab];
					Print["diff=",diff];
					Return[Indeterminate];
				];
			];
			Print["Found expression ",Short[genericexpr]];
			Return[genericexpr];
		];
		If[!ValueQ[algebra["maxlength"],Method->"TrialEvaluation"],
			algebra["maxlength"]=10;
		];
		algebra["GetWordAux"][pdeg_][Op_]:=Module[
			{lengthtab={},length,ans}
		,
			For[length=0,length<=algebra["maxlength"],length++,
				Print["length=",length];
				AppendTo[lengthtab,length];
				ans=algebra["GetWordAux"][lengthtab,pdeg][Op];
				If[ans=!=Indeterminate,Return[algebra["Collect"][ans]]];
			];
			Print["Failed to find polynomial of degree ",algebra["maxlength"]," for an operator"];
			Return[Indeterminate];
		];
		algebra["GetWord"][HoldPattern[SeriesData[p,0,coefftab_,pdeglow_,pdeghigh_,1]]]:=Module[
			{Op,word=0,pdeg,leadingword,Opdeg}
		,
			Op=Normal[SeriesData[p,0,coefftab,pdeglow,pdeghigh,1]];
			For[pdeg=0,pdeg<pdeghigh,pdeg+=1,
				Print["pdeg=",pdeg];
				leadingword=algebra["GetWordAux"][pdeg][Op];
				Op-=p^pdeg  leadingword;
				word+=p^pdeg leadingword;
			];
			Return[word+O[p]^pdeghigh];
		];
		(*Defining normal ordering relations*)
		algebra["NonCommutativeMultiply"][X___,Ob,Oa,Y___]:=Q^2 algebra["NonCommutativeMultiply"][X,Oa,Ob,Y]-(Q^2-1)algebra["NonCommutativeMultiply"][X,Oc,Y];
		algebra["NonCommutativeMultiply"][X___,Oc,Ob,Y___]:=Q^2 algebra["NonCommutativeMultiply"][X,Ob,Oc,Y]+(1+1/Q^2-Q^2-Q^4)algebra["NonCommutativeMultiply"][X,Oa,Y];
		Unprotect[SeriesData];
		SeriesData[p,0,{A___,algebra["NonCommutativeMultiply"][X___,Oc,Oa,Y___],B___},pdeglow_,pdeghigh_,1]:=SeriesData[p,0,{A,0,B},pdeglow,pdeghigh,1]+p^(pdeglow+Length[List[A]]) (Q^-2 algebra["NonCommutativeMultiply"][X,Oa,Oc,Y]+Q^-1 (Q-Q^-1)algebra["qCommOcOa"][pdeghigh-pdeglow-Length[List[A]]]);
		Protect[SeriesData];
		(*Defining automorphism Ob*)
		algebra["aut"]["Db"][expr_]:=expr/.{algebra["Oa"]->(Q/(1-Q^4))algebra["NonCommutativeMultiply"][algebra["Oa"],algebra["Ob"]]-(Q^3/(1-Q^4))algebra["NonCommutativeMultiply"][algebra["Ob"],algebra["Oa"]]};
	];
);

DefineFull[algebra_]:=(
	If[!ValueQ[algebra["checkdecomposition"],Method->"TrialEvaluation"],
		algebra["checkdecomposition"]=True;
	];
	If[!ValueQ[algebra["Oa"],Method->"TrialEvaluation"],
		algebra["Oa"]=Global`Oa;
	];
	If[!ValueQ[algebra["Ob"],Method->"TrialEvaluation"],
		algebra["Ob"]=Global`Ob;
	];
	If[!ValueQ[algebra["x"],Method->"TrialEvaluation"],
		algebra["x"]=Global`x;
	];
	If[!ValueQ[algebra["Q"],Method->"TrialEvaluation"],
		algebra["Q"]=Global`Q;
	];
	If[!ValueQ[algebra["T"],Method->"TrialEvaluation"],
		algebra["T"]=Global`T;
	];
	If[!ValueQ[algebra["p"],Method->"TrialEvaluation"],
		algebra["p"]=Global`p;
	];
	If[!ValueQ[algebra["s"],Method->"TrialEvaluation"],
		algebra["s"]=Global`s;
	];
	With[
		{Q=algebra["Q"],T=algebra["T"],p=algebra["p"],s=algebra["s"],x=algebra["x"],Oa=algebra["Oa"],Ob=algebra["Ob"],Oc=algebra["Oc"]}
	,
		(*Defining \[Psi]-functions*)
		algebra[pdeg_]["\[Psi]"][l_]:=algebra[pdeg]["\[Psi]"][l]=EllipticSystems`Shiraishi`\[Psi][l,pdeg][x,p,s,Q^4,T^2]+O[p]^(pdeg+1);
		algebra[pdeg_]["\[Psi]val"][i_Integer,j_Integer]:=algebra[pdeg]["\[Psi]val"][i,j]=algebra[pdeg]["\[Psi]"][i]/.{x->Xval[j,Q,T]};
		DefinePsiDecomposition[algebra];
		(*Defining associative algebra*)
		If[!ListQ[algebra["groundfield"]["generators"]],
			algebra["groundfield"]["generators"]={x,Q,T,p,s,Subscript[algebra["c"], ___]}
		];
		If[!ValueQ[algebra["Id"],Method->"TrialEvaluation"],
			algebra["Id"]=Global`Id
		];
		algebra[pdeg_]["generators"]=algebra["generators"]={algebra["Oa"],algebra["Ob"]};
		AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[algebra];
	];	
);

(*Defining finite-dimensional representations*)
ClearAll[gFactor];
gFactor[j_][q_,t_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(m = 0\), \(j - 1\)]\(\((\((1 - 
\*SuperscriptBox[\(q\), \(j - m\)])\) \((1 - 
\*SuperscriptBox[\(q\), \(m\)] 
\*SuperscriptBox[\(t\), \(2\)])\))\)/\((\((1 - 
\*SuperscriptBox[\(q\), \(j - m - 1\)] t)\) \((1 - 
\*SuperscriptBox[\(q\), \(m + 1\)] t)\))\)\)\);
T[Q_,K_]:=I Q^(-K);

gFactor[j_,Q_,K_]:=gFactor[j][Q^4,T[Q,K]^2];

xval[j_Integer,Q_,K_]:=I Q^(-K+2j);

Framing[j_,Q_,K_]:=Q^(-j^2) T[Q,K]^(-j);

OaEigenvalue[j_,Q_,K_]:=Q^(2j) T[Q,K]+Q^(-2j) T[Q,K]^-1;

ClearAll[dFactor,dFactorAux];

\[Alpha]Factor[Q_,K_]:=FullSimplify[(2 Product[1+Q^(-2K+4m),{m,1,K-1}])^(-1/2),Assumptions->0<Q<1];

DefineRepresentation[rep_]:=(
	If[!ValueQ[rep["algebra"],Method->"TrialEvaluation"],
		Print["Underlying algebra is not defined"];
		Return[Indeterminate];
	];
	(*Defining \[Psi] functions and its evaluations*)
	With[
		{x=rep["algebra"]["x"],Q=rep["algebra"]["Q"],p=rep["algebra"]["p"],s=rep["algebra"]["s"]}
	,
		rep[K_]["p"]:=p;
		rep[K_]["x"]:=x;
		rep[K_][pdeg_]["\[Psi]"][i_]:=rep[K][pdeg]["\[Psi]"][i]=Module[
			{ans,F}
		,
			StartTimer["Series1"];
			ans=Series[rep["algebra"][pdeg]["\[Psi]"][i]/.{rep["algebra"]["T"]->T[Q,K]},{p,0,pdeg}];
			StopTimer["Series1"];
			StartTimer["SeriesLaurentCollect1"];
			ans=SeriesLaurentCollect[ans,x];
			StopTimer["SeriesLaurentCollect1"];
			Return[ans];
		];
		rep[K_][pdeg_]["\[Psi]val"][i_Integer,j_Integer]:=rep[K][pdeg]["\[Psi]val"][i,j]=Module[
			{ans}
		,
			StartTimer["\[Psi]valSeriesFactor"];
			ans=SeriesFactor[rep[K][pdeg]["\[Psi]"][i]/.{x->xval[j,Q,K]}];
			StopTimer["\[Psi]valSeriesFactor"];
			Return[ans];
		];
		(*Defining Decomposition of fuunctions w.r.t. basis*)
		rep[K_]["DecomposeK"]:=rep[K]["DecomposeK"]=(
			DefinePsiDecomposition[rep[K]];
			rep[K]["DecomposeKAux"][expr_]:=Module[
				{rules}
			,
				rules=rep[K]["Decompose"][expr];
				Return[Append[Select[rules,#[[1,1]]<=K&],rules[[-1]]]];
			];
			rep[K]["DecomposeKAux"]
		);
		rep[K_][pdeg_]["GetMatrix"][Op_]:=Module[
			{ans,indtab,j,i}
		,
			ans=Table[Table[{i},{i,0,K}]/.rep[K]["DecomposeK"][Op[rep[K][pdeg]["\[Psi]"][j]]/.{rep["algebra"]["T"]->T[Q,K]}],{j,0,K}];
			Return[Transpose[ans]];
		];
		(*Defining S-matrix*)
		rep[K_][pdeg_]["dFactor"][j_Integer]:=rep[K][pdeg]["dFactor"][j]=Module[
			{ans,p0,s0,numerator,denominator,x0,xj}
		,
			StarTimer["dFactornum"];
			numerator=Factor[rep[K][0]["\[Psi]"][0]/.{x->xval[0,rep["Q"],K]}];
			StopTimer["dFactornum"];
			StartTimer["dFactorden"];
			denominator=SeriesFactor[SeriesLimit[rep[K][pdeg]["\[Psi]"][0]/.{x->xval[j,Q,K]},{s->0}]];
			Print["denominator=",denominator];
			StopTimer["dFactorden"];
			If[SeriesCoefficient[denominator,{p,0,0}]===0,
				Print["Unexpected leading power in demoninator =",denominator];
				Return[Indeterminate];
			];
			Return[numerator/denominator];
		];
		rep[K_][pdeg_]["SMatrixElement"][i_,j_]:=rep[K][pdeg]["SMatrixElement"][i,j]=Module[
			{ans}
		,
			ans=rep[K][pdeg]["dFactor"][j]rep[K][pdeg]["\[Psi]val"][i,j]/gFactor[j,Q,K];
			StartTimer["SMatrixElement"];
			ans=SeriesFactor[ans];
			StoprTimer["SMatrixElement"];
			Return[ans];
		];
		rep[K_][pdeg_]["S"]:=rep[K][pdeg]["S"]=Table[rep[K][pdeg]["SMatrixElement"][i,j],{i,0,K},{j,0,K}];
		rep[K_][pdeg_]["T"]:=rep[K][pdeg]["T"]=Table[KroneckerDelta[i,j]Framing[i,Q,K] ,{i,0,K},{j,0,K}];
		rep[K_][pdeg_]["Da"]:=rep[K][pdeg]["T"];
		rep[K_][pdeg_]["Db"]:=rep[K][pdeg]["Db"]=Inverse[rep[K][pdeg]["T"]] . (rep[K][pdeg]["S"]/.{p->p/s}) . Inverse[rep[K][pdeg]["T"]];
		(*Defining Knot operators*)
		rep[K_][pdeg_]["Oa"]:=rep[K][pdeg]["Oa"]=Table[KroneckerDelta[i,j]OaEigenvalue[i,Q,K],{i,0,K},{j,0,K}];
		rep[K_][pdeg_]["Ob"]:=rep[K][pdeg]["Ob"]=Transpose[rep[K][pdeg]["GetMatrix"][(x+1/x)#&]];
	];
);

End[]

Begin["`AlgebraK2`"]

Inv:=Global`Inv;
\|01d7d9=Global`\|01d7d9;

Define[algebra_]:=With[{
		Q=algebra["Q"],p=algebra["p"],s=algebra["s"],pExp=algebra["pExp"],
		\[Sigma]=algebra["\[Sigma]"],
		Oa=algebra["Oa"],Ob=algebra["Ob"],
		a=algebra["a"],b=algebra["b"],S=algebra["S"],
		\[CapitalMu]=algebra["M"]
	}
	,
	(*Defining ring of Plethystic exponentials*)
	algebra["pring"]["plethysticvariables"]={Q,p,s};
	algebra["pring"]["pExp"]=pExp;
	EllipticSystems`InfiniteProducts`DefinePlethysticExponentRing[algebra["pring"]];
	(*Defining Free_2*)
	algebra["Free2"]["groupgenerators"]={a,b};
	If[!ValueQ[algebra["Free2"]["Id"],Method->"TrialEvaluation"],
		algebra["Free2"]["Id"]=\|01d7d9;
	];
	If[!ValueQ[algebra["Free2"]["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		algebra["Free2"]["NonCommutativeMultiply"]=SmallCircle;
	];
	AbstractAlgebra`FinitelyGenerated`DefineGroupAlgebra[algebra["Free2"]];
	AbstractAlgebra`Homomorphisms`DefineOnGenerators[\[Sigma],algebra["Free2"]];
	\[Sigma][a]=b;
	\[Sigma][b]=a;
	\[Sigma][\[Sigma][x_]]:=x;
	algebra["PowQ"][gen_][seq___]:=Module[
		{tab=List[seq]}
	,
		tab=DeleteCases[tab,gen];
		tab=DeleteCases[tab,Inv[gen]];
		Return[tab=={}];
	];
	(*Defining algebra F*)
	algebra["F"]["groundfield"]["generators"]=algebra["groundfield"]["generators"];
	algebra["F"]["generators"]={Oa[_],Ob[_]};
	If[!ValueQ[algebra["F"]["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		Unprotect[NonCommutativeMultiply];
		ClearAll[NonCommutativeMultiply];
		algebra["F"]["NonCommutativeMultiply"]=NonCommutativeMultiply;
	];
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[algebra["F"]];
	(*Defining mcg and its action*)
	AbstractAlgebra`CompositionAlgebra`DefineCompositionAlgebra[algebra["Free2"]];
	With[{
		NonCommutativeMultiply=algebra["F"]["NonCommutativeMultiply"],
		SmallCircle=algebra["Free2"]["NonCommutativeMultiply"]
	},
		(*Defining Action of S*)
		S[Oa[g_]]:=Ob[\[Sigma][g]];
		S[Ob[g_]]:=Oa[\[Sigma][g]];
		Inv[S][expr_]:=S[expr];
		(*Defining action of a*)
		a[Oa[g_]]:=a[Oa[g]]=algebra["F"]["Collect"][
			-(1/(Q^2-Q^-2)^2)Oa[\|01d7d9]**Oa[SmallCircle[g,Inv[a]]]**Oa[\|01d7d9]
		,Factor];
		a[Ob[g_]]:=a[Ob[g]]=algebra["F"]["Collect"][
			Q/(Q^2-Q^-2) Oa[\|01d7d9]**Ob[SmallCircle[g,Inv[a]]]-Q^(-1)/(Q^2-Q^-2) Ob[SmallCircle[g,Inv[a]]]**Oa[\|01d7d9]
		,Factor];
		(*Defining the action of Inv[a]*)
		Inv[a][Oa[g_]]:=Inv[a][Oa[g]]=algebra["F"]["Collect"][
			-(1/(Q^2-Q^-2)^2)Oa[\|01d7d9]**Oa[SmallCircle[g,a]]**Oa[\|01d7d9]
		,Factor];
		Inv[a][Ob[g_]]:=Inv[a][Ob[g]]=algebra["F"]["Collect"][
			-(Q^(-1)/(Q^2-Q^-2))Oa[\|01d7d9]**Ob[g\[SmallCircle]a]+Q/(Q^2-Q^-2) Ob[SmallCircle[g,a]]**Oa[\|01d7d9]
		,Factor];
		(*Defining action of b*)
		b[expr_]:=SmallCircle[S,a,S][expr];
		Inv[b][expr_]:=SmallCircle[S,Inv[a],S][expr];
		(*Defining explicit relations*)
		algebra["Relation"][0,Oa,g_]:=Oa[a\[SmallCircle]g]-Oa[g];
		algebra["Relation"][0,Ob,g_]:=Ob[b\[SmallCircle]g]-Ob[g];
		algebra["Relation"][1,O_,g_]:=O[g]**O[g]-O[1]**O[1];
		algebra["Relation"][2,g1_,g2_,g3_]:=Ob[g1]**Oa[g2]**Ob[g3];
		algebra["Relation"][3,g1_,g2_,g3_]:=Oa[g1]**Ob[g2]**Oa[g3];
		algebra["Relation"][4,O_,g_]:=O[1]**O[1]**O[g]+(Q^2-Q^-2)^2 O[g];
		algebra["Relation"][5,O_,g_]:=O[g]**O[1]**O[1]+(Q^2-Q^-2)^2 O[g];
		algebra["Relation"][6,g_]:=Oa[1]**Oa[1]**Ob[g]+(Q^2-Q^-2)^2 Ob[g]+Ob[g]**Oa[1]**Oa[1];
		algebra["Relation"][7,g_]:=Ob[1]**Ob[1]**Oa[g]+(Q^2-Q^-2)^2 Oa[g]+Oa[g]**Ob[1]**Ob[1];
		(*(ST)^3 relations*)
		algebra["Relation"][8,g1_,g2_]:=Oa[g2]**Oa[g1\[SmallCircle]a\[SmallCircle]b\[SmallCircle]a\[SmallCircle]g2]**Ob[a\[SmallCircle]g2]+Ob[a\[SmallCircle]g2]**Oa[g1\[SmallCircle]a\[SmallCircle]b\[SmallCircle]a\[SmallCircle]g2]**Oa[g2]-Ob[g2]**Ob[\[Sigma][g1]\[SmallCircle]g2]**Ob[g2];
		algebra["Relation"][9,g1_,g2_]:=Ob[g2]**Ob[g1\[SmallCircle]b\[SmallCircle]a\[SmallCircle]b\[SmallCircle]g2]**Oa[b\[SmallCircle]g2]+Oa[b\[SmallCircle]g2]**Ob[g1\[SmallCircle]b\[SmallCircle]a\[SmallCircle]b\[SmallCircle]g2]**Ob[g2]-Oa[g2]**Oa[\[Sigma][g1]\[SmallCircle]g2]**Oa[g2];
		algebra["Relation"][10,g1_,g2_]:=Oa[g2]**Oa[g1\[SmallCircle]Inv[a]\[SmallCircle]Inv[b]\[SmallCircle]Inv[a]\[SmallCircle]g2]**Ob[Inv[a]\[SmallCircle]g2]+Ob[Inv[a]\[SmallCircle]g2]**Oa[g1\[SmallCircle]Inv[a]\[SmallCircle]Inv[b]\[SmallCircle]Inv[a]\[SmallCircle]g2]**Oa[g2]-Ob[g2]**Ob[\[Sigma][g1]\[SmallCircle]g2]**Ob[g2];
		algebra["Relation"][11,g1_,g2_]:=Ob[g2]**Ob[g1\[SmallCircle]Inv[b]\[SmallCircle]Inv[a]\[SmallCircle]Inv[b]\[SmallCircle]g2]**Oa[Inv[b]\[SmallCircle]g2]+Oa[Inv[b]\[SmallCircle]g2]**Ob[g1\[SmallCircle]Inv[b]\[SmallCircle]Inv[a]\[SmallCircle]Inv[b]\[SmallCircle]g2]**Ob[g2]-Oa[g2]**Oa[\[Sigma][g1]\[SmallCircle]g2]**Oa[g2];
	];
	AbstractAlgebra`Homomorphisms`DefineHomomorphism[a,algebra["F"],algebra["F"]];
	AbstractAlgebra`Homomorphisms`DefineHomomorphism[Inv[a],algebra["F"],algebra["F"]];
	AbstractAlgebra`Homomorphisms`DefineHomomorphism[S,algebra["F"],algebra["F"]];
	(*Defining main algebra with relations*)
	If[!ValueQ[algebra["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		algebra["NonCommutativeMultiply"]=Star;
	];
	If[!ValueQ[algebra["donotsimplifyideal"],Method->"TrialEvaluation"],
		algebra["donotsimplifyideal"]=True;
	];
	algebra["generators"]=algebra["F"]["generators"];
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[algebra];
	With[
		{Star=algebra["NonCommutativeMultiply"],relation=algebra["relation"],
		coeff=-((((-1+Q^2)^2) ((1+Q^2)^2) )/Q^4)}
	,
		algebra["Reduce"][expr_]:=algebra["Collect"][expr/.{relation[__]->0},Factor];
		algebra["ExplicitlyInIdealQ"][expr_]:=(algebra["Reduce"][expr]===0);
		algebra["SimplifyFurtherQ"][args___]:=If[algebra["donotsimplifyideal"],
			!algebra["ExplicitlyInIdealQ"][Star[args]]
		,
			True
		];
		(*Identification of generators*)
		Oa[a]=Oa[Inv[a]]=Oa[\|01d7d9];
		Ob[b]=Ob[Inv[b]]=Ob[\|01d7d9];
		Oa[SmallCircle[a,g__]]:=Oa[SmallCircle[g]](*+relation[0,Oa,SmallCircle[g]]*);
		Oa[SmallCircle[Inv[a],g__]]:=Oa[SmallCircle[g]](*-relation[0,Oa,SmallCircle[Inv[a],g]]*);
		Ob[SmallCircle[b,g__]]:=Ob[SmallCircle[g]](*+relation[0,Ob,SmallCircle[g]]*);
		Ob[SmallCircle[Inv[b],g__]]:=Ob[SmallCircle[g]](*-relation[0,Ob,SmallCircle[Inv[b],g]]*);
		(*Simplificiation of the seven relations*)
		Star[X___,O_[g_],O_[g_],Y___]:=Star[X,O[\|01d7d9],O[\|01d7d9],Y]+X\[Star]relation[1,O,g]\[Star]Y/;
			g=!=\|01d7d9&&algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,Ob[g1_],Oa[g2_],Ob[g3_],Y___]:=X\[Star]relation[2,g1,g2,g3]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,Oa[g1_],Ob[g2_],Oa[g3_],Y___]:=X\[Star]relation[3,g1,g2,g3]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,O_[\|01d7d9],O_[\|01d7d9],O_[g_],Y___]:=coeff Star[X,O[g],Y]+X\[Star]relation[4,O,g]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,O_[g_],O_[\|01d7d9],O_[\|01d7d9],Y___]:=coeff Star[X,O[g],Y]+X\[Star]relation[5,O,g]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,Oa[\|01d7d9],Oa[\|01d7d9],Ob[g_],Y___]:=coeff Star[X,Ob[g],Y]-Star[X,Ob[g],Oa[\|01d7d9],Oa[\|01d7d9],Y]+X\[Star]relation[6,g]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
		Star[X___,Oa[g_],Ob[\|01d7d9],Ob[\|01d7d9],Y___]:=coeff Star[X,Oa[g],Y]-Star[X,Ob[\|01d7d9],Ob[\|01d7d9],Oa[g],Y]+X\[Star]relation[7,g]\[Star]Y/;
			algebra["SimplifyFurtherQ"][X]&&algebra["SimplifyFurtherQ"][Y];
	];
	(*Defining reduction w.r.t. first seven relations*)
	algebra["Simplify7"][Oa[g_]]:=Oa[g];
	algebra["Simplify7"][Ob[g_]]:=Ob[g];
	AbstractAlgebra`Homomorphisms`DefineHomomorphism[algebra["Simplify7"],algebra["F"],algebra];
	algebra["Reduce7"][expr_]:=algebra["Reduce"][algebra["Simplify7"][expr]];
	(*Introducing algebra of hat operators*)
	algebra["HatOperators"]["groundfield"]=algebra["groundfield"];
	algebra["HatOperators"]["generators"]={algebra["\[Delta]"][__],algebra["M"][_]};
	If[!ValueQ[algebra["HatOperators"]["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		algebra["HatOperators"]["NonCommutativeMultiply"]=Diamond;
	];
	AbstractAlgebra`CompositionAlgebra`DefineCompositionAlgebra[algebra["HatOperators"]];
	AbstractAlgebra`Localization`LocalizeAlgebra[algebra["HatOperators"]];
	algebra["\[Delta]"][subst_][expr_]:=expr/.subst;
	algebra["M"][m1_][v_]:=m1 . v;
	algebra["\[Delta]"][{p->p,s->s}]=algebra["HatOperators"]["Id"];
	algebra["M"][IdentityMatrix[3]]=algebra["HatOperators"]["Id"];
	\[CapitalMu]/:Times[X___,\[CapitalMu][m_],Y___]:=algebra["M"][algebra["pring"]["Simplify"][Times[X,Y,m]]];
	\[CapitalMu]/:Plus[X___,\[CapitalMu][m1_],algebra["M"][m2_],Y___]:=Plus[X,algebra["M"][algebra["pring"]["Simplify"][m1+m2]],Y];
	Inv[algebra["\[Delta]"][subst_]]:=Module[
		{pnew,snew,sol}
	,
		sol=Solve[{pnew,snew}==({p,s}/.subst),{p,s}];
		If[Length[sol]!=1,
			Print["unexpected number of solutions when inverting ",subst];
			Print["sol=",sol];
			Return[Indeterminate];
		];
		Return[algebra["\[Delta]"][{p->((p/.sol[[1]])/.{pnew->p,snew->s}),s->((s/.sol[[1]])/.{pnew->p,snew->s})}]];
	];
	Inv[algebra["M"][m_]]:=algebra["M"][algebra["pring"]["Simplify"][Inverse[m]]];
	With[
		{Diamond=algebra["HatOperators"]["NonCommutativeMultiply"]}
	,
		Diamond[X___,algebra["\[Delta]"][subst1_],algebra["\[Delta]"][subst2_],Y___]:=Module[
			{subst}
		,
			subst=Table[subst2[[i,1]]->(subst2[[i,2]]/.subst1),{i,1,Length[subst2]}];
			Diamond[X,algebra["\[Delta]"][subst],Y]
		];
		Diamond[X___,algebra["M"][m1_],algebra["M"][m2_],Y___]:=Diamond[X,algebra["M"][algebra["pring"]["Simplify"][m1 . m2]],Y];
		Diamond[X___,algebra["\[Delta]"][subst_],algebra["M"][m_],Y___]:=Diamond[X,algebra["M"][algebra["\[Delta]"][subst][m]],algebra["\[Delta]"][subst],Y];
		(*Defining SL(2,Z) representation in hat operators*)
		algebra["DA"]=Diamond[algebra["M"][{
			{1,0,0},
			{0,-I Q,0},
			{0,0,-1}
		}],algebra["\[Delta]"][{p->p s,s->s}]];
		algebra["DB"]=Diamond[algebra["M"][Map[algebra["pring"]["Simplify"],{
			{pExp[-(((Q^8-Q^-8)p s^-1 (s^2+2p s+p))/((1-s^2)(1-p^2/s^2)))],(2Q)/(1-Q^4) pExp[-(((Q^8-Q^-8)p s^-1 (s+2p s+p))/((1-s^2)(1-p^2/s^2)))],(2Q^4)/(1-Q^4)^2 pExp[-(((Q^8-Q^-8)p s^-1 (s^2+2p s+p))/((1-s^2)(1-p^2/s^2)))]},
			{-((1-Q^4)/Q^3)pExp[-(((Q^8-Q^-8)p(s+2p+1))/((1-s^2)(1-p^2/s^2)))],0,(2Q)/(1-Q^4) pExp[-(((Q^8-Q^-8)p(s+2p+1))/((1-s^2)(1-p^2/s^2)))]},
			{(1-Q^4)^2/(2Q^4) pExp[-(((Q^8-Q^-8)p s^-1 (s^2+2p s+p))/((1-s^2)(1-p^2/s^2)))],-((1-Q^4)/Q^3)pExp[-(((Q^8-Q^-8)p s^-1 (s+2p s+p))/((1-s^2)(1-p^2/s^2)))],pExp[-(((Q^8-Q^-8)p s^-1 (s^2+2p s+p))/((1-s^2)(1-p^2/s^2)))]}
		},{2}]],algebra["\[Delta]"][{p->p,s->s/p}]];
		algebra["DS"]:=algebra["DS"]=algebra["DA"]\[Diamond]algebra["DB"]\[Diamond]algebra["DA"];
	];
	(*Defining representation basic matrices*)
	algebra["OA"][\|01d7d9]=algebra["M"][{
		{I Q^-2-I Q^2,0,0},
		{0,0,0},
		{0,0,I Q^2-I Q^-2}
	}];
	algebra["OB"][\|01d7d9]=algebra["M"][{
		{0,pExp[((Q^8-Q^-8)p s (1-p))/((1-s^2)(1-p^2))],0},
		{-((1-Q^4)^2/(2 Q^4))pExp[-(((Q^8-Q^-8)p s (1-p))/((1-s^2)(1-p^2)))],0,pExp[-(((Q^8-Q^-8)p s(1-p))/((1-s^2)(1-p^2)))]},
		{0,-((1-Q^4)^2/(2Q^4))pExp[((Q^8-Q^-8)p s (1-p))/((1-s^2)(1-p^2))],0}
	}];
	(*Defining homomorphism \[CurlyPhi] and structure constants*)
	algebra["\[CurlyPhi]"][a]={{1,-1},{0,1}};
	algebra["\[CurlyPhi]"][b]={{1,0},{1,1}};
	AbstractAlgebra`MatrixRepresentations`DefineRepresentation[algebra["\[CurlyPhi]"],algebra["Free2"]];
	algebra["cp"][h_,g_]:=Module[
		{G,HG}
	,
		G=algebra["\[CurlyPhi]"][g];
		HG=algebra["\[CurlyPhi]"][algebra["Free2"]["NonCommutativeMultiply"][h,g]];
		pExp[(Q^8-Q^-8)/((1+s^-G[[2,2]] p^G[[2,1]])(1+s^-HG[[1,2]] p^HG[[1,1]])(1+s^HG[[2,2]] p^-HG[[2,1]]))]
	];
	algebra["cm"][h_,g_]:=Module[
		{G,HG}
	,
		G=algebra["\[CurlyPhi]"][g];
		HG=algebra["\[CurlyPhi]"][algebra["Free2"]["NonCommutativeMultiply"][h,g]];
		pExp[-(Q^8-Q^-8)/((1+s^-G[[2,2]] p^G[[2,1]])(1+s^HG[[1,2]] p^-HG[[1,1]])(1+s^HG[[2,2]] p^-HG[[2,1]]))]
	];
	(*Defining recursively higher matrices*)
	With[{
		SmallCircle=algebra["Free2"]["NonCommutativeMultiply"],
		Diamond=algebra["HatOperators"]["NonCommutativeMultiply"]
	}
	,
		algebra["OA"][a]=algebra["OA"][\|01d7d9];
		algebra["OA"][SmallCircle[a,X___]]:=algebra["OA"][SmallCircle[X]];
		algebra["OA"][SmallCircle[Inv[a],X___]]:=algebra["OA"][SmallCircle[X]];
		algebra["OB"][g_]:=algebra["OB"][g]=Inv[algebra["DS"]]\[Diamond]algebra["OA"][\[Sigma][g]]\[Diamond]algebra["DS"];
		(*Main recursion for OA*)
		algebra["OARecPlus"][apow_,g_]:=Module[
			{c}
		,
			c=algebra["cp"][SmallCircle[b,apow],SmallCircle[g]];
			c algebra["OA"][g]+(Q^2-Q^-2)^-2 (c-c^-1)Diamond[algebra["OB"][\|01d7d9],algebra["OB"][\|01d7d9],algebra["OA"][g]]
		];
		algebra["OARecMinus"][apow_,g_]:=Module[
			{c}
		,
			c=algebra["cm"][SmallCircle[Inv[b],apow],SmallCircle[g]];
			c algebra["OA"][g]+(Q^2-Q^-2)^-2 (c-c^-1)Diamond[algebra["OB"][\|01d7d9],algebra["OB"][\|01d7d9],algebra["OA"][g]]
		];
		algebra["OA"][b]:=algebra["OA"][b]=algebra["OARecPlus"][\|01d7d9,\|01d7d9];
		algebra["OA"][Inv[b]]:=algebra["OA"][Inv[b]]=algebra["OARecMinus"][\|01d7d9,\|01d7d9];
		algebra["OA"][SmallCircle[b,apowseq___?(algebra["PowQ"][a]),gseq___]]:=(
			algebra["OA"][SmallCircle[b,apowseq,gseq]]=algebra["OARecPlus"][SmallCircle[apowseq],SmallCircle[gseq]]
		)/;If[Length[List[gseq]]==0,
			True
		,
			algebra["PowQ"][b][List[gseq][[1]]]
		];
		algebra["OA"][SmallCircle[Inv[b],apowseq___?(algebra["PowQ"][a]),gseq___]]:=(
			algebra["OA"][SmallCircle[Inv[b],apowseq,gseq]]=algebra["OARecMinus"][SmallCircle[apowseq],SmallCircle[gseq]]
		)/;If[Length[List[gseq]]==0,
			True
		,
			algebra["PowQ"][b][List[gseq][[1]]]
		];
	];
	(*Defining homomorphism to matrices*)
	algebra["\[CapitalPsi]"][Oa[g_]]:=algebra["OA"][g];
	algebra["\[CapitalPsi]"][Ob[g_]]:=algebra["OB"][g];
	AbstractAlgebra`Homomorphisms`DefineHomomorphism[algebra["\[CapitalPsi]"],algebra["F"],algebra["HatOperators"]];
];

(*Generating TeX Output for K=2*)
DefineLaTeXOutput[algebra_]:=With[{
	Q=algebra["Q"],p=algebra["p"],s=algebra["s"],
	\[Sigma]=algebra["\[Sigma]"],
	Oa=algebra["Oa"],Ob=algebra["Ob"],relation=algebra["relation"],
	NonCommutativeMultiply=algebra["F"]["NonCommutativeMultiply"],Star=algebra["NonCommutativeMultiply"],
	a=algebra["a"],b=algebra["b"],
	\[CapitalPsi]=algebra["\[CapitalPsi]"],
	\[Alpha]=algebra["\[Alpha]"],
	g=Global`g,g1=Global`g1,g2=Global`g2,g3=Global`g3,f=Global`f,
	OA=Global`OA,OB=Global`OB,
	TeXg=algebra["TeXg"],TeXO=algebra["TeXO"],TeXWord=algebra["TeXWord"],TeXPoly=algebra["TeXPoly"],
	\[Alpha]powtext=algebra["\[Alpha]powtext"],\[Alpha]powtextQ=algebra["\[Alpha]powtextQ"],TeX\[Alpha]Poly=algebra["TeX\[Alpha]Poly"],
	TeXString=algebra["TeXString"]
},
	TeXg[gg_]:=Switch[gg,
	algebra["Free2"]["Id"],"1",
	a,"a",
	b,"b",
	Inv[a],"a^{-1}",
	Inv[b],"b^{-1}",
	f,"f",
	g,"g",
	g1,"g_1",
	g2,"g_2",
	g3,"g_3",
	\[Sigma][g],"\\sigma(g)",
	\[Sigma][g1],"\\sigma(g_1)",
	\[Sigma][g2],"\\sigma(g_2)",
	_SmallCircle,
		Module[{args=gg},
			args[[0]]=List;
			Return[StringJoin@@Map[TeXg,args]];
		]
	];
	TeXg[g1_,gg__]:=TeXg[g1]<>","<>TeXg[gg];
	TeXO[O_[g_]]:=(
	Switch[O,
	Oa,"\\Oa",
	Ob,"\\Ob",
	OA,"O_A",
	OB,"O_B"
	]<>"^{("<>TeXg[g]<>")}"
	);
	TeXWord[1]:="";
	TeXWord[Oa[g_]]:=TeXO[Oa[g]];
	TeXWord[Ob[g_]]:=TeXO[Ob[g]];
	TeXWord[OA[g_]]:=TeXO[OA[g]];
	TeXWord[OB[g_]]:=TeXO[OB[g]];
	TeXWord[a[expr_]]:="\\mathbf a\\big("<>TeXWord[expr]<>"\\big)";
	TeXWord[b[expr_]]:="\\mathbf b\\big("<>TeXWord[expr]<>"\\big)";
	TeXWord[relation[n_Integer,Oa,gg__]]:="\\R_{"<>ToString[n]<>",A}^{("<>TeXg[gg]<>")}";
	TeXWord[relation[n_Integer,Ob,gg__]]:="\\R_{"<>ToString[n]<>",B}^{("<>TeXg[gg]<>")}";
	TeXWord[relation[n_Integer,gg__]]:="\\R_{"<>ToString[n]<>"}^{("<>TeXg[gg]<>")}";
	TeXWord[\[CapitalPsi][expr_]]:="\\Psi\\big("<>TeXWord[expr]<>"\\big)";
	TeXWord[NonCommutativeMultiply[Op_,X__]]:=TeXWord[Op]<>TeXWord[NonCommutativeMultiply[X]];
	TeXWord[Star[Op_,X__]]:=TeXWord[Op]<>TeXWord[Star[X]];
	TeXPoly[expr_]:=Module[
		{rules,ans="",i,coeffstring,stdcoeff}
	,
		rules=algebra["Rules"][expr];
		For[i=1,i<=Length[rules],i++,
			stdcoeff=StandardForm[rules[[i,2]]];
			coeffstring=ToString[TeXForm[stdcoeff]];
			coeffstring=StringReplace[coeffstring,{
				"\\sqrt{q}"->"q^{1/2}",
				"\\frac{1}{Q^"->"Q^{-",
				"\\frac{1}{Q}"->"Q^{-1}"
			}];
			If[coeffstring=="1",coeffstring=""];
			If[coeffstring=="-1",coeffstring="-"];
			If[StringLength[coeffstring]>0,
				Switch[stdcoeff,
				_Plus,coeffstring="("<>coeffstring<>")"
				];
			];
			(*Print["rules[[i,2]]=",rules[[i,2]]];
			Print["coeffstring=",coeffstring];*)
			ans=ans<>coeffstring<>TeXWord[rules[[i,1]]]<>"+";
		];
		ans=StringDrop[ans,-1];
		ans=StringReplace[ans,{"+-"->"-","\\frac{1}{q^{"->"q^{-"}];
		ans=StringReplace[ans,{"}}"->"}"}];
		Return[ans];
	];
	\[Alpha]powtext[n_]:=Switch[n,
	0,"",
	1,"\\big(q^{1/2}-q^{-1/2}\\big)",
	_?(#>1&),\[Alpha]powtext[1]<>"^"<>ToString[n],
	-1,"\\frac1{q^{1/2}-q^{-1/2}}",
	_?(#<-1&),"\\frac1{\\big(q^{1/2}-q^{-1/2}\\big)^"<>ToString[-n]<>"}"
	];
	\[Alpha]powtextQ[n_]:=Switch[n,
	0,"",
	1,"\\big(Q^2-Q^{-2}\\big)",
	_?(#>1&),\[Alpha]powtextQ[1]<>"^"<>ToString[n],
	-1,"\\frac1{Q^2-Q^{-2}}",
	_?(#<-1&),"\\frac1{\\big(Q^2-Q^{-2}\\big)^"<>ToString[-n]<>"}"
	];
	TeX\[Alpha]Poly[expr_]:=Module[
		{\[Alpha]expr,\[Alpha]rules,ans="",i,sign="",polytext}
	,
		\[Alpha]expr=algebra["Collect"][expr,Factor[Factor[#]/.{Q-1->(\[Alpha] Q^2)/(1+Q+Q^2+Q^3),1-Q->-((\[Alpha] Q^2)/(1+Q+Q^2+Q^3))}]&];
		\[Alpha]rules=CommonDefinitions`Rational`LaurentCoefficientRules[\[Alpha]expr,{\[Alpha]}];
		If[Length[\[Alpha]rules]==0,Return[ToString[0]]];
		For[i=1,i<=Length[\[Alpha]rules],i++,
			Switch[\[Alpha]rules[[i,2]],
			_Plus,ans=ans<>\[Alpha]powtextQ[\[Alpha]rules[[i,1,1]]]<>"\\Big("<>TeXPoly[\[Alpha]rules[[i,2]]]<>"\\Big)+",
			_,
				polytext=TeXPoly[\[Alpha]rules[[i,2]]];
				If[StringPart[polytext,1]=="-",
					sign="-";
					polytext=StringDrop[polytext,1];
				];
				ans=ans<>sign<>\[Alpha]powtextQ[\[Alpha]rules[[i,1,1]]]<>polytext<>"+";
			];
		];
		ans=StringDrop[ans,-1];
		ans=StringReplace[ans,{"+-"->"-"}];
		Return[ans];
	];
	(*Setting power fractions style*)
	algebra["LaTeXstyle"]["powers"]="frac";
	TeXString[expr_]:=Module[
		{ans}
	,
		ans=TeX\[Alpha]Poly[expr];
		Switch[algebra["LaTeXstyle"]["powers"],
		"frac",ans=StringReplace[ans,{
			"{-3/4}"->"{-\\frac34}",
			"{-1/2}"->"{-\\frac12}",
			"{-1/4}"->"{-\\frac14}",
			"{1/4}"->"{\\frac14}",
			"{1/2}"->"{\\frac12}",
			"{3/4}"->"{\\frac34}"
		}];
		Return[ans];
		];
	];
];

End[]

EndPackage[]

