(* ::Package:: *)

BeginPackage["AbstractAlgebra`"]

Off[Solve::svars];
Off[LinearSolve::nosol];

Begin["`GroundField`"]

debug=False;
debugAll=False;
safemode=True;

FieldElementQ[expr_,field_]:=Module[
	{i,xtab}
,
	Switch[expr,
		_?NumericQ,
			Return[True],
		_Plus,
			For[i=1,i<=Length[expr],i++,
				If[!FieldElementQ[expr[[i]],field],Return[False]];
			];
			Return[True],
		_Times,
			For[i=1,i<=Length[expr],i++,
				If[!FieldElementQ[expr[[i]],field],Return[False]];
			];
			Return[True],
		_Power,
			If[FieldElementQ[expr[[1]],field]&&FieldElementQ[expr[[2]],field],
				Return[True]
			,
				If[safemode,
					Print["Warning: Power is used for element outside groundfield, expr=",expr, ", generators",field["generators"]];
				];
				Return[False]
			],
		_?(Or@@Table[MatchQ[#,field["generators"][[i]]],{i,1,Length[field["generators"]]}]&),
			Return[True],
		_,
			Return[False];
	];
];

FactorFieldOut[expr0_,field_]:=Module[
	{comm,ncm,i,counter,expr=expr0}
,
	Switch[expr,
		_Times,
			expr[[0]]=List;
			comm=ncm=1;
			counter=0;
			For[i=1,i<=Length[expr],i++,
				If[FieldElementQ[expr[[i]],field],
					comm=comm expr[[i]]
				,
					counter++;
					If[safemode&&(counter==2),
						Print["Unexpected Input in FactorFieldOut (Times) ",expr0," generators ",field["generators"],", comm=",comm,", ncm=",ncm,", expr[[i]]=",expr[[i]]];
						Return[Indeterminate];
					];
					ncm=ncm expr[[i]];
				];
			];
			Return[{comm,ncm}],
		_?(FieldElementQ[#,field]&),
			Return[{expr,1}],
		_Power,
			Return[{expr,1}],
		_,
			Return[{1,expr}]
	];
];

(*FactorizableFieldElementQ[x_Times,groundfield_]:=Module[
	{xtab=x}
,
	xtab[[0]]=List;
	Return[Or@@Map[FieldElementQ[#,groundfield]&,xtab]];
];*)

SetMultiLinear[F_,groundfield_,SimplifyF_]:=Module[
	{pos}
,
	If[AtomQ[F],
		If[Position[Attributes[F],Flat]!={}||Position[Attributes[F],OneIdentity]!={}||Position[Attributes[F],Protected]!={},
			Print["Incompatible built-in attributes ",Attributes[F]," for ",F];
		];
	];
	F[x___,y_Plus,z___]:=Module[
		{ytab=y}
	,
		ytab[[0]]=List;
		Return[SimplifyF[Plus@@Map[F[x,#,z]&,ytab]]];
	];
	F[x___,y_Times,z___]:=Module[
		{comm,ncm}
	,
		{comm,ncm}=FactorFieldOut[y,groundfield];
		Return[comm F[x,ncm,z]];
	](*/;FactorizableFieldElementQ[y,groundfield]*);
	F[x___,0,z___]:=0;
	F[x___,y_?(#=!=1&&FieldElementQ[#,groundfield]&),z___]:=y F[x,1,z];
];

SetMultiLinear[MultF_,groundfield_]:=SetMultiLinear[MultF,groundfield,#&];

(*Field of Elementary Functions*)

elementaryfunctions=FromEntity/@MathematicalFunctionData["ElementaryFunctions"];

BareFunction[expr_]:=Switch[expr,
	_Function,
		expr[[1,0]],
	_,
		expr
];

bareelementaryfunctions=DeleteDuplicates[Map[BareFunction,elementaryfunctions]];

ElementaryFunctionQ[expr_]:=Position[bareelementaryfunctions,expr[[0]],1]!={};

End[]

Begin["`Associative`"]

debug=False;

DefineAssociativeMultiplication[MultF_,groundfield_]:=(
	If[debug,Print["Defining Associative Multiplication ",{MultF,groundfield}]];
	MultF[x_]:=x;
	AbstractAlgebra`GroundField`SetMultiLinear[MultF,groundfield];
	MultF[x___,y_MultF,z___]:=Module[
		{ytab=y}
	,
		ytab[[0]]=List;
		Return[MultF[x,Sequence@@ytab,z]];
	];
);

DefineUnitalMultiplication[MultF_,groundfield_,unit_]:=(
	DefineAssociativeMultiplication[MultF,groundfield];
	MultF[Sequence[]]:=unit;
	MultF[x___,y_?(AbstractAlgebra`GroundField`FieldElementQ[#,groundfield]&),z___]:=y MultF[x,z];
	MultF[x___,unit,y___]:=MultF[x,y];
);

DefineUnitalMultiplication[MultF_,groundfield_]:=DefineUnitalMultiplication[MultF,groundfield,1];

End[]

Begin["`TensorAlgebra`"]

(*Basic operations*)
(*Permutation map*)
DefinePermutation[\[CapitalSigma]_,\[Sigma]_,CircleTimes_,groundfield_]:=(
	Subscript[\[CapitalSigma], permutation_List]:=Subscript[\[CapitalSigma], permutation]=Module[
		{\[Sigma]Aux:=Subscript[\[Sigma], permutation]}
	,
		Print["Defining ",\[CapitalSigma]," for ",permutation];
		AbstractAlgebra`GroundField`SetMultiLinear[\[Sigma]Aux,groundfield];
		If[permutation=={1},
			\[Sigma]Aux[x_]:=x
		,
			\[Sigma]Aux[x_CircleTimes]:=Module[
				{xtab=x}
			,
				xtab[[0]]=List;
				Return[CircleTimes@@Permute[xtab,permutation]];
			]/;Length[x]==Length[permutation];
		];
		Return[\[Sigma]Aux];
	];
);

(*Multiplication map*)
DefineMultiplicationMap[\[Mu]_,CircleTimes_,NonCommutativeMultiply_,groundfield_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[\[Mu],groundfield];
	\[Mu][CircleTimes[x_,y__]]:=NonCommutativeMultiply[x,y];
);

(*Multiplication of elements*)
DefineTensorModuleMultiplication[CircleTimes_,NCMultiply_]:=(
	With[{NonCommutativeMultiply=NCMultiply}
	,
		NonCommutativeMultiply[x___,y_CircleTimes,z_CircleTimes,w___]:=Module[
			{yz}
		,
			If[Length[y]!=Length[z],
				Print["Unexpected Input in Tensor Bimodule Multiplication ",List[x,y,z,w]];
			];
			yz=Table[y[[i]]**z[[i]],{i,1,Length[y]}];
			Return[NonCommutativeMultiply[x,(CircleTimes@@yz),w]];
		];
	];
);

End[]

Begin["`General`"]

Rules[expr0_,groundfield_]:=Module[
	{ans={},i,comm,ncm,pos,expr}
,
	expr=Expand[expr0];
	Switch[expr,
	_Plus,
		For[i=1,i<=Length[expr],i++,
			{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[expr[[i]],groundfield];
			pos=Position[ans,ncm,2];
			pos=DeleteCases[pos,{_,2}];
			If[Length[pos]>1,Print["Error in NonCommutative Rules, ",expr," ",ncm," ",pos]];
			If[pos=={},
				AppendTo[ans,ncm->comm]
			,
				pos=pos[[1,1]];
				ans[[pos,2]]=ans[[pos,2]]+comm
			];
		];
		Return[ans],
	_,
		{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[expr,groundfield];
		Return[{ncm->comm}];
	];
];

MRules[expr_,groundfield_]:=MRules[expr,groundfield]=Rules[expr,groundfield];

Monomials[expr_,groundfield_]:=Map[#[[1]]&,AbstractAlgebra`General`Rules[expr,groundfield]];

NCCollect[expr_,groundfield_,SimplifyF_]:=Module[
	{rules}
,
	rules=Rules[expr,groundfield];
	Return[Plus@@Map[SimplifyF[#[[2]]]#[[1]]&,rules,1]];
];

NCCollect[expr_,groundfield_]:=NCCollect[expr,groundfield,#&];

End[]

Begin["`MatrixRepresentations`"]

debugAll=False;

DefineRepresentation[RepF_,algebra_,n_,MultF_]:=Module[
	{i,j}
,
	With[{NonCommutativeMultiply=MultF}
	,
		RepF[algebra["Id"]]=SparseArray[Table[{i,i}->1,{i,1,n}]];
		(*RepF[x_?(AbstractAlgebra`GroundField`FieldElementQ[#,algebra["groundfield"]]&)]:=SparseArray[Table[{i,i}->x,{i,1,n}]];*)
		RepF[x_Times]:=Module[
			{comm,ncm}
		,
			{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,algebra["groundfield"]];
			Return[comm RepF[ncm]];
		];
		RepF[x_Plus]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Total[Map[RepF,xtab]]];
		];
		RepF[x_NonCommutativeMultiply]:=RepF[x]=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Dot[RepF[NonCommutativeMultiply@@Drop[xtab,-1]],RepF[xtab[[-1]]]]];
		];
		RepF[Global`Inv[x_]]:=Inverse[RepF[x]];
		RepF[x_CircleTimes]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[TensorProduct@@Map[RepF,xtab]];
		];
	];
];

DefineRepresentation[RepF_,algebra_,n_]:=DefineRepresentation[RepF,algebra,n,algebra["NonCommutativeMultiply"]];

DefineRepresentation[RepF_,algebra_]:=DefineRepresentation[RepF,algebra,Length[RepF[algebra["generators"][[1]]]]];

GetRelationsAux[algebra_,RepF_,length_]:=Module[
	{rulestab,M,reltab}
,
	rulestab=Map[Flatten[RepF[#]]&,algebra["basis"][length]];
	If[debugAll,Print["rulestab = ",rulestab]];
	M=Transpose[SparseArray[rulestab]];
	If[debugAll,Print["M = ",M]];
	reltab=NullSpace[M];
	If[reltab!={},reltab=RowReduce[SparseArray[reltab]]];
	If[debugAll,Print["reltab = ",reltab]];
	Return[Table[Total[Map[algebra["basis"][length][[#[[1,1]]]]#[[2]]&,ArrayRules[reltab[[i]]]]],{i,1,Length[reltab]}]];
];

DefineCatRepresentation[Rep_,cat_,DimF_,CompositionF_]:=Module[
	{i,j}
,
	With[{SmallCircle=CompositionF}
	,
		Rep[x_?(cat["IdentityMorphismQ"])]:=SparseArray[Table[{i,i}->1,{i,1,DimF[cat["s"][x]]}]];
		Rep[x_Times]:=Module[
			{comm,ncm}
		,
			{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,cat["groundfield"]];
			Return[comm Rep[ncm]];
		];
		Rep[x_Plus]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Total[Map[Rep,xtab]]];
		];
		Rep[x_SmallCircle]:=(*Rep[x]=*)Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[Dot[Rep[SmallCircle@@Drop[xtab,-1]],Rep[xtab[[-1]]]]];
		];
		Rep[Global`Inv[x_]]:=Rep[Global`Inv[x]]=Inverse[Rep[x]];
		Rep[x_CircleTimes]:=Module[
			{xtab=x}
		,
			xtab[[0]]=List;
			Return[TensorProduct@@Map[Rep,xtab]];
		];
	];
];

DefineCatRepresentation[Rep_,cat_,DimF_]:=DefineCatRepresentation[Rep,cat,DimF,cat["Composition"]];

End[]

Begin["`CompositionAlgebra`"]

debug=False;

DefineVectorSpaceOfOperators[groundfield_]:=(
	If[debug,Print["Defining Vector Space of operators ",groundfield]];
	Unprotect[Plus];
	Plus[x_,y__][z_]:=x[z]+Plus[y][z];
	Protect[Plus];
	Unprotect[Times];
	Times[x___,y_?(AbstractAlgebra`GroundField`FieldElementQ[#,groundfield]&),z___][w_]:=y Times[x,z][w];
	Protect[Times];
);

DefineCompositionAction[algebra_]:=(
	(*Defining Action of Composition of Operators*)
	If[!ValueQ[algebra["Id"],Method->"TrialEvaluation"],
		algebra["Id"]=Global`Id;
	];
	algebra["Id"][x_]:=x;
	If[!ValueQ[algebra["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		algebra["NonCommutativeMultiply"]=SmallCircle;
	];
	With[
		{SmallCircle=algebra["NonCommutativeMultiply"]}
	,
		AbstractAlgebra`Associative`DefineAssociativeMultiplication[algebra["NonCommutativeMultiply"],algebra["groundfield"]];
		SmallCircle[x__,y_][z_]:=SmallCircle[x][y[z]];
		SmallCircle[x___,algebra["Id"],y___]:=SmallCircle[x,y];
	];
);

DefineCompositionAlgebra[algebra_]:=(
	DefineVectorSpaceOfOperators[algebra["groundfield"]];
	DefineCompositionAction[algebra];
);

DefineCompositionCategory[cat_,ElementaryQ_]:=With[
	{CircleTimes=cat["CircleTimes"]}
,
	DefineVectorSpaceOfOperators[cat["groundfield"]];
	(*Defining Action of Identity Operators*)
	If[!ValueQ[cat["Id"],Method->"TrialEvaluation"],
		cat["Id"]=Global`Id;
	];
	Subscript[cat["Id"],_][x_?ElementaryQ]:=x;
	(*Defining Action of Composition of Operators*)
	If[!ValueQ[cat["Composition"],Method->"TrialEvaluation"],
		cat["Composition"]=SmallCircle
	];
	cat["objects"]={Subscript[cat["V"], _]};
	AbstractAlgebra`FinitelyGenerated`DefineCategory[cat];
	With[
		{SmallCircle=cat["Composition"]}
	,
		SmallCircle[x__,y_][z_]:=SmallCircle[x][y[z]];
	];
	(*Defining Source of Tensor Product of Operators*)
	CircleTimes[Subscript[cat["V"], i_],Subscript[cat["V"], j_],z___]:=CircleTimes[Subscript[cat["V"], i+j],z];
	(*Defining Tensor Product of Operators*)
	CircleTimes[x_,y__][0]:=0;
	CircleTimes[x_,y__][z_Plus]:=Module[
		{ztab=z}
	,
		ztab[[0]]=List;
		Return[Plus@@Map[CircleTimes[x,y],ztab]];
	];
	CircleTimes[x_,y__][m_Times]:=Module[
		{comm,ncm}
	,
		{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[m,cat["groundfield"]];
		Return[comm CircleTimes[x,y][ncm]]
	];
	CircleTimes[x_,y__][z_?ElementaryQ]:=Module[
		{ztab,n}
	,
		Switch[z,
		_CircleTimes,
			ztab=z;
			ztab[[0]]=List,
		_,
			ztab={z}
		];
		Switch[cat["s"][x],
		_Subscript,
			n=cat["s"][x][[2]],
		_,
			Print["Unexpected Source of ",x,", source = ",cat["s"][x]];
			Return[Indeterminate];
		];
		Return[CircleTimes[x[CircleTimes@@Take[ztab,n]],CircleTimes[y][CircleTimes@@Drop[ztab,n]]]];
	];
	(*Defining Operators With Zero Arguments*)
	With[{TensorNull=Global`TensorNull},
		CircleTimes[]:=TensorNull;
		TensorNull/:X_?(cat["s"][#]==Subscript[cat["V"], 0]&)[TensorNull]:=X;
	];
];

End[]

Begin["`Homomorphisms`"]

Inv:=Global`Inv;

DefineHomomorphism[\[Psi]_,algebra1_,algebra2_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[\[Psi],algebra1["groundfield"],AbstractAlgebra`General`NCCollect[#,algebra1["groundfield"],Factor]&];
	\[Psi][algebra1["NonCommutativeMultiply"][X_,Y__]]:=algebra2["NonCommutativeMultiply"][\[Psi][X],\[Psi][algebra1["NonCommutativeMultiply"][Y]]];
	\[Psi][algebra1["Id"]]=algebra2["Id"];
	\[Psi][Inv[X_]]:=Inv[\[Psi][X]];
);

(*Old functions for reverse compatibility*)
DefineOnGenerators[\[Tau]_,algebra_,multpatterns_]:=(
	AbstractAlgebra`GroundField`SetMultiLinear[\[Tau],algebra["groundfield"],AbstractAlgebra`General`NCCollect[#,algebra["groundfield"],Factor]&];
	\[Tau][algebra["Id"]]=algebra["Id"];
	\[Tau][x_?(Or@@Table[MatchQ[#,multpatterns[[i]]],{i,1,Length[multpatterns]}]&)]:=Module[
		{xtab=x,op=x[[0]]}
	,
		xtab[[0]]=List;
		Return[AbstractAlgebra`General`NCCollect[op@@Map[\[Tau],xtab],algebra["groundfield"],Factor]];
	];
	\[Tau][Global`Inv[x_]]:=Global`Inv[\[Tau][x]];
);

DefineOnGenerators[\[Tau]_,algebra_]:=With[
	{NonCommutativeMultiply=algebra["NonCommutativeMultiply"]}
,
	DefineOnGenerators[\[Tau],algebra,{_NonCommutativeMultiply,_CircleTimes}];
];

DefineAutomorphismGroupAlgebra[algebra_,aut_]:=(
	aut["groundfiend"]=algebra["groundfield"];
	If[!ValueQ[aut["NonCommutativeMultiply"],Method->"TrialEvaluation"],
		aut["NonCommutativeMultiply"]=SmallCircle
	];
	AbstractAlgebra`FinitelyGenerated`DefineGroupAlgebra[aut];
	AbstractAlgebra`CompositionAlgebra`DefineCompositionAlgebra[aut];
	With[
		{NonCommutativeMultiply=algebra["NonCommutativeMultiply"]}
	,
		Map[DefineOnGenerators[#,algebra,{_NonCommutativeMultiply,_CircleTimes}]&,aut["generators"]];
	];
);

End[]

Begin["`FinitelyGenerated`"]

DefineAssociativeAlgebra[algebra_]:=(
	(*Testing preinitialized values*)
	If[!ListQ[algebra["generators"]],
		Print["Generators of ",algebra," undefined"];
		Return[Indeterminate];
	];
	(*Setting default values*)
	If[!ListQ[algebra["groundfield"]["generators"]],algebra["groundfield"]["generators"]={}];
	If[!ValueQ[algebra["NonCommutativeMultiply"],Method->"TrialEvaluation"],
			Unprotect[NonCommutativeMultiply];
			ClearAll[NonCommutativeMultiply];
			algebra["NonCommutativeMultiply"]=NonCommutativeMultiply
	];
	(*Defining associative multiplication*)
	If[!ValueQ[algebra["Id"],Method->"TrialEvaluation"],algebra["Id"]=1];
	AbstractAlgebra`Associative`DefineUnitalMultiplication[algebra["NonCommutativeMultiply"],algebra["groundfield"],algebra["Id"]];
	With[
		{MultF=algebra["NonCommutativeMultiply"]}
	,
		(*Defining Basic Test Functions*)
		algebra["FieldElementQ"][expr_]:=AbstractAlgebra`GroundField`FieldElementQ[expr,algebra["groundfield"]];
		algebra["GeneratorQ"][expr_]:=(Or@@Map[MatchQ[expr,#]&,algebra["generators"]]);
		algebra["AssociativeMonomialQ"][expr_]:=Switch[expr,
		_?(AbstractAlgebra`GroundField`FieldElementQ[#,algebra["groundfield"]]&),True,
		_?(algebra["GeneratorQ"]),True,
		_?(MatchQ[#,_MultF]||MatchQ[#,_Times]&),Module[
			{exprtab=expr}
		,
			exprtab[[0]]=List;
			Return[And@@Map[algebra["AssociativeMonomialQ"],exprtab,1]]
		],
		_,False
		];
		(*Defining General Functions*)
		algebra["Collect"][expr_,F_]:=AbstractAlgebra`General`NCCollect[expr,algebra["groundfield"],F];
		algebra["Collect"][expr_]:=algebra["Collect"][expr,#&];
		algebra["Rules"][expr_]:=AbstractAlgebra`General`Rules[expr,algebra["groundfield"]];
		algebra["ElementQ"][expr_]:=Module[
			{rules,i}
		,
			rules=algebra["Rules"][expr];
			For[i=1,i<=Length[rules],i++,
				If[!algebra["FieldElementQ"][rules[[i,2]]],Return[False]];
				If[!algebra["AssociativeMonomialQ"][rules[[i,1]]],Return[False]];
			];
			Return[True];
		];
	];
);

DefineGroupAlgebra[algebra_]:=(
	algebra["generators"]=Join[algebra["groupgenerators"],Map[Global`Inv,algebra["groupgenerators"],1]];
	DefineAssociativeAlgebra[algebra];
	AbstractAlgebra`Localization`LocalizeAlgebra[algebra];
);

DefineTensorAlgebra[algebra_]:=(
	(*Setting default values*)
	If[!ValueQ[algebra["CircleTimes"],Method->"TrialEvaluation"],algebra["CircleTimes"]=CircleTimes];
	AbstractAlgebra`Associative`DefineAssociativeMultiplication[algebra["CircleTimes"],algebra["groundfield"]];
	(*Defining Permutation Map*)
	AbstractAlgebra`TensorAlgebra`DefinePermutation[algebra["\[CapitalSigma]"],algebra["\[Sigma]"],algebra["CircleTimes"],algebra["groundfield"]];
	(*Defining Test Functions*)
	algebra["TensorMonomialQ"][expr_]:=Switch[expr,
	_?(algebra["AssociativeMonomialQ"]),True,
	_?(algebra["IdentityMorphismQ"]),True,
	_?(algebra["ElementaryMorphismQ"]),True,
	_CircleTimes,Module[
		{exprtab=expr}
	,
		exprtab[[0]]=List;
		Return[And@@Map[algebra["TensorMonomialQ"],exprtab,1]]
	],
	_,False
	];
);

DefineTensorAlgebraWithModules[algebra_]:=(
	DefineAssociativeAlgebra[algebra];
	DefineTensorAlgebra[algebra];
	AbstractAlgebra`TensorAlgebra`DefineTensorModuleMultiplication[algebra["CircleTimes"],algebra["NonCommutativeMultiply"]];
	AbstractAlgebra`TensorAlgebra`DefineMultiplicationMap[algebra["\[Mu]"],algebra["CircleTimes"],algebra["NonCommutativeMultiply"],algebra["groundfield"]];
);

DefineIdentityMorphisms[cat_]:=Module[
	{i}
,
	(*Setting default notations*)
	If[!ValueQ[cat["Id"],Method->"TrialEvaluation"],cat["Id"]=Global`e];
	If[!ValueQ[cat["idmorphisms"],Method->"TrialEvaluation"],cat["idmorphisms"]=Map[Subscript[cat["Id"], #]&,cat["objects"]]];
	(*Defining sources and targets for identity morphisms*)
	cat["s"][Subscript[cat["Id"], v_]]:=v;
	cat["t"][Subscript[cat["Id"], v_]]:=v;
	(*Defining composition rules for identity morphisms*)
	For[i=1,i<=Length[cat["idmorphisms"]],i++,
		With[{e=cat["idmorphisms"][[i]]},
			cat["Composition"][x__,e,y__]:=If[cat["s"][cat["Composition"][x]]===cat["s"][e]===cat["t"][cat["Composition"][y]],
				cat["Composition"][x,y]
			,
				Print["NonComposable expression (1)",{x,e,y}," at ",{cat["Composition"][x],e,cat["Composition"][y],cat}];
				Indeterminate
			];
			cat["Composition"][x__,e]:=If[cat["s"][cat["Composition"][x]]===cat["s"][e],
				cat["Composition"][x]
			,
				Print["NonComposable expression (2) ",{x,e}," at ",{cat["Composition"][x],e,cat}];
				Indeterminate
			];
			cat["Composition"][e,y__]:=If[cat["s"][e]===cat["t"][cat["Composition"][y]],
				cat["Composition"][y]
			,
				Print["NonComposable expression (3) ",{e,y}," at ",{e,cat["Composition"][y],cat}];
				Indeterminate
			];
		];
	];
];

DefineSourcesAndTargets[cat_]:=With[
	{CompositionF=cat["Composition"]}
,
	(*Basic functions*)
	cat["s"][x_CompositionF]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[cat["s"][xtab[[-1]]]];
	];
	cat["t"][x_CompositionF]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[cat["t"][xtab[[1]]]];
	];
	(*Definitions for Localized categories*)
	cat["s"][Global`Inv[x_]]:=cat["t"][x];
	cat["t"][Global`Inv[x_]]:=cat["s"][x];
	(*Defining sources and targets of morphisms in a linear category*)
	cat["s"][x_Times]:=Module[
		{comm,ncm}
	,
		{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,cat["groundfield"]];
		Return[cat["s"][ncm]]
	];
	cat["t"][x_Times]:=Module[
		{comm,ncm}
	,
		{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,cat["groundfield"]];
		Return[cat["t"][ncm]]
	];
	cat["s"][x_Plus]:=Module[
		{xtab=x,ans}
	,
		xtab[[0]]=List;
		ans=DeleteDuplicates[Map[cat["s"],xtab]];
		If[Length[ans]!=1,
			Print["Source of the sum is not defined, ",ans];
			Return[Indeterminate]
		,
			Return[ans[[1]]];
		];
	];
	cat["t"][x_Plus]:=Module[
		{xtab=x,ans}
	,
		xtab[[0]]=List;
		ans=DeleteDuplicates[Map[cat["t"],xtab]];
		If[Length[ans]!=1,
			Print["Target of the sum is not defined, ",ans];
			Return[Indeterminate]
		,
			Return[ans[[1]]];
		];
	];
	(*Composability Test*)
	cat["ComposableQ"][x_]:=Module[
		{F}
	,
		Return[Catch[
		F[y___]:=Module[
			{ytab=y,i}
		,
			ytab[[0]]=List;
			For[i=1,i<Length[ytab],i++,
				If[cat["s"][ytab[[i]]]=!=cat["t"][ytab[[i+1]]],Throw[False]];
			];
		];
		x/.{NonCommutativeMultiply->F,SmallCircle->F};
		Throw[True];
		]];
	];
	(*Tensor categories*)
	cat["s"][x_CircleTimes]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[CircleTimes@@Map[cat["s"],xtab]];
	];
	cat["t"][x_CircleTimes]:=Module[
		{xtab=x}
	,
		xtab[[0]]=List;
		Return[CircleTimes@@Map[cat["t"],xtab]];
	];
	(*Sources and Targets for Localized Categories*)
	cat["s"][Global`Inv[x_]]:=cat["t"][x];
	cat["t"][Global`Inv[x_]]:=cat["s"][x];
	(*Topological Notation*)
	If[ValueQ[cat["TopologicalNotation"],Method->"TrialEvaluation"],
		If[cat["TopologicalNotation"],
			Needs["Notation`"];
			Notation[ParsedBoxWrapper[RowBox[{"cat", "[", "\"T\"", "]"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"cat", "[", "\"t\"", "]"}]]];
			Notation[ParsedBoxWrapper[RowBox[{"cat", "[", "\"H\"", "]"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"cat", "[", "\"s\"", "]"}]]];
		];
	];
];

DefineCategory[cat_]:=Module[
	{MultF}
,
	If[!ValueQ[cat["Composition"],Method->"TrialEvaluation"],cat["Composition"]=SmallCircle];
	cat["Composition"][x_]:=x;
	AbstractAlgebra`Associative`DefineUnitalMultiplication[cat["Composition"],cat["groundfield"]];
	DefineIdentityMorphisms[cat];
	DefineSourcesAndTargets[cat];
	(*Defining test functions*)
	MultF=cat["Composition"];
	cat["IdentityMorphismQ"][expr_]:=(Or@@Map[MatchQ[expr,#]&,cat["idmorphisms"]]);
	cat["GeneratorQ"][expr_]:=Or@@Map[MatchQ[expr,#]&,cat["generators"]];
	cat["AtomicQ"][expr_]:=(Or@@Join[
		Map[MatchQ[expr,#]&,cat["generators"]],
		Map[MatchQ[expr,#]&,cat["idmorphisms"]]
	]);
	cat["ElementaryMorphismQ"][expr_]:=Switch[expr,
	_?(AbstractAlgebra`GroundField`FieldElementQ[#,cat["groundfield"]]&),True,
	_?(cat["IdentityMorphismQ"]),True,
	_?(cat["GeneratorQ"]),True,
	_?(MatchQ[#,_MultF]||MatchQ[#,_Times]&),Module[
		{exprtab=expr}
	,
		exprtab[[0]]=List;
		Return[And@@Map[cat["ElementaryMorphismQ"],exprtab,1]]
	],
	_,False
	];
];

DefineLinearGroupoid[cat_]:=(
	cat["GroupoidGeneratorQ"][expr_]:=Or@@Map[MatchQ[expr,#]&,cat["groupoidgenerators"]];
	cat["generators"]=Join[cat["groupoidgenerators"],Map[Global`Inv,cat["groupoidgenerators"],1]];
	DefineCategory[cat];
	AbstractAlgebra`Localization`LocalizeCategory[cat];
);

DefineTensorCategory[cat_]:=(
	DefineCategory[cat];
	DefineTensorAlgebra[cat];
	AbstractAlgebra`TensorAlgebra`DefineTensorModuleMultiplication[cat["CircleTimes"],cat["Composition"]];
	AbstractAlgebra`TensorAlgebra`DefineMultiplicationMap[cat["\[Mu]"],cat["CircleTimes"],cat["Composition"],cat["groundfield"]];
	AbstractAlgebra`TensorAlgebra`DefinePermutation[cat["\[CapitalSigma]"],cat["\[Sigma]"],cat["CircleTimes"],cat["groundfield"]];
);

DefineLinearGroupoidWithTensorProduct[cat_]:=(
	DefineLinearGroupoid[cat];
	DefineTensorAlgebra[cat];
	AbstractAlgebra`TensorAlgebra`DefineTensorModuleMultiplication[cat["CircleTimes"],cat["Composition"]];
	AbstractAlgebra`TensorAlgebra`DefineMultiplicationMap[cat["\[Mu]"],cat["CircleTimes"],cat["Composition"],cat["groundfield"]];
	AbstractAlgebra`TensorAlgebra`DefinePermutation[cat["\[CapitalSigma]"],cat["\[Sigma]"],cat["CircleTimes"],cat["groundfield"]];
);

DefineSubcategory[subcat_,cat_]:=Module[
	{MultF}
,
	(*Inherrited Functions*)
	subcat["groundfield"]=cat["groundfield"];
	subcat["Composition"]=cat["Composition"];
	subcat["Id"]=cat["Id"];
	subcat["idmorphisms"]=Map[Subscript[subcat["Id"], #]&,subcat["objects"]];
	subcat["s"]=cat["s"];
	subcat["t"]=cat["t"];
	subcat["Deg"]=cat["Deg"];
	(*Boolean Functions*)
	subcat["IdentityMorphismQ"][expr_]:=(Or@@Map[MatchQ[expr,#]&,subcat["idmorphisms"]]);
	subcat["GeneratorQ"][expr_]:=Or@@Map[MatchQ[expr,#]&,subcat["generators"]];
	subcat["AtomicQ"][expr_]:=(Or@@Join[
		Map[MatchQ[expr,#]&,subcat["generators"]],
		Map[MatchQ[expr,#]&,subcat["idmorphisms"]]
	]);
	MultF=cat["Composition"];
	subcat["ElementaryMorphismQ"][expr_]:=Switch[expr,
	_?(AbstractAlgebra`GroundField`FieldElementQ[#,subcat["groundfield"]]&),True,
	_?(subcat["IdentityMorphismQ"]),True,
	_?(subcat["GeneratorQ"]),True,
	_?(MatchQ[#,_MultF]||MatchQ[#,_Times]&),Module[
		{exprtab=expr}
	,
		exprtab[[0]]=List;
		Return[And@@Map[cat["ElementaryMorphismQ"],exprtab,1]]
	],
	_,False
	];
];

(*Display graph with generators*)
DisplayGenerators[cat_,options_]:=Module[
	{edgeslist}
,
	edgeslist=Sort[Map[Labeled[Style[DirectedEdge[cat["s"][#],cat["t"][#]],Dashed,Red],#]&,cat["generators"]]];
	Print[Graph[edgeslist,options]];
];
DisplayGenerators[cat_]:=DisplayGenerators[cat,VertexLabels->"Name"];

DisplayGroupoidGenerators[cat_,options_]:=Module[
	{edgeslist}
,
	edgeslist=Sort[Map[Labeled[Style[DirectedEdge[cat["s"][#],cat["t"][#]],Dashed,Red],#]&,cat["groupoidgenerators"]]];
	Print[Graph[edgeslist,options]];
];
DisplayGroupGenerators[cat_]:=DisplayGroupGenerators[cat,VertexLabels->"Name"];

End[]

Begin["`Localization`"]

Inv:=Global`Inv;

LocalizeAux[algebra_,NonCommutativeMultiply_]:=(
	Inv[x_?(AbstractAlgebra`GroundField`FieldElementQ[#,algebra["groundfield"]]&)]:=1/x;
	Inv[x_Times]:=Module[
		{comm,ncm}
	,
		{comm,ncm}=AbstractAlgebra`GroundField`FactorFieldOut[x,algebra["groundfield"]];
		Return[1/comm Inv[ncm]];
	];
	Inv[Inv[a_]]:=a;
	Inv[NonCommutativeMultiply[a_,b__]]:=NonCommutativeMultiply[Inv[NonCommutativeMultiply[b]],Inv[a]];
);

LocalizeAlgebra[algebra_,NonCommutativeMultiply_]:=(
	LocalizeAux[algebra,NonCommutativeMultiply];
	NonCommutativeMultiply[a___,Inv[b_],b_,c___]:=NonCommutativeMultiply[a,c];
	NonCommutativeMultiply[a___,b_,Inv[b_],c___]:=NonCommutativeMultiply[a,c];
);

LocalizeAlgebra[algebra_]:=LocalizeAlgebra[algebra,algebra["NonCommutativeMultiply"]];

LocalizeCategory[cat_]:=With[
	{CompositionF=cat["Composition"]}
,
	LocalizeAux[cat,CompositionF];
	CompositionF[a___,Inv[b_],b_,c___]:=CompositionF[a,Subscript[cat["Id"], cat["s"][b]],c];
	CompositionF[a___,b_,Inv[b_],c___]:=CompositionF[a,Subscript[cat["Id"], cat["t"][b]],c];	
];

End[]

Begin["`MatrixOperations`"]

NCDot[A_,B_]:=Inner[NonCommutativeMultiply,A,B,Plus];

NCMatrixPow[A_,k_]:=Switch[k,
	1, A,
	_?(IntegerQ[#]&&(#>1)&),NCDot[NCMatrixPow[A,k-1],A],
	_,
		Print["Unexpected Power in NCMatrixPow ",k];
		Return[Indeterminate];
];

End[]

Begin["`InnerProduct`"]

debugAll=False;
silent=False;

RulesInnerProduct[rules1_,rules2_]:=Module[
	{ans=0,i,j}
,
	For[i=1,i<=Length[rules1],i++,
		For[j=1,j<=Length[rules2],j++,
			If[rules1[[i,1]]===rules2[[j,1]],ans=ans+rules1[[i,2]]rules2[[j,2]]];
		];
	];
	Return[ans];
];

MInnerProduct[expr1_,expr2_,groundfield_]:=MInnerProduct[expr1,expr2,groundfield]=RulesInnerProduct[
	AbstractAlgebra`General`MRules[expr1,groundfield],AbstractAlgebra`General`MRules[expr2,groundfield]
];

(*In the function below xtab is asssumed to be pairwise orthogonal*)
OrthogonalPart[xtab_,x_,groundfield_]:=Module[
	{ctab}
,
	If[debugAll,Print["Entering OrthogonalPart ",xtab]];
	ctab=Map[(MInnerProduct[#,x,groundfield]/MInnerProduct[#,#,groundfield])&,xtab];
	Return[x-Sum[ctab[[i]]xtab[[i]],{i,1,Length[xtab]}]];
];

OrthogonalizeTab[xtab_,groundfield_]:=Module[
	{ans={},i,diff}
,
	For[i=1,i<=Length[xtab],i++,
		diff=AbstractAlgebra`General`NCCollect[OrthogonalPart[ans,xtab[[i]],groundfield],groundfield,Factor];
		If[diff=!=0,
			AppendTo[ans,diff]
		,
			If[!silent,
				Print[xtab[[i]]," is not independent"];
			];
		];
	];
	Return[ans];
];

DefineAssociativeBasis[algebra_,NonCommutativeMultiply_]:=(
	algebra["basis"][0]={algebra["Id"]};
	algebra["basis"][n_Integer]:=(algebra["basis"][n]=Module[
		{expr,i,j,ans=algebra["basis"][n-1]}
	,
		For[i=1,i<=Length[algebra["basis"][n-1]],i++,
			For[j=1,j<=Length[algebra["generators"]],j++,
				expr=Expand[OrthogonalPart[ans,NonCommutativeMultiply[algebra["basis"][n-1][[i]],algebra["generators"][[j]]],algebra["groundfield"]]];
				If[expr=!=0,AppendTo[ans,expr]];
			];
		];
		Return[ans];
	])/;n>0;
);

DefineAssociativeBasis[algebra_]:=DefineAssociativeBasis[algebra,algebra["NonCommutativeMultiply"]];

DefineFreeMorphismBasis[cat_,lowerdegflag_]:=(
	cat["basis"][0]=cat["idmorphisms"];
	cat["basis"][n_]:=cat["basis"][n]=Module[
		{i,j,ans}
	,
		If[!(IntegerQ[n]&&n>0),Return[Indeterminate]];
		If[lowerdegflag,
			ans=cat["basis"][n-1]
		,
			ans={}
		];
		For[i=1,i<=Length[cat["basis"][n-1]],i++,
			For[j=1,j<=Length[cat["generators"]],j++,
				If[cat["s"][cat["basis"][n-1][[i]]]===cat["t"][cat["generators"][[j]]],
					AppendTo[ans,cat["Composition"][cat["basis"][n-1][[i]],cat["generators"][[j]]]];
				];
			];
		];
		Return[DeleteDuplicates[ans]];
	];
);

DefineFreeMorphismBasis[cat_]:=DefineFreeMorphismBasis[cat,True];

End[]

Begin["`Graded`"]

DefineGraded[algebra_]:=Module[
	{}
,
	If[!ValueQ[algebra["GradingMultF"],Method->"TrialEvaluation"],
		algebra["GradingMultF"]=Plus;
	];
	Switch[algebra["GradingMultF"],
		Plus,algebra["Deg"][Global`Inv[x_]]:=-algebra["Deg"][x],
		Times,algebra["Deg"][Global`Inv[x_]]:=1/algebra["Deg"][x],
		_,Print[""]
	];
	If[!ValueQ[algebra["GradedOperationQ"],Method->"TrialEvaluation"],
		algebra["Deg"][Times]=0;
		algebra["Deg"][Star]=0;
		algebra["Deg"][algebra["NonCommutativeMultiply"]]=0;
		algebra["Deg"][algebra["Composition"]]=0;
		With[
			{NonCommutativeMultiply=algebra["NonCommutativeMultiply"],Composition=algebra["Composition"]}
		,
			algebra["GradedOperationQ"]=Switch[#,
				_Times,True,
				_NonCommutativeMultiply, True,
				_Composition,True,
				_, False
			]&;
		];
	];
	algebra["Deg"][x_?NumericQ]:=algebra["GradingMultF"][];
	algebra["Deg"][x_?(algebra["GradedOperationQ"])]:=Module[
		{xtab=x,degtab,opdeg}
	,
		xtab[[0]]=List;
		degtab=Map[algebra["Deg"],xtab];
		AppendTo[degtab,algebra["Deg"][x[[0]]]];
		Return[algebra["GradingMultF"]@@degtab];
	];
	algebra["Deg"][x_Plus]:=Module[
		{xtab=x,degtab}
	,
		xtab[[0]]=List;
		degtab=Map[algebra["Deg"],xtab];
		If[Equal@@degtab,
			Return[degtab[[1]]]
		,
			Print["Failure in Deg, element ",x," is not homogeneous"];
			Return[Indeterminate];
		]
	];
	algebra["GetHomogeneousDecomposition"][expr_]:=Module[
		{rules,degtab={},deg,HomogeneousF,i}
	,
		rules=AbstractAlgebra`General`Rules[expr,algebra["groundfield"]];
		For[i=1,i<=Length[rules],i++,
			deg=algebra["Deg"][rules[[i,1]]];
			If[Position[degtab,deg,1]=={},
				AppendTo[degtab,deg];
				HomogeneousF[deg]=rules[[i,2]]rules[[i,1]]
			,
				HomogeneousF[deg]=HomogeneousF[deg]+rules[[i,2]]rules[[i,1]]
			];
		];
		Return[{degtab,HomogeneousF}];
	];
	algebra["HomogeneousQ"][expr_]:=(Length[algebra["GetHomogeneousDecomposition"][expr][[1]]]==1);
];

(*SuperMultiplication of Subscript[Z, 2] graded modules*)
DefineSuperTensorModuleMultiplication[algebra_,CircleTimes_,NonCommutativeMultiply_]:=(
	NonCommutativeMultiply[x___,y_CircleTimes,z_CircleTimes,w___]:=Module[
		{yz,ytab=y,ztab=z,ydeg,zdeg,sign=1,i}
	,
		ytab[[0]]=List;
		ztab[[0]]=List;
		If[Length[ytab]!=Length[ztab],
			Print["Unexpected Input in Super Tensor Bimodule Multiplication ",List[x,y,z,w]];
		];
		yz=Table[ytab[[i]]**ztab[[i]],{i,1,Length[ytab]}];
		(*Determining Sign*)
		ydeg=Map[algebra["Deg"],ytab];
		zdeg=Map[algebra["Deg"],ztab];
		For[i=1,i<=Length[ztab],i++,
			sign*=(-1)^(zdeg[[i]]Total[Drop[ydeg,i]]);
		];
		Return[sign x**(CircleTimes@@yz)**w];
	];
);

End[]

Begin["`Filtered`"]

DefineFiltration[algebra_]:=Module[
	{}
,
	If[!ValueQ[algebra["GradingMultF"],Method->"TrialEvaluation"],
		algebra["GradingMultF"]=Plus;
	];
	If[!ValueQ[algebra["GradedOperationQ"],Method->"TrialEvaluation"],
		algebra["Deg"][Times]=0;
		algebra["Deg"][Star]=0;
		With[
			{NonCommutativeMultiply=algebra["NonCommutativeMultiply"]}
		,
			algebra["GradedOperationQ"]=Switch[#,
				_Times,True,
				_NonCommutativeMultiply, True,
				_, False
			]&;
		];
	];
	With[
		{NonCommutativeMultiply=algebra["NonCommutativeMultiply"]}
	,
		If[!ValueQ[algebra["Deg"][NonCommutativeMultiply],Method->"TrialEvaluation"],
			algebra["Deg"][NonCommutativeMultiply]=algebra["GradingMultF"]@@{};
		];
	];
	algebra["Deg"][algebra["Id"]]=algebra["GradingMultF"]@@{};
	algebra["Deg"][x_?NumericQ]:=algebra["GradingMultF"][];
	algebra["Deg"][x_?(algebra["GradedOperationQ"])]:=Module[
		{xtab=x,degtab,opdeg}
	,
		xtab[[0]]=List;
		degtab=Map[algebra["Deg"],xtab];
		AppendTo[degtab,algebra["Deg"][x[[0]]]];
		Return[algebra["GradingMultF"]@@degtab];
	];
	algebra["Deg"][x_Plus]:=Module[
		{xtab=x,degtab}
	,
		xtab[[0]]=List;
		degtab=Map[algebra["Deg"],xtab];
		Return[Max@@degtab];
	];
	algebra["Deg"][x_Power]:=x[[2]]algebra["Deg"][x[[1]]];
];

DefineStrictFilteredSpan[algebra_,substN_]:=(
	algebra["fspan"][deg_]:={}/;(deg<0)||Or@@Map[#<0&,deg];
	algebra["fspan"][deg_]:={algebra["Id"]}/;(deg==0)||And@@Map[#==0&,deg];
	algebra["fspan"][deg_]:=algebra["fspan"][deg]=Module[
		{ans={},i,j,n}
	,
		For[i=1,i<=Length[algebra["generators"]],i++,
			ans=Join[ans,Map[algebra["NonCommutativeMultiply"][algebra["generators"][[i]],#]&,algebra["fspan"][deg-algebra["Deg"][algebra["generators"][[i]]]]]];
		];
		Switch[algebra["Deg"][algebra["generators"][[1]]],
		_?NumericQ,
			ans=Join[ans,algebra["fspan"][deg-1]],
		_List,
			n=Length[algebra["Deg"][algebra["generators"][[1]]]];
			ans=Join[ans,Flatten[Table[algebra["fspan"][deg-Table[KroneckerDelta[i,j],{j,1,n}]],{i,1,n}]]],
		_,
			Print["Unexpected type of degree, ",algebra["Deg"][algebra["generators"][[1]]]];
			Return[Indeterminate];
		];
		ans=DeleteDuplicates[Map[AbstractAlgebra`General`NCCollect[#,algebra["groundfield"],Factor]&,ans]];
		Return[ans];
	];
	algebra["gspan"][deg_]:=algebra["gspan"][deg]=Module[
		{n,ans}
	,
		Switch[algebra["Deg"][algebra["generators"][[1]]],
		_?NumericQ,
			ans=Complement[algebra["fspan"][deg],algebra["fspan"][deg-1]],
		_List,
			n=Length[algebra["Deg"][algebra["generators"][[1]]]];
			ans=Complement[algebra["fspan"][deg],Flatten[Table[algebra["fspan"][deg-Table[KroneckerDelta[i,j],{j,1,n}]],{i,1,n}]]],
		_,
			Print["Unexpected type of degree, ",algebra["Deg"][algebra["generators"][[1]]]];
			Return[Indeterminate];
		];
		Return[ans];
	];
	algebra["BasisCoefficients"][basis_,expr_,c_]:=Module[
		{diff,rules,lhs,M,subst0,b,sol}
		,
		diff=expr-Sum[Subscript[c, i]basis[[i]],{i,1,Length[basis]}];
		rules=AbstractAlgebra`General`Rules[diff,algebra["groundfield"]];
		lhs=Map[#[[2]]&,rules];
		M=SparseArray[Table[Coefficient[lhs[[i]],Subscript[c, j]],{i,1,Length[lhs]},{j,1,Length[basis]}]];
		subst0=Table[Subscript[c, i]->0,{i,1,Length[basis]}];
		b=-lhs/.subst0;
		sol=LinearSolve[M,b];
		If[!ListQ[sol],Return[Indeterminate]];
		Return[sol];
	];
	algebra["SpannedQ"][basis_,expr_,c_]:=(algebra["BasisCoefficients"][basis,expr,c]=!=Indeterminate);
	(*Basis works only for algebras graded by single nonnegative integer so far.
	Word problem must be solved and implemented in algebra["NonCommutativeMultiply"]*)
	algebra["fbasis"][deg_]:={}/;(deg<0);
	algebra["fbasis"][deg_]:={algebra["Id"]}/;(deg==0);
	algebra["gbasis"][deg_]:=algebra["gbasis"][deg]=Select[algebra["fbasis"][deg],algebra["Deg"][#]==deg&];
	algebra["fbasis"][deg_]:=algebra["fbasis"][deg]=Module[
		{ans,i,expr,cofactors,candidates,j}
	,
		If[Position[algebra["groundfield"]["generators"],algebra["c"]]=={},
			AppendTo[algebra["groundfield"]["generators"],Subscript[algebra["c"], __]];
		];
		ans=algebra["fbasis"][deg-1];
		For[i=1,i<=Length[algebra["generators"]],i++,
			cofactors=algebra["gbasis"][deg-algebra["Deg"][algebra["generators"][[i]]]];
			candidates=Join[Map[algebra["NonCommutativeMultiply"][algebra["generators"][[i]],#]&,cofactors],
			Map[algebra["NonCommutativeMultiply"][#,algebra["generators"][[i]]]&,cofactors]];
			candidates=Map[AbstractAlgebra`General`NCCollect[#,algebra["groundfield"],Factor[#/.substN]&]&,candidates];
			For[j=1,j<=Length[candidates],j++,
				Switch[candidates[[j]],
					_Plus,Null,
					_Times,Null,
					_,If[!algebra["SpannedQ"][ans,candidates[[j]],algebra["c"]],AppendTo[ans,candidates[[j]]]];
				];
			];
		];
		Return[ans];
	];
);

DefineStrictFilteredSpan[algebra_]:=DefineStrictFilteredSpan[algebra,{}];

DefineStrictlyFiltered[algebra_]:=(
	AbstractAlgebra`FinitelyGenerated`DefineAssociativeAlgebra[algebra];
	DefineFiltration[algebra];
	DefineStrictFilteredSpan[algebra];
);

End[]

Begin["`Ideals`"]
(*Word problem in the underlying algebra must be solved and implemented in NonCommutativeMultiply,
Assuming the algebra is filtered with generators in strictly positive degrees*)
silent=False;
debug=False;
debugAll=False;

(*Gives arbitrary decomposition, when it exists*)
GetCoefficientsLinearSolve[basis_,expr_,groundfield_,c_]:=Module[
	{diff,rules,lhs,i,sol,ptemp,M,b,subst0}
,
	If[debug,ptemp=PrintTemporary["Calculating difference with generic expression, number of terms = ",Length[basis]]];
	If[Length[basis]==0&&AbstractAlgebra`General`NCCollect[expr,groundfield,Factor]=!=0,Return[Indeterminate]];
	diff=expr-Sum[Subscript[c, i]basis[[i,4]],{i,1,Length[basis]}];
	rules=AbstractAlgebra`General`Rules[diff,groundfield];
	lhs=Map[#[[2]]&,rules];
	If[debugAll,
		NotebookDelete[ptemp];
		ptemp=PrintTemporary["Solving equations for coefficients, # of equations=",Length[lhs]]
	];
	M=SparseArray[Table[Factor[Coefficient[lhs[[i]],Subscript[c, j]]],{i,1,Length[lhs]},{j,1,Length[basis]}]];
	subst0=Table[Subscript[c, i]->0,{i,1,Length[basis]}];
	b=-lhs/.subst0;
	sol=LinearSolve[M,b];
	If[debug,NotebookDelete[ptemp]];
	If[!ListQ[sol],Return[Indeterminate]];
	Return[sol];
];

(*Tests if decomposition exists*)
SpannedQ[basis_,expr_,groundfield_,c_]:=(GetCoefficientsLinearSolve[basis,expr,groundfield,c]=!=Indeterminate);

(*Gives decomposition with free remaining parameters*)
GetCoefficientsSolve[basis_,expr_,groundfield_,c_]:=Module[
	{diff,rules,eqs,sol}
,
	diff=expr-Sum[Subscript[c, i]basis[[i,4]],{i,1,Length[basis]}];
	rules=AbstractAlgebra`General`Rules[diff,groundfield];
	eqs=Map[#[[2]]==0&,rules];
	sol=Solve[eqs,Table[Subscript[c, i],{i,1,Length[basis]}]];
	If[Length[sol]==0,Return[Indeterminate]];
	Return[Table[Subscript[c, i],{i,1,Length[basis]}]/.sol[[1]]];
];

(*Compute cofactrors for generator, so that the sum of all three defrees equals to totdeg*)
PrincipalIdealSpanPairs[generator_,totdeg_,algebra_]:=Module[
	{ltab,rtab,coeffpairs={},i,j,degL}
,
	For[degL=totdeg-algebra["Deg"][generator],degL>=0,degL--,
		ltab=algebra["gbasis"][degL];
		rtab=algebra["gbasis"][totdeg-degL-algebra["Deg"][generator]];
		coeffpairs=Join[coeffpairs,Flatten[Outer[{#1,#2}&,ltab,rtab],1]];
	];
	Return[coeffpairs];
];

LeftPrincipalIdealSpanPairs[generator_,totdeg_,algebra_]:=Module[
	{ltab,rtab,coeffpairs={},i,j}
,
	ltab=algebra["gbasis"][totdeg-algebra["Deg"][generator]];
	rtab={algebra["Id"]};
	coeffpairs=Join[coeffpairs,Flatten[Outer[{#1,#2}&,ltab,rtab],1]];
	Return[coeffpairs];
];

RightPrincipalIdealSpanPairs[generator_,totdeg_,algebra_]:=Module[
	{ltab,rtab,coeffpairs={},i,j,degL}
,
	ltab={algebra["Id"]};
	rtab=algebra["gbasis"][totdeg-algebra["Deg"][generator]];
	coeffpairs=Join[coeffpairs,Flatten[Outer[{#1,#2}&,ltab,rtab],1]];
	Return[coeffpairs];
];

(*Degree is calculated by the top degree in expressions Rg_i L, not by the actual degree of the sum
In other words, ideal["basis"][deg] gives basis for the span of all sums Rg_iL with sum of the three degrees in each term not exceeding maxdeg
Format {L,i,R,Lg_iR}*)
DefineIdealBasis[ideal_,c_,substN_]:=Module[
	{algebra=ideal["algebra"],groundfield=ideal["algebra"]["groundfield"]}
,
	ideal["span"][deg_]:={}/;(deg<0)||Or@@Map[#<0&,deg];
	ideal["span"][deg_]:=ideal["span"][deg]=Module[
		{ans,i,j,coeffpairs,expr}
	,
		ans=ideal["span"][deg-1];
		For[i=1,i<=Length[ideal["generators"]],i++,
			Switch[ideal["type"],
			"TwoSided",coeffpairs=PrincipalIdealSpanPairs[ideal["generators"][[i]],deg,algebra],
			"Left",coeffpairs=LeftPrincipalIdealSpanPairs[ideal["generators"][[i]],deg,algebra],
			"Right",coeffpairs=LeftPrincipalIdealSpanPairs[ideal["generators"][[i]],deg,algebra],
			_,
				Print["Unexpected ideal type, ",ideal["type"]];
				Return[Indeterminate];
			];
			For[j=1,j<=Length[coeffpairs],j++,
				expr=ideal["algebra"]["NonCommutativeMultiply"][coeffpairs[[j,1]],ideal["generators"][[i]],coeffpairs[[j,2]]];
				expr=AbstractAlgebra`General`NCCollect[expr,groundfield];
				AppendTo[ans,{coeffpairs[[j,1]],i,coeffpairs[[j,2]],expr}]
			];
		];
		Return[ans];
	];
	(*Precalculating expressions*)
	ideal["PrecalculateProduct"][num_,coeffpair_]:=Module[
		{expr,ans}
	,
		expr=ideal["algebra"]["NonCommutativeMultiply"][coeffpair[[1]],ideal["generators"][[num]],coeffpair[[2]]];
		expr=AbstractAlgebra`General`NCCollect[expr,groundfield];
		Return[{coeffpair[[1]],num,coeffpair[[2]],expr}];
	];
	(*Selecting Candidates*)
	ideal["SelectCandidates"][basis_,coeffpairs_]:=Module[
		{ans,ansN,ptemp,j,redundancycounter=0,expr}
	,
		ans=basis;
		ansN=ans/.substN;
		If[debug,ptemp=PrintTemporary["Adding basis elements for ",ideal,", ",Dynamic[{j,Length[ans],redundancycounter}],"/",{Length[coeffpairs]}]];
		For[j=1,j<=Length[coeffpairs],j++,
			If[Global`interfacemode=="BRC"&&RandomInteger[30]==0,Print["{j,|ans|,redundancycounter}/{coeffpairs}=",{j,Length[ans],redundancycounter},"/",{Length[coeffpairs]}]];
			expr=coeffpairs[[j,4]];
			If[!SpannedQ[ansN,expr/.substN,groundfield,c],
				AppendTo[ans,coeffpairs[[j]]];
				AppendTo[ansN,coeffpairs[[j]]/.substN]
			,
				redundancycounter++
			];
		];
		ans=Drop[ans,Length[basis]];
		If[debug,
			NotebookDelete[ptemp];
		];
		Return[ans];
	];
	(*Coefficient candidates with a single generator*)
	ideal["principalselected"][deg_,num_]:=Module[
		{filename,candidates,ans}
	,
		(*Trying to load the answer*)
		If[ValueQ[ideal["cachedir"],Method->"TrialEvaluation"],
			filename=FileNameJoin[{ideal["cachedir"],"principal-candidates-"<>ToString[{deg,num}]<>".m"}];
			If[FileExistsQ[filename],Return[Import[filename]]];
		];
		(*Computing candidates*)
		Switch[ideal["type"],
		"TwoSided",
			candidates=PrincipalIdealSpanPairs[ideal["generators"][[num]],deg,algebra],
		"Left",
			candidates=LeftPrincipalIdealSpanPairs[ideal["generators"][[num]],deg,algebra],
		"Right",
			candidates=LeftPrincipalIdealSpanPairs[ideal["generators"][[num]],deg,algebra],
		_,
			Print["Unexpected ideal type, ",ideal["type"]];
			Return[Indeterminate];
		];
		candidates=Map[ideal["PrecalculateProduct"][num,#]&,candidates,1];
		ans=ideal["SelectCandidates"][ideal["basis"][deg-1],candidates];
		(*Saving the answer*)
		If[ValueQ[ideal["cachedir"],Method->"TrialEvaluation"],
			Export[filename,ans]
		];
		Return[ans];
	];
	(*Defining ideal basis which is computed recursively*)
	ideal["basis"][deg_]:={}/;(deg<0)||Or@@Map[#<0&,deg];
	ideal["basis"][deg_]:=ideal["basis"][deg]=Module[
		{ans,i,coeffpairs,filename}
	,
		(*Trying to load cached answer*)
		If[ValueQ[ideal["cachedir"],Method->"TrialEvaluation"],
			filename=FileNameJoin[{ideal["cachedir"],ToString[deg]<>".m"}];
			If[FileExistsQ[filename],
				Return[Import[filename]]
			];
		];
		(*loading candidates and selecting independent*)
		coeffpairs=Flatten[Table[ideal["principalselected"][deg,i],{i,1,Length[ideal["generators"]]}],1];
		If[debugAll,Print["coeffpairs=",coeffpairs]];
		ans=Join[ideal["basis"][deg-1],ideal["SelectCandidates"][ideal["basis"][deg-1],coeffpairs]];
		(*Saving cached answer*)
		If[ValueQ[ideal["cachedir"],Method->"TrialEvaluation"],Export[filename,ans]];
		Return[ans];
	];
	(*The following function presents elemtent of the ideal as expression in generators*)
	ideal["GetCoefficientsFull"][expr_,optionssubst_]:=Module[
		{deg,coeff,ans={},i,coeffN,spanningset,subst0,SpanN,options,SpanF,subst}
	,
		If[debugAll,Print["Starting ",ideal,"['GetCoefficientsFull'], options=",optionssubst]];
		options={"spanningset","useN","freeparameters","maxextradeg"};
		options=options/.optionssubst;
		options=options/.{"spanningset"->"basis","useN"->True,"freeparameters"->False,"maxextradeg"->5};(*default options*)
		SpanF[deg_]:=ideal[options[[1]]][deg];
		(*Using numeric solution to remove unnecessary coefficients if requested*)
		If[options[[2]],
			subst=substN
		,
			subst={}
		];
		If[debugAll,Print["subst=",subst]];
		SpanN[deg_]:=SpanN[deg]=ideal[options[[1]]][deg]/.subst;
		(*Finding the smallest degree with solution*)
		For[deg=algebra["Deg"][expr],deg<=algebra["Deg"][expr]+options[[4]],deg++,
			Print["deg=",deg];
			If[True,Print["deg=",deg,", SpanN[deg]=",Short[SpanN[deg]]]];
			If[options[[3]],
				coeffN=GetCoefficientsSolve[SpanN[deg],expr/.subst,groundfield,c]
			,
				coeffN=GetCoefficientsLinearSolve[SpanN[deg],expr/.subst,groundfield,c]
			];
			If[coeffN=!=Indeterminate,Break[]];
		];
		If[coeffN===Indeterminate,Return[Indeterminate]];
		If[debugAll,Print[coeffN]];
		If[options[[2]],
			spanningset={};
			For[i=1,i<=Length[SpanF[deg]],i++,
				If[coeffN[[i]]=!=0,AppendTo[spanningset,SpanF[deg][[i]]]];
			];
			If[debugAll,Print["Spanning set=",spanningset]]
			(*Reconstructing full formula with parameters*)
			If[options[[3]],
				coeff=GetCoefficientsSolve[spanningset,expr,groundfield,c]
			,
				coeff=GetCoefficientsLinearSolve[spanningset,expr,groundfield,c]
			];
			If[debugAll,Print[coeff]];
			If[coeff===Indeterminate,
				Print["Failed to reconstruct full formula in GetCoefficients after getting numeric solution."];
				Return[Indeterminate];
			]
		,
			(*If numeric substitution was never used, utilizing coefficients from the previous step*)
			spanningset=SpanN[deg];
			coeff=coeffN;
		];
		(*Removing elements from spanning set with identically zero coefficients*)
		For[i=1,i<=Length[coeff],i++,
			If[coeff[[i]]=!=0,
				AppendTo[ans,spanningset[[i]]->coeff[[i]]];
			];
		];
		Return[ans];
	];
	ideal["GetCoefficients"][expr_,optionssubst_]:=Module[
		{rules}
	,
		rules=ideal["GetCoefficientsFull"][expr,optionssubst];
		Return[Map[Take[#[[1]],3]->#[[2]]&,rules]];
	];
	ideal["GetCoefficients"][expr_]:=ideal["GetCoefficients"][expr,{}];
	ideal["BelongQ"][expr_]:=(ideal["GetCoefficients"][expr]=!=Indeterminate);
];

DefineIdealBasis[ideal_,c_]:=DefineIdealBasis[ideal,c,{}];

End[]

Begin["`NormalOrdering`"]

Inv:=Global`Inv;

ResolveProduct[A_,B_,rhs_,MultiplyF_]:=(
	MultiplyF[x___,A,B,y___]:=MultiplyF[x,rhs,y];
);
ResolveProduct[A_,B_,rhs_]:=ResolveProduct[A,B,rhs,NonCommutativeMultiply];

AssignCommutative[A_,B_,MultiplyF_]:=ResolveProduct[B,A,MultiplyF[A,B],MultiplyF];
AssignCommutative[A_,B_]:=AssignCommutative[A,B,NonCommutativeMultiply];

AssignCommutativeSubalgebra[Atab_,MultiplyF_]:=Module[
	{i,j}
,
	For[i=1,i<Length[Atab],i++,
		For[j=i+1,j<=Length[Atab],j++,
			AssignCommutative[Atab[[i]],Atab[[j]],MultiplyF];
			AssignCommutative[Atab[[i]],Inv[Atab[[j]]],MultiplyF];
			AssignCommutative[Inv[Atab[[i]]],Atab[[j]],MultiplyF];
			AssignCommutative[Inv[Atab[[i]]],Inv[Atab[[j]]],MultiplyF];
		];
	];
];
AssignCommutativeSubalgebra[Atab_]:=AssignCommutativeSubalgebra[Atab,NonCommutativeMultiply];

End[]

EndPackage[]

