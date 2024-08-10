(* ::Package:: *)

getmomentumrep5cev[checkfn_]:=Module[{x2c,motherfn},
x2c=checkfn@@(checkfn//getargument)//.backtomomentum[8]/.{P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"]}/.P[l_,pl_]->P[xkc[l],pl]/.q[l_,pl_]->q[xkc[l],pl]/.xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="CEVp"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc1_,xkc4_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getmomentumrep6cev[checkfn_]:=Module[{x2c,motherfn},
x2c=checkfn@@(checkfn//getargument)//.backtomomentum[8]/.{P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"]}/.P[l_,pl_]->P[xkc[l],pl]/.q[l_,pl_]->q[xkc[l],pl]/.xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="CEVp"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc1_,xkc4_,xkc5_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getmomentumrep7cev[checkfn_]:=Module[{x2c,motherfn},
x2c=checkfn@@(checkfn//getargument)//.backtomomentum[8]/.{P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"]}/.P[l_,pl_]->P[xkc[l],pl]/.q[l_,pl_]->q[xkc[l],pl]/.xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="CEVp"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc1_,xkc4_,xkc5_,xkc6_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getmomentumrep8cev[checkfn_]:=Module[{x2c,motherfn},
x2c=checkfn@@(checkfn//getargument)//.backtomomentum[8]/.{P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"]}/.P[l_,pl_]->P[xkc[l],pl]/.q[l_,pl_]->q[xkc[l],pl]/.xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="CEVp"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc1_,xkc4_,xkc5_,xkc6_,xkc7_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getMomentumRepCEV[pler_]:=Module[{lp},lp=Length[pler];Switch[lp,1,getmomentumrep5cev[pler],2,getmomentumrep6cev[pler],3,getmomentumrep7cev[pler],4,getmomentumrep8cev[pler],_,Print[f::boole="CEV not in the library ",pler]]]





getmomentumrep5[checkfn_]:=Module[{x2c,motherfn},x2c=checkfn@@(checkfn//getargumentpev)//.backtomomentum[6]/. P[l_,pl_]->P[xkc[l],pl]/. q[l_,pl_]->q[xkc[l],pl]/. xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="PEVup"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc3_,xkc4_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getmomentumrep6[checkfn_]:=Module[{x2c,motherfn},x2c=checkfn@@(checkfn//getargumentpev)//.backtomomentum[6]/. P[l_,pl_]->P[xkc[l],pl]/. q[l_,pl_]->q[xkc[l],pl]/. xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="PEVup"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc3_,xkc4_,xkc5_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


getmomentumrep7[checkfn_]:=Module[{x2c,motherfn},x2c=checkfn@@(checkfn//getargumentpev)//.backtomomentum[6]/. P[l_,pl_]->P[xkc[l],pl]/. q[l_,pl_]->q[xkc[l],pl]/. xkc[l_]:>ToExpression["xkc"<>ToString[l]];
motherfn="PEVup"<>StringDelete[ToString[axc@@(List@@checkfn)],"axc"]<>"[xkc3_,xkc4_,xkc5_,xkc6_]:="<>ToString[x2c//InputForm];
motherfn//ToExpression;]


Clear@P


getMomentumRepPEV[pler_]:=Module[{lp},lp=Length[pler];Switch[lp,3,getmomentumrep5[pler],4,getmomentumrep6[pler],5,getmomentumrep7[pler],_,Print[f::boole="PEV not in the library ",pler]]]


quickMinimalRepPEV[pler_]:=(pler@@(pler//getargumentpev));


quickMinimalRepCEV[pler_]:=(pler@@(pler//getargument));


ReggeFactorImpact[h1_,h2_,h3_,hn_,n_]:=If[MemberQ[{p},hn],(P[1,"-"] P[2,"+"])/(q[n-3,"\[Perpendicular]"]q[n-3,"\[Perpendicular]*"]) P[n,"\[Perpendicular]*"]/P[n,"\[Perpendicular]"]/.rl//getMinimalgn[#,n]&//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)//PowerExpand//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&),If[MemberQ[{m},hn],(P[1,"-"] P[2,"+"])/(q[n-3,"\[Perpendicular]"]q[n-3,"\[Perpendicular]*"]) P[n,"\[Perpendicular]"]/P[n,"\[Perpendicular]*"]/.rl//getMinimalgn[#,n]&//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)//PowerExpand//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)]]


getIMPc[p_,sn_,{h1_,h2_,h3_,hn_}]:=(Series[#1,{Subscript[X, sn-3],\[Infinity],0}]&)[(p//PowerExpand)/ReggeFactorImpact[h1,h2,h3,hn,sn]];


satMtoYuy[opq_]:=opq//ReplaceRepeated[#,{Spaa[Sp[x_],Sp[y_]]->ab[x,y],Spbb[x_,y_]->sb[x,y]}]&//ReplaceAll[#,sb[Sp[x4_],Sp[x3_]]->sb[x4,x3]]&//ReplaceAll[#,s[x__]:>sy[x]]&;


alllplusallminuslist[pl_]:=pl/.{PEVu[P,P][___]->0,PEVu[P,P,P][___]->0,PEVu[P,P,P,P][___]->0,PEVu[M,M][___]->0,PEVu[M,M,M][___]->0,MEVu[M,M,M,M][___]->0};


moveCToFirst[expression_]:=Module[{pos,newExpression},pos=Position[expression,_?(StringTake[ToString[#1],-1]=="c"&)];If[Length[pos]>0,newExpression=Prepend[DeleteCases[expression,expression[[pos[[1,1]]]]],expression[[pos[[1,1]]]]],newExpression=expression];newExpression]


moveCToFirstX[expr_]:=Module[{pos,newExpression},pos=Position[expr,_?(StringTake[ToString[#1],-1]=="c"&)];
newExpression=PEVu@@Flatten[Prepend[Extract[expr,Complement[List/@Range[4],pos]],Reverse[List@@expr[[pos//Flatten]]]]];
newExpression];


moveCToFirstXn[expr_,xn_]:=Module[{pos,newExpression},pos=Position[expr,_?(StringTake[ToString[#1],-1]=="c"&)];
newExpression=PEVu@@Flatten[Prepend[Extract[expr,Complement[List/@Range[xn],pos]],Reverse[List@@expr[[pos//Flatten]]]]];
newExpression];


ads=-1;
rl={ab[2,i_]/;i!=1->-I Sqrt[-P[2,"+"]/P[i,"+"]]P[i,"\[Perpendicular]"],ab[i_,2]/;i!=1->I Sqrt[-P[2,"+"]/P[i,"+"]]P[i,"\[Perpendicular]"],
sb[2,i_]/;i!=1->-I Sqrt[-P[2,"+"]/P[i,"+"]]P[i,"\[Perpendicular]*"]ads,sb[i_,2]/;i!=1->I Sqrt[-P[2,"+"]/P[i,"+"]]P[i,"\[Perpendicular]*"]ads,
ab[i_,1]/;i!=2->I Sqrt[-P[1,"-"]P[i,"+"]],ab[1,i_]/;i!=2->-I Sqrt[-P[1,"-"]P[i,"+"]],
sb[i_,1]/;i!=2->I Sqrt[-P[1,"-"]P[i,"+"]]ads,sb[1,i_]/;i!=2->-I Sqrt[-P[1,"-"]P[i,"+"]]ads,
ab[2,1]->-Sqrt[P[2,"+"]P[1,"-"]],ab[1,2]->Sqrt[P[2,"+"]P[1,"-"]],
sb[2,1]->Sqrt[P[2,"+"]P[1,"-"]],sb[1,2]->-Sqrt[P[2,"+"]P[1,"-"]],
ab[i_,j_]/;(i!=2&&j!=1&&i!=1&&j!=2)-> (Sqrt[P[j,"+"]/P[i,"+"]]P[i,"\[Perpendicular]"]- Sqrt[P[i,"+"]/P[j,"+"]]P[j,"\[Perpendicular]"]),
sb[j_,i_]/;(i!=2&&j!=1&&i!=1&&j!=2)-> (Sqrt[P[j,"+"]/P[i,"+"]]P[i,"\[Perpendicular]*"]- Sqrt[P[i,"+"]/P[j,"+"]]P[j,"\[Perpendicular]*"])};


addcc1[qcwe_,x_]:=qcwe//Map[ReplacePart[#,{x->#[[x]]/.{P->Pc,M->Mc,qP->qPc,qM->qMc}}]&,#]&;


rlu[n_]:={P[i_,"\[Perpendicular]"]/;3<i<n->q[i-3,"\[Perpendicular]"]/(1-Subscript[z, i-3]),P[i_,"\[Perpendicular]*"]/;3<i<n->q[i-3,"\[Perpendicular]*"]/(1-Subscript[zb, i-3]),
Subscript[z, n-3]->0,Subscript[zb, n-3]->0,
q[i_,"\[Perpendicular]"]/;1<i<=n-3->-Subscript[z, i-1] q[i-1,"\[Perpendicular]"]/(1-Subscript[z, i-1]),q[i_,"\[Perpendicular]*"]/;1<i<=n-3->-Subscript[zb, i-1] q[i-1,"\[Perpendicular]*"]/(1-Subscript[zb, i-1])
,P[i_,"+"]/;3<=i<=n-1->P[i+1,"+"]Subscript[X, i-2],P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"],P[n,"\[Perpendicular]*"]->q[n-3,"\[Perpendicular]*"],P[n,"\[Perpendicular]"]->q[n-3,"\[Perpendicular]"],
P[x5_,"-"]/;3<=x5<=n->(P[x5,"\[Perpendicular]"] P[x5,"\[Perpendicular]*"])/P[x5,"+"]};


rlualt[n_]:={P[i_,"\[Perpendicular]"]/;3<i<n->q[i-3,"\[Perpendicular]"]/(1-Subscript[z, i-3]),P[i_,"\[Perpendicular]*"]/;3<i<n->q[i-3,"\[Perpendicular]*"]/(1-Subscript[zb, i-3]),
Subscript[z, n-3]->0,Subscript[zb, n-3]->0,
q[i_,"\[Perpendicular]"]/;1<i<=n-3->-Subscript[z, i-1] q[i-1,"\[Perpendicular]"]/(1-Subscript[z, i-1]),q[i_,"\[Perpendicular]*"]/;1<i<=n-3->-Subscript[zb, i-1] q[i-1,"\[Perpendicular]*"]/(1-Subscript[zb, i-1])
,P[i_,"+"]/;3<i<=n->P[i-1,"+"]/Subscript[X, i-3],P[3,"\[Perpendicular]"]->-q[1,"\[Perpendicular]"],P[3,"\[Perpendicular]*"]->-q[1,"\[Perpendicular]*"],P[n,"\[Perpendicular]*"]->q[n-3,"\[Perpendicular]*"],P[n,"\[Perpendicular]"]->q[n-3,"\[Perpendicular]"],
P[x5_,"-"]/;3<=x5<=n->(P[x5,"\[Perpendicular]"] P[x5,"\[Perpendicular]*"])/P[x5,"+"]};


minimalvaraddednew[n_]:={P[i_,"+"]/;(3<=i<=n-1)->P[i+1,"+"]Subscript[X, i-2]};
minimalvaraddednewalt[n_]:=P[i_,"+"]/;3<i<=n->P[i-1,"+"]/Subscript[X, i-3];


p2lnewg[n_]:=Solve[Sum[P[i,"+"],{i,2,n}]==0//.minimalvaraddednew[n],P[2,"+"]]//Flatten
p1lnewg[n_]:=Solve[(P[1,"-"]+Sum[P[i,"-"],{i,3,n}]==0/.{P[z_,"-"]/;z!=1->(P[z,"\[Perpendicular]"]P[z,"\[Perpendicular]*"])/P[z,"+"]}//.minimalvaraddednew[n]),P[1,"-"]]//Flatten//ReplaceRepeated[#,rl]&//ReplaceRepeated[#,rlu[n]]&


getMinimalgn[x_,n_]:=x//.rl//.rlu[n]/.p2lnewg[n]/.p1lnewg[n](*//Map[(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&),#]&*)


getccs[cc_]:=Module[{input,getccss,getccssto,output},input=cc;
getccss=input//Cases[#,ss[__],Infinity]&//DeleteDuplicates;
getccssto=getccss//Map[ReplaceAll[#,ss[x___]:>(Table[If[i<j,ss[i,j],Nothing],{i,Cases[ss[x],_Integer,Infinity]},{j,Cases[ss[x],_Integer,Infinity]}]//Flatten//Total)]&,#]&;
output=cc/. Map[Rule[getccss[[#]],getccssto[[#]]]&,Range[Length@getccss]]//ReplaceAll[#,ss[i_,j_]:>-Subscript[ab,i,j] Subscript[sb,i,j]]&;Return[output];];



Tofun[p_]:=p/.{q[1,"\[Perpendicular]*"]->q1pb,q[1,"\[Perpendicular]"]->q1p,Subscript[z, 1]->z1,Subscript[zb, 1]->z1b,Subscript[z, 2]->z2,Subscript[zb, 2]->z2b};


Tofung[p_]:=p/.{q[1,"\[Perpendicular]*"]->q1pb,q[1,"\[Perpendicular]"]->q1p,Subscript[z, i_]:>ToExpression["z"<>ToString[i]],Subscript[zb, i_]:>ToExpression["z"<>ToString[i]<>"b"],Subscript[X, i_]:>ToExpression["X"<>ToString[i]]};


ToPp[p_]:=p//ReplaceAll[#,{P[1,"-"]->-Pp[1,"-"],P[2,"+"]->-Pp[2,"+"]}]&;


ToPpinv[p_]:=p//ReplaceAll[#,{P[1,"-"]->-Pp[1,"-"],P[2,"+"]->-Pp[2,"+"]}]&;


tosy[p_]:=p/.s[x__]:>sy[x]/.Sp[u_]->u/.(sy[x___]:>(Table[If[i<j,sy[i,j],Nothing],{i,{x}},{j,{x}}]//Flatten//Total))/.sy[i_,j_]->ab[i,j]sb[j,i]


ReggeFactorn[h1_,h2_,h3_,hn_,n_]:=If[MemberQ[{p},hn],(P[1,"-"] P[2,"+"])/(q[1,"\[Perpendicular]"]q[1,"\[Perpendicular]*"]q[n-3,"\[Perpendicular]"]q[n-3,"\[Perpendicular]*"]) P[n,"\[Perpendicular]*"]/P[n,"\[Perpendicular]"]/.rl//getMinimalgn[#,n]&//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)//PowerExpand//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&),If[MemberQ[{m},hn],(P[1,"-"] P[2,"+"])/(q[1,"\[Perpendicular]"]q[1,"\[Perpendicular]*"]q[n-3,"\[Perpendicular]"]q[n-3,"\[Perpendicular]*"]) P[n,"\[Perpendicular]"]/P[n,"\[Perpendicular]*"]/.rl//getMinimalgn[#,n]&//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)//PowerExpand//(Simplify[#,Assumptions->Subscript[X, _]>0&&P[n,"+"]>0&&P[1,"-"]<0&&P[2,"+"]<0]&)]]


getCEV[p_,sn_,{h1_,h2_,h3_,hn_}]:=p/ReggeFactorn[h1,h2,h3,hn,sn]/.Subscript[X, sn-3]->Subscript[X, 1]//Series[#,{Subscript[X, 1],\[Infinity],0}]&;


getCEVsw[p_,sn_,{h1_,h2_,h3_,hn_}]:=-1 p/ReggeFactorn[h1,h2,h3,hn,sn]/.Subscript[X, sn-3]->Subscript[X, 1]//Series[#,{Subscript[X, 1],\[Infinity],0}]&;


MinimalVarfromGGT[x_,n_]:=x//GGTtoSpinors//SpOpen//satMtoYuy//tosy//ReplaceAll[rl]//ReplaceAll[#,{P[1,"-"]->-Pp[1,"-"],P[2,"+"]->-Pp[2,"+"]}]&//PowerExpand//ReplaceAll[{(P[x4_,"\[Perpendicular]"] Sqrt[P[x5_,"+"]])/Sqrt[P[x4_,"+"]]-(Sqrt[P[x4_,"+"]] P[x5_,"\[Perpendicular]"])/Sqrt[P[x5_,"+"]]->(P[x4,"\[Perpendicular]"] P[x5,"+"]-P[x4,"+"] P[x5,"\[Perpendicular]"])/(Sqrt[P[x4,"+"]] Sqrt[P[x5,"+"]]),(P[x4_,"\[Perpendicular]*"] Sqrt[P[x5_,"+"]])/Sqrt[P[x4_,"+"]]-(Sqrt[P[x4_,"+"]] P[x5_,"\[Perpendicular]*"])/Sqrt[P[x5_,"+"]]->(P[x4,"\[Perpendicular]*"] P[x5,"+"]-P[x4,"+"] P[x5,"\[Perpendicular]*"])/(Sqrt[P[x4,"+"]] Sqrt[P[x5,"+"]])}]//Factor//ReplaceAll[{Pp[1,"-"] ->-P[1,"-"] ,Pp[2,"+"]->-P[2,"+"]  }]//getMinimalgn[#,n]&//Factor


GetMinimalVar[x_,n_]:=x//satMtoYuy//tosy//ReplaceAll[rl]//ReplaceAll[#,{P[1,"-"]->-Pp[1,"-"],P[2,"+"]->-Pp[2,"+"]}]&//PowerExpand//ReplaceAll[{(P[x4_,"\[Perpendicular]"] Sqrt[P[x5_,"+"]])/Sqrt[P[x4_,"+"]]-(Sqrt[P[x4_,"+"]] P[x5_,"\[Perpendicular]"])/Sqrt[P[x5_,"+"]]->(P[x4,"\[Perpendicular]"] P[x5,"+"]-P[x4,"+"] P[x5,"\[Perpendicular]"])/(Sqrt[P[x4,"+"]] Sqrt[P[x5,"+"]]),(P[x4_,"\[Perpendicular]*"] Sqrt[P[x5_,"+"]])/Sqrt[P[x4_,"+"]]-(Sqrt[P[x4_,"+"]] P[x5_,"\[Perpendicular]*"])/Sqrt[P[x5_,"+"]]->(P[x4,"\[Perpendicular]*"] P[x5,"+"]-P[x4,"+"] P[x5,"\[Perpendicular]*"])/(Sqrt[P[x4,"+"]] Sqrt[P[x5,"+"]])}]//Factor//ReplaceAll[{Pp[1,"-"] ->-P[1,"-"] ,Pp[2,"+"]->-P[2,"+"]  }]//getMinimalgn[#,n]&//Factor


Clear@backtomomentum


backtomomentum[n_]:={Subscript[X, i_]:>P[i+2,"+"]/P[i+3,"+"],Subscript[z, i_]->(P[3+i,"\[Perpendicular]"]-q[i,"\[Perpendicular]"])/P[3+i,"\[Perpendicular]"],q[i_,"\[Perpendicular]"]->-Sum[P[j+2,"\[Perpendicular]"],{j,1,i}],Subscript[zb, i_]->(P[3+i,"\[Perpendicular]*"]-q[i,"\[Perpendicular]*"])/P[3+i,"\[Perpendicular]*"],q[i_,"\[Perpendicular]*"]->-Sum[P[j+2,"\[Perpendicular]*"],{j,1,i}]}


nptx={Subscript[X, 2]->1.2 ,Subscript[X, 3]->1.32,Subscript[X, 4]->1.4,q[1,"\[Perpendicular]"]->1.5+1.4261911402732099` I,q[1,"\[Perpendicular]*"]->1.5` -1.4261911402732099` I,Subscript[z, 1]->1.386` +1.16829418456618872` I,Subscript[zb, 1]->1.386` -1.16829418456618872` I,Subscript[z, 2]->1.213456` +1.112934186192713848` I,Subscript[zb, 2]->1.213456` -1.112934186192713848` I,Subscript[z, 3]->1.878912` +1.7689139481684852` I,Subscript[zb, 3]->1.878912` -1.7689139481684852` I,Subscript[z, 4]->1.12346` +1.49334127119122674` I,Subscript[zb, 4]->1.12346` -1.49334127119122674` I};


nptxX1={Subscript[X, 1]->1.5 ,Subscript[X, 2]->1.2 ,Subscript[X, 3]->1.32,Subscript[X, 4]->1.4,q[1,"\[Perpendicular]"]->1.5+1.4261911402732099` I,q[1,"\[Perpendicular]*"]->1.5` -1.4261911402732099` I,Subscript[z, 1]->1.386` +1.16829418456618872` I,Subscript[zb, 1]->1.386` -1.16829418456618872` I,Subscript[z, 2]->1.213456` +1.112934186192713848` I,Subscript[zb, 2]->1.213456` -1.112934186192713848` I,Subscript[z, 3]->1.878912` +1.7689139481684852` I,Subscript[zb, 3]->1.878912` -1.7689139481684852` I,Subscript[z, 4]->1.12346` +1.49334127119122674` I,Subscript[zb, 4]->1.12346` -1.49334127119122674` I};


getmrkM[infn_,X2_]:=Module[{exf,nlc,nfres},
exf=infn//Tofn//Level[#,1]&;
nlc=exf//getmrkc[#,X2]&;
nfres=Total@Map[If[Abs[#]>1000,0,#]&,nlc];
nfres]


Tofn[qpl_]:=qpl/.{PEVuc->PEVu,CEVc->CEV}


getmrkX1[pl_,X2_]:=pl//Tofn//ReplaceAll[{X2->2^64}]//ReplaceAll[nptxX1]


getmrk[pl_,X2_]:=pl//Tofn//ReplaceAll[{X2->2^64}]//ReplaceAll[nptx]


getmrkAna[pl_,X2_]:=pl//Tofn//SeriesCoefficient[#,{X2,\[Infinity],0}]&//ReplaceAll[nptx]


getmrkc[pl_,X2_]:=pl//ReplaceAll[{X2->2^64}]//ReplaceAll[nptx]


getmrkx[pl_,X2_,nc_]:=pl//Tofn//#/X2^nc&//ReplaceAll[{X2->2^64}]//ReplaceAll[nptx]


getargumentpev[pl_]:=({Table[Subscript[X, cv],{cv,1,(Length@pl)-2}],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"],Table[{Subscript[z, cb],Subscript[zb, cb]},{cb,1,(Length@pl)-2}]}//Flatten)


getargument[pl_]:=({Table[Subscript[X, cv],{cv,2,Length@pl}],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"],Table[{Subscript[z, cb],Subscript[zb, cb]},{cb,1,Length@pl}]}//Flatten)


Soft[P][x3_,x4_,x5_]:=softp[x3,x4,x5]


Soft[M][x3_,x4_,x5_]:=softm[x3,x4,x5]


theconjugate[xac_]:=xac/.{P->M,M->P,Pc->Mc,Mc->Pc}


softList7={{Subscript[X, 3],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 2],Subscript[zb, 2],Subscript[z, 3],Subscript[zb, 3]},{Subscript[X, 2] Subscript[X, 3],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 1],Subscript[zb, 1],Subscript[z, 3],Subscript[zb, 3]},{Subscript[X, 2],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 1],Subscript[zb, 1],Subscript[z, 2],Subscript[zb, 2]}};


softRL7={{Subscript[X, 2]->\[Epsilon] Subscript[X, 2],Subscript[z, 1]->Subscript[z, 1]/\[Epsilon] ,Subscript[zb, 1]->Subscript[zb, 1]/\[Epsilon] },{Subscript[X, 2]-> Subscript[X, 2]/\[Epsilon],Subscript[z, 2]->Subscript[z, 2]/\[Epsilon] ,Subscript[zb, 2]->Subscript[zb, 2]/\[Epsilon] ,Subscript[X, 3]->\[Epsilon] Subscript[X, 3]},{Subscript[X, 3]-> Subscript[X, 3]/\[Epsilon],Subscript[z, 3]->Subscript[z, 3]/\[Epsilon] ,Subscript[zb, 3]->Subscript[zb, 3]/\[Epsilon] }};


softRL8={{Subscript[X, 2]->\[Epsilon] Subscript[X, 2],Subscript[z, 1]->Subscript[z, 1]/\[Epsilon] ,Subscript[zb, 1]->Subscript[zb, 1]/\[Epsilon] },{Subscript[X, 2]-> Subscript[X, 2]/\[Epsilon],Subscript[z, 2]->Subscript[z, 2]/\[Epsilon] ,Subscript[zb, 2]->Subscript[zb, 2]/\[Epsilon] ,Subscript[X, 3]->\[Epsilon] Subscript[X, 3]},{Subscript[X, 3]-> Subscript[X, 3]/\[Epsilon],Subscript[z, 3]->Subscript[z, 3]/\[Epsilon] ,Subscript[zb, 3]->Subscript[zb, 3]/\[Epsilon] ,Subscript[X, 4]->\[Epsilon] Subscript[X, 4]},{Subscript[X, 4]-> Subscript[X, 4]/\[Epsilon],Subscript[z, 4]->Subscript[z, 4]/\[Epsilon] ,Subscript[zb, 4]->Subscript[zb, 4]/\[Epsilon] }};


softList8={{Subscript[X, 3],Subscript[X, 4],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"],Subscript[z, 2],Subscript[zb, 2],Subscript[z, 3],Subscript[zb, 3],Subscript[z, 4],Subscript[zb, 4]},{Subscript[X, 2] Subscript[X, 3],Subscript[X, 4],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 1],Subscript[zb, 1],Subscript[z, 3],Subscript[zb, 3],Subscript[z, 4],Subscript[zb, 4]},{Subscript[X, 2],Subscript[X, 3] Subscript[X, 4],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 1],Subscript[zb, 1],Subscript[z, 2],Subscript[zb, 2],Subscript[z, 4],Subscript[zb, 4]},{Subscript[X, 2],Subscript[X, 3],q[1,"\[Perpendicular]"],q[1,"\[Perpendicular]*"] ,Subscript[z, 1],Subscript[zb, 1],Subscript[z, 2],Subscript[zb, 2],Subscript[z, 3],Subscript[zb, 3]}};


softRLall={{Subscript[X, 1]->\[Epsilon] Subscript[X, 1],Subscript[z, 1]->1-\[Epsilon]+\[Epsilon] Subscript[z, 1],Subscript[zb, 1]->1-\[Epsilon]+\[Epsilon] Subscript[zb, 1]},{Subscript[X, 2]->\[Epsilon] Subscript[X, 2],Subscript[z, 1]->Subscript[z, 1]/\[Epsilon] ,Subscript[zb, 1]->Subscript[zb, 1]/\[Epsilon] },{Subscript[X, 2]-> Subscript[X, 2]/\[Epsilon],Subscript[z, 2]->Subscript[z, 2]/\[Epsilon] ,Subscript[zb, 2]->Subscript[zb, 2]/\[Epsilon] ,Subscript[X, 3]->\[Epsilon] Subscript[X, 3]},{Subscript[X, 3]-> Subscript[X, 3]/\[Epsilon],Subscript[z, 3]->Subscript[z, 3]/\[Epsilon] ,Subscript[zb, 3]->Subscript[zb, 3]/\[Epsilon] ,Subscript[X, 4]->\[Epsilon] Subscript[X, 4]},{Subscript[X, 4]-> Subscript[X, 4]/\[Epsilon],Subscript[z, 4]->Subscript[z, 4]/\[Epsilon] ,Subscript[zb, 4]->Subscript[zb, 4]/\[Epsilon] }};


collinear[pl_,{x4_,x6_},{p4_,p6_}]:=pl//ReplaceAll[#,{P[p4,"+"]->x4 P["+"],P[p6,"+"]->x6  P["+"]}]&//ReplaceAll[k["+"]->0]//ReplaceAll[{k["+"]->-P^2/(2P["+"]),k["\[Perpendicular]"]->-Sqrt[x4 x6]P}]//ReplaceAll[#,{P[p4,"\[Perpendicular]"]->x4 P["\[Perpendicular]"]+k["\[Perpendicular]"],P[p6,"\[Perpendicular]"]->x6  P["\[Perpendicular]"]-k["\[Perpendicular]"],P[p4,"\[Perpendicular]*"]->x4 P["\[Perpendicular]*"]+k["\[Perpendicular]*"],P[p6,"\[Perpendicular]*"]->x6  P["\[Perpendicular]*"]-k["\[Perpendicular]*"]}]&


detectLeftRight[element_,list_]:=Module[{position},position=Position[list,element];
If[Length[position]==1,With[{pos=First[position][[1]]},{If[pos>1,list[[pos-1]],None],element,If[pos<Length[list],list[[pos+1]],None]}],"Element not found in the list."]]


toconjugate[plo_]:=plo/. {qMc->qPc,qPc->qMc,Mc->Pc,Pc->Mc,P->M,M->P,qP->qM,qM->qP}


getIMPcG[p_,sn_,{h1_,h2_,h3_,hn_}]:=(PowerExpand[p]/ReggeFactorImpact[h1,h2,h3,hn,sn]/. P[sn,"+"]->1/.Subscript[X, sn-3]->1/xinv//Factor//PowerExpand)/.xinv->0
