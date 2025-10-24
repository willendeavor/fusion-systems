// Functions that generate fusion systems and candidate automisers, groups etc



intrinsic CentreTest(B::Grp,S::Grp, Essentials::SeqEnum,AutF::Assoc)->Bool
    {Tests is action on Z(S) by B and that induced by memebers of AutF is consistent};
    Z:= Centre(S);
    ZB:=  AutYX(B,Z);
    ZA:= sub<Z`autogrp|>;
    for e in Essentials do 
    Orb, NN:=  AutOrbit(e,Z,AutF[e]);
    ZA := sub<Z`autogrp|ZA,Generators(NN)>;
    end for;
    TT:={x in ZB: x in Generators(ZA)};
    return TT eq {true};
end intrinsic;

///////////////////////////////

intrinsic CentreTest(B::Grp,S::Grp,P::Grp,A::GrpAuto)->Bool
    {Tests is action on Z(S) by B and that induced by members of A is consistent};
    ZS:= Centre(S);
    SubZ:= Subgroups(ZS);
    for zz in SubZ do 
        Z:= zz`subgroup; if #Z eq 1 then continue; end if;
        ZB:=  AutYX(Normalizer(B,Z),Z);
        Orb, NN:=  AutOrbit(P,Z,A);
        ZA:= sub<Z`autogrp|Generators(NN)>;
        TT:={x in ZB: x in Generators(ZA)};
        if TT ne {true} then return false; end if; 
    end for;
    return true;
end intrinsic;



intrinsic AutFPCandidates(B::Grp,S::Grp,P::Grp,ProtoEssentials::SeqEnum,Cand::Assoc, FirstTime::BoolElt:Printing:=false)->Assoc
{determines possible automisers of possibly protoessentail subgroups}

p:= FactoredOrder(S)[1][1];
ZZ:= Integers();
NSP:= Normalizer(S,P);

 ///////////////////////////////////////////////////////
 /////This checks if the automiser of N_S(P) comes from B.
 /////if it does, then this forms the basis of a check for consistency
 ////For this we require that N_S(P) doesn't have any morphisms 
 ///from essentail subgroups. I.e |N_S(P)| > |E| for all E essential.
  //////////////////////////////////////////////////////////
max:= Max({#ee:ee in ProtoEssentials});
maxenough := false;
if #NSP gt max then maxenough:= true; end if;
 
if #NSP eq max and  not exists(t){x:x in ProtoEssentials| IsConjugate(B,NSP,x)}  then maxenough:= true; end if;
 
 
//The next test  
 
 PC:= Core(S,P);
 if Index(NSP,P) eq p and Index(S,NSP) eq p and 
    Index(P,PC) eq p and IsCharacteristic(NSP,PC) then 
        if p ge 5 then maxenough:=true;  end if;
        if p in {2,3} and exists(x){x:x in ProtoEssentials| IsConjugate(B,NSP,x)} 
        then a,b:= IsConjugate(B, x,NSP);
        beta:= ConjtoHom(x,NSP,b); 
        alpha:= ConjtoHom(NSP,x,b^-1);
        Z:= Conjugates(S,P);
        if 
        forall{mm: mm in x`autF |  
                    exists{gamma: gamma in Generators(mm)|not SubMap( beta*gamma*alpha,NSP,P) in Z}} 
                    then maxenough:= true; 
        end  if;
        end if;
 end if;      
        
    
         
 

 

MakeAutos(P);
AutP:=P`autogrp;
mapP:= P`autopermmap;
AutPp:= P`autoperm;
InnP:=AutYX(P,P);
InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
AutSP:=AutYX(Normalizer(S,P),P );
AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;
AutBP:=AutYX(Normalizer(B,P),P );
AutBPp:=sub<P`autoperm|{mapP(g): g in Generators(AutBP)}>;
NormAutSPp:=Normalizer(AutPp,AutSPp);
 

Candidates :=[];
 

 
 ct:= 0;
for Ga in Cand[P] do ct:= ct+1;  
//if Printing then if ct mod 10 eq 1 then print "done (modulo 10)", ct, "of ", #Cand[P]; end if; end if;
    
    GG:=SubMap(mapP,AutPp,Ga);  
    NGSP:= Normalizer(GG,AutSPp);
    SubsNGSP := Subgroups(NGSP:OrderMultipleOf:= #AutSPp); 
    
    TGG:={};
    
    if FirstTime then
        if  maxenough  then vv, ww:= IsConjugate(NormAutSPp,NGSP,AutBPp); 
            if vv then TGG:= TGG join {GG^ww}; else continue Ga; end if;
            else flag:=false;
            for subNGSP in  SubsNGSP  do 
                sw:= subNGSP`subgroup;   
                vv, ww:= IsConjugate(NormAutSPp,sw,AutBPp); 
                if vv then  TGG:= TGG join {GG^ww}; flag := true; end if; 
            end for; 
            if flag eq false then  continue Ga; end if;
        end if;//maxenough
    NormAutBPp:=Normalizer(AutPp,AutBPp);
     
      
        for GG in TGG do  
          //This uses Sylow's Theorem 
          NGP:= Normalizer(GG,AutSPp);  
          GGa:=sub<AutP|{Inverse(mapP)(g):g in Generators(GG)}>;
          NGPa:=sub<AutP|{Inverse(mapP)(g):g in Generators(NGP)}>;  
           
          NormAutBPa:= sub<AutP|{Inverse(mapP)(g):g in Generators(NormAutBPp)}>;
          XX,YY:=AutFCore([S,P],[AutYX(B,S),sub<AutP|NGPa,NormAutBPa> ]);
          BBB:=SubMap(XX`autopermmap,XX`autoperm,AutYX(B,XX)); 
          SSS:=SubMap(XX`autopermmap,XX`autoperm,AutYX(S,XX));
          NGPap:=SubMap(XX`autopermmap,XX`autoperm,NGPa);
          NormAutBPXXa:= sub<XX`autogrp |{(Inverse(mapP)(alpha)): alpha in
            Generators(NormAutBPp)}>; 
          NormAutBPXXap:= SubMap(XX`autopermmap,XX`autoperm,NormAutBPXXa);
          Tran1:= Transversal(NormAutBPXXap,Normalizer(NormAutBPXXap,NGPap));
          
          if Printing then   print "Tran1 has ", #Tran1, "elements";  end if;
          ToB :={};
             for tr in Tran1 do 
                YY2:= sub<XX`autoperm|NGPap^tr,BBB>; 
                ToB:= ToB join {BBB eq Normalizer(YY2,SSS)}; 
                if true in ToB then   break tr; end if;
             end for; 
          if ToB eq {false} then continue GG; end if; 
           
          
          Transv:=Transversal(NormAutBPp,Normalizer(NormAutBPp,GG));  
          if Printing then   print "Transv has ", #Transv, "elements";  end if;

                for aa in Transv  do 
                    NGPxx:= NGP^aa;
                    NGPxxa:=sub<AutP|{Inverse(mapP)(alpha):alpha in Generators(NGPxx)}>;
                    YYY1:=SubMap(XX`autopermmap,XX`autoperm,sub<XX`autogrp|{w: w in Generators(NGPxxa)}>);
                    YYY:=sub<XX`autoperm|YYY1,BBB>; 
                    if  (Normalizer(YYY,SSS) eq BBB)  then 
                        NewSub:=sub<AutP|{Inverse(mapP)(gg^aa): gg in Generators(GG)}>; 
                        for xxx in Candidates do 
                            if xxx eq NewSub then continue aa; end if; 
                        end for;
                        Append(~Candidates,NewSub); 
                    end if;
                end for;//aa
           end for;//GG
           end if;

    
    if FirstTime eq false then   
        if  maxenough  then 
            if AutBPp subset GG  
            then  
            Append(~Candidates,Ga);  
             
            end if; 
        else 
            Append(~Candidates,Ga); 
          
        end if;
    end if;
    
end for;//Ga
  
if Printing then print  "In AutFPCand we find", #Candidates, "candidates";end if;

return  Candidates; 
end intrinsic;







intrinsic CreateFusionSystem(Autos::SeqEnum) -> FusionSystem
    {Creates the FusionSystem from automiser sequence. 
    The first term in always the group on which the fusion system is 
    erected. We make everything into a PCGrp }
     
    require forall{A:A in Autos|Type(A) eq GrpAuto}: 
    "Tuple entries not all automorphism groups"; 
    F:= New(FusionSystem);
      
    S1:= Group(Autos[1]);
    p:= FactoredOrder(S1)[1][1];
    F`prime:=p;


    bounds:=[8,6,6,6];
    primes:=[2,3,4,4];
    ///Puts the essentials in the standard order using group names.  
    //This will break if order of S is too big. Hence the else below
     
    if p in primes and #S1 le p^bounds[Index(primes,p)]  then  
    RO:=[IdentifyGroup( Group(x)):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos);
    else
    RO:=[#Group(x):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos); 
    end if; 
        
      
    InnS1:=AutYX(S1,S1);   
    AutS1:=S1`autogrp;
    map:=S1`autopermmap;
    AutSp:= S1`autoperm;
      
       
    //////////////////////////////////////////////////
    ///We now  make the Borel subgroup and make things into a PCgrp.
    ////////////////////////////////////////////////// 
    InnFp:=sub<AutSp|{map(g): g in Generators(InnS1)}>;
    AutFSp:=sub<AutSp|{map(g): g in Generators(Autos[1])}>;  
      C:=Random(Complements(AutFSp,InnFp));  
    C:=SubInvMap(map,AutS1,C); 
    if #C gt 1 then 
         Ba, phi1:= Holomorph(GrpFP,S1,C); 
         Sa:= sub<Ba|[phi1(x):x in Generators(S1)]>; 
         phi2:=iso<Sa->S1|[<phi1(S1.i),S1.i>: i in [1..#Generators(Sa)]]>; 
         L:= sub<Ba|{x: x in Generators(Ba)| not x in Sa}>;  
         theta, Bb:= CosetAction(Ba,L); B,thetaB:= PCGroup(Bb);
        phiB:= phi1*theta*thetaB; 
        S:= sub<B|[phiB(x):x in Setseq(Generators(S1))]>;
        InvphiB := Inverse(thetaB)*Inverse(theta)*phi2;
       
         else
         B:= S1; 
         B,phiB:= PCGroup(B); InvphiB := Inverse(phiB);
    end if;
    S:= phiB(S1); 
    F`group:= S;    
    F`borel:= B;  
      
      MakeAutos(S);
      F`essentialautos:= [];
       F`essentials:=[phiB(Group(Autos[i])):i in [1..#Autos]];
     for x in F`essentials do MakeAutos(x); end for;
        for ix in [1..#Autos] do
            x:= F`essentials[ix];  
       XX:=sub<x`autogrp|[InvphiB*w*phiB:w in Generators(Autos[ix])]>; 
        
        F`essentialautos:= Append( F`essentialautos,XX); 
        end for;
      
    ////////////////////////
    ////The essentials and essential autos have been assigned. 
    ////We treat S as an essential. 
    ////////////////////////

    ////////////////////////
    //////We now create all the subgroups of the fusion system up to B conjugacy 
    //////Perhaps this could be done later.
    //////////////////////
    subsBS:=Subgroups(B: OrderDividing:=#S);

    ////////////////////////
    //////Perhaps the algorithm doesn't select our essentials as representatives of 
    /////their B-conjugacy class. We correct this
    //////////////////////

    //
    F`subgroups:=[x`subgroup:x in subsBS];
    for ii := 1 to #F`essentials do
        X:= F`essentials[ii];
        if X in F`subgroups eq false then 
            for jj in [1..#F`subgroups] do
                w:= F`subgroups[jj];
                if IsConjugate(B,w , X) then   F`subgroups[jj]:= X; break jj; end if;
            end for;
        end if;
    end for;
    //////////////////////////////////////////
    ///////We initialise F`AutF and place in the automorphism of essentials 
    ///////////////////////////// 
    F`AutF:= AssociativeArray(F`subgroups);

    for x in F`essentials do 
       F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
    end for; 

    //We make all autos of S-centric subgroups. Perhaps this is a place we can save
    //memory
    for ii in [1..#F`subgroups] do 
    x:= F`subgroups[ii]; 
    if IsSCentric(S,x) then 
    MakeAutos(x);end if; end for;
     
    return F;
end intrinsic;
