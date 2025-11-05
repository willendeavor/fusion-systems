// Functions that generate fusion systems and candidate automisers, groups etc



intrinsic CentreTest(B::Grp,S::Grp, Essentials::SeqEnum,AutF::Assoc)->Bool
    {Tests if action on Z(S) by B and that induced by memebers of AutF is consistent};
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
    {Tests if action on Z(S) by B and that induced by members of A is consistent};
    ZS:= Centre(S);
    SubZ:= Subgroups(ZS);
    for zz in SubZ do 
        Z:= zz`subgroup; 
        if #Z eq 1 then 
            continue; 
        end if;
        ZB:=  AutYX(Normalizer(B,Z),Z);
        Orb, NN:=  AutOrbit(P,Z,A);
        ZA:= sub<Z`autogrp|Generators(NN)>;
        TT:={x in ZB: x in Generators(ZA)};
        if TT ne {true} then 
            return false; 
        end if; 
    end for;
    return true;
end intrinsic;



intrinsic AutFPCandidates(B::Grp,S::Grp,P::Grp,ProtoEssentials::SeqEnum,Cand::Assoc, FirstTime::BoolElt:Printing:=false)->Assoc
{determines possible automisers of possibly protoessential subgroups}

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
            MakeAutos(x);
        end if; 
    end for;
    return F;
end intrinsic;






intrinsic  GroupFusionSystem(G::Grp,T::Grp)->FusionSystem
    {Creates the fusion system on the p-subgroup S of G}
    p:= FactoredOrder(T)[1][1];
    ZZ:= Integers();
    B1:= Normalizer(G,T); T1:= Sylow(B1,p);
    require  T1 eq sub<G|T,Centralizer(T1,T)>:"system cannot be saturated";   
    Testers:= {Sylow(SL(2,p^2), p),Sylow(SL(2,p^3), p),Sylow(SL(2,p^4), p),Sylow(SL(2,p^5), p),
    Sylow(SL(2,p^6), p), Sylow(SU(3,p), p),Sylow(SU(3,p^2), p)};// Add more?
            



    B2, PhiB:= PCGroup(B1);

    SST:= [SubInvMap(PhiB,B1,x`subgroup):x in Subgroups(B2:OrderDividing:=#T)];
     
    SS:= [x:x in SST|IsSCentric(T,x)];

    EE:=[T];
    GrpEssentialAutos:=AssociativeArray(SS);
    GrpEssentialAutos[T]:=AutomiserGens(B1,T);

    for x in SS do 

    if x eq T then continue; end if;

    NTx:= Normalizer(T,x);
    Q:=NTx/x;
    QC:= IsQuaternionOrCyclic(Q);
        if QC eq false then 
                if #Q le p^6 then TesT:= false;
                   for SP in Testers do
                     if IsIsomorphic(Q,SP) then TesT := true; break; end if;
                    end for;
                 if TesT eq false  then continue; end if;
            end if;
        end if;  
        Nx:= Normalizer(G,x);
        
        if Index(Nx,NTx) mod p eq 0 then continue; end if;  
        kk := sub<G|Centralizer(G,x), x>;

        if QC eq false and #Factorisation(ZZ!(#Nx/#kk)) le 2 then continue; end if;


       ISPE:=IsStronglypEmbeddedMod(Nx,kk,p);
        if ISPE then 
        EE:= Append(EE,x);
     
        GrpEssentialAutos[x]:= AutomiserGens(Nx,x);
        
     
        end if; 
    end for; 
     
     
     

    B2, PhiB:= PCGroup(B1);
    EEPC:=[SubMap(PhiB,B2,x):x in EE];
    EEAA:=[];
    for i := 1 to #EEPC do
    Es:= EEPC[i];
    MakeAutos(Es);
    EEAA[i]:= sub<Es`autogrp|[Inverse(PhiB)*gamma*PhiB:gamma in GrpEssentialAutos[EE[i]]]>; 
    end for;

    F:=CreateFusionSystem(EEAA);
     
    F`grpsystem:=G;
    F`grppgrp:=T;
    F`saturated := true;
    return F;
end intrinsic



intrinsic  GroupFusionSystem(G::Grp, p::RngIntElt)->FusionSystem
    {Makes the group fusion system on the Sylow p-subgroup}
    T:= Sylow(G,p);F:= GroupFusionSystem(G,T);F`saturated:= true;

    return F;
end intrinsic;




 intrinsic FusionTower(F::FusionSystem,P::GrpPC, AFP::GrpAuto)-> SeqEnum
     {Determines the fusion systems on normalizer tower when possible}
     S:= F`group;
     B:= F`borel; 
     NBP:=Normalizer(B,P);
     L:=Random(Complements(NBP,Normalizer(S,P)));
     AFPS:=AutYX(NBP,P);
     
     
     require  {x in AFP: x in  Generators(AFPS)} eq {true}: "the system F isn't saturated"; 
     AFPS:= sub<AFP|Generators(AFPS)>;
     AFPp:= SubMap(P`autopermmap,P`autoperm, AFP);
     AFPSp:= SubMap(P`autopermmap,P`autoperm, AFPS);
     ASp:= SubMap(P`autopermmap,P`autoperm,AutYX(Normalizer(S,P), P));
     

     InnSp:=SubMap(S`autopermmap,S`autoperm,Inn(S));
     
    if not AFPSp eq Normalizer(AFPp,ASp) then print "construction not applicable"; return []; end if;

    Tower :=  NormalizerTower(S,P);
    FF:=[];

    for T in Tower do BT:= sub<B|L,T>; Autos:=[AutYX(BT,T),AFP]; 
    Append(~FF,CreateFusionSystem(Autos));
    end for;
    return FF;
 
end intrinsic;





// Procedure that obtains some protoessentials depending on whether S is max class or not
procedure MaxClassTest(S,S_centrics, ~ProtoEssentials)
    p:= FactoredOrder(S)[1][1]; 
    nn:= Valuation(#S,p);
    if IsMaximalClass(S) and #S ge p^5 then 
        LL:= LowerCentralSeries(S);  
        // T will be the set of protoessentials that are pearls and the two step centralisers of index p
        T:=[];
        // Calculate the two step centralisers C_S(Z_2(S)) and \gamma_1(S)
        C_1 := Centralizer(S, LL[2],LL[4]);
        C_2 := Centralizer(S, LL[nn-2]);
        Append(~T, C_1);
        if not C_1 eq C_2 then 
            Append(~T,C_2); 
        end if; 
        // By Grazian and Parker a pearl is not contained in C_1 or C_2 but does contain Z(S) or Z_2(S)
        T:= T cat [x:x in S_centrics| #x eq p^2 and LL[nn-1] subset x and not x subset C_1 and not x subset C_2] 
            cat 
            [x:x in S_centrics| #x eq p^3 and LL[nn-2] subset x and not x subset C_1 and not x subset C_2]; 
        TT:=[];
        // For each element of T check if it is radical
        for x in T do 
            if not IsRadical(S,x) then 
                continue x; 
            end if;
            Append(~TT,x);
        end for;         
        ProtoEssentials := TT;
    end if; 

            
    if not IsMaximalClass(S) or #S le p^4 then  
        for x in S_centrics do   
            if x eq S then 
                continue x; 
            end if; 
            if IsCyclic(x) then  
                continue x; 
            end if;
            if not IsRadical(S,x) then 
                continue x; 
            end if;
            Nx:=Normalizer(S,x);
            A:=AutYX(Nx,x);
            Ap:= SubMap(x`autopermmap,x`autoperm ,A);
            Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            P:= Index(Ap,Innerp);
            Frat:=FrattiniSubgroup(x);
            FQTest := Index(x,Frat) ge P^2;
            //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
            //The order of such faithful modules is at least $|\Out_S(x)|^2$.
            if not FQTest then 
                continue x; 
            end if; 
            SylTest, QC:=IsStronglypSylow(Ap/Innerp);
            //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
            //Here we check that the Sylow $p$-subgroup is compatible with this.
            if not SylTest then 
                continue x; 
            end if; 
            if not QC and IsSoluble(x`autoperm)  then   
                continue x; 
            end if; 
            ProtoEssentials:= Append(ProtoEssentials,x); 
        end for;
    end if;
end procedure;







intrinsic AllProtoEssentials(S::Grp:OpTriv:=false, pPerfect:= false, Printing:= false)-> SeqEnum
    {Makes all protosessentials up to automorphisms of S the parameters ask for  O_p(F)=1 and O^p(\F)= \F}
    ZZ:= Integers(); //Integer Ring
    p:= FactoredOrder(S)[1][1]; 
    nn:= Valuation(#S,p);
    //Here are automorphisms of S and centric subgroups of S
    S:= PCGroup(S);
    MakeAutos(S);
    InnS:=Inn(S);
    AutS:= S`autogrp;
    map:= S`autopermmap;
    AutSp:= S`autoperm;
    InnSp:= SubMap(map,AutSp, InnS);

    // Create a list of S-centric subgroups
    Sbar, bar:= S/Centre(S);
    TT:= Subgroups(Sbar);
    S_centrics:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
    if Printing eq true then 
        print "the group has", #S_centrics, "centric subgroups"; 
    end if;

    ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
    // If S has max class we can be more efficient obtaining protoessentials
    MaxClassTest(S,S_centrics, ~ProtoEssentials);
    if  #ProtoEssentials eq 0 then 
        return []; 
    end if; 


    ///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
    ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
    ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
     
      
    if OpTriv then 
        if CharSbgrpTest(ProtoEssentials,S) then 
            return []; 
        end if; 
    end if;

       
    if pPerfect then 
        H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
        if  H ne S then 
            return []; 
        end if; 
    end if;
       
    /////////////////////
    ///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials 
    ///////and check that they have strongly p-embedded subgroups.
    ///////////////////


    for i in [1..#ProtoEssentialAutClasses] do 
        P:= ProtoEssentialAutClasses[i];
        MakeAutos(P);
        AutP:=P`autogrp;
        mapP:= P`autopermmap;
        AutPp:= P`autoperm;
        InnP:=Inn(P);
        InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
        AutSP:=AutYX(Normalizer(S,P),P );
        AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;  
        Q:= AutSPp/InnPp;
        M:=SubnormalClosure(AutPp,AutSPp);
        Candidates :=[];
        pVal:=Valuation(#AutPp,p);
        NormVal:=Valuation(#AutSPp,p);
        QC:=IsQuaternionOrCyclic(Q); 
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
            APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
            for kk in [1..#AutPCandidates] do  
                GG:= AutPCandidates[kk];
                Sylow:=SylowSubgroup(GG,p);
                a,b:=IsConjugate(AutPp,Sylow,AutSPp);
                if a then 
                    Append(~APC,GG^b); 
                end if; 
            end for;
            AutPCandidates:= APC;
        end if;//QC
                
        if QC and IsCyclic(Q)  then
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p);
        end if;  
    
        if QC and not IsAbelian(Q) then  
        Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
                AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
        APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
        for kk in [1..#AutPCandidates] do  
                    GG:= AutPCandidates[kk];
                Sylow:=SylowSubgroup(GG,p);
                    a,b:=IsConjugate(AutPp,Sylow,AutSPp);
            if a then Append(~APC,GG^b); end if; 
        end for;
        AutPCandidates:= APC;
        end if;
            
        P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

            for GG in AutPCandidates do
            if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
                NGG:= Normalizer(AutPp,GG);  
                NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)| 
                                    GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
                    for GGs in NGGsubs do 
                        Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>); 
                    end for; 
            end for;//GG  
    end for;  // i in [1..ProtoEssentialAutClasses]  



    ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
    ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

    if Printing then 
        print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  
    end if;
    if Printing then 
        for x in ProtoEssentialAutClasses do  
            print "the protoessential aut class  representaive have ", #x`autF, "potential automorphism groups"; 
         end for; 
    end if;
    return ProtoEssentialAutClasses;
end intrinsic;



intrinsic AllFusionSystems(ordergrp::RngIntElt)-> SeqEnum
    {Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n}
     range:=[1..NumberOfSmallGroups(ordergrp)];
    SatFS:=[];
    for count in range do 
    print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
    S:= SmallGroup(ordergrp,count);
    if IsAbelian(S) eq false then
    SatFS := SatFS cat AllFusionSystems(S:SaveEach:=false);
    end if;
    end for;
    return SatFS;
end intrinsic;



intrinsic AllFusionSystems(ordergrp::RngIntElt, range::SeqEnum:Printing:=false)-> SeqEnum
    {Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n from small groups library in the asserted range}
      
    SatFS:=[];
    for count in range do 
    print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
    S:= SmallGroup(ordergrp,count);
    if IsAbelian(S) eq false then
    AA:=AllFusionSystems(S:Printing:=Printing,SaveEach:=false);
    if #AA ne 0 then 
     FileName:="F" cat IntegerToString(#S) cat "-" cat IntegerToString(count)cat "-" cat IntegerToString(range[1]) cat "-" cat IntegerToString(range[#range]);
                  SaveFS(FileName, AA);
                  end if; 

     
    end if;
    end for;
    return SatFS;
end intrinsic;







intrinsic AbelianPearls(S::Grp:fusion:=true)->SeqEnum
    {Returns all fusion systems with just abelian Pearls provide anu such exists}
    S:= PCGroup(S);

    require IsMaximalClass(S): "S does not have maximal class";
    p:= FactoredOrder(S)[1][1];
    ZZ:= Integers();
     
    L:= LowerCentralSeries(S);
    gamma1:= Centralizer(S,L[2],L[4]);
    Z2:= L[#L-2]; 
    SS:= Subgroups(S:OrderEqual:=p^2);
    PotPearls:= {x`subgroup: x in SS| Normalizer(S,x`subgroup) eq sub<S|Z2,x`subgroup> and Exponent(x`subgroup) eq p};
    if #PotPearls eq 0 then return[]; end if;  
    MakeAutos(S);
    AutS:= S`autogrp;
    AutSp:= S`autoperm;
    map:= S`autopermmap;
    pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
    BorelsandS:=[];
    if m lt p-1 then return[]; end if;
            
    PAut, tt:= PCGroup(AutSp); 
    H:=HallSubgroup(PAut,-p); 
    K:= [wx`subgroup:wx in Subgroups(H)|wx`order ge p-1];


    BCand:=[];
    for k:= 1 to #K do  
        K1:= K[k]; 
            for K2 in BCand do 
                if IsConjugate(PAut,K1,K2) then   continue k;   end if;
            end for; 
        Append(~BCand,K1); 
    end for;
    BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
    Z:= Centre(S);
    MakeAutos(Z);
     
    BCand:= [k: k in BCand|#sub<Z`autogrp|Generators(  SubInvMap(map, AutS,k))> eq p-1];





    for CC in BCand do
             f:=hom<CC->AutS|g:->Inverse(map) (g)>;
              C:= SubMap(f,AutS,CC);  
              B,phiB:=Holomorph(GrpFP,S, sub<AutS|C>); 
            T:= phiB(S);  
             B, theta := PCGroup(B); T:= theta(T);
            BB:=[B,T];
             for x in PotPearls do Append(~BB,SubMap(phiB*theta,T,x)); end for;
         Append(~BorelsandS,BB);
    end for;
            
            AllPearls:=[];
            
    for Bor in  BorelsandS  do
        B:= Bor[1];
        S:= Bor[2];
        L:= LowerCentralSeries(S);
        PotPearls:=[Bor[j]: j in [3..#Bor]];   

        PotPearls2:=[];

            for PP in PotPearls do 
                for PP1 in PotPearls2 do
                    if IsConjugate(B,PP,PP1) then continue PP; end if;
                end for;
                Append(~PotPearls2, PP); 
            end for;
        PotPearls:= PotPearls2;  

        Pearls:=[B];
        for PP in  PotPearls do 
            N:= Normalizer(B,PP); 
            
            MakeAutos(PP);
            AutN:= AutYX(N,PP);
            SL2:= SubInvMap(PP`autopermmap, PP`autogrp,DerivedSubgroup(PP`autoperm));
            AutSPP:= AutYX(Normalizer(S,PP),PP);
            D:=sub<PP`autogrp|AutN,SL2>;
             if #Normalizer(SubMap(PP`autopermmap, PP`autoperm,D), SubMap(PP`autopermmap, PP`autoperm,AutSPP)) eq #AutN then
             Append(~Pearls,PP); end if;
        
        end for;
        if #Pearls ne 1 then Append(~AllPearls,Pearls); end if;
    end for;


    FusSys:=[];
    AutomiserSequences:=[];
    for FS in AllPearls do
    B:= FS[1]; 
    S:= pCore(B,p);
    A1:= AutYX(B,S);
    AutSeq:=[A1];
        for ii in [2..#FS] do
            Pearl:= FS[ii];
            N:= Normalizer(FS[1],Pearl);
            A2:= AutYX(N,Pearl);
            SL2:= SubInvMap(Pearl`autopermmap,  Pearl`autogrp,DerivedSubgroup(Pearl`autoperm));
            Append(~AutSeq, sub<Pearl`autogrp| SL2,A2>);
        end for;
        Autos:= AutSeq;

    Append(~AutomiserSequences,AutSeq);
    if fusion then
        
        Bbar, bar:= B/Centre(S);
        subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
        subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
         
    bounds:=[8,6,6,6];
    primes:=[2,3,4,4]; 
    ///Puts the essentials in the standard order using group names.  
    //This will break if order of S is too big. Hence the else below
     
     
     
    if p in primes and #S le p^bounds[Index(primes,p)]  then  
    RO:=[IdentifyGroup( Group(x)):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos);
    else
    RO:=[#Group(x):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos); 
    end if; 
        
    F:= New(FusionSystem);
    F`prime:=p;
    F`group:= S;    
    F`borel:= B;
    F`subgroups:=[x:x in subsBS];
    F`essentialautos:= Autos;
    F`essentials := [];
    for x in Autos do
    Append(~F`essentials, Group(x)); end for;
    F`AutF:= AssociativeArray(F`subgroups);
    for x in F`essentials do 
    F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
    end for; 
        
        
        
        
    Append(~FusSys,F);
    end if;
    end for;
    if fusion then
    if #FusSys eq 0 then return []; end if;
    FusSys1:=[FusSys[1]];
    for x in FusSys do 
        for y in FusSys1 do
            if IsIsomorphic(x,y) then continue x; end if;
        end for;
        Append(~FusSys1,x); 
    end for;

    return FusSys;
    else return AutomiserSequences;
    end if;


end intrinsic;