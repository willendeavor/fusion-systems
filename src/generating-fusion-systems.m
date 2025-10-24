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













intrinsic AllProtoEssentials(S::Grp:OpTriv:=false, pPerfect:= false,Printing:= false)-> SeqEnum
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
    Sbar, bar:= S/Centre(S);
    TT:= Subgroups(Sbar);
    SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
    if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
     


    ///////////////////////////////////
    ///We precalculate certain properties of S. The objective here is to eliminate
    ///most  p-groups S before we calculate and construct the possible Borel subgroups 
    ///associated with S.
    ///We do this first as there may be many  of Borel subgroups which we don't need 
    ///to calculate in some circumstances.
    /////////////////////////////////////

    ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
    //
    if IsMaximalClass(S) and #S ge p^5 then 
        LL:= LowerCentralSeries(S);  
        T:=[];
         Append(~T,Centralizer(S, LL[2],LL[4]));
         C:= Centralizer(S, LL[nn-2]);
         if C in T eq false then 
            Append(~T,C); end if; 
         T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
         cat 
         [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
          TT:=[];
         for x in T do 
                Nx:=Normalizer(S,x);
                A:=AutYX(Nx,x);
                Ap:= SubMap(x`autopermmap,x`autoperm ,A);
                Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
                RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
                if not RadTest then continue x; end if;
                Append(~TT,x);
         end for;         
           ProtoEssentials:=   TT;
    end if; 
            
    if IsMaximalClass(S) eq false  or #S le p^4 then  
    for x in SS do   
        if x eq S then continue x; end if; 
        if IsCyclic(x) then  continue x; end if;
        Nx:=Normalizer(S,x);
        A:=AutYX(Nx,x);
        Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        Inner:= Inn(x);
        Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
        RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
        if not RadTest then continue x; end if;
        P:= Index(Ap,Innerp);
        Frat:=FrattiniSubgroup(x);
        FQTest := Index(x,Frat) ge P^2;
            //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
            //The order of such faithful modules is at least $|\Out_S(x)|^2$.
        if FQTest eq false then continue x; end if; 
        SylTest, QC:=IsStronglypSylow(Ap/Innerp);print "here";
            //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
            //Here we check that the Sylow $p$-subgroup is compatible with this.
        if SylTest eq false   then continue x; end if; 
        if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
        ProtoEssentials:= Append(ProtoEssentials,x); 
    end for;
    end if;
    ////////////////////////////////
    ///We need some subgroups in ProtoEssentials;
    ///////////////////////////////////
     
    if  #ProtoEssentials eq 0 then return []; end if; 


    ///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
    ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
    ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
     
      
    if OpTriv then if CharSbgrpTest(ProtoEssentials,S) eq true then return []; end if; end if;
       
     
        ///This test takes Q as the intersection of all the members of the members 
        //of ProtoEssentials and checks if any of them are characteristic in all members 
        //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

       
    if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
    if  H ne S then return []; end if; end if;
     //This tests is with this set of protoessentials that O^p(\F) <F. 
       
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
                if a then Append(~APC,GG^b); end if; 
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

















intrinsic AllFusionSystems(S::Grp:SaveEach:=false,Printing:=false,OutFSOrders:=[],OpTriv:=true,pPerfect:= true)-> SeqEnum
    {Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F}
     
     
     
    FNumber:=0; //This is to help when saving fusion systems
    ZZ:= Integers(); //Integer Ring
    FF:=[]; //We will put the possible systems in here  

    p:= FactoredOrder(S)[1][1]; 
     nn:= Valuation(#S,p);



    //Use that we know fusion systems with an abelian subgroup

    if IsAbelian(S) then return FF; end if;

    ///Lemma~7.1 shows that $S:Z(S) \gt p^2 or |S|\le p^3

    if Index(S,Centre(S)) le p^2 and #S ge p^4  then return FF; end if; 
     
     

    //Here are automorphisms of S and centric subgroups of S
    S:= PCGroup(S);

    MakeAutos(S);
    InnS:=Inn(S);
    AutS:= S`autogrp;
    map:= S`autopermmap;
    AutSp:= S`autoperm;
    InnSp:= SubMap(map,AutSp, InnS);

    //We use Cor 6.2 from ANTONIO Diaz, ADAM GLESSER, NADIA MAZZA, AND SEJONG PARK
    if p ge 5 and #FactoredOrder(S`autogrp) eq 1 then return []; end if; 


    Sbar, bar:= S/Centre(S);
    TT:= Subgroups(Sbar);
    SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
    if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
     
     
     
     
    ///////////////////////////////////
    ///We precalculate certain properties of S. The objective here is to eliminate
    ///most  p-groups S before we calculate and construct the possible Borel subgroups 
    ///associated with S.
    ///We do this first as there may be many  of Borel subgroups which we don't need 
    ///to calculate in some circumstances.
    /////////////////////////////////////

    ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
    //
    if IsMaximalClass(S) and #S ge p^5 then 
        LL:= LowerCentralSeries(S);  
        T:=[];
         Append(~T,Centralizer(S, LL[2],LL[4]));
         C:= Centralizer(S, LL[nn-2]);
         if C in T eq false then 
            Append(~T,C); end if; 
         T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
         cat 
         [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
          TT:=[];
         for x in T do 
                Nx:=Normalizer(S,x);
                A:=AutYX(Nx,x);
                Ap:= SubMap(x`autopermmap,x`autoperm ,A);
                Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
                RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
                if not RadTest then continue x; end if;
                Append(~TT,x);
         end for;         
           ProtoEssentials:=   TT;
    end if; 

            
    if IsMaximalClass(S) eq false  or #S le p^4 then  
    for x in SS do   
        if x eq S then continue x; end if; 
        if IsCyclic(x) then  continue x; end if;
        Nx:=Normalizer(S,x);
        A:=AutYX(Nx,x);
        Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        Inner:= Inn(x);
        Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
        RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
        if not RadTest then continue x; end if;
        P:= Index(Ap,Innerp);
        Frat:=FrattiniSubgroup(x);
        FQTest := Index(x,Frat) ge P^2;
            //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
            //The order of such faithful modules is at least $|\Out_S(x)|^2$.
        if FQTest eq false then continue x; end if; 
        SylTest, QC:=IsStronglypSylow(Ap/Innerp);
            //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
            //Here we check that the Sylow $p$-subgroup is compatible with this.
        if SylTest eq false   then continue x; end if; 
        if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
        ProtoEssentials:= Append(ProtoEssentials,x); 
    end for;
    end if;
    ////////////////////////////////
    ///We need some subgroups in ProtoEssentials;
    ///////////////////////////////////
     
     


    ///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
    ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
    ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
     
      
    if OpTriv and  CharSbgrpTest(ProtoEssentials,S)   then return FF; end if;  
       
     
        ///This test takes Q as the intersection of all the members of the members 
        //of ProtoEssentials and checks if any of them are characteristic in all members 
        //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

       
    if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
    if  H ne S then return []; end if; end if;
     //This tests is with this set of protoessentials that O^p(\F) <F. 
         
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
                if a then Append(~APC,GG^b); end if; 
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

    if #ProtoEssentialAutClasses eq 0 then return []; end if;
     
     

    if OpTriv and CharSbgrpTest(ProtoEssentialAutClasses,S)   then return []; end if;  
    if Printing then print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  end if;


    //We calculate the possible Borel subgroups and S pairs.


    pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
    BorelsandS:=[];
    if m ne 1  then
        if IsSoluble(AutSp) then 
            PAut, tt:= PCGroup(AutSp); 
            H:=HallSubgroup(PAut,-p); 
            K:=[];
            if OutFSOrders eq [] then 
             K:= [wx`subgroup:wx in Subgroups(H)];
             else  
            for x in OutFSOrders do K:= K cat [wx`subgroup:wx in 
            Subgroups(H:OrderEqual:=x)]; 
            end for; 
            end if;
            BCand:=[]; 
           
        for k:= 1 to #K do  
            K1:= K[k]; 
                for K2 in BCand do 
                if IsConjugate(PAut,K1,K2) then   continue k;   end if;
                end for; 
            Append(~BCand,K1); 
        end for;
        BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
     else
      if OutFSOrders eq [] then OutFSOrders:= [1..m]; end if;
        SubsAutS:= Subgroups(AutSp:OrderDividing:=m);   
        BCand:=  [sub<AutSp|x`subgroup,InnSp>: x in SubsAutS|Index(x`subgroup,InnSp meet x`subgroup) mod p ne 0];
        BCand:= [Random(Complements(AA,InnSp)):AA in BCand];
        BCand:=[ AA:AA in BCand| #AA in OutFSOrders]; 
     end if;
     

     
        for CC in BCand do
        if not IsSoluble(CC) then print "Execution failed: The Borel group is not soluble ";   return []; end if;
            f:=hom<CC->AutS|g:->Inverse(map) (g)>;
            C:= SubMap(f,AutS,CC);  
            if #C ne 1 then B,phiB:= Holomorph(GrpFP,S, sub<AutS|C>); else B,phiB:= Holomorph(S, sub<AutS|C>);  end if; 
           // B,phiB:= Holomorph(S, sub<AutS|C>);  
            T:= phiB(S);  
           
             B, theta := PCGroup(B); T:= theta(T); ///This will not work if B is not soluble.
            BB:=[B,T];
            
            a, alpha:= IsIsomorphic(S,T); //phiB*theta does not work when Holomorph is calculcated with FP group
              for x in ProtoEssentialAutClasses do Append(~BB,SubMap(alpha,T,x)); end for;
            for ii in [3..#BB] do 
            xx:= BB[ii];
            yy:= ProtoEssentialAutClasses[ii-2];
            MakeAutos(xx);
              
                WW:=[];
                for jj in   [1..#yy`autF] do 
                Wx:= yy`autF[jj]; 
                WGens :=[
                Inverse(alpha)*gamma*alpha: gamma in  Generators(Wx)];
                WW[jj]:=sub<xx`autogrp|WGens>; 
                end for;
                xx`autF:= WW;
            end for;
         Append(~BorelsandS,BB);
    end for;
    else
     T, theta := PCGroup(S);
        BB:=[T,T];
        for x in ProtoEssentialAutClasses do Append(~BB,SubMap( theta,T,x)); end for;
            for ii in [3..#BB] do 
                xx:= BB[ii];yy:= ProtoEssentialAutClasses[ii-2]; MakeAutos(xx);WW:=[];
                for jj in   [1..#yy`autF] do 
                    WGens:=[]; Wx:= yy`autF[jj]; 
                        for gamma in Generators(Wx) do  
                            Append(~WGens,Inverse( theta)*gamma* theta); 
                        end for;
                    WW[jj]:=sub<xx`autogrp|WGens>; 
                end for;
                xx`autF:= WW; 
            end for;
         Append(~BorelsandS,BB);
    end if;








    if Printing then print "This group has ", #BorelsandS, " Borel groups";end if;

    count:=0;
    for Bor in BorelsandS do
       

        count := count+1;  
    print "**********************************************";
    print " Borel", count, "of", #BorelsandS, FactoredOrder(Bor[1]);
    print "**********************************************";
     
      B:= Bor[1];    
    S:= Bor[2];  

    //We use the fact that if $B=S$ and p ge 5 then $O^p(\F)<\F$.
    if p ge 5 and B eq S then continue; end if;
    MakeAutos(S);
        
            Bbar, bar:= B/Centre(S);
        subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
        subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
        SS:= [x:x in subsBS|IsSCentric(S,x)]; 
        AutFS:=AutYX(B,S);
        InnS:=Inn(S);
        AutS:= S`autogrp;
        alpha:= S`autopermmap;
        AutSp:= S`autoperm; 
        InnSp:= SubMap(alpha,AutSp, InnS);
        AutBS:= AutYX(B,S);
        AutBp:= SubMap(alpha,AutSp, AutBS);
     
        NAutBp:= Normalizer(AutSp,AutBp);
        NAutB:= SubInvMap(alpha,AutS,NAutBp);
        ProtoEssentialAutClasses:=[Bor[j]:j in [3 ..#Bor]];

    //We explode the autclasses to get all protoessentials and ajoin their potential autogrps.
    ProtoEssentials:=[];
    for x in ProtoEssentialAutClasses do
        Xx, Stx, Rx := AutOrbit(S,x,S`autogrp); 
        PNew := [];
        for y in SS do
            if y in Xx then 
                MakeAutos(y); 
                Append(~ProtoEssentials,y); 
                Append(~PNew,y);
            end if; 
        end for;
        
        if #PNew ne 0 then 
            for j := 1 to #PNew do
                y:= PNew[j];
                y`autF:=[];
                for AP in x`autF do
                            y`autF := Append(y`autF, sub<y`autogrp|[Inverse(Rx[Index(Xx,y)])*gamma*Rx[Index(Xx,y)]: gamma in Generators(AP)]>);
                end for;
            end for; 
        end if;
    end for;//x


    if OpTriv then 
    //The next test uses Lemma 4.10 to show that P1 and P2 are not both essential.
    // If P1 is essential, then P1' ne 1 and is normalized by Aut_\F(S) and Aut_F(E_1). This gives O_p(F) ne 1.
        if #ProtoEssentials eq 2 and p ge 5 and #S lt p^(p+3) then 
            P1:= ProtoEssentials[1]; 
            P2:= ProtoEssentials[2]; 
                if #P1 le #P2 then PP:= P2; P2:= P1; P2:= PP; end if; 
            NSP2:= Normalizer(S,P2);  
            PC:= Core(S,P2);
            if IsConjugate(B,P1,NSP2) and Index(NSP2,P2) eq p and Index(S,NSP2) eq p and 
            Index(P2,PC) eq p and IsCharacteristic(NSP2,PC) and IsNormal(B,DerivedSubgroup(P1)) then        ProtoEssentials:=[P2];
                end if;
        end if;    
    end if; //OpTriv
        








    Candidates:= AssociativeArray(ProtoEssentials);

    for x in ProtoEssentials do Candidates[x]:= x`autF; end for; 

    if pPerfect then 
    //The next check is a preliminary focal subgroup check using that we know the Borel  subgroup. 
    //This often gets rid of the case when $B=S$
        SB:= CommutatorSubgroup(S,B);
        S1:= sub<S|SB,ProtoEssentials>;
        if S1 ne S then   continue Bor; end if;
    end if;

    if OpTriv   and #ProtoEssentials eq 1   and IsNormal(B,ProtoEssentials[1]) then continue Bor; end if; 
      


    if Printing then print "There are", #ProtoEssentials, "proto-essential subgroups before the extension test.\nThey have orders", 
     Explode([#ProtoEssentials[i]: i in [1..#ProtoEssentials]]);end if;

    //We now make all the candidates for Aut_F(E) given our class representatives in 
    //E`autF. This means that we check if the automorphisms in $Aut(N_B(E),E)$ restrict to members of $\Aut_\F(E)$.

    FirstTime := true;
    ProtoEssentialsT:= ProtoEssentials;
    ProtoEssentialsTT:= [];

    while #ProtoEssentialsT ne #ProtoEssentialsTT  do
        ProtoEssentialsTT:= ProtoEssentialsT; 
        
        if #ProtoEssentialsT eq 0 then
        if Printing then    print #ProtoEssentialsT, "proto-essentials which pass the  strongly p-embedded and extension test";
        end if; continue Bor; 
        end if;
     
        Candidates1:=AssociativeArray(ProtoEssentialsT);
        
        Done :={};
        for i in [1..#ProtoEssentialsT] do
            P:=ProtoEssentialsT[i];
            if P in Done then continue i; end if;
            MakeAutos(P);
             if Printing then print "About to Apply AutFPC"; end if;
            Candidates1[P]:=AutFPCandidates(B,S,P,ProtoEssentialsT,Candidates,FirstTime:Printing:= Printing); 
            //next we transfer the automorphisms to everything in the AutOrbit.
             if Printing then print "AutFPC complete"; end if;
            OrbP, SSt, Repp:= AutOrbit(S,P, NAutB);
            if Printing then print "the set Repp has", #Repp, "Members"; end if;
            for nn in [2..#Repp] do
                P1:=OrbP[nn];
                MakeAutos(P1);
                beta:= Repp[nn]; 
                Candidates1[P1]:= [];
                for AP in Candidates1[P] do
                    Append(~Candidates1[OrbP[nn]],
                            sub<P1`autogrp|[Inverse(beta)*theta*beta: theta in Generators(AP)]>);
                end for;
            end for;
        Done := Done join Seqset(OrbP);
         if Printing then print "the set Done", #Done, "Members"; end if;
        end for; //i
      ProtoEssentialsT:=[ProtoEssentialsT[Index(ProtoEssentialsT,x)]:x in ProtoEssentialsT| #Candidates1[x] ne 0];
    Candidates:= Candidates1; FirstTime:=false;
    end while;     

     

    ProtoEssentials:= ProtoEssentialsT;
    if #ProtoEssentials eq 0 then continue Bor; end if;

    if Printing then print  #ProtoEssentialsT, 
    "proto-essentials which pass both the  strongly p-embedded 
    and extension test";end if;


    D:= Subsets({1..#ProtoEssentials});



    ////////////////////////////////
    ///We look at the orbits of $N_Aut(S)(Aut_\F(S))$ on D. 
    ///As we will consider all possible automisers of members of protoessentials
    ///It suffices to look at $N_Aut(S)(Aut_\F(S))$ orbits and this will give us all 
    ///automorphism classes of fusion systems
    //////////////////////////

    NN:= NAutBp;
    for Pr in ProtoEssentials do 
    a, NNN:= AutOrbit(S,Pr,NAutB);
    NN := NN meet SubMap(alpha,AutSp,NNN);
    end for;

       // NN:= sub<NAutBp|NN>; 
    TNB:= Transversal(NAutBp,NN);
    TransAutSB:=[Inverse(alpha)(xxx):xxx in TNB];

    DD:= D;
    DNew:={};
    while #DD ne 0 do 
        x:= Rep(DD); 
        DNew:= DNew join{x}; 
        DDD:={x};
       
        for beta in TransAutSB do 
        xnew := {beta(ProtoEssentials[w]):w in x};
        L:={};
        for ll in xnew do
            for Proto in ProtoEssentials do 
            aa, bb:= IsConjugate(B, ll, Proto);
                if aa then L:= L join{Index(ProtoEssentials,Proto)}; end if;
            end for;
        end for;
      

    DDD:= DDD join {L};   
       end for; //beta
    DD := DD diff DDD;
    end while; 

     
    D:= DNew;
     
    D:= Setseq(D);
     D1:= [#x:x in D];
    ParallelSort(~D1,~D);
    D:=Reverse(D);

     // this tests if there is a conjugate of essential x  which is $B$ conjugate to a subgroup of essential $y$ which using all posibilities for Aut_\F(y) is we can see $x$ is not fully Normalized
     Forbiddenpairs :={};
     
     for x in ProtoEssentials do 
        NSx := Normalizer(S,x);
        for y in ProtoEssentials do
             
            if exists(tt){ tt: tt in Conjugates(B,x)|tt subset y} then 
                if forall{w:w in Candidates[y]| exists{cc:cc in AutOrbit(y,tt,w)|#Normaliser(S,cc) gt #NSx}} 
                then Forbiddenpairs:= Forbiddenpairs join{{x,y}}; 
                end if;
            end if;
        end for;
    end for;
    if Printing then print "The number of forbidden pairs of essential subgroups is ", #Forbiddenpairs;end if;
    /////


    ////////////////Main Search starts here. 



    for ss in [1..#D] do//This is the main loop considering all subsets of ProtoEssentials
        EssSup:= D[ss];//This set specifies which essential subgroups we select from ProtoEssentials.

        if #EssSup eq 0 then continue ss;
        end if; //the fusion system must have rank at least one
        ssSequence:=SetToSequence(EssSup);
        
        Essentials:=[ProtoEssentials[i]: i in EssSup];
       if OpTriv then if #EssSup eq 1 and IsNormal(B,Essentials[1]) then continue ss; end if;end if;
        if exists{w: w in Forbiddenpairs| w subset Essentials} then continue ss; end if;

      max:= Max({#e: e in Essentials});
    Candidates1:=Candidates; 
    Maxes:= {e:e in Essentials|#e eq max};

     
    FLAG := false;
    for P in Essentials do 
        if p*#P ge max and IsNormal(S,P) eq false  then  
             PB:= Conjugates(B,P); 
             Tst:={};  
             for M in Maxes do 
                Tst := Tst join {x subset M:x in PB};
             end for;
              if Tst eq {false} or P in Maxes then 
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
                for II in [1.. #Candidates[P]] do AP:= Candidates[P][II]; 
                    APp:=SubMap(P`autopermmap, P `autoperm,AP);
                     if Normalizer(APp,AutSPp) ne AutBPp then 
                         Candidates1[P][II]:=sub<AP|>; FLAG:= true; 
                     end if;
                end for;//II
            end if;// #Tst;
        end if;
    end for;            
            
            
    if FLAG then 
    CandidatesNew:=AssociativeArray(ProtoEssentials); 
    for x in ProtoEssentials do
    CandidatesNew[x]:=[];
    for y in Candidates1[x] do if #y ne 1 then Append(~CandidatesNew[x],y); end if; end for;
    end for;
    else CandidatesNew:=Candidates;
    end if;
      

     
    ////This next test makes sure that if we have essential subgroups x<y then 
    ////|N_S(x)|\ge  N_S(x\alpha) for all alpha in $\Aut_F(y)$
    Candidates1 := CandidatesNew;

    FLAG := false;
    for x in Essentials do 
        for y in Essentials do 
        if x subset y and x ne y then 
            for II in [1..#CandidatesNew[y]] do AutFy:= CandidatesNew[y][II];
                xOrb:= AutOrbit(y,x,AutFy);
                for w in xOrb do  
                    if #Normalizer(S,w) gt #Normalizer(S,x) then     
                        Candidates1[y][II]:=sub<AutFy|>; FLAG:= true;
                    end if;
                end for;
            end for;
        end if; 
        end for;
    end for; 


    if FLAG then 
    CandidatesNew:=AssociativeArray(ProtoEssentials); 
    for x in ProtoEssentials do
        CandidatesNew[x]:=[]; 
        for y in Candidates1[x] do 
            if #y ne 1 then Append(~CandidatesNew[x],y); 
            end if; 
        end for;
    end for;
    end if;
      
      
      
     
    CandidatesNewp:= AssociativeArray(ProtoEssentials);


    for xP in ProtoEssentials do
        CandidatesNewp[xP]:=[ SubMap(xP`autopermmap, xP`autoperm,CandidatesNew[xP][kk]): kk in [1..#CandidatesNew[xP]]];
        
    end for;

     
     

     
     
      Cart:=[];
      for e in EssSup do
        Cart:=Append(Cart,[1..#CandidatesNew[ProtoEssentials[e]]]);
      end for;

     CPCart:=CartesianProduct(Cart);

         // now run through all possible fusion systems on the chosen set of essential subgoups
     
    if Printing then print "Checking", #CPCart, "automizer sequences with", #EssSup, 
    "essentials of orders:", Explode([#ProtoEssentials[i]: i in EssSup]);end if;


    /////////////////////////////////////////////////////////////////////////////////
    /////for each subset we make a cartesian product, where each element gives a
    ///// potential fusion system
    ///// The set EssSup, Essentials support, defines the essentials subgroups of the fusion system
    /////  For each EssSup we run through the various assignments of automisers to the essentials
    //////For example if EssSup<--> [S,E_1,dots, E_k] then we run through all the possibilities for
    //// Aut_F(E_1) ...
    /////////////////////////////////////////////////////////////////////////////////
     

    //First we make the subgroup of Aut(S) which normalizes all the essential subgroups and B.

    NAutBQp:=NAutBp;

    for Q in Essentials do
    Orb, NN:=AutOrbit(S, Q,NAutB);
    NAutBQp:= NAutBQp meet SubMap(S`autopermmap, S`autoperm,NN);
    end for;


    T2:= Transversal(NAutBp,NAutBQp);
    L:= Set(Essentials);
    T3:= {y: y in T2|{Inverse(alpha)(y)(x): x in L} eq  L};
    NAutBQp:= sub<NAutBp|NAutBQp,T3>;


    NAutBQ:= SubInvMap( alpha, S`autogrp,NAutBQp); 


    CPCart:= Set(CPCart); 

    cpc:= #CPCart; 
     
    //This defines an action of CPCart 
      alpha:=S`autopermmap;
      function Act(x)
         tup:= x[1];ff:= x[1];
         theta := x[2];
         for i in [1..#Essentials] do 
                    ee:= Essentials[i];  
                    jj:= Index(Essentials,SubMap(theta,S,ee));
                    eee:= Essentials[jj];  
                    J:= sub<eee`autogrp|[Inverse(theta)*gen*theta:gen in 
                    Generators(CandidatesNew[ee][ff[i]])]>; 
                    Jp:= SubMap(eee`autopermmap, eee`autoperm,J);
                    kk:= Index(CandidatesNewp[eee],Jp); 
                    jjj:= Index(Essentials,eee);
                    tup[jjj]:=kk;
                end for;
                return tup;
     end function;

      
      
      
      
      
      while #CPCart ne 0 do  
       Bob:= false; 
       possFSys:=Rep(CPCart); 
     
      //POrb is a partial orbit.  This speeds things up as finding large  full orbits seems to be more time consuming. This routine will with high probability find small orbits anyway. The strange choice to perform it twice is to get a balance between speed and getting enough elements of the orbit.

         POrb:= {possFSys, Act(<possFSys,NAutBQ.1>)  };
         for i:= 1 to 2 do 
          POrb2:= POrb;
            for x in Generators(NAutBQ) do;
                for ff in POrb2 do
                    z:= Act(<ff,x>);
                    if not z in CPCart then Bob := true; break i; end if;
                    POrb:= POrb join {z};
                end for;
        end for;
         end for;
         if Bob then CPCart:= CPCart diff POrb;continue; end if;//continues while
       Bob:= false;
         POrb2:= POrb;
         for j := 1 to 3 do 
            x:= Random(Generators(NAutBQ));
            POrb2:= POrb;
            for ff in POrb2 do
                    z:= Act(<ff,x>);
                    if not z in CPCart then Bob := true; break j; end if;
                    POrb:= POrb join {z};
                end for;
         end for;
      
     
        CPCart:= CPCart diff POrb; //removes the partial orbit
       if Bob then continue; end if;//continues while
       Bob:= false;
       
        AutF:=AssociativeArray(ProtoEssentials); //this is the fusion system we will make
        AutF[S]:=AutFS; // this was fixed at the start it is Aut_B(S)
        ////We now populate AutF with the appropriate candidate automisers
        for k in [1..#possFSys] do
           AutF[ProtoEssentials[ssSequence[k]]]:=CandidatesNew[ProtoEssentials[ssSequence[k]]][possFSys[k]];
        end for;
        Autos:=[AutF[S]]; ///Autos is the automiser sequence.
               
        for e in Essentials do 
                Autos:= Append(Autos,AutF[e]);    
        end for;
         
        if Printing then print "Remains to do",#CPCart, "of",cpc; end if; 
         
        if pPerfect and not FocalSubgroupTest(B,S, Essentials,AutF) then  continue; //while
        end if;  
        
        
        if OpTriv and  not FCoreTest(S,Essentials,AutF) then  continue; end if;   


      //    This next test checks that if P is normal in S that its "obvious" automiser has $\Aut_S(P) as a Sylow.
        
        for xx in SS do 
            if IsNormal(S,xx) eq false or #xx eq 1 then continue xx; end if;
            Exx:={w:w in Essentials|xx subset w};
            if #Exx ne 0 then 
                MakeAutos(xx);
                Axx:= sub<xx`autogrp|AutYX(Normalizer(B,xx),xx)>;
                for yy in Exx do
                    Oxx,xxStab := AutOrbit(yy, xx,AutF[yy]);
                    Axx:= sub<xx`autogrp|Axx,Generators(xxStab)>;
                end for;
                if ZZ!(#Axx/#AutYX(S,xx)) mod p eq 0 then Bob:= true; break xx; end if;
            end if;
        end for;
       if Bob then continue; end if;//continues while
       Bob:= false;
         
    //    

      
        N:= {1..#Essentials}; 
        NN:= Subsets(N);
        NN:= Setseq(NN);
        RO:=[#x:x in NN];
            ParallelSort(~RO,~NN);
        NN:= Reverse(NN);
            
            for sNN in NN do
                        if #sNN eq 0 or #sNN eq #Essentials then continue sNN; end if;
                        Es:=[Essentials[ww]: ww in sNN];Append(~Es,S);
                        AutE:= [Autos[ww+1]:ww in sNN];Append(~AutE,AutF[S]);
                        Cor,AutCor:= AutFCore(Es,AutE);
                        n:=ZZ!(#AutCor/#AutYX(S,Cor));
                        if n mod p eq 0 then  Bob:=true; break sNN; end if;///Tests if Aut_S(x) a sylow p of AutCore.
            end for;//sNN
               
               if Bob then continue; end if;//continues while
                Bob:=false;
               
               
               
    //We now create the fusion system. We don't use the standard call as we have already done most of the calculation



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
           //We only need  to check saturation on centrics. So we make a partial fusion graph.       
    if assigned(F`fusiongraph) eq false then  
        F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
    end if;
    F`classes:= ConnectedComponents(F`fusiongraph);
            
            if assigned(F`centrics) eq false then 
                F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if; 

                      for G in FF do 
                              if IsIsomorphic(F,G) then delete F; Bob:= true; break; end if; 
                      end for;
                      if Bob then continue; end if;Bob:=false;
                IS:= IsSaturated(F);
                if Printing then print "Executed saturation test: result is",IS; end if; 
                    if assigned(F`essentials) and IS then  
                        if SaveEach then FNumber:= FNumber +1; 
                            SaveAsGo(FNumber, F);   
                               else    
                            Append(~FF,F);
                        end if; 
                    end if; 
     delete F; 
       end while; //  possFSys
     
    end for;//ss
    end for;//Bor

    GG:= FF;
    if #FF le 1 then return FF; end if; 
    FF:= [FF[1]];
     for i in [2.. #GG] do
        x:= GG[i];  
        for y in FF do 
            if IsIsomorphic(x,y) then continue i; end if;
        end for; 
        Append(~FF,x); 
     end for; 
     
    return FF;
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