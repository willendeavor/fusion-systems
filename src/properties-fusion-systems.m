// Functions that determine properties of a given fusion system


// Duplicated in the original file
intrinsic AutFCore(Es::SeqEnum,AutE::SeqEnum)->Grp,GrpAuto
    {calculates F core and action on it}
    F:= Es[1];
    for i := 2 to #Es do  F:= F meet Es[i];end for; 
     Fn:= sub<F|>;
     while F ne Fn do
     Fn:= F;
     for i := 1 to #Es do
        A:= AutOrbit(Es[i],F,AutE[i]);
        for x in A do F := F meet x; end for;
     end for;
     end while;
    MakeAutos(F); K:= Inn(F); 
        for i := 1 to #Es do  K:=  sub<F`autogrp|K,Generators(AutE[i])>; end for;
        return F,K;
end intrinsic;




intrinsic FCoreTest(S::Grp,Essentials::SeqEnum, AutF::Assoc)->Bool, Grp
    {Test is F core is trivial and returns FCore}
    F:= S; FC:= sub<S|>; AA:=Append(Essentials,S);
    for x in Essentials do F := F meet x; end for;
    SF:=[x`subgroup:x in  NormalSubgroups(F)];
    SF:= Reverse(SF);

      

    for x in SF do 
     if IsNormal(S,x) eq false then continue x; end if;
        for E in AA do
            for y in Generators (AutF[E]) do
                for xx in Generators(x) do
                    if y(xx) in x eq false   then 
                    continue x; end if;
                end for;
            end for;
        end for;
        FC:= sub<S|x>; break;
     end for;
     
     
    return #FC eq 1, FC;
end intrinsic;



intrinsic FocalSubgroupTest(B::Grp,S::Grp, Essentials::SeqEnum,AutF::Assoc)->Bool,Grp
    {Tests if S eq Focal subgroup in potential system};
    Foc:=sub<S|{(s,b):s in Generators(S),  b in Generators(B)}>;
    for e in Essentials do  
    Foc:= sub<S|Foc, {x^-1*aa(x): x in e, aa in Generators(AutF[e])}>;
    end for;
    return Foc eq S, Foc;
end intrinsic;
 


intrinsic Core(F::FusionSystem)->Grp
    {Returns  F core }
    FF:= F`group; 

    FC:= sub<FF|>; AA:=Append(F`essentials,FF);
    for x in F`essentials do FF := FF meet x; end for;
    SF:=[x`subgroup:x in  NormalSubgroups(FF)];
    SF:= Reverse(SF);

      
    AutF:= F`AutF;
    for x in SF do 
     if IsNormal(F`group,x) eq false then continue x; end if;
        for E in AA do
            for y in Generators (AutF[E]) do
                for xx in Generators(x) do
                    if y(xx) in x eq false   then 
                    continue x; end if;
                end for;
            end for;
        end for;
        FC:= sub<FF|x>; break;
     end for;
     
     
    return #FC eq 1, FC;
end intrinsic;



intrinsic FocalSubgroup(F::FusionSystem)->Grp
    {Creates the focal subgroup of the fusion system}
    S:= F`group;  
    Foc:=sub<S| >;
    for e in F`essentials do 
        i:= Index(F`essentials,e);
        AutFE:= F`essentialautos[i];
        Foc:= sub<S|Foc, {x^-1*aa(x): x in e, aa in Generators(AutFE)}>;
    end for;
    return Foc;
end  intrinsic;



intrinsic FusionGraph(F::FusionSystem)->GrphUnd, Assoc
{Returns the labeled fusion graph}

if assigned(F`fusiongraph)  then return F`fusiongraph,F`maps; end if;

Essentials := F`essentials;
SS:= F`subgroups;
S:= F`group;
B:=F`borel;
Gamma := Graph<#SS|>;
SSxSS:= [[n,m]:n in [1..#SS],m in [1..#SS]];
Maps:=AssociativeArray(SSxSS);


for E in Essentials do 
        if E eq S then continue E; end if; 
    
    NBE := Normalizer(B,E);
        SubsE := Subgroups(NBE:OrderDividing:= #E);
        SSSE:={x`subgroup:x in SubsE|x`subgroup subset E};
        while #SSSE ne 0 do
        Q:= Rep(SSSE);
        for X in SS do
            a,h:= IsConjugate(B,X,Q); 
            if a then
                v:= Index(SS,X); 
                g:=ConjtoHom( SS[v], Q,h); 
                g1 :=ConjtoHom(Q, SS[v],h^-1); 
                break;
            end if;
        end for;
        Orb, NN, Elt := AutOrbit(E,Q,F`essentialautos[Index(F`essentials,E)]);
        for x in Orb do 
            if IsConjugate(B,Q,x) then continue; 
            end if;
            for y in SS do
                a,b:= IsConjugate(B,x,y);
                if a  then w:= Index(SS,y); namex:= Index(Orb,x);
                theta := g*Elt[namex]*ConjtoHom(x,y,b);
                theta1:= ConjtoHom(y,x,b^-1)*Elt[namex]^-1*g1;
                break; end if;
            end for;
            if v ne w then
                AddEdge(~Gamma,v,w);
                Maps[[v,w]]:= theta;
                //Maps[[w,v]]:= theta^-1;
            Maps[[w,v]]:= theta1;
            end if;
         end for;
         SSSE := SSSE diff Set(Orb);
        end while;
end for;
return  Gamma, Maps;
end intrinsic;



intrinsic FusionGraphSCentrics(F::FusionSystem)->GrphUnd, Assoc
    {Returns the labeled fusion graph on S centrics}

    if assigned(F`fusiongraph)  then return F`fusiongraph,F`maps; end if;

    Essentials := F`essentials; 

    S:= F`group;
    B:=F`borel;
    SS:=  F`subgroups;
    Gamma := Graph<#SS|>;
    SSxSS:= [[n,m]:n in [1..#SS],m in [1..#SS]];
    Maps:=AssociativeArray(SSxSS);


    for E in Essentials do 
            if E eq S then continue E; end if; 
        
        NBE := Normalizer(B,E);
            SubsE := Subgroups(NBE:OrderDividing:= #E);
            SSSE:={x`subgroup:x in SubsE|(x`subgroup subset E) and (IsSCentric(S,x`subgroup))};
            while #SSSE ne 0 do
            Q:= Rep(SSSE);
            for X in SS do
                a,h:= IsConjugate(B,X,Q); 
                if a then
                    v:= Index(SS,X); 
                    g:=ConjtoHom( SS[v], Q,h); 
                    g1 :=ConjtoHom(Q, SS[v],h^-1); 
                    break;
                end if;
            end for;
            Orb, NN, Elt := AutOrbit(E,Q,F`essentialautos[Index(F`essentials,E)]);
            for x in Orb do 
                if IsConjugate(B,Q,x) then continue; 
                end if;
                for y in SS do
                    a,b:= IsConjugate(B,x,y);
                    if a  then w:= Index(SS,y); namex:= Index(Orb,x);
                    theta := g*Elt[namex]*ConjtoHom(x,y,b);
                    theta1:= ConjtoHom(y,x,b^-1)*Elt[namex]^-1*g1;
                    break; end if;
                end for;
                if v ne w then
                    AddEdge(~Gamma,v,w);
                    Maps[[v,w]]:= theta;
                    //Maps[[w,v]]:= theta^-1;
                Maps[[w,v]]:= theta1;
                end if;
             end for;
             SSSE := SSSE diff Set(Orb);
            end while;
    end for;
    return  Gamma, Maps;
end intrinsic;



intrinsic  FConjugacyClasses(F)-> Set
    {Returns FConjugacyClasses}
     B:= F`borel;
     BC:= ConjugacyClasses(B);
     CCC:={};kk:=0;
     for t in BC do
        s:= t[3]; for cc in CCC do if s in cc then continue; end if; end for;
        if s in F`group eq false then continue; end if;
        k:= #FConjugacyClass(F,s); kk:= kk+k;
        CCC:= CCC join {FConjugacyClass(F,s)};
        if kk eq #F`group then break; end if;
     end for;
     
    return CCC; 
end intrinsic;



intrinsic  SizeFConjugacyClasses(F)-> RngElt
    {Returns Size of  FConjugacyClasses}
    return #FConjugacyClasses(F);
end intrinsic;





intrinsic MakeAllAutFCentric(FF::FusionSystem:saturationtest)->Assoc, Bool
    {Makes all AutF for centric subgroups unless parameter saturated test eq true in which case it stops early when the system is not saturated .}

    ZZ:=Integers();
    SS:= FF`subgroups;
    S:= FF`group; 
    B:= FF`borel; 
    AutF:= FF`AutF; 
    Essentials:= FF`essentials; 

    if assigned(FF`fusiongraph) eq false then FF`fusiongraph,FF`maps:= FusionGraph(FF);
       
    end if;
     FF`classes:= ConnectedComponents(FF`fusiongraph);
    if assigned(FF`centrics) eq false then FF`centrics:={x:x in FF`subgroups|IsCentric(FF,x)}; end if;
    Maps:= FF`maps;  
    ConComp:= FF`classes; 
    Fac:= FactoredOrder(S);
    ExpS:=Fac[1][2]; p:= FF`prime;
    expP:= ExpS-1;

     
    for x in SS do   
        if #x eq p^expP and ((x in Essentials) eq false) then
            AutF[x]:= AutYX(Normalizer(B,x),x);
        end if;
    end for;

      TTTn:={x:x in FF`centrics|   IsFullyNormalized(FF,x) and (x in Essentials) eq false};
    for subexponent:=ExpS-2 to 2 by -1 do
      
        TTT :={x: x in TTTn|#x eq p^subexponent };
      
     
        while  #TTT ne 0 do 
            P:= Random(TTT);
        //If P is F-conjugate to a member of Essentials, then Aut_F(P) is F-conjugate to Aut_F(E). Transfer the data and move to next P.

            for E in Essentials do 
                aa,bb:=IsConjugate(FF,P,E); 
                aa,bbb:=IsConjugate(FF,E,P); 
                if aa  then  //bbb:= Inverse(bb);
                    AutF[P]:=  sub<P`autogrp|{hom<P->P|gg:->bbb(hh(bb(gg)))> :hh in Generators(AutF[E])}>;
                    TTT:= TTT diff {P};continue; 
                end if; 
            end for; //E
            
        ///Now P is not F-conjugate to E.

               NBP:=Normalizer(B,P);
               AutF[P] :=  AutYX(NBP,P); 
           AFSP:=AutF[P];
              
           NBPoverP, a := NBP/P;
            ///TTTS contains representative of all non-trivial $p$-subgroups in N_S(P)/P
     
                TTTS:= [sub<NBP|SubInvMap(a, NBP, x`subgroup),P>:x in Subgroups(NBPoverP:OrderDividing:=#S)|x`order ne 1];
                    for ccc:= 1 to #TTTS do
                     x := TTTS[ccc]; 
                        MakeAutos(x);

                        if x in SS then
                            AutFx := AutF[x];
                            j:= x`autopermmap;  Ap:=x`autoperm;
                        else  
                               Ax:=x`autogrp;
                                for ww in SS do
                                aa, bb := IsConjugate(B,ww,x);
                                    if aa then
                                        bbb:= ConjtoHom(ww,x,bb);  bbb1:= ConjtoHom(x,ww,bb^-1);
                                        AutFx:= sub<Ax|{bbb1*gen*bbb : gen in Generators(AutF[ww])}>; break ww;
                                    end if;
                                 end for;//for ww
                        j:=x`autopermmap; Ap:= x`autoperm; 
                        end if;// if x in ss, then, else, end if
                    AFp:= sub<Ap|{j(pp):pp in Generators(AutFx)}>;
                    jinverse:=Inverse(j);
                    AA, NN, Elt:= AutOrbit(x,P,AutFx);
                    MM:= sub<Ap|{j(n):n in Generators(NN)}>;
                    Trp := Transversal(AFp,MM);
                    Tr:= {jinverse(t):t in Trp};
                    ////////////////////////////////
                    //We look at maps between TTTS[ccc] and TTTS[ddd] that are extensions of maps in AutF[P].  
                    ///We don't need to do it both ways around as adding an element is the same as adding its inverse.
                    //////////////////////////////////////////////////
                        for ddd:= ccc to #TTTS do  
                            y := TTTS[ddd]; W:={};
                            if x eq y then 
                                    for nn in Generators(NN) do  mmP:= iso<P->P| w:->nn(w)>; 
                                    W:= W join {mmP};
                                end for;
                                AutF[P]:=sub<P`autogrp|AutF[P],W>;
                            else
                            aa, bb:= IsConjugate(FF,x,y);
                                if aa then 
                                W:={alpha*bb:alpha in Tr |(alpha*bb)(P) eq P}; 
                                AutF[P]:=sub<P`autogrp|AutF[P],W>;
                                end if;
                            end if;
                        end for;//ddd
                         if saturationtest then 
                            if ZZ!(#AutF[P]/#AFSP) mod p eq 0 then  
                            return AutF, false;
                            end if;  
                         end if; 
                    end for; //ccc
                    
                  isp:=Index(SS,P);

                    for C in FF`classes do
                        if isp  in C then D:= C; break; end if;
                    end for;
                    //Check that calculated data coincides with information from essentials. 
                    //I.e if P if F-conjugate to some F`essential, then auto groups should be the same.
                    
                     for iiii in [1..#Essentials] do E:= Essentials[iiii];
                        mm:= Index(SS,E); 
                        if mm in D then
                         TransP:=TransportAutomorphismsYtoX(FF,AutF,P,E);
                         if TransP ne FF`essentialautos[iiii] then 
                         if saturationtest then
                            return AutF, false; 
                          else print "the automiser sequence is not consistent in this system"; return AutF,_;
                          end if;
                          end if;
                         end if;
                    end for;
                     //we now can define AutF for  all the F-conjugates of P
                     for kk in D do jj:= Index(kk); 
                        if jj eq isp then  TTT:= TTT diff {P};   continue; end if;
                        AutF[SS[jj]]:= TransportAutomorphismsYtoX(FF,AutF,P,SS[jj]);  
                        TTT:= TTT diff {SS[jj]};
                    end for;  //
                    
               end while; //TTT
         end for;//subexponent
    delete TTT; delete TTTS;

    return AutF, _;

end intrinsic;





intrinsic IsSaturated(F::FusionSystem)-> Bool
    {Determines if F is saturated}

    if assigned(F`saturated) then return F`saturated; end if;
     
    SS:= F`subgroups; 
    S:= F`group; 
    B:= F`borel; 
    Essentials:= F`essentials;
     

    if assigned(F`fusiongraph) eq false then  
    F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
    end if;
    F`classes:= ConnectedComponents(F`fusiongraph);

    Maps:= F`maps; 
    AutF:= F`AutF;

    ConComp:= F`classes; 
     
     
    for x in F`essentials do 
        if IsCentric(F,x) eq false then 
        F`saturated := false; return F`saturated; 
        end if; 
         if IsFullyNormalized(F,x) eq false then 
        F`saturated := false; return F`saturated; 
        end if; 
    end for;

     

    if assigned(F`centrics) eq false then F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if;
      
        W:= {x: x in F`centrics|IsDefined(F`AutF,x) };
        i:=0;
         for x in Reverse(Setseq(F`centrics)) do  
            if x in W then continue; end if; 
            for w in W do
                a,b:=IsConjugate(F,x,w);
                if a then    aa,cc:=IsConjugate(F,w,x);    
                F`AutF[x] := sub<x`autogrp| {b*gamma*cc: gamma in Generators(F`AutF[w])} >; 
                 W:= W join{x}; continue x; 
            end if;
            end for;
            
           F`AutF[x]:= AutomorphismGroup(F,x);  
           if IsFullyNormalized(F,x) then 
                if not IsFullyAutomised(F,x) then return false; end if;
           end if; 
           W:= W join{x};
         end for;
     

    Saturated:= true;
    for C in ConComp do
        for vv in C do
            PP:= SS[Index(vv)];
                if PP eq S then continue C; end if;
                if IsCentric(F,PP) eq false then continue C; end if;
                if IsFullyNormalized(F,PP) eq false then continue vv; end if;
                if RadicalTest(S,PP) eq false then   continue vv; end if;
                if IsFullyAutomised(F,PP) eq false then return false; end if;
            Saturated, sat := SurjectivityProperty(F,PP:saturationtest:=true);
            if  assigned(sat) then  return sat; end if;
                if Saturated then continue C; end if;
        end for;
        if Saturated eq false then break C; end if;
    end for; 
    delete F`fusiongraph;//This is a fix to make sure that IsConjugate works for non-centric subgroups



    F`saturated := Saturated;
    return Saturated;
end intrinsic;



intrinsic IsGroupFusionSystem(F::FusionSystem)->Bool
    {Return true if F is constructed from G }
    if assigned(F`grpsystem) then return true; end if;
    return false; 
end intrinsic;




intrinsic IsIsomorphic(B::Grp,Autos::SeqEnum,F2::FusionSystem)->Bool{}
    a, theta := IsIsomorphic(B,F2`borel);
    if a eq false then return false; end if; 
    p:= F2`prime;
    bounds:=[8,8,6,6];
    primes:=[2,3,4,4];



    /////////////////////////////////////////////////////////
    ///F2 has its automiser sequence in the canonical order.
    ///We should reorder Autos.
    //////////////////////////////////////////////////////////
    if p in primes and #F2`group le p^bounds[Index(primes,p)]  then  
    RO:=[IdentifyGroup( Group(x)):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos);
    else
    RO:=[#Group(x):x in Autos];
    ParallelSort(~RO,~Autos);
    Reverse(~Autos); 
    end if; 
      
      
      
    F1essentials := [Group(x):x in Autos];

    if p in primes and #F2`group le p^bounds[Index(primes,p)]  then
    RO1:=[IdentifyGroup( x):x in F1essentials];
    RO2:=[IdentifyGroup(x):x in F2`essentials];
    else
    RO1:=[#x:x in F1essentials];
    RO2:=[#x:x in F2`essentials];
    end if; 
    if  RO1 ne RO2 then return false; end if; 

    //The automisers should have the same orders.
    RO1:=[#x :x in Autos];
    RO2:=[#x :x in F2`essentialautos];
    Sort(~RO1);
    Sort(~RO2);
    if RO1 ne RO2 then return false; end if; 
     
     
     
        


    AutBp:= (F2`essentials[1])`autoperm;

    alpha:= (F2`essentials[1])`autopermmap;

    NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
    NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp); 
    TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
    Trans:=[Inverse(alpha)(xxx):xxx in TNB];
     

    //transfer to same group. And make an image for each transversal map.
    ImEssentials:=[];

    for mu in Trans do
    ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1essentials] ); 
    end for;

    ImAutEssentials:= AssociativeArray({1..#Trans});

    for zz in [1..#ImEssentials] do 
        ImEssentialsCalc:= ImEssentials[zz]; 
        mu:= Trans[zz];// theta. mu maps x in F1essentials to a subgroup of F2`group
           //Initialize the automorphism group of the images
            for ii in [1..#ImEssentialsCalc] do  
                x:= ImEssentialsCalc[ii];
                MakeAutos(x); 
            end for;     
        ImAutEssentialsCalc:=[];
        for x in ImEssentialsCalc do 
                AutF1:= Autos[Index(ImEssentialsCalc,x)];
                XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
                ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
        end for;
         
    ImAutEssentials[zz]:=ImAutEssentialsCalc;
     
    end for;

    for XXct in [1..#ImEssentials] do 
        XX:=ImEssentials[XXct];
        for ii in [1..#XX] do 
        e:= XX[ii]; 
         if e in F2`subgroups then continue; end if;
            jj:= IdentifyBClass(F2,e);
            P:= F2`subgroups[jj];
            MakeAutos(P);
            a,b :=IsConjugate(F2`borel,e,P);
            bb:= ConjtoHom(e,P,b); 
            bbb:= ConjtoHom(P,e,b^-1);    
            XX[ii]:=P;
            ImAutEssentials[XXct][ii]:= sub<P`autogrp|
                {hom<P->P|gg:-> bb(gen(bbb(gg)))>:
                gen in  Generators(ImAutEssentials[XXct][ii])}>;
    end for;
    end for;
                
     
            jj:= {1..#F2`essentials};
            for ii in [1..#ImAutEssentials] do 
                kk:= jj;
                for mm in ImAutEssentials[ii] do
                    for aa in jj do
                        if mm eq F2`essentialautos[aa] then kk:= kk diff {aa}; end if;
                    end for; 
                 if #kk eq 0 then return true;end if;
                end for;
            end for; 
     return false;
end intrinsic;



intrinsic CharSbgrpTest(ProtoEssentials::SeqEnum,S::Grp)->Bool                     
    {Checks if theres a characteristic subgroups of all essentials 
    and S contained in the intersection of protop essentials}

    Q:= S; 
    for xx in ProtoEssentials do 
        Q := Q meet xx; 
    end for;

    QQ:= NormalSubgroups(Q);
    SProtoEssentials := Append(ProtoEssentials,S);
    for w in QQ do 
        ww:= w`subgroup;
        if #ww ne 1 then 
            for xx in SProtoEssentials do 
            wwChar := IsCharacteristic (xx,ww);
                if wwChar eq false then  continue w; end if; 
            end for;
            if wwChar eq true  then return true;end if;
        end if; 
    end for;
    return false;
end intrinsic; 