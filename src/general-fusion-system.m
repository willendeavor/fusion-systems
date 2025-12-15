// General functions dealing with fusion systems

import "properties-fusion-systems.m" : MakeAllSubgroups;


intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
    {checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    if #E1 ne #E2 then return false; end if; 
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    
    return Eq;
end intrinsic;



intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
    {checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    return Eq;
end intrinsic;



intrinsic NPhi(S::Grp, Q::Grp,phi::Map)->Grp
     {for a subgroup and homomorphism from the second 
     term to the first create the control subgroup}
     P:=Image(phi);
     phii:=iso<Q->P|x:->phi(x)>;
     TSP:= Transversal(Normalizer(S,P),Centralizer(S,P));
     Nphi:= Q;
     T:= Transversal(Normalizer(S,Q),Q);
        for t in T do
                if t in Nphi then continue; end if;
            alpha:=ConjtoHom(Q,Q,t);
            beta :=iso<Q->P|x:-> phii(alpha(x))>;
                for g in TSP do
                    gg:= ConjtoHom(P,P,g);
                    betag :=iso<Q->P|x:-> gg(phii(x))>;
                        if homeq(beta,betag) then   
                            Nphi:= sub<S|Nphi,t>; break; 
                        end if;
                end for;
        end for;
    return Nphi;
end intrinsic;




intrinsic IsIsomorphic (F1::FusionSystem,F2::FusionSystem)->Bool{}
    a, theta := IsIsomorphic(F1`borel,F2`borel);
    if a eq false then 
        return false; 
    end if; 
    p:= F1`prime;
    bounds:=[8,6,6,6];
    primes:=[2,3,4,4];

    if not #F1`essentials eq #F2`essentials then
        return false;
    end if; 
    // Checked the same number of essentials so duplicates don't matter
    if p in primes and #F1`group le p^bounds[Index(primes,p)]  then
        RO1:={IdentifyGroup(x):x in F1`essentials};
        RO2:={IdentifyGroup(x):x in F2`essentials};
    else
        RO1:={#x:x in F1`essentials};
        RO2:={#x:x in F2`essentials};
    end if; 
    if RO1 ne RO2 then  
        return false; 
    end if; 

     

    //The automisers should have the same orders.
    RO1:=[#x :x in F1`essentialautos];
    RO2:=[#x :x in F2`essentialautos];
    Sort(~RO1);
    Sort(~RO2);
    if RO1 ne RO2 then   return false; end if; 
     
     

    AutBp:=(F2`essentials[1])`autoperm;

    alpha:= (F2`essentials[1])`autopermmap;

    NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
    NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp);
    TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
    Trans:=[Inverse(alpha)(xxx):xxx in TNB];
     

    //transfer to same group. And make an image for each transversal map.
    ImEssentials:=[];

    for mu in Trans do
    ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1`essentials] ); 
    end for;

    ImAutEssentials:= AssociativeArray({1..#Trans});

    for zz in [1..#ImEssentials] do 
        ImEssentialsCalc:= ImEssentials[zz]; 
        mu:= Trans[zz];// theta. mu maps xin F1 essentials to a subgroup of F2`group
           //Initialize the automorphism group of the images
            for ii in [1..#ImEssentialsCalc] do  
                x:= ImEssentialsCalc[ii]; 
                x`autogrp :=AutomorphismGroup(x); 
                x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp); 
            end for;     
        ImAutEssentialsCalc:=[];
        for x in ImEssentialsCalc do 
                AutF1:= F1`essentialautos[Index(ImEssentialsCalc,x)];
                XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
                ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
        end for;
        
    ImAutEssentials[zz]:=ImAutEssentialsCalc;
    MakeAllSubgroups(F2);
    end for;
    for XXct in [1..#ImEssentials] do XX:=ImEssentials[XXct];
        for ii in [1..#XX] do e:= XX[ii]; if e in F2`subgroups then continue; end if;
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


