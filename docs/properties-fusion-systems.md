// Functions that determine properties of a given fusion system



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
