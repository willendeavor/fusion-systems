// Functions related to properties of a subgroup within the fusion system


intrinsic IdentifyBClass(F::FusionSystem,P::Grp)->RngIntElt,GrpElt
    {Identifies a AutFS-conjugacy class}
     
     SS:= F`subgroups; B:= F`borel;
     for ii := 1 to #SS do 
        aa,bbb:=IsConjugate(B,P,SS[ii]);
        if aa then return ii,bbb; end if; 
     end for;
end intrinsic;


intrinsic IdentifyBClass(B::Grp,SS::SeqEnum,P::Grp)->RngIntElt,GrpElt
     {Identifies a AutFS-conjugacy class}
     for ii := 1 to #SS do 
        aa,bbb:=IsConjugate(B,P,SS[ii]);
        if aa then return ii,bbb; end if; 
     end for;
end intrinsic;



intrinsic IdentifyFOrbit(F::FusionSystem,P::Grp)->SetEnum
   {identifies the connected component of the fusion graph corresponding to P}    
      if assigned(F`fusiongraph) eq false then 
          F`fusiongraph, F`maps:= FusionGraph(F); 
      end if;   F`classes:= ConnectedComponents(F`fusiongraph);
      ii:= Index(F`subgroups,P);
                for C in F`classes do
                    if ii in C then D:= C; break; end if;
                end for;
      return D;
end intrinsic;



intrinsic ConjugacyClass(F::FusionSystem,P:Grp)-> SetEnum
   {Determines the F-conjugacy class of a subgroup}
   SS:= F`subgroups;S:= F`group;
       if assigned(F`fusiongraph) eq false then 
           F`fusiongraph,F`maps:= FusionGraph(F);  
           
       end if; F`classes:= ConnectedComponents(F`fusiongraph);

   ii:= IdentifyBClass(F,P);

   Clss:= IdentifyFOrbit(F,SS[ii]);  
   FCls:={};
   for w in Clss do 
       FCls:= FCls join{ SS[Index(w)]^x:x in F`borel}; 
   end for;
   return FCls;
end intrinsic;



intrinsic IsConjugate(F::FusionSystem, P::Grp,Q::Grp)->Bool,Map 
   {returns a homomorphism and true if the groups are F-conjugate}

   SS:= F`subgroups; S:= F`group; B:= F`borel; 
   if assigned(F`fusiongraph) eq false then 
       F`fusiongraph,F`maps:= FusionGraph(F);  
       
   end if;
   F`classes:= ConnectedComponents(F`fusiongraph); 
   Maps:= F`maps; 
   V:= Vertices(F`fusiongraph);

   conj := false; gg:= Id(S);
       if #P ne #Q then return false, _; end if;
      
      
   ii, b1:= IdentifyBClass(F,P);
   jj, b2:= IdentifyBClass(F,Q);

               if Reachable(V!ii, V!jj) then
                  gg:=  ConjtoHom(P,SS[ii],b1); 
                  hh:=ConjtoHom(SS[jj],Q,b2^-1);
                  Geo:=Geodesic(V!ii,V!jj);
                  if #Geo eq 0 then conj eq false;
                       else conj := true;
                       for iii:= 1 to #Geo-1 do 
                           gg:= gg*Maps[[Index(Geo[iii]),Index(Geo[iii+1])]]; 
                       end for;
                 end if;
                 gg:=gg*hh;
             end if;
   return conj,gg;
end intrinsic;



intrinsic IsConjugate(F::FusionSystem, g::GrpElt,h::GrpElt)->Bool,Map 
   {returns a homomorphism and true if the elements are F-conjugate}
   S:= F`group;
   B:= F`borel;

   a,b := IsConjugate(B,g,h);
   if a then b :=  ConjtoHom(B, B, b); return true,b;end if;


   if assigned(F`fusiongraph) eq false then 
       F`fusiongraph,F`maps:= FusionGraph(F); 
   end if;

   G:= sub<B|g>; H:= sub<B|h>;
   a,b:=IsConjugate(F , G,H);
   if a eq false then return false; end if; 
   g1:= b(g);
    
   a1, bb:= IdentifyBClass(F,H);

   P:= H^bb;

   APH:= AutomorphismGroup(F,P);
   g2 := g1^bb;
   h1 := h^bb;

   CC, JJ, KK:= AutOrbit(P, g2, APH);
   if h1 in CC eq false then return false; 
       else k:= Index(CC,h1); mp:= KK[k];
       map := b*ConjtoHom(S,S,bb)*mp*ConjtoHom(S,S,bb^-1); return true, map;
       end if;
       
   return false,_;
end intrinsic;



intrinsic FConjugacyClass(F::FusionSystem,x::GrpElt)->  Set
   {Returns set of all F-conjugates of x}
   B:= F`borel;
   BC:= ConjugacyClasses(B);
   CC:={};
   for t in BC do
       s:= t[3]; 
       if Order (s) ne Order (x) then continue; end if;
       a:= IsConjugate(F,x,s); 
       if a then CC:= CC join Class(B,s); end if;
   end for;
   return CC;
end intrinsic;



intrinsic  SizeFConjugacyClass(F::FusionSystem,x::GrpElt)->  RngElt
   {Returns size of the F-class of x}
    return #FConjugacyClass(F,x);
end intrinsic;



intrinsic IsCentric(F::FusionSystem,P::Grp)->Bool
   {Returns true if P is F-centric}

   SS:= F`subgroups; S:= F`group; B:= F`borel; 
   if assigned(F`fusiongraph) eq false then 
       F`fusiongraph,F`maps:= FusionGraph(F); 
   end if;
     F`classes:= ConnectedComponents(F`fusiongraph); 
   Cent:= true;

   ii:= IdentifyBClass(F,P);
   P:= F`subgroups[ii];
   C:=  IdentifyFOrbit(F,P);
        for jj in C do
           if Centre(SS[Index(jj)]) ne Centralizer(S,SS[Index(jj)]) 
               then return false;
           end if;
        end for;
 return Cent;
 end intrinsic;


intrinsic IsFullyNormalized(F::FusionSystem, P::Grp)->Bool
   {Is the subgroup full F-Normalized}
   SS:= F`subgroups; S:= F`group; B:= F`borel; 
   if assigned(F`fusiongraph) eq false then 
   F`fusiongraph,F`maps:= FusionGraph(F);  
   end if;
    F`classes:= ConnectedComponents(F`fusiongraph); 
    
   FN:= true;

   ii:= IdentifyBClass(F,P);
   P:= F`subgroups[ii];

   n:=#Normalizer(S,P);
   C:=IdentifyFOrbit(F,P);
   for jj in C do 
       m:= #Normalizer(S,SS[Index(jj)]);    
       if m gt n then FN:= false;
           break jj; 
       end if; 
   end for; 

   return FN;
end intrinsic;



intrinsic IsFullyCentralized(F::FusionSystem, P::Grp)->Bool{Is the subgroup full F-Centralized}
   SS:= F`subgroups; S:= F`group; B:= F`borel; 
   if assigned(F`fusiongraph) eq false then F`fusiongraph,F`maps:=FusionGraph(F);  
   end if;
    F`classes:= ConnectedComponents(F`fusiongraph); 

       FC:= true;
       n:=#Centralizer(S,P);

   ii:= IdentifyBClass(F,P);
   P:= F`subgroups[ii];

   C:=IdentifyFOrbit(F,P);
   for jj in C do 
       m:= #Centralizer(S,SS[Index(jj)]);    
       if m gt n then FC:= false;
           break jj; 
       end if; 
   end for; 
   return FC;
end intrinsic;




//////////////////////////////////////////////////////////////////////
///Transports for ww in SS and x B-conjugate to AutF(ww) to AutF(x). 
///The second one transports with known origin and X in SS.  
//So AY= AutF[SS[ii]] is known and X is F-conjugate to Y=SS[ii]
//////////////////////////////////////////////////////////////////////

intrinsic TransportAutomorphismsYtoX(F::FusionSystem,AutF::Assoc,Y::Grp,X::Grp)
                ->GrpAuto
    {Transports the automorphism group of the first group to 
    the second assuming they are F-conjugate}
    require IsConjugate(F,Y,X):"The groups are not F-conjugate";
     MakeAutos(X);


        Ax:= X`autogrp;
        AY:= AutF[Y];
        SS:= F`subgroups; S:= F`group; B:= F`borel; 
    if assigned(F`fusiongraph) eq false then 
        F`fusiongraph,F`maps:= FusionGraph(F);  
       
    end if; F`classes:= ConnectedComponents(F`fusiongraph); 
        V:= Vertices(F`fusiongraph);
        Maps:=F`maps;
        jj:= Index(SS,X);
        ii:= Index(SS,Y);

        Geo:=Geodesic(V!ii,V!jj);
        alpha:= Identity(AY);
        beta:= Identity(Ax);
            for iii:= 1 to #Geo-1 do
                alpha:= alpha*Maps[[Index(Geo[iii]),Index(Geo[iii+1])]];
            end for;
            for iii:= #Geo to 2 by -1 do
                beta:= beta*Maps[[Index(Geo[iii]),Index(Geo[iii-1])]];
            end for;
        AutX:= sub<Ax|{beta*gen*alpha:gen in Generators(AY)}>;
    return AutX;
end intrinsic;



intrinsic SurjectivityProperty(F::FusionSystem,P::Grp:saturationtest)->Bool, Bool
    {Determines whether the surjectivity property hold for P}

    if saturationtest and assigned(F`saturated) then 
    return F`saturated, F`saturated; end if;

    require IsCentric(F,P):"subgroup not F-centric";

    SS:= F`subgroups; 
    S:= F`group; 
    B:= F`borel; 
    Essentials:= F`essentials;

    Maps:= F`maps; 
    ConComp:= F`classes; 
    AutF:= F`AutF;

     
     
    SurP:= true;
    NSP:= Normalizer(S,P);

    NSPoverP, a := NSP/P; 
    SSP:= [sub<NSP|SubInvMap(a, NSP, x`subgroup),P>:x in Subgroups(NSPoverP)|x`order ne 1];
       for OverGrpP in SSP do 
            BClassOverGrpP, alpha:= IdentifyBClass(F,OverGrpP);
            RepOverGrpP:= SS[BClassOverGrpP];
            MakeAutos(OverGrpP);
            Ax:=  OverGrpP`autogrp;
            beta:= ConjtoHom(RepOverGrpP,OverGrpP,alpha^-1);
            beta1:= ConjtoHom(OverGrpP,RepOverGrpP,alpha); 
            AutFx:= sub<Ax|{beta1*gen*beta : gen in Generators(AutF[RepOverGrpP])}>;      
            AA:= AutF[P]; 
            MakeAutos(P);
            AAp:= sub<P`autoperm|{P`autopermmap(gAA):gAA in Generators(AA)}>;
            action := AutYX (OverGrpP,P);
            actionp:= SubMap(P`autopermmap,AAp,action);
            Naction:= Normalizer(AAp,actionp);
            NBB:= SubInvMap(P`autopermmap,P`autogrp,Naction);
            Orb,NN, Elts:= AutOrbit(OverGrpP,P,AutFx);
            ResNN:=sub<P`autogrp|Generators(NN)>;
            if ResNN ne NBB then  SurP := false; break; end if;
        end for;
        if assigned(F`saturated) then
     return SurP, F`saturated; else return SurP, _;end if; 
 end intrinsic;




 intrinsic IsFullyAutomised(F::FusionSystem,P::Grp)->Bool
     {Is P fully F-automised}
     S:= F`group;   
     p:= F`prime;
     require #P gt 1 : "We require P non-trivial";
     
    if  IsDefined(F`AutF,P) eq false then 
        F`AutF[P]:=  AutomorphismGroup(F,P);
    end if;

    ZZ:= Integers();
    m:= #Normalizer(S,P)/#Centralizer(S,P);
    m:= ZZ!m;
    F:= FactoredOrder(F`AutF[P]); q:=1;
    for x in F do 
        if x[1] eq p then q:= p^x[2]; end if; 
    end for;
    if q eq m then FA:= true; else FA:= false; end if;
    return FA;
end intrinsic;



intrinsic IsWeaklyClosed(F::FusionSystem, P::Grp)->Bool
    {Returns true if the subgroups is weakly closed}
    WC:= false;
    if IsNormal(F`borel,P) eq false then return false; end if;
    if #ConjugacyClass(F,P) eq 1 then WC := true; end if;
    return WC;
end intrinsic;



intrinsic IsStronglyClosed(F::FusionSystem, P::Grp)->Bool
    {Returns true if the subgroups is strongly closed}
    SC:= true;
    if IsWeaklyClosed(F,P) eq false then return false; end if;

    X:= {x`subgroup: x in Subgroups(P)};
    for x in X do 
        xC:= ConjugacyClass(F,x);  
        for w in xC do
            if w subset P eq false then return false; end if; 
        end for;
    end for; 
    return SC;
end intrinsic;



intrinsic AutomorphismGroup(F::FusionSystem,P::Grp)-> GrpAuto
    {Calculates the automorphism group of P}
    SS:= F`subgroups;
    Essentials:= F`essentials;
    B:= F`borel;
    S:= F`group;
    if assigned(F`fusiongraph) eq false then 
              F`fusiongraph, F`maps:= FusionGraph(F); 
          end if; 
    Gamma:= F`fusiongraph;
    Theta := F`maps; 

    V:= Vertices(Gamma);
    IP:= V!Index(SS,P);

    ComponentP:= Setseq(IdentifyFOrbit(F,P));
     
    for x in ComponentP do MakeAutos(SS[Index(x)]); end for;

    AutP:= P`autogrp;

    AP := sub<AutP|>;


    //First we make all the maps between members of ComponentP
     


    for v in ComponentP do 
    Theta[[Index(v),Index(v)]]:= Identity(SS[Index(v)]`autogrp); 
    end for;

    for i in[1.. #ComponentP] do
        for j in [i+1.. #ComponentP] do
            ii:= ComponentP[i];jj:= ComponentP[j]; 
            Geo:=Geodesic(ii,jj); 
            gg := Identity(SS[Index(ii)]`autogrp); 
            for iii:= 1 to #Geo-1 do 
                gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii+1])]];  
            end for;
             Theta[[Index(ii),Index(jj)]]:= gg;
            gg := Identity(SS[Index(jj)]`autogrp); 
            
            for iii:= #Geo to 2 by -1 do 
                gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii-1])]];  
            end for;
            Theta[[Index(jj),Index(ii)]]:= gg; 
        end for;
    end for;

    TranB:= AssociativeArray(ComponentP);
    for x in ComponentP do
        TranB[x]:= Transversal(B,Normalizer(B,SS[Index(x)])); 
    end for;



    CP:= CartesianProduct(Essentials,ComponentP);
    PsinEs:=AssociativeArray(CP);
    for E in Essentials do 
        if E eq S then continue; end if;
        for xx in  ComponentP do 
                PsinEs[<E,xx>]:= [b:b in TranB[xx]|SS[Index(xx)]^b subset E]; 
        end for;
    end for;


    

    //Now we start building AP=Aut_F(P)

    AP:= AutYX(Normalizer(B,P),P);

    for ii in ComponentP do
        R := SS[Index(ii)]; 
        if R eq P then continue; end if; 
        AR := AutYX(Normalizer(B,R),R);
            AP := sub<AutP|AP,{Theta[[Index(IP),Index(ii)]]*gg*Theta[[Index(ii),Index(IP)]]: gg in Generators(AR) }>; 
    end for;
     
    for ii in ComponentP do R := SS[Index(ii)]; 
        if R eq P then continue ii; end if; 
        for jj in ComponentP do T := SS[Index(jj)]; 
        if T in {P, R} then continue jj; end if; 
        AP := sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*Theta[[Index(ii),Index(jj)]]*Theta[[Index(jj),Index(IP)]]>;
        end for;
    end for;
        
     
      
     
        for ee in [2..#Essentials ] do 
             E:= Essentials[ee]; 
             AE:= F`essentialautos[ee];
    Done:={};
             for ii in ComponentP do 
                R:= SS[Index(ii)];
                for b in PsinEs[<E,ii>] do
                    Rb:= R^b; if Rb in Done then continue b; end if;
                    cb:=ConjtoHom(R,Rb,b);
                    cb1:=ConjtoHom(Rb,R,b^-1);
                    OO,AFRb, TT:= AutOrbit(E,Rb,AE); 
                    gamma:= {Theta[[Index(IP),Index(ii)]]*cb*gg*cb1*Theta[[Index(ii),Index(IP)]]:gg in Generators(AFRb)};
                    AP:=sub<AutP|AP,gamma>;
                    for tt in TT do
                        Rbtt:= SubMap(tt,S,Rb);
                        for jj in ComponentP do a,d:=IsConjugate(B,Rbtt,SS[Index(jj)]); 
                        if a then kk:= jj;break; end if; 
                        end for; //jj
                        cd1:= ConjtoHom(SS[Index(kk)], Rbtt, d^-1);
                        ThetaRbtoRbtt:= cb1*Theta[[Index(ii),Index(kk)]]*cd1;
                    AP:=sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*cb*ThetaRbtoRbtt*tt^-1*cb1*Theta[[Index(ii),Index(IP)]]>;
                    end for; //tt
                    Done := Done join Seqset(OO);
                end for; //b
            end for; //ii
        end for;//ee
        return AP;
end intrinsic;





