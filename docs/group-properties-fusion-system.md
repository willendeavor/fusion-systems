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
