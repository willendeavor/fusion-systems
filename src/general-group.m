// General group theoretic functions






intrinsic SubInvMap(j::Map,K::Grp,W::Grp)-> Grp
	{applies inverse of a map to a subgroup}
	k:= Inverse(j);
	return sub<K| {k(x): x in Generators(W)},Kernel(j)>;
end intrinsic;



intrinsic SubMap(j::Map,K::Grp,W::Grp)-> Grp{applies a map to a subgroup}
	return sub<K| { j(x): x in Generators(W)}>;
end intrinsic;



intrinsic ConjtoHom(X::Grp, Y::Grp,g::GrpElt)->GrpHom
	{Return the homomorphism induced by conjugation}
	require  X^g subset Y: "X not conjugate in Y by g"; 
	alpha:=hom<X->Y|x:->x^g>;
	return alpha;
end intrinsic;



intrinsic ConjtoAuto(X::Grp,g::GrpElt,AA::GrpAuto)->GrpAutoElt
	{Return the automorphism induced by conjugation}
	require  X^g subset X: "X not not normalized by g"; 
	MakeAutos(X);
	alpha:=AA!hom<X->X|x:->x^g>;
	return alpha;
end intrinsic;



intrinsic MakeAutos(x::Grp)
	{Makes an automorphism group and its permutation representation}
	if assigned(x`autogrp) then return; end if;
	 x`autogrp := AutomorphismGroup(x);
	    x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp); 
	   // return x`autogrp;
end intrinsic;



intrinsic AutYX(Y::Grp,X::Grp)-> GrpAuto
	{Creates the automorphism group of X induced by conjugation by elements of Y}
	require IsNormal(Y,X):"X is not a normal subgroup of Y";
	MakeAutos(X); 
	A:= sub<X`autogrp|{ConjtoHom(X,X,y):y in Generators(Y)}>;
	return A;
end intrinsic;



intrinsic Inn(X::Grp)-> GrpAuto
	{Creates the inner automorphism group of X}
	A:= AutYX(X,X);
	return A;
end intrinsic;



intrinsic Automiser(G::Grp,P::Grp)->GrpAuto
	{Given a subgroup of a group, determine the automiser of that subgroup}
	H:= Normalizer(G,P);
	A:=AutYX(H,P);
	return(A);
end intrinsic;



intrinsic Automizer(G::Grp,P::Grp)->GrpAuto{Just another name for Automiser}
	return Automiser(G,P);
end intrinsic;



intrinsic AutomiserGens(G::Grp,P::Grp)->SetEnum
	{Given a subgroup of a group, determine the a set of automorphism which generate the automiser}
	H:= Normalizer(G,P);
	A:= {ConjtoHom(P,P,y):y in Generators(H)};
	return A;
end intrinsic;



intrinsic IsCharacteristic(G::Grp,H::Grp)->Bool
	{Checks if subgroup H of G is characteristic}
	require H subset G:"second term is not a subgroup of first";
	MakeAutos(G);
	for a in Generators(G`autogrp) do
	if (a(H) eq H) eq false then return false; end if;
	end for;
	return true;
end intrinsic;



intrinsic IsInvariant(A::GrpAuto,G::Grp,H::Grp)->Bool
	{Checks if subgroup H is invariant under the automorphisms A of G }
	require H subset G:"second term is not a subgroup of first";
	MakeAutos(G);
	for a in Generators(A) do
	if (a(H) eq H) eq false then return false; end if;
	end for;
	return true;
end intrinsic;

intrinsic IsStronglypEmbeddedMod(G::Grp,ker::Grp,p::RngIntElt)->Bool
	{Determines whether G/ker has a strongly p-embedded subgroup}
	Sylow:=sub<G|SylowSubgroup(G,p),ker>; 
	  if IsNormal(G,Sylow) then return false; end if;
	        SSylow:= {sub<G|x`subgroup,ker>:x in Subgroups(Sylow:OrderEqual:=p*#ker)}; 
	        HS:= sub<G|{Normalizer(G,x):x in SSylow}>;
	        HS:= sub<G|HS,Normalizer(G,Sylow)>;
	       if #HS eq #G then return false; end if;
	return true;
end intrinsic;



intrinsic IsStronglypEmbedded(G::Grp,p::RngIntElt)->Bool
	{returns true if G has a strongly p-embedded subgroup}
	require #G mod p eq 0:"the group has trivial Sylow p-subgroup";

	Sylow:=SylowSubgroup(G,p);

	 if #pCore(G,p) ne 1 then return false; end if;
	 CCl:= ConjugacyClasses(Sylow); 
	 XX:={x[3]: x in CCl|x[1] eq p}; 
	 if #XX ne p-1 and  IsSoluble(G) then return false; end if; 
	   RR:=[];
	   HS:= Normalizer(G,Sylow);
	   F:= ConjugacyClasses(HS); 
	   for x in F do 
		   if x[1] eq p then 
		    	HS:=sub<G|HS, Normalizer(G,sub<G|x[3]>)>; 
		   end if;
	       if HS eq G then return false; end if;
	   end for; 
	return true;
end intrinsic;



intrinsic RandomAuto(A::GrpAuto)->Map
	{Selects a  random element from the automorphism group}
	a,B:=  PermutationRepresentation(A);
	alpha := Inverse(a)(Random(B));
	return alpha;
end intrinsic;



intrinsic AutOrbit(P::Grp,Q::Grp,AFP::GrpAuto:Printing:=false)->SeqEnum,Grp,SeqEnum
	{Determines the orbits of a subgroup Q under the automorphism group AFPQ of 
	of P}
   require Q subset P:"the second term in not a subgroup of the first";
    MakeAutos(P);
    N:= Normalizer(P,Q);
    gamma:= P`autopermmap;
    Pp:=P`autoperm;
    StB:= sub<AFP|{ ConjtoAuto(P,n,AFP):n in Generators(N)}>; 
    StBp:= sub<Pp| {gamma(ConjtoAuto(P,n,P`autogrp)):n in Generators(N)}>;
    T:= Transversal(P,N); 
    Elt:= [ConjtoAuto(P,n,AFP):n in T];
    EltOrig:=Elt;
    Orb:= [Q^n:n in T];

    afp:= #AFP;
    while afp ne #StB*#Orb do  if Printing then  afp,  #StB*#Orb; end if; 
        alpha:= RandomAuto(AFP);  
    
            Q:= Orb[1];
            Qwalpha :=  SubMap(alpha, P, Q);
             y:= Index(Orb,Qwalpha);
             //if y ne 0, then Qwalpha is in the orbit and we add a generator to StB. 
             if y ne 0 then
                alphanew :=   alpha*Elt[y]^-1; 
                alphanewp:=gamma(P`autogrp!alphanew); 
                if alphanewp in StBp eq false then
                    StB:= sub<AFP|StB,alphanew>; 
              StBp:= sub<P`autoperm|StBp,alphanewp>;
                    if  afp eq #StB*#Orb then  return Orb, StB, Elt; end if;
              end if;  
             end if;
             //if y eq 0, then we have a new element for the orbit.
             if y eq 0 then
                    Eltw:= [AFP!(e*alpha):e in EltOrig];
                    Orbw:= [e(Q): e in Eltw];       
                    Orb:= Orb cat Orbw;
                    Elt := Elt cat Eltw; 
                    if  afp eq #StB*#Orb then   return Orb, StB, Elt ;end if;
             end if;
    end while;    
    return Orb, StB, Elt;
end intrinsic;




intrinsic AutOrbitOld(P::Grp,Q::Grp,AFP::GrpAuto)->SeqEnum,Grp,SeqEnum
	{Determines the orbits of a subgroup Q under the automorphism group A of of P}
    require Q subset P:"the second term in not a subgroup of the first";
    MakeAutos(P); 
    N:= Normalizer(P,Q);
    gamma:= P`autopermmap;
    Pp:=P`autoperm;
    StB:= sub<AFP|{ ConjtoHom(P, P,n):n in Generators(N)}>; 
    StBp:= sub<Pp| {gamma(P`autogrp!ConjtoHom(P, P,n)):n in Generators(N)}>;
    T:= Transversal(P,N); 
    Elt:= [AFP!ConjtoHom(P, P,n):n in T];
    Orb:= [Q^n:n in T];

    afp:= #AFP;
    while afp ne #StB*#Orb do  
        alpha:= RandomAuto(AFP); 
        for w in [1..#Orb] do
            W:= Orb[w];
            Qwalpha :=  SubMap(alpha, P, W);
             y:= Index(Orb,Qwalpha);
             //if y ne 0, then Qwalpha is in the orbit and we add a generator to StB. 
             if y ne 0 then
                alphanew :=   Elt[w]*alpha*Elt[y]^-1; 
                alphanewp:=gamma(P`autogrp!alphanew); 
                 if alphanewp in StBp eq false then
                    StB:= sub<AFP|StB,alphanew>; 
               StBp:= sub<P`autoperm|StBp,alphanewp>;
                    if  afp eq #StB*#Orb then    return Orb, StB, Elt; end if;
              end if; 
             end if;
             //if y eq 0, then we have a new element for the orbit.
             if y eq 0 then 
                    Nwalpha:= Normalizer(P,Qwalpha); 
                    Tw:= Transversal(P,Nwalpha);
                    Eltw:= [AFP!(Elt[w]*alpha*ConjtoHom(P, P,n)):n in Tw];
                    Orbw:= [Qwalpha^n:n in Tw];
                    Orb:= Orb cat Orbw;
                    Elt := Elt cat Eltw; 
                    if  afp eq #StB*#Orb then   return Orb, StB, Elt; end if;
             end if;
        end for;  

    end while;
    
    return Orb, StB, Elt;
end intrinsic;



intrinsic AutOrbit(P::Grp,Q::GrpElt,AFP::GrpAuto)->SeqEnum,Grp,SeqEnum
	{Determines the orbits of an element Q under the automorphism group A of 
	of Aut(P)}
    require Q in P:"the second term in not a subgroup of the first";
    Orb:= [Q];
    Elt:= [Identity(AFP)];
    NN:= sub<AFP| >;
    while #AFP ne #NN*#Orb do
        xx:= RandomAuto(AFP);
        for W in Orb do
            Qwx :=  xx(W);
            w:= Index(Orb,W);
                if Qwx in Orb then y:= Index(Orb,Qwx);
                    NN:= sub<AFP|NN,Elt[w]*xx*Elt[y]^-1>;
                else
                    Orb := Append(Orb,Qwx);   Elt := Append(Elt,Elt[w]*xx); 
                end if;
        end for; 
    end while;
    return Orb, NN, Elt;
end intrinsic;



intrinsic IsSCentric(S::Grp,P::Grp)->Bool
	{Is the subgroup P of S  S-centric?}
	require P subset S:" the second term is not a subgroup of the first";
	 if Centralizer(S,P) subset P then return true; end if;
	 return false;
end intrinsic;



intrinsic IsStronglypSylow(Q::Grp)->Bool, Bool
	{Can Q be the Sylow subgroup of a group with a strongly p-embedded Sylow p? Also returns whether cyclic or quaternion}

	p:= FactoredOrder(Q)[1][1];

	QC:=IsQuaternionOrCyclic(Q);
	    if QC eq false then
	   
	X:=PCGroup(CyclicGroup(p));
	Y:=X;
	Testers:={};
	for i := 1 to 7 do 
	Y:= DirectProduct(Y,X); Testers:= Testers join{Y};
	end for;

	Testers:= Testers join{
	PCGroup(ClassicalSylow(SU(3,p), p)),
	PCGroup(ClassicalSylow(SU(3,p^2), p))};
	if p eq 3 then Testers:= Testers join {PCGroup(Sylow(PGammaL(2,8),3))}; end if;
	if p eq 2   then Testers:= Testers join {PCGroup(Sylow(ChevalleyGroup("2B",2,8),2))}; end if;
	if p eq 5   then Y:= sub<Sym(25)|
	   (6, 10, 9, 8, 7)(11, 14, 12, 15, 13)(16, 18, 20, 17, 19)(21, 22, 23, 24, 25),
	    (1, 11, 23, 10, 19, 2, 12, 24, 6, 20, 3, 13, 25, 7, 16, 4, 14, 21, 8, 17, 5,
	        15, 22, 9, 18)>; 
	Testers:= Testers join {PCGroup(Y)}; end if;

	 
	        ///If QC is not quaternion or cyclic, then Out_F(P) cannot be soluble. 
	        //So there should be 3 or more prime factors by ///Burnside#s p^aq^b theorem. 
	        //Next we know that if not quaternion or cyclic, then Q should be isomorphic to one of 
	        //the Sylow's listed above. Because we are assuming that $|S|$ is small, testers suffices. Can easily add more.
	        //// We check that |Q|\le p^7 just in case.
	        if #Q le p^7 then TesT:= false;
	            for SP in Testers do 
	             if    IsIsomorphic(Q,SP) then TesT := true; break; end if;
	            end for;
	         if TesT eq false  then return false,_; end if;
	        end if;
	    end if;
	return true, QC;
end intrinsic;



intrinsic RadicalTest(S::Grp,P::Grp)->Boolean{Checks if P could be a radical subgroup}
	A:=AutYX(Normalizer(S,P),P);
	Ap:= SubMap(P`autopermmap,P`autoperm ,A);
	Inner:= Inn(P);
	Innerp:= SubMap(P`autopermmap,P`autoperm ,Inner);
	RadTest:=#(Ap meet pCore(P`autoperm, FactoredOrder(S)[1][1])) eq  #Innerp;
	return RadTest;
end intrinsic;




