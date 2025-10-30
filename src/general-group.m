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
	if assigned(x`autogrp) then 
		return; 
	end if;
	x`autogrp := AutomorphismGroup(x);
	x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp);
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
		if (a(H) eq H) eq false then 
			return false; 
		end if;
	end for;
	return true;
end intrinsic;



intrinsic IsInvariant(A::GrpAuto,G::Grp,H::Grp)->Bool
	{Checks if subgroup H is invariant under the automorphisms A of G }
	require H subset G:"second term is not a subgroup of first";
	MakeAutos(G);
	for a in Generators(A) do
		if (a(H) eq H) eq false then 
			return false; 
		end if;
	end for;
	return true;
end intrinsic;



intrinsic IsStronglypEmbeddedMod(G::Grp,ker::Grp,p::RngIntElt)->Bool
	{Determines whether G/ker has a strongly p-embedded subgroup}
	Sylow:=sub<G|SylowSubgroup(G,p),ker>; 
	if IsNormal(G,Sylow) then 
		return false; 
	end if;
	SSylow:= {sub<G|x`subgroup,ker>:x in Subgroups(Sylow:OrderEqual:=p*#ker)}; 
	HS:= sub<G|{Normalizer(G,x):x in SSylow}>;
	HS:= sub<G|HS,Normalizer(G,Sylow)>;
	if #HS eq #G then 
		return false; 
	end if;
	return true;
end intrinsic;



intrinsic IsStronglypEmbedded(G::Grp,p::RngIntElt)->Bool
	{returns true if G has a strongly p-embedded subgroup}
	require #G mod p eq 0:"the group has trivial Sylow p-subgroup";
	Sylow:=SylowSubgroup(G,p);
	if #pCore(G,p) ne 1 then 
		return false; 
	end if;
	CCl:= ConjugacyClasses(Sylow); 
	XX:={x[3]: x in CCl|x[1] eq p}; 
	if #XX ne p-1 and IsSoluble(G) then 
		return false; 
	end if; 
	RR:=[];
	HS:= Normalizer(G,Sylow);
	F:= ConjugacyClasses(HS); 
	for x in F do 
		if x[1] eq p then 
			HS:=sub<G|HS, Normalizer(G,sub<G|x[3]>)>; 
		end if;
	    if HS eq G then 
	    	return false; 
	    end if;
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
	if Centralizer(S,P) subset P then 
	 	return true; 
	end if;
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



intrinsic IsRadical(S::Grp,P::Grp)->Boolean
	{Checks if P is a radical subgroup of S}
	A:=AutYX(Normalizer(S,P),P);
	Ap:= SubMap(P`autopermmap,P`autoperm ,A);
	Inner:= Inn(P);
	Innerp:= SubMap(P`autopermmap,P`autoperm ,Inner);
	RadTest:=#(Ap meet pCore(P`autoperm, FactoredOrder(S)[1][1])) eq  #Innerp;
	return RadTest;
end intrinsic;



intrinsic NormalizerTower(S::Grp,E::Grp)->SeqEnum
	{Creates a normalizer tower}

	NT:= [Normalizer(S,E)];
	while NT[#NT] ne S do Append(~NT,Normalizer(S,NT[#NT])); end while;
	return NT;
end intrinsic; 



intrinsic AllMaximalSubgroups(G)-> SeqEnum
	{Creates all maximal subgroups of G}
	 
	M:= MaximalSubgroups(G);
	AM:=[];
	for x in M do 
		m:= x`subgroup;Index(G,m); t:= Transversal(G,m); 
		for y in t do Append(~AM,m^y); end for;
	end for; 
	return AM;
end intrinsic;



intrinsic MaximalOverGroups(G::Grp,H::Grp, p::RngIntElt)-> SeqEnum
	{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}
	M:= MaximalSubgroups(G);
	AM:=[];
	for x in M do 
		m:= x`subgroup; Cm:= ConjugacyClasses(Sylow(m,p)); J:= Sylow(H,p);
		
		if #m mod #H eq 0 then  W:={xx[3]:xx in Cm|IsConjugate(G,xx[3],J.1)}; if #W ne 0 then
			t:= Transversal(G,m); 
			for y in t do Append(~AM,m^y); end for;
		end if; end if;
	end for; 
	AMH:=[];
	for x in AM do
		if H subset x then Append(~AMH, x);end if;
	end for;
	return Set(AMH);
end intrinsic;



intrinsic OverGroups(G::Grp,H::Grp)-> SeqEnum
	{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}
	AllOvers:={};
	ONew:={G};
	while ONew ne {H} do 
		AllOvers := AllOvers join ONew;#AllOvers;
		Overs := ONew; 
		ONew:={H};
			for x in Overs do
				ONew:= ONew join MaximalOverGroups(x,H); 
			end for;
	end while;
	return AllOvers;
end intrinsic;



intrinsic OverGroupsSylowEmbedded(G::Grp,H::Grp,INN::Grp,p::RngIntElt)-> SeqEnum
	{Creates overgrps of H in G which have H as a sylow p-subgroup and such that they are generated by conjugates of H. To get the full list we will use the Fratinni argument}

	require IsPrime(p):"p is not a prime";
	require #H mod p eq 0 :"H does not have order divisible by p";
	require IsNormal(G,INN) :"Inn not normal in G";

	J:= Sylow(H,p);
	JJ, mp:= J/INN;

	require IsCyclic(JJ) :"H/Inn does not have cyclic sylow subgroups";

	NGH:= Normalizer(G,J);


	JJJ:= Generators(JJ); JJJ:= {j: j in JJJ|Order(j) eq #JJ};
	J1:= Inverse(mp)(Rep(JJJ)); // So J1 generates J mod INN and it is an element



	AllOvers:={};
	ONew:={SubnormalClosure(G,H)};
	while ONew ne {H} do 
	    Overs := ONew diff AllOvers;  j:= 0;
		AllOvers := AllOvers join ONew; 
		ONew:={H};
			for x in Overs do  j:= j+1;  
				  y:=SubnormalClosure(x,H); 
				M:= MaximalSubgroups(y);
				AM:=[];
				for mm in M do 
					m:= mm`subgroup; 
					if INN subset m then 
					    if #m mod #H eq 0 then  
						Cm:= ConjugacyClasses(m);
						for cc in Cm do  
							aa, bb := IsConjugate(y,cc[3],J1); 
							
							if aa then  mbb:= m^bb;  
								for am in AM do 
	                                aaa, bbb := IsConjugate(NGH,am,mbb); 
	                                if aaa then continue cc;  end if;
								end for;  
								AM:= AM cat [SubnormalClosure(mbb,H)]; 
							end if; 
						end for;//cc		 
					    end if;//#m mod #H
					end if;//II subset m
				end for; //mm in M

			 
		AM:= Seqset(AM);
				 
			for xx in AM do 
				xxin := false;
				for yy in ONew do 
					if xx subset yy then 
						xxin := true; 
						continue xx; 
					end if; 
				end for;
				if xxin eq false then
					ONew := ONew join {xx}; end if;
			end for; 

			ONew1 :={Rep(ONew)};
				for on in ONew do OUT := true;
					for on1 in ONew1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
				if OUT then ONew1 := ONew1 join{on}; end if;
				end for;
	ONew :=ONew1;
	 
			end for;
	end while;
	 




	AllOvers1:= {Rep(AllOvers)};


	for on in AllOvers do OUT := true;
					for on1 in AllOvers1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
				if OUT then AllOvers1 := AllOvers1 join{on}; end if;
				end for;
	AllOvers:= AllOvers1;

	AAM:=[x: x in AllOvers|Index(x,H) mod p ne 0];
	return AAM;
end intrinsic;




intrinsic SubgroupsAutClasses(S::PCGrp)-> SeqEnum
	{Calculates centric subgroups of S up to Aut(S) conjugacy}
	SS:= [x`subgroup:x in Subgroups(S)|IsSCentric(S,x`subgroup)];
	A,beta:= Holomorph(S);
	SSb :=[SubMap(beta,A,x):x in SS];
	TT:=[];K:={1};k:=1;
	for i := 1 to #SSb do 
		T:= SSb[i]; 
		if #K ne 0 then 
			k:= Min(K); 
		end if; 
		K:={};
	    for j := k to i-1 do 
	    	print i,j;
	        if #T ne #SSb[j] then 
	        	continue j; 
	        else K:= K join {j};
	        end if;
	        if IsConjugate(A, T,SSb[j]) eq true then 
	        	continue i; 
	        end if;
	    end for;
	    Append(~TT,SS[i]);
	end for;
	return TT;
end intrinsic;



intrinsic SemiDirectProduct(V::ModGrp:Perm:= false)-> Grp
	{Constructs the semidirect product of a module and the module for the group}
	G:= Group(V);
	F:= Field(V);
	T:= TrivialModule(G,F);
	W:= DirectSum(T,V);
	G1:= MatrixGroup(W);
	n:= Dimension(W);
	H:= GL(n,F);
	K:= sub<H|G1>;
	for k in [1..n-1] do 
		J:= Identity(H);
		J:= Eltseq(J);
		J[k*n+1]:= Identity(F);
		J:= H!J;  
		K:= sub<H|J,K>;
	end for;
	if Perm then 
		K:= CosetImage(K,G1); 
	end if;
	return K;
end intrinsic;




intrinsic Blackburn(p::RngIntElt,n::RngIntElt,alpha::RngIntElt,beta::RngIntElt,gamma::RngIntElt,delta::RngIntElt)->Grp
	{constructs Blackburns metaabelian maximal class group of order p^n}
	require IsPrime(p) : "the first element must be a prime"; 
	require n eq 6:"this is only implemented for n=6";


	        S<s, s1,s2,s3,s4,s5> := Group<s, s1,s2,s3,s4,s5|
	        (s1,s)*s2^(-1),
	        (s2,s)*s3^(-1),
	        (s3,s)*s4^(-1),
	        (s4,s)*s5^(-1),
	         (s,s5), 
	        
	        //(32) from Blackburn.
	        (s1,s2)*s5^(-beta)*s4^(-alpha),//(33)
	        (s1,s3)*s5^(-alpha),//(34)
	        (s1,s4),//(35)
	        (s1,s5),//(35)

	        s^p*s5^(-delta),//(36)


	        s1^p*s2^Binomial(p,2)*s3^Binomial(p,3)*s4^Binomial(p,4)*s5^Binomial(p,5)*s5^(-gamma),//(37)
	        //s2^p,s3^p,s4^p, 
	        
	       s2^p*s3^Binomial(p,2)*s4^Binomial(p,3)*s5^Binomial(p,4),

	        s3^p*s4^Binomial(p,2)*s5^Binomial(p,3),

	        s4^p*s5^Binomial(p,2),

	        s5^p>;S:= PCGroup(S);
	 return S;
 end intrinsic;



 intrinsic homeq(x::Map,y::Map)->Bool{checks if two maps are equal}
	X:=Domain(x); 
	X1:= Image(x);
	Y:=Domain(y); 
	Y1 := Image(y);
	if X ne Y  or X1 ne Y1 then 
	    return false; 
	end if;
	gens:=Generators(X);
    for gg in gens do
    	if x(gg) ne y(gg) then 
        	return false; 
        end if;
    end for;
	return true;
 end intrinsic;



  intrinsic IsQuaternionOrCyclic(G::Grp)->Bool
	 {Is a quaternion or a cyclic group}
	 if #G eq 1 then 
	 	return true;
	 end if; 
	 p:= FactoredOrder(G)[1][1];
	 C:= ConjugacyClasses(G);
	 if # {x: x in C|x[1] eq p} eq p-1 then 
	 	return true; 
	 end if;
	 return false;
 end intrinsic;



intrinsic piResidual(G::Grp, pi::SeqEnum)-> Grp
	{Determine O^\pi(G)}
	JJ:= PrimeFactors(#G);
	Resid:=sub<G|>;
	for x in JJ do 	
		if x in pi then 
			continue x; 
		end if;
		P:= Sylow(G,x);
		N:= NormalClosure(G,P);
		Resid:= sub<G|Resid,N>;
	end for;
	return Resid;
end intrinsic;



intrinsic pResidual(G::Grp, p::RngIntElt)-> Grp
	{Determine O^p(G)}
	R:=piResidual(G,[p]);
	return R;
end intrinsic;



intrinsic piprimeResidual(G::Grp, pi :: SeqEnum)-> Grp
	{Determine O^p(G)}
	JJ:= PrimeFactors(#G);
	pistar:= {w: w in JJ| (w in pi) eq false};
	R:=piResidual(G,pistar);
	return R;
end intrinsic;



intrinsic pprimeResidual(G::Grp, p::RngIntElt)-> Grp
	{Determine O^p(G)}
	P:= Sylow(G,p);
	return NormalClosure(G,P);
end intrinsic;



intrinsic IsMaximalClass(G::Grp)-> Bool
	{Check if G is maximal class}
	f:= FactoredOrder(G);
	require #f eq 1 : "the group  is not a p-group"; 
	n:= NilpotencyClass(G);
	return n eq (f[1][2]-1);
end intrinsic;



intrinsic MaximalAbelian(G::Grp)-> Bool
	{Check if G gas a maximal abelian subgroup}
	f:= FactoredOrder(G);
	require #f eq 1:"the group  is not a p-group"; 
	M:= MaximalSubgroups(G);
	for x in M do 
	    y:= x`subgroup; 
	    if IsAbelian(y) then 
	    	return true; 
	    end if; 
	end for;
	return  false;
end intrinsic;



intrinsic SubnormalClosure(G::Grp,T::Grp)-> Grp
	{Determines the subnormal closure of $T$ in G}
	SNew:= NormalClosure(G,T);
	SN:= G;
	while SN ne SNew do
		SN:= SNew;
		SNew:= NormalClosure(SN,T);
	end while;
	return SN;
end intrinsic;



intrinsic Centralizer(G::Grp,A::Grp,B:Grp)->Grp
	{Return the centralizer in G of the the quotient A/B}
	require IsNormal(G,B): "B is not normalized by G"; 
	K:= Normalizer(G,A);
	Q,a:= K/B;
	C := Centralizer(Q,a(A));
	C := SubInvMap(a,K,C); 
	return C;
end intrinsic;
