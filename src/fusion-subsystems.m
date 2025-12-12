// Functions that calculate certain subsystems of a given fusion system.


intrinsic IsSubsystem(F_1::FusionSystem, F_2:: FusionSystem) -> Bool
	{Determine if F_2 is a subsystem of F_1}
	// We simply need each AutF_2(E) < AutF_1(E) for all E essential, then all compositions/restrictions are in F_2
	// Should probably check this in more detail
	if not F_1`group subset F_2`group then
		return false;
	end if;
	for i in [1..F_1`essentials] do
		E := F_1`essentials[i];
		AE := F_1`essentialautos[i];
		if not AE subset AutomorphismGroup(F_2, E) then
			return false;
		end if;
	end for; 
	return true;
end intrinsic;



// Calculate quotient subsystem for a strongly closed subgroup



// Calculating restriction to a strongly closed subgroup


intrinsic RestrictionSubsystem(F::FusionSystem, T::Grp) -> FusionSystem
	{Given T strongly closed in F return F restricted to T}

end intrinsic;

// Calculating O^p(F)

intrinsic HyperFocalSystem(F::FusionSystem) -> FusionSystem
	{Calculates the hyperfocal system O^p(F)}
	hyp := HyperFocalSubgroup(F);
	EA := [Inn(hyp)];
end intrinsic;

// Calculating residual subsystem O^{p'}(F)


function CalculateAutFES(S,E, AutFS, AutFE)
	p := GetPrime(S);
	permmap := E`autopermmap;
	// Calculate N_\Aut_\F(S)(E)
	N_AutFS := sub<AutFS | {alpha : alpha in Generators(AutFS) | alpha(E) eq E}>;
	Opprime := pprimeResidual(permmap(AutFE), p);
	AutFES_gens := [];
	for alpha in Generators(N_AutFS) do 
		// Determine if \alpha|_E in O^{p'}(Aut_\F(E))
		alphaE := AutFE!hom<E->E | x:->alpha(x)>;
		if permmap(alphaE) in Opprime then
			Append(~AutFES_gens, alpha);
		end if;
	end for;
	AutFES := sub<AutFS | AutFES_gens>;
	return AutFES;
end function;



intrinsic CalculateAutSResidual(F::FusionSystem) -> Grp
	{calculate Aut_F^0(S)}
	S := F`group;
	AutFS := F`essentialautos[1];
	AutFES_list := [];
	for i in [2..#F`essentials] do 
		AutFES := CalculateAutFES(S,F`essentials[i], AutFS, F`essentialautos[i]);
		Append(~AutFES_list, AutFES);
	end for;
	AutF0S := sub<AutFS | AutFES_list, Inn(S)>;
	print #AutF0S/#Inn(S);
	return AutF0S;
end intrinsic;



intrinsic IsResidual(F::FusionSystem) -> Bool
	{returns if F is its residual subsystem}
	S := F`group;
	MakeAutos(S);
	permmap := S`autopermmap;
	return CalculateAutSResidual(F) eq F`essentialautos[1];
end intrinsic;



intrinsic CalculateSubResidual(F::FusionSystem) -> FusionSystem
	{calculate the smallest subsystem F_0 containing all pprime residual automisers}
	S := F`group;
	automisers := [CalculateAutSResidual(F)];
	for i in [2..#F`essentials] do 
		E := F`essentials[i];
		permmap := E`autopermmap;
		AutFE := permmap(F`essentialautos[i]);
		// Get Opprime as a subgroup of the permutation representation
		Opprime := pprimeResidual(AutFE, GetPrime(S));
		Append(automisers, SubInvMap(permmap, F`essentialautos[i], Opprime));
	end for;
	F0 := CreateFusionSystem(automisers);
	return F0;
end intrinsic;






