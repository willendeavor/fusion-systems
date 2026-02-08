// Adds support for calculating the direct product of n-fusion systems



// Define a new type for direct products, makes keeping track easier
declare type DirectProductGroup;
declare attributes DirectProductGroup: group, embed, proj, factors;
declare attributes FusionSystem: directproductgrp, factors;

intrinsic Print(D::DirectProductGroup){}
	print(D`group);
end intrinsic;


intrinsic MakeDirectProductGroup(G_factors::SeqEnum[Grp]) -> DirectProductGroup
	{given the factors make all aspects of a DirectProductGroup}
	G := New(DirectProductGroup);
	try
		G`group, G`embed, G`proj := DirectProduct(G_factors);
	catch e
		error "DirectProduct embedding/projection unsupported for this group type";
	end try;
	G`factors := G_factors;
	return G;
end intrinsic;


intrinsic MakeDirectProductGroup(G_1::Grp, G_2::Grp) -> DirectProductGroup
	{two argument version}
	return MakeDirectProductGroup([G_1, G_2]);
end intrinsic;


intrinsic TransportDirectProductGroup(D::DirectProductGroup, phi::Map) -> DirectProductGroup
	{Given a DirectProductGroup D and a phi: D -> G remake phi(D) in G}
	G := New(DirectProductGroup);
	G`group := phi(D`group);
	G_emb := [];
	G_proj := [];
	for emb in D`embed do 
		D_i := Image(emb);
		G_i := phi(D_i);
	end for;
end intrinsic;


intrinsic AutEltRestriction(phi::GrpAutoElt, H::Grp) -> GrpAutoElt
	{Given phi an automorphism of some G normalising H le G return the restriction}
	require phi(H) eq H : "phi does not normalise H";
	MakeAutos(H);
	phi_H := H`autogrp!hom<H -> H | x :-> phi(x)>;
	return phi_H;
end intrinsic;


intrinsic AutRestriction(A::GrpAuto, H::Grp) -> GrpAuto
	{Given A leq N_Aut(G)(H) and H leq G return A restricted to H}
	gens := [AutEltRestriction(phi, H) : phi in Generators(A)];
	A_H := sub<H`autogrp | gens>;
	return A_H;
end intrinsic;



// Unused but might be handy if we ever want to calculate hands on
intrinsic AutDirectProduct(a::GrpAutoElt, b::GrpAutoElt) -> GrpAutoElt
	{Given a in Aut(A) and b in Aut(B) return a x b in Aut(A x B)}
	A := Domain(a);
	B := Domain(b);
	AB,embed,proj := DirectProduct(A,B);
	MakeAutos(AB);
	ab := hom<AB -> AB | x:-> embed[1](a(proj[1](x)))*embed[2](b(proj[2](x)))>;
	ab_real := AB`autogrp!ab;
	return ab_real;
end intrinsic;


// Only used with the overgroup option
intrinsic AutDirectProduct(A_1::GrpAuto, A_2::GrpAuto : Overgroup := false) -> GrpAuto
	{Given A_i < Aut(G_i) return A_1 x A_2 < Aut(G_1 x G_2) and if given an overgroup D ensure G_1 x G_2 is a subgroup}
	G_1 := Group(A_1);
	G_2 := Group(A_2);
	if Type(Overgroup) eq DirectProductGroup then 
		embed := Overgroup`embed;
		proj := Overgroup`proj;
		G := sub<Overgroup`group | embed[1](G_1), embed[2](G_2)>;
	else 
		G,embed,proj := DirectProduct(G_1,G_2);
	end if;
	MakeAutos(G);
	// For each generator of A_i embed into Aut(G)
	A_1_gens := [];
	for alpha in Generators(A_1) do 
		alpha_embed := hom<G -> G | x:-> embed[1](alpha(proj[1](x)))*embed[2](proj[2](x))>;
		alpha_real := G`autogrp!alpha_embed;
		Append(~A_1_gens, alpha_real);
	end for;
	A_2_gens := [];
	for alpha in Generators(A_2) do 
		alpha_embed := hom<G -> G | x:-> embed[1](proj[1](x))*embed[2](alpha(proj[2](x)))>;
		alpha_real := G`autogrp!alpha_embed;
		Append(~A_2_gens, alpha_real);
	end for;
	// Take the product A_1 x A_2
	A := sub<G`autogrp | A_1_gens, A_2_gens>;
	return A;
end intrinsic;


// This is now uneccessary since we recursively calculate the fusion systems but keeping it just in case
intrinsic AutDirectProduct(A_list::SeqEnum[GrpAuto] : Overgroup := false) -> GrpAuto 
	{Given a list of groups A_i < Aut(G_i) return the embedding of A_1 ... A_n < Aut(G_1...G_n)}
	// Recursively calculate as (((A_1 x A_2) x A_2) x A_3) x....) x A_n
	A := AutDirectProduct(A_list[1], A_list[2]: Overgroup := Overgroup);
	if #A_list eq 2 then
		return A;
	end if;
	Remove(~A_list, 1);
	Remove(~A_list, 2);
	for A_i in A_list do 
		A := AutDirectProduct(A, A_i: Overgroup := Overgroup);
	end for;
	return A;
end intrinsic;



// This was originally based on calculating a list, hence why we iterate despite only having two factors
intrinsic FusionDirectProduct(F_1::FusionSystem, F_2:: FusionSystem) -> FusionSystem
	{Given two fusion systems F_1 and F_2 return F_1 x F_2}
	F_factors := [F_1, F_2];
	S_factors := [F_i`group : F_i in F_factors];
	try
		S := MakeDirectProductGroup(S_factors);
	catch e
		print "Unable to make a DirectProductGroup";
	end try;
	AutFS_i_list := [F_i`essentialautos[1] : F_i in F_factors];
	// Make the first automiser sequence element, Aut_F(S)
	aut_seq := [AutDirectProduct(AutFS_i_list: Overgroup := S)];
	// The essentials are given by E_i x S_i^* where E_i is F_i-essential and S_i^* is product of all factors except S_i
	for F_i in F_factors do 
		// Get list of Aut_{F_j}(S_j), j neq i
		AutFE := [x : x in AutFS_i_list | x ne F_i`essentialautos[1]];
		AutFE_i_list := Remove(F_i`essentialautos,1);
		for AutFE_i in AutFE_i_list do 
			// Add Aut_{F_i}(E_i) and calculate Aut_F(E), note we maintain position
			AutFEE := Insert(AutFE, Index(F_factors, F_i), AutFE_i);
			Append(~aut_seq, AutDirectProduct(AutFEE: Overgroup := S));
		end for;
	end for;
	F := CreateFusionSystem(aut_seq);
	F`factors := F_factors;
	// Move the factors to the borel so they are subgroups of F`group
	S_factors_new := [F`borelmap(Image(S`embed[i])) : i in [1..#S`factors]];
	F`directproductgrp := MakeDirectProductGroup(S_factors_new);
	return F;
end intrinsic;


intrinsic FusionDirectProduct(F_factors::SeqEnum[FusionSystem]) -> FusionSystem
	{Given a list of fusion systems calculate their direct product}
	if #F_factors eq 1 then
		return F_factors[1];
	end if;
	F := FusionDirectProduct(F_factors[1], F_factors[2]);
	if #F_factors eq 2 then
		return F;
	end if;
	Remove(~F_factors, 1);
	Remove(~F_factors, 2);
	for F_i in F_factors do 
		F := FusionDirectProduct(F, F_i);
	end for;
	return F;
end intrinsic;



//////// Is Indecomposable //////////////////////////////////

/*
Ideas: Start with just for a reduced fusion systems
(1): Decompose S as a direct product of p-groups S_1 x ... x S_n, each of order at least p^3 (otherwise not reduced)
(1a): Do this recursively, 
(2): For each candidate of the i-th factor, find one that is strongly closed in F, repeat for all i
(3): Since O^{p'}(F) = F it must now split so just need to calculate the factor fusion systems either as F|_{S_i} or a different
*/




intrinsic IsIndecomposablee(G::Grp) -> BoolElt, SeqEnum
	{Determines if a group is indecomposable into two factors}
	Ns := NormalSubgroups(G);
	all_normal := [r`subgroup : r in Ns | #(r`subgroup) ne 1 and #(r`subgroup) ne #G ];
	for G_1 in all_normal do 
		complement_candidates := [x : x in all_normal | #x eq #G/#G_1];
		for G_2 in complement_candidates do  
			if IsTrivial(G_1 meet G_2) then  
				return false, [G_1, G_2];	
			end if;
		end for;
	end for;
	return true;
end intrinsic;




function AllSplittings(S)
	// Returns the list of factorisations of a group into a direct product of two groups or false if group is indecomposable
	p := FactoredOrder(S)[1];
	n := FactoredOrder(S)[1][2];
	Ns := NormalSubgroups(S);
	all_normal := [r`subgroup : r in Ns | #(r`subgroup) ne 1 and #(r`subgroup) ne #S ];
	pairs := [];
	for S_1 in all_normal do 
		cands := [x : x in all_normal | #x eq #S/#S_1];
		for S_2 in cands do  
			if IsTrivial(S_1 meet S_2) then  
				Append(~pairs, [S_1, S_2]);			
			end if;
		end for;
	end for;
	return pairs;
end function;



function GetOneSidedEssentials(F, S_factors, i)
	S_i := S_factors[i];
	S_i_star := sub<F`group | [S_factors[j] : j in [x : x in [1..#S_factors] | x ne i]]>;
	essentials_i := [];
	for j in [2..#F`essentials] do 
		if S_i_star subset F`essentials[j] then
			Append(~essentials_i, j);
		end if;
	end for;
	return essentials_i;
end function;


intrinsic OneSidedFusionSystem(F::FusionSystem, S_factors::SeqEnum, i::RngIntElt) -> FusionSystem
	{Creates F_i^bullet = <Aut_F(S), Aut_F(E) | E = S_i^* x E_i>}
	aut_seq_i := [F`essentialautos[j] : j in GetOneSidedEssentials(F, S_factors, i)];
	aut_seq := [F`essentialautos[1]] cat aut_seq_i;
	return CreateFusionSystem(aut_seq);
end intrinsic;



intrinsic FusionSystemDecomposition(F::FusionSystem, S_factors::SeqEnum : return_decomposition := false) -> Bool, SeqEnum
	{Given a reduced fusion system over S and a list of internal subgroups S_factors such that S = \prod S_factors determine if F splits}
	// Importantly this is not F`directproductgrp for a direct product
	S := F`group;
	if not S eq sub<S | S_factors> then
		print "S is not a direct product of the given factors \n";
		return false,_;
	end if;

	for S_i in S_factors do 
		if not IsStronglyClosed(F, S_i) then
			printf "The %o-th factor is not strongly closed \n", Index(S_factors, S_i);
			return false,_;
		end if;
	end for;

	if not return_decomposition then
		return true, _;
	end if;

	// Now we obtain the fusion subsystems over each S_i using the fact that an essential is of the form S_i^* x (E cap S_i)
	F_factors := [];
	to_be_sorted := [2..#F`essentials];
	for i in [1..#S_factors] do 
		S_i := S_factors[i];
		S_i_star := sub<S | [S_factors[j] : j in [x : x in [1..#S_factors] | x ne i]]>;
		// Get essentials (indices) that contain S_i_star
		essentials_i := [];
		for j in to_be_sorted do 
			if S_i_star subset F`essentials[j] then
				Append(~essentials_i, j);
			end if;
		end for;
		// Remove these so we don't repeatedly search them
		to_be_sorted := [x : x in to_be_sorted | not x in essentials_i];
		// Now calculate the restrictions, first element is of course Aut_F_i(S_i)
		essentialautos_i := [AutRestriction(F`essentialautos[1], S_i)];
		for k in essentials_i do  
			E := F`essentials[k];
			E_i := E meet S_i;
			AE := F`essentialautos[k];
			AE_i := AutRestriction(AE, E_i);
			Append(~essentialautos_i, AE_i);
		end for;
		Append(~F_factors, CreateFusionSystem(essentialautos_i));
	end for;
	return true, F_factors;
end intrinsic;


intrinsic IsIndecomposable(F::FusionSystem: return_decomposition := false) -> Bool, SeqEnum
	{Determine if F splits as F_1 x F_2}
	if IsIndecomposable(F`group) then  
		print "S is indecomposable";
		return true;
	end if;

	pairs := AllSplittings(F`group);
	if pairs eq [] then 
		print "S in indecomposable";
		return true;
	end if;

	for pair in pairs do 
		decomposable, decomp := FusionSystemDecomposition(F, pair: return_decomposition := return_decomposition);
		if decomposable then
			if return_decomposition then 
				return not decomposable, decomp;
			else
				return not decomposable,_;
			end if;
		end if;
	end for;
	return true;
end intrinsic;

