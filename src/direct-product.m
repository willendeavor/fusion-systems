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
	F`directproductgrp := S;
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





/*
intrinsic FusionDirectProduct(F_factors::SeqEnum[FusionSystem]) -> FusionSystem
	{Given a list of fusion systems calculate their direct product}
	n := #F_factors;
	S_factors := [F_i`group : F_i in F_factors];
	S := MakeDirectProductGroup(S_factors);
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
			print "added one";
		end for;
	end for;
	F := CreateFusionSystem(aut_seq);
	try
		F`directproductgrp := MakeDirectProductGroup(S_factors);
	catch e
		print "Unable to make a DirectProductGroup";
	end try;
	F`factors := F_factors;
	return F;
end intrinsic;
*/