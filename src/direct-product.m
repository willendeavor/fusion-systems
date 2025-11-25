// Adds support for calculating the direct product of n-fusion systems


/* 
Rough overview of how it (might) work:
Given F_1, .., F_n a list of fusion systems over S_1,...,S_n
First make the direct product S and the actual subgroups S_i < S
Then make Aut_F(S) = Aut_{F_1}(S_1) x ... x Aut_{F_n}(S_n) \leq Aut(S)
to do this embed each Aut_{F_i}(S_i) in Aut(S) by defining alpha in Aut_{F_i}(S_i) 
as (1,...1,\alpha,1,...1)
Every F-essential of F = F_1 x ... x F_n is of the form E = E_i x S_i^* where
S_i^* = prod_{j \neq i} S_j and E_i is Aut_{\F_i}(E_i)-essential

*/











// Define a new type for direct products
declare type DirectProductGroup;
declare attributes DirectProductGroup: group, embed, proj, factors;

intrinsic Print(D::DirectProductGroup){}
	print(D`group);
end intrinsic;


intrinsic MakeDirectProductGroup(G_factors::SeqEnum[Grp]) -> DirectProductGroup
	{given the factors make all aspects of a DirectProductGroup}
	G := New(DirectProductGroup);
	G`group, G`embed, G`proj := DirectProduct(G_factors);
	G`factors := G_factors;
	return G;
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





intrinsic AutDirectProduct(A_1::GrpAuto, A_2::GrpAuto) -> GrpAuto
	{Given A_i \leq Aut(G_i) return A_1 x A_2 \leq Aut(G_1 x G_2)}
	G_1 := A_1`Group;
	G_2 := A_2`Group;
	G,embed,proj := DirectProduct(G_1,G_2);
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


intrinsic AutDirectProduct(A_list::SeqEnum[GrpAuto]) -> GrpAuto 
	{Given a list of groups A_i < Aut(G_i) return the embedding of A_1 ... A_n < Aut(G_1...G_n)}
	// Recursively calculate as (((A_1 x A_2) x A_2) x A_3) x....) x A_n
	A := AutDirectProduct(A_list[1], A_list[2]);
	Remove(~A_list, 1);
	Remove(~A_list, 2);
	for A_i in A_list do 
		A := AutDirectProduct(A, A_i);
	end for;
	return A;
end intrinsic;











/*
intrinsic DirectProduct(F_factors::SeqEnum[FusionSystem]) -> FusionSystem
	{Given a list of fusion systems calculate their direct product}
	S_factors := [F_i`group : F_i in F_factors];
	S_d := MakeDirectProductGroup(S_factors);
	S := S_d`group;
	// Get the factors as actual subgroups of S
	S_factors_internal := [Image(S`embed[i]) : i in [1..#S`factors]];
	MakeAutos(S);
	// The essentials are given by E_i x S_i^* where E_i is F_i-essential and S_i^* is product of all factors except S_i
	for F_i in F_factors do 
		i := Index(F_factors,F_i);
		S_i_star := sub<S | [S_factors_internal[k] : k in not_i];
		for E_i in F_i`essentials do 
			E := sub<S | E_i, S_i_star>;
		end for;
	end for;
end intrinsic;
*/