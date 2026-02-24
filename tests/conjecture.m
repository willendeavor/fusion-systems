// Tests the claim that for F over S = S_1 x S_2 where S_1 and S_2 have maximal class there exists \alpha such that
// S_1 and S_2 are strongly closed in F^alpha and hence if O^{p'}(F) = F then it splits


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



















counterexamples := [];
p := 3;
n := 6;
/*
S_decomposable := [];
list_i := [];
for i in [1..NumberOfSmallGroups(p^n)] do 
	print i;
	S := SmallGroup(p^n, i);
	if IsAbelian(S) then 
		continue;
	end if;
	if not AllSplittings(S) eq [] then
		Append(~S_decomposable, S);
		Append(~list_i, i);
	end if;
end for;

print list_i;

printf "There are %o indecomposable groups of order %o^%o \n", #S_decomposable, p, n; 

*/

list_i := [ 103, 105, 106, 138, 139, 140, 141, 142, 144, 146, 239, 240, 242, 245, 246,
247, 253, 255, 256, 261, 263, 265, 268, 274, 276, 277, 278, 279, 286, 392, 394,
395, 396, 402, 403, 404, 416, 417, 418, 419, 420, 421, 425, 426, 427, 428, 430,
431, 433, 434, 435, 436, 438, 453, 455, 458, 476, 477, 479, 480, 481, 482, 483,
484, 485, 486, 487, 488, 498, 499, 500, 501, 502 ];

S_decomposable := [SmallGroup(p^n, i) : i in list_i];

/*
for S in S_decomposable do 
	_, FS_indices := NumberSmallFusionSystems(S:almost_reduced:=false);
	for i in FS_indices do 
		printf "Testing SmallFusionSystem(%o^%o, %o) \n", p,n,i;
		F := SmallFusionSystem(p^n, i);
		if IsIndecomposable(F) then  
			Append(~counterexamples, i);
		end if;
	end for;
end for;

print counterexamples;
*/

// Test the claim that strongly closed in F_i^\bullet implies strongly closed in F
for S in S_decomposable do 
	_, FS_indices := NumberSmallFusionSystems(S:almost_reduced:=false);
	for i in FS_indices do 
		printf "Testing SmallFusionSystem(%o^%o, %o) \n", p,n,i;
		F := SmallFusionSystem(p^n, i);
		S_pairs := AllSplittings(F`group);
		for pair in S_pairs do  
			F_1 := OneSidedFusionSystem(F, pair, 1);
			F_2 := OneSidedFusionSystem(F, pair, 2);
			if IsStronglyClosed(F_1, pair[1]) and IsStronglyClosed(F_2, pair[2]) then
				if IsStronglyClosed(F, pair[1]) and IsStronglyClosed(F, pair[2]) then
					printf "Confirmed for SmallFusionSystem(%o^%o, %o) \n", p,n,i;
				else
					Append(~counterexamples, i);
				end if;
			end if;
		end for;
	end for;
end for;
print counterexamples;