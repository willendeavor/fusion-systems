flag := true;
F_1 := SmallFusionSystem(3^3, 2);
F_2 := SmallFusionSystem(3^3, 3);
F := FusionDirectProduct(F_1, F_2);
S := F`directproductgrp;
// The interal S_i of the F`group are stored in S`factors but F`group is not F`directproductgrp, currently
S_1 := S`factors[1];
S_2 := S`factors[2];
decomposable, factors := FusionSystemDecomposition(F, [S_1, S_2]);
if not decomposable then:
	flag := false;
	print "Error: F_1 x F_2 is not indecomposable \n";
end if;

if not IsIsomorphic(F_1, factors[1]) then 
	flag := false;
	print "Error: F_1 is not isomorphic to F|S_1 \n";
end if;


if not IsIsomorphic(F_2, factors[2]) then 
	flag := false;
	print "Error: F_2 is not isomorphic to F|S_2 \n";
end if;

print flag;
