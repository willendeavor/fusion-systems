// Tests if there is a subgroup P of \gamma_1(S) such that P = M \times Q where M has max class.
function TestSubgroups(S)
	L:= LowerCentralSeries(S);
    gamma_1:= Centralizer(S,L[2],L[4]);
    p := FactoredOrder(S)[1][1];
    if FactoredOrder(gamma_1)[1][2] le 4 then
    	return false,_,_,_;
    end if;
    max_exp := FactoredOrder(gamma_1)[1][2] - 5;
    potential_orders := [4..max_exp];
    for i in potential_orders do 
    	subs := Subgroups(gamma_1:OrderEqual := p^i);
    	for M in subs do  
    		if not IsMaximalClass(M) then 
    			continue;
    		else
    			C := Centralizer(gamma_1, M);
    			for Q in Subgroups(C : OrderEqual := p) do 
    				if IsTrivial(M meet Q) then
    					P := sub<gamma_1 | M,Q>;
    					return true, P, M, Q;
    				end if;
    			end for;
    		end if;
   		end for;
    end for;
    return false,_,_,_;
end function;


intrinsic TestConjecture(order) -> BoolElt
	{}
	for i in [1..NumberOfSmallGroups(order)] do 
		S := SmallGroup(order,i);
		if IsMaximalClass(S) then
			printf "Testing SmallGroup(%o, %o)", order, i;
			flag, P,M,Q := TestSubgroups(S);
			if flag then
				printf "SmallGroup(%o, %o) is a counterexample \n", order, i;
				printf "Orders (P, M, Q) are (%o, %o, %o, %o)", FactoredOrder(P)[1][2], FactoredOrder(M)[1][2], FactoredOrder(Q)[1][2];
				return false;
			end if;
		end if;
	end for;
	return true;
end intrinsic;




function TestSaturationConjecture(F, S_factors)
	for i in [1..#S_factors] do 
		F_i := OneSidedFusionSystem(F, S_factors, i);
		print "hey";
		if IsSaturated(F_i) then
			print "F_i is saturated and furthermore...";
			print S_factors[i] subset F_i`group;
			if IsStronglyClosed(F_i, S_factors[i]) then 
				print "S_i is strongly closed";
			else 
				print "S_i is not strongly closed";
			end if;
		else 
			print "F_i is not saturated";
		end if;
	end for;
	return true;
end function;


intrinsic TestSaturationConjecture(F::FusionSystem) -> BoolElt
	{tests if F_i^bullet is saturated}
	S := F`group;
	pairs := AllSplittings(S);
	for pair in pairs do 
		TestSaturationConjecture(F,pair);
	end for;
end intrinsic





intrinsic FindExamples() -> SeqEnum, BoolElt
	{temp}
	X := ExtraSpecialGroup(3,1);
	S := DirectProduct(X,X);
	FS := AllSmallFusionSystems(S: almost_reduced := false);
	examples := [];
	for F in FS do 
		S := F`group;
		dummy, S_factors := GroupDecomposition(S);
		if (#GetOneSidedEssentials(F, S_factors, 1) eq #F`essentials - 1) 
			or (#GetOneSidedEssentials(F, S_factors, 2) eq #F`essentials - 1) then 
			Append(~examples, F);
			print "Found one";
		else 
			continue;
		end if;
		print "Testing for strong closure";
		pairs := AllSplittings(S);
		flag := false;
		for pair in pairs do 
			if IsStronglyClosed(F, pair[1]) and IsStronglyClosed(F, pair[2]) then
				print "Fusion system splits";
				flag := true;
			end if;
		end for;
		if flag eq false then 
			printf "Conjecture has failed for SFS%o \n", IdentifyFusionSystem(F);
		end if; 
	end for;
	return examples, flag;
end intrinsic;