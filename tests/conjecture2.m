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