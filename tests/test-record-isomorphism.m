// Test that the results of the isomorphism test via records is the same
// as the IsIsomorphism fusion system output

flag := true;
FS := [SmallFusionSystemRecord(5^5, i) : i in [1..NumberSmallFusionSystems(5^5)]];

for i in [1..#FS - 1] do 
	R := FS[i];
	F := LoadFusionSystem(R);
	if not IsIsomorphicFusionRecords(R,R) then 
		flag := false;
		print "Failed: Record is not isomorphic to itself \n";
	end if;
	if not (IsIsomorphic(F, F) eq IsIsomorphicFusionRecords(R,R)) then 
		flag := false;
		print "Failed: Testing isomorphic to self failed \n";
		printf "IsIsomorphicFusionRecords(R,R) : %o \n", IsIsomorphicFusionRecords(R,R);
		printf "IsIsomorphic(F,F) : %o \n", IsIsomorphic(F,F);
	end if;
	for j in [i+1..#FS] do 
		RR := FS[j];
		FF := LoadFusionSystem(RR);
		if not (IsIsomorphic(F, FF) eq IsIsomorphicFusionRecords(R,RR)) then
			flag := false;
			print "Failed: IsIsomorphism is not equal to IsIsomorphicFusionRecords \n";
		end if;
	end for;
	printf "Test %o passed \n", i;
end for;

print flag;