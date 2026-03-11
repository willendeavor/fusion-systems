// Testing the hyperfocal subgroup calculation
flag := true;
FS := AllSmallFusionSystems(3^5);
for F in FS do 
	S := F`group;
	foc := sub<S | DerivedSubgroup(S), HyperFocalSubgroup(F)>;
	if not FocalSubgroup(F) eq foc then
		flag := false;
		print "Test failed";
	end if;
end for;

print flag;