// Test all fusion systems


flag := true;
// Example with InsolubleBorelCandidates time: 3.110
// #FS = 3
FS := AllFusionSystems(ExtraSpecialGroup(5,1,));
if not #FS eq 3 then
	print "Failed soluble: Expected different number of FS \n";
	flag := false;
end if;



// Example with SolubleBorelCandidates time : 1.800
FS := AllFusionSystems(AllFusionSystems(WreathProduct(CyclicGroup(3), CyclicGroup(3))));
if not #FS eq 6 then
	print "Failed insoluble: Expected different number of FS \n";
	flag := false;
end if;