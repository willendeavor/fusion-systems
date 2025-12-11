// Test SmallFusionSystems package
/*
Overview: Take a known small group fusion system, check that it is already in the database
		  once we know it is in there delete it's file and re-add it. Reload it and check it
		  is still isomorphic to the original
*/

flag := true;
F := GroupFusionSystem(SL(3,3),3); //<27,1> as of v2.0.0
S := F`group;
index := IdentifyFusionSystem(F);
// Check that it is an actual small fusion system
if index eq <0,0> then
	flag := false;
	print "Test failed, IdentifyFusionSystem did not find F";
end if;



FF := SmallFusionSystem(index[1], index[2]);
// Check the returned fusion system is isomorphic
if not IsIsomorphic(F,FF) then
	flag := false;
	print "Test failed, identified fs and input are not the same";
end if;



// Now delete the original filename so we can make it again, watch out for directory changes here
p := FactoredOrder(S)[1][1];
n := FactoredOrder(S)[1][2];
// Don't use isomorphism class version cause that requires loading the files
number := NumberSmallFusionSystems(p^n);
path := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, index[2]);
print "Deleting file";
Pipe("rm " cat path, "");
Pipe("rm " cat path cat ".sig", "");
// Check deleted correctly
if not number-1 eq NumberSmallFusionSystems(p^n) then
	flag := false;
	print "File was not deleted";
else 
	print "File deleted successfully";
end if;

// Rewrite the file, note we are not using AddFS since they does not account for
// gaps in the numbering, I'll fix that at some point
WriteFusionRecord(path, F);
print "File written successfully";
FFF := SmallFusionSystem(index[1], index[2]);
printf "Loaded fusion system %o \n", FFF;

if not IsIsomorphic(F,FFF) or not IsIsomorphic(FF,FFF) then 
	flag := false;
	print "Created FS is not isomorphic to the input";
else 
	print "Created FS is isomorphic to input";
end if;


if not NumberSmallFusionSystems(S) eq number then
	flag := false;
	print "Fusion System was not replaced";
else
	print "Fusion System was replaced";
end if;

print flag;