// Test SmallFusionSystems package. Use test_data if you want to test
/*
Test 1: Creating, identifying and saving
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

printf "Test 1 result: %o \n", flag;




/*
Test 2: Verifying and updating
Overview: Check that a corrupted file (2^3, 2) is found and adding all small fusion systems recovers it
*/
flag := true;
VerifyAllSmallFusionSystemsRecords([0]);
if errors eq [] then
	flag := false;
	print "Corrupted file was not found \n";
elif [2,3,2] in errors then
	print "Corrupted file found \n";
	number := NumberSmallFusionSystems(8);
	path := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", 2, 3, 2);
	Pipe("rm " cat path, "");
	Pipe("rm " cat path cat ".sig", "");
	if not number-1 eq NumberSmallFusionSystems(8) then
		flag := false;
		print "File was not deleted";
	else 
		print "File deleted successfully";
	end if;
end if;


// Fix the corrupted file, need to be careful about indexing
FS := AllFusionSystems(2^3);
for F in FS then
	if IdentifyFusionSystem(F) eq <0,0> then
		WriteFusionRecord(path, F);
		print "Fixed corrupted fusion system \n";
	end if;
end for;

// Check it is the original
FF := LoadFusionSystem("data/SmallFusionSystems/FS_2_original");
F := SmallFusionSystem(8,2);
if not IsIsomorphic(F,FF) then
	flag := false;
	print "Test failed: recovered fusion system is not the same";
end if;


