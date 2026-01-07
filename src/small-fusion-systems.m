// Implements a database similar to SmallGroups


////////////////////// File path and log functions //////////////////////////////////////////////////////////////////////////////////////////////////////////////

procedure UpdateLog(entry)
	log_file := Open("data/update.log", "a");
	date := Trim(Pipe("date '+%Y-%m-%d %H:%M:%S'", ""));
	fprintf log_file, "\n %o: %o", date, entry;
	delete log_file;
end procedure;


procedure ErrorLog(entry)
	errors_log := Open("data/errors.log", "a");
	date := Trim(Pipe("date '+%Y-%m-%d %H:%M:%S'", ""));
	fprintf errors_log, "\n %o: %o", date, entry;
	delete errors_log;
end procedure;


intrinsic SetSmallFusionSystemDirectory() -> MonStgElt
	{Returns the path to the database}
	return GetCurrentDirectory();
end intrinsic


// Creates the name FS_pp_nn_i with i padded with 0s to width 5
function GetSmallFusionSystemFileName(order, i)
	p := Factorisation(order)[1][1];
	n := Factorisation(order)[1][2];
	padded := Sprint(i);
	while #padded lt 5 do 
		padded := "0" cat padded;
	end while;
	filename := Sprintf("FS_p%o_n%o_%o.m", p, n, padded);
	return filename;
end function;

// Returns the full file path
function GetSmallFusionSystemFilePath(order, i)
	p := Factorisation(order)[1][1];
	n := Factorisation(order)[1][2];
	filename := GetSmallFusionSystemFileName(order,i);
	filepath := Sprintf("data/SmallFusionSystems/p_%o/n_%o/%o", p, n, filename);
	return filepath;
end function;


// Returns an associate array of p : [n_1, n_2, ..]
function GetAllpn()
	p_list := Pipe("ls " cat "data/SmallFusionSystems", "");
	p_list := Split(p_list, "\n");
	p_list := [Split(x, "_")[2] : x in p_list];
	all_list := AssociativeArray(p_list);
	for p in p_list do 
		path := Sprintf("data/SmallFusionSystems/p_%o", p);
		n_list := Pipe("ls " cat path, "");
		n_list := Split(n_list, "\n");
		n_list := [Split(x, "_")[2] : x in n_list];
		all_list[p] := n_list;
	end for;
	return all_list;
end function;

procedure AddToVerificationQueue(order,i)
	filename := "data/verification_queue.log";
	F := Open(filename, "a");
	fprintf F, " \n %o : %o", order,i;
	delete F; 
end procedure;
































//////////////////////// Loading SmallFusionSystems //////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic SmallFusionSystem(order::RngIntElt, i::RngIntElt) -> FusionSystem
	{Return the i-th fusion system on a group of given order}
	// Recall that loading the fusion system record does not load the fusion system
	return LoadFusionSystem(GetSmallFusionSystemFilePath(order, i));
end intrinsic;



intrinsic SmallFusionSystemRecord(order::RngIntElt, i::RngIntElt) -> Rec 
	{Return the record only for a small fusion system}
	return LoadFusionSystemRecord(GetSmallFusionSystemFilePath(order, i));
end intrinsic;



intrinsic IdentifyFusionSystem(F::FusionSystem) -> SeqEnum
	{If F is a small fusion system return its identifying pair}
	S := F`group;
	m, indices := NumberSmallFusionSystems(S: almost_reduced := false);
	for i in indices do 
		F_i := SmallFusionSystem(#S, i);
		if IsIsomorphic(F_i, F) then
			index := <#S, i>;
			printf "Input fusion system is small fusion system %o \n", index;
			return index;
		end if;
	end for;
	print "Fusion is not a small fusion system";
	return <0,0>;
end intrinsic;
























////////////////////////////// Adding fusion systems /////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic AddSmallFusionSystem(F::FusionSystem) -> BoolElt, SeqEnum
	{Given a fusion system check if it is already in the database, otherwise add it, returns whether a new one has been added}
	S := F`group;
	m, indices := NumberSmallFusionSystems(S:almost_reduced := false);
	// Compare records only for a drastic improvement in speed in certain cases
	WriteFusionRecord("temp_candidate.m", F);
	R := LoadFusionSystemRecord("temp_candidate.m");
	for i in indices do 
		R_i := SmallFusionSystemRecord(#S, i);
		printf "Checking if F is isomorphic to fusion system %o \n", i;
		if IsIsomorphicFusionRecords(R_i, R: preloaded := F) then
			delete R;
			System("rm temp_*");
			print "Fusion system is already in database \n";
			return false, [#S, i];
			break;
		end if;
	end for;
	delete R;
	System("rm temp_*");

	p := FactoredOrder(S)[1][1];
	n := FactoredOrder(S)[1][2];
	filepath := Sprintf("data/SmallFusionSystems/p_%o/n_%o", p, n);
	System(Sprintf("mkdir -p %o", filepath));
	i := NumberSmallFusionSystems(#S:almost_reduced := false) + 1;
	// filename := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, NumberSmallFusionSystems(#S) + 1);
	filename := GetSmallFusionSystemFilePath(p^n, i);
	WriteFusionRecord(filename, F);
	print "Successfully added new fusion system \n";
	AddToVerificationQueue(#S, i);
	UpdateLog(Sprintf(
		"Added SmallFusionSystem(%o^%o, %o)", p, n, i));
	return true, [#S, i];
end intrinsic;


intrinsic AddSmallFusionSystems(FS::SeqEnum)
	{Given a list of fusion systems, add them to the database}
	for F in FS do 
		AddSmallFusionSystem(F);
	end for;
end intrinsic;


intrinsic AllSmallFusionSystems(S::Grp: almost_reduced := true) -> SeqEnum
	{Given a group S return all small fusion systems over S}
	m, indices := NumberSmallFusionSystems(S:almost_reduced := almost_reduced);
	FS := [LoadFusionSystem(SmallFusionSystemRecord(#S, i)) : i in indices];
	return(FS);
end intrinsic;


intrinsic AllSmallFusionSystems(S_order::RngIntElt: almost_reduced := true) -> SeqEnum
	{Return all small fusion systems on a p-group of S_order}
	m, indices := NumberSmallFusionSystems(S_order:almost_reduced := almost_reduced);
	FS := [SmallFusionSystem(S_order,i) : i in indices];
	return(FS);
end intrinsic;



intrinsic AddGroupFusionSystem(F::FusionSystem : overwrite := false)
	{Given a group fusion system find it in the SmallFusionSystem library and add the FusionGroup}
	require assigned F`grpsystem : "F is not a group fusion system";
	pair := IdentifyFusionSystem(F);
	G := F`grpsystem;
	// Replace G by G/O_{p'}(G)
	if pair eq <0,0> then
		message := Sprintf("Adding group fusion system of %o", GroupName(G));
		UpdateLog(message);
		AddSmallFusionSystem(F);
	else
		R := SmallFusionSystemRecord(pair[1], pair[2]);
		if (assigned R`FusionGroup and overwrite eq true) or not assigned R`FusionGroup then
			UpdateSmallFusionSystemAttributes(pair[1], pair[2], ["FusionGroup"] : FusionGroup := G);
			message := Sprintf("Added FusionGroup to SmallFusionSystem(%o, %o)", pair[1], pair[2]);
			UpdateLog(message);
		else
			printf "SmallFusionSystem(%o, %o) already has group %o attached", pair[1], pair[2], R`FusionGroup_name;
		end if;
	end if;
	
end intrinsic;



intrinsic AddAllFusionSystems(order::RngIntElt: resume := 1, OpTriv := true, pPerfect := true, id_list := [])
    {Add all fusion systems over a group of given order}
    if resume eq 1 and id_list eq [] then
    	UpdateLog(Sprintf("Attempting to add all fusion systems of order %o", order));
    end if;

    if id_list eq [] then
    	id_list := [resume..NumberOfSmallGroups(order)];
    end if;

    for i in id_list do
        m := Sprintf("Starting adding all fusion systems over SmallGroup(%o, %o)", order, i);
        UpdateLog(m);
        print m;
        AddAllFusionSystems(SmallGroup(order,i): OpTriv := OpTriv, pPerfect := pPerfect);
        m := Sprintf("Finished adding all fusion systems over SmallGroup(%o, %o)", order, i);
        UpdateLog(m);
        print m;
    end for;
    UpdateLog(Sprintf("Finished adding all fusion systems of order %o", order));
end intrinsic;



intrinsic AddAllFusionSystems(S::Grp: OpTriv := true, pPerfect := true)
    {Adds all fusion systems possible to the SmallFusionSystems database}
    FF := AllFusionSystems(S:OpTriv := OpTriv, pPerfect := pPerfect);
    AddSmallFusionSystems(FF);
end intrinsic;



intrinsic AddAllDirectProducts(order_1::RngIntElt, order_2::RngIntElt : resume := [1,1])
	{Create all direct products of all small fs starting at SFS(order_1, resume[1]) and SFS(order_2, resume[2])}
	for i in [resume[1]..NumberSmallFusionSystems(order_1: almost_reduced := false)] do 
		if order_1 eq order_2 then
			range := [i..NumberSmallFusionSystems(order_1:almost_reduced := false)];
		else
			range := [resume[2]..NumberSmallFusionSystems(order_2:almost_reduced := false)];
		end if;
		for j in range do  
			F_1 := SmallFusionSystem(order_1, i);
			F_2 := SmallFusionSystem(order_2, j);
			F := FusionDirectProduct(F_1, F_2);
			F`factors := [<order_1, i>, <order_2, j>];
			F`indecomposable := false;
			new, ind := AddSmallFusionSystem(F);
			if not new then
				print "Adding factors to existing entry \n";
				UpdateSmallFusionSystem(ind[1], ind[2]);
				UpdateSmallFusionSystemAttribute(ind[1], ind[2], "factors" : factors := F`factors);
			end if;
		end for;
	end for;
end intrinsic;






























//////////////// Loading information about all fusion systems //////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic NumberSmallFusionSystems(S_order::RngIntElt: almost_reduced := true) -> RngIntElt, SeqEnum
	{Returns the number of small fusion systems over a group of order S_order and a list of their indices}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	path := Sprintf(" data/SmallFusionSystems/p_%o/n_%o/", p, n);
	try 
		files := Pipe("ls" cat path, "");
	catch e
		return 0, [];
	end try;
    filelist := Split(files, "\n");
    count := #[s : s in filelist | Split(s, "_")[1] eq "FS" and Split(s, ".")[2] eq "m"];
    if almost_reduced then
    	indices := [];
    	for i in [1..count] do  
    		R := SmallFusionSystemRecord(S_order, i);
    		if R`core_trivial eq true and R`pPerfect eq true then 
    			Append(~indices, i);
    		end if;
    	end for;
    	return #indices, indices;
    end if;

    return count, [1..count];
end intrinsic;



intrinsic NumberSmallFusionSystems(S::Grp: almost_reduced := true) -> RngIntElt, SeqEnum
	{Returns the number of small fusion systems over S and the indices of them}
	p := FactoredOrder(S)[1][1];
	n := FactoredOrder(S)[1][2];
	indices := [];
	m, all_indices := NumberSmallFusionSystems(#S: almost_reduced := almost_reduced);
	for i in all_indices do 
		R := SmallFusionSystemRecord(#S, i);
		if IsIsomorphic(S, R`S) then 
			Append(~indices, i);
		end if;
	end for;
	return #indices, indices;
end intrinsic;



intrinsic AllSmallFusionSystemsGroups(S_order::RngIntElt: almost_reduced := true) -> SeqEnum
	{Given S_order return a list of all groups which have a small fusion system}
	grps := [];
	m, indices := NumberSmallFusionSystems(S_order: almost_reduced := almost_reduced);
	for i in indices do 
		R := SmallFusionSystemRecord(S_order,i);
		S := R`S;
		if forall{not IsIsomorphic(S,T) : T in grps} then
			Append(~grps, S);
		end if;
	end for;
	return grps;
end intrinsic;


intrinsic GetSmallFusionSystemTotals()
	{Returns the total number of almost reduced and all FS}
	pn := GetAllpn();
	print "(p,n) : Almost reduced (Total) \n";
	for pp in Keys(pn) do 
		for nn in pn[pp] do  
			p := StringToInteger(pp);
			n := StringToInteger(nn);
			printf "(%o, %o) : %o (%o) \n", 
				p,n, NumberSmallFusionSystems(p^n), NumberSmallFusionSystems(p^n : almost_reduced := false);
		end for;
	end for;
end intrinsic






























///////////////// Updating and verifying /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////




intrinsic UpdateSmallFusionSystems(S_order::RngIntElt)
	{Update the files in the SmallFusionSystems S_order database}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	path := Sprintf("data/SmallFusionSystems/p_%o/n_%o/", p, n);
	F_list := Split(Pipe("ls " cat path, ""), "\n");
	// Get only file names with correct extension
	F_list := [x : x in F_list | Split(x, ".")[2] eq "m"];
	for i in F_list do 
		filename := path cat i;
		UpdateFusionRecord(filename);
		printf "Updated %o \n", i;
		j := Split(i, ".")[1];
		j := StringToInteger(Split(j, "_")[4]);
		AddToVerificationQueue(S_order, j);
		UpdateLog(Sprintf("Updated SmallFusionSystem(%o, %o)", p^n, j));
	end for;
end intrinsic;



function NeedsUpdate(R, options, overwrite)
	if overwrite then
		return true;
	else
		return exists{x : x in options | not assigned R``x};
	end if;
end function;


intrinsic UpdateSmallFusionSystemAttributes(order :: RngIntElt, i::RngIntElt, options::SeqEnum[MonStgElt]: FusionGroup := false, overwrite := false, factors := [])
	{Updates a given attribute e.g. core in a fusion systems record}
	// Check first if we actually need to do anything
	R := SmallFusionSystemRecord(order, i);
	need_update := NeedsUpdate(R,options,overwrite);
	if not need_update then
		print "Record does not need updating \n";
		return;
	end if;
	// Else here comes the expensive calculations
	F := SmallFusionSystem(order, i);
	if "core" in options or "core_trivial" in options then 
		F`core_trivial, F`core := Core(F);
	end if;
	if "focal_subgroup" in options or "pPerfect" in options then 
		F`focal_subgroup := FocalSubgroup(F);
		F`pPerfect := F`focal_subgroup eq F`group;
	end if;
	if "FusionGroup" in options and ISA(Type(FusionGroup), Grp) then
		F`FusionGroup := FusionGroup;
	end if;
	if "factors" in options and not factors eq [] then
		F`factors := factors;
		F`indecomposable := false;
	end if;
	WriteFusionRecord(GetSmallFusionSystemFilePath(order, i), F);
	AddToVerificationQueue(order,i);
	message := Sprintf("Updated SmallFusionSystem(%o, %o) attributes %o", order, i, options);
	UpdateLog(message);
end intrinsic;



intrinsic UpdateSmallFusionSystemAttribute(order :: RngIntElt, i::RngIntElt, option::MonStgElt : FusionGroup := false, overwrite := false, factors := [])
	{Updates a given attribute e.g. core in a fusion systems record, single argument version}
	UpdateSmallFusionSystemAttributes(order, i, [option] : FusionGroup := FusionGroup, overwrite := overwrite, factors := factors);
end intrinsic;



intrinsic UpdateAllSmallFusionSystemsAttributes(order::RngIntElt, options::SeqEnum[MonStgElt] : resume := 1, overwrite := false)
	{Update the attributes of all SmallFusionSystems of a particular order}
	m := NumberSmallFusionSystems(order:almost_reduced := false);
	for i in [resume..m] do 
		UpdateSmallFusionSystemAttributes(order, i, options: overwrite := overwrite);
	end for;
	message := Sprintf("Updated ALL SmallFusionSystem(%o, i) attributes %o", order, options);
	UpdateLog(message);
end intrinsic;



intrinsic UpdateSmallFusionSystem(order::RngIntElt, i::RngIntElt)
	{Updates a small fusion system to reflect any changes in record format}
	filename := GetSmallFusionSystemFilePath(order,i);
	UpdateFusionRecord(filename);
	message := Sprintf("Updated SmallFusionSystem(%o, %o)", order, i);
	print message cat "\n";
	UpdateLog(message);
end intrinsic;


intrinsic UpdateAllSmallFusionSystems()
	{Update every single file in the SmallFusionSystems database}
	p_list := Pipe("ls " cat "data/SmallFusionSystems", "");
	p_list := Split(p_list, "\n");
	for p in p_list do 
		path := Sprintf("data/SmallFusionSystems/%o", p);
		n_list := Pipe("ls " cat path, "");
		n_list := Split(n_list, "\n");
		for n in n_list do 
			n_path := path cat Sprintf("/%o/", n);
			F_list := Split(Pipe("ls " cat n_path, ""), "\n");
			// Get only file names with correct extension
			F_list := [x : x in F_list | Split(x, ".")[2] eq "m"];
			for i in F_list do 
				filename := n_path cat i;
				UpdateFusionRecord(filename);
				printf "Updated %o \n", i;
			end for;
		end for;
	end for;
	UpdateLog("Updated all SmallFusionSystems");
end intrinsic;



intrinsic VerifyAllSmallFusionSystemRecords(resume::SeqEnum)
	{Check that every fusion record at least returns a fusion system}
	if resume eq [0] then
		resume := [2,3,1];
	end if;
	p_list := Pipe("ls " cat "data/SmallFusionSystems", "");
	p_list := Split(p_list, "\n");
	p_list := [x : x in p_list | StringToInteger(Split(x, "_")[2]) ge resume[1]];
	errors := [];
	for p in p_list do 
		path := Sprintf("data/SmallFusionSystems/%o", p);
		n_list := Pipe("ls " cat path, "");
		n_list := Split(n_list, "\n");
		// If p is the resume value then we need only resumed n
		p_int := StringToInteger(Split(p, "_")[2]);
		if p_int eq resume[1] then
			n_list := [x : x in n_list | StringToInteger(Split(x, "_")[2]) ge resume[2]];
		end if;
		for n in n_list do 
			n_path := path cat Sprintf("/%o/", n);
			F_list := Split(Pipe("ls " cat n_path, ""), "\n");
			// Get only file names with no extension
			F_list := [x : x in F_list | Split(x, ".")[2] eq "m"];
			// If we are at (p,n) resume then get only those above resume
			n_int := StringToInteger(Split(n, "_")[2]);
			if p_int eq resume[1] and n_int eq resume[2] then
				F_list := [x : x in F_list | StringToInteger(Split(Split(x, "_")[4], ".")[1]) ge resume[3]];
			end if;
			for i in F_list do 
				filename := n_path cat i;
				try 
					F := LoadFusionSystem(filename);
					printf "Verified %o \n", filename;
				catch e
					message := Sprintf("Failed to load %o \n", filename);
					ErrorLog(message);
					print message;
					Append(~errors, [p_int, n_int, StringToInteger(Split(Split(i, "_")[4], ".")[1])]);
				end try;
			end for;
		end for;
	end for;
	print errors;
end intrinsic;



intrinsic VerifyNewFusionSystemRecords()
	{Verifies any new fusion systems that have been added since last verification}
	queuefile := "data/verification_queue.log";
	txt := Read(queuefile);
	lines := [l : l in Split(txt, "\n") | l ne ""];
	// Remove header
	lines := lines[2..#lines];
	keep := lines;
	for l in lines do 
		pair := Split(l, ":");
		order := StringToInteger(pair[1]);
		i := StringToInteger(pair[2]);
		filename := GetSmallFusionSystemFilePath(order,i);
		try 
			F := LoadFusionSystem(filename);
			printf "Verified %o \n", filename;
			Exclude(~keep, l);
		catch e 
			message := Sprintf("Failed to load %o \n", filename);
			ErrorLog(message);
			print message;
		end try;
	end for;
	// Rewrite file
	F := Open(queuefile, "w");
	fprintf F, "The following fusion systems need to be verified: \n";
	for l in keep do 
		fprintf F, "%o \n", l;
	end for;
	delete F;
end intrinsic;



intrinsic CheckDuplicatesSmallFusionSystem(order::RngIntElt: resume := 1, almost_reduced := true) -> SeqEnum
	{Check if there are duplicates in the database, of course most important for the almost_reduced}
	duplicates := [];
	_, id_list := NumberSmallFusionSystems(order: almost_reduced := almost_reduced);
	id_list := [x : x in id_list | x ge resume];
	for i in id_list do 
		printf "Checking for duplicates of FS_%o \n", i;
		R := SmallFusionSystemRecord(order,i);
		S := R`S;
		m, indices := NumberSmallFusionSystems(S : almost_reduced := almost_reduced);
		// Get only those we haven't checked yet
		checks := [x : x in indices | x gt i ];
		for j in checks do  
			RR := SmallFusionSystemRecord(order, j);
			if IsIsomorphicFusionRecords(R, RR) then 
				printf "SmallFusionSystems (%o, %o) and (%o, %o) are isomorphic \n", order,i, order, j;
				Append(~duplicates, [i,j]);
			end if;
		end for;
	end for;
	if IsEmpty(duplicates) then
		print "No duplicates found";
	end if;
	return duplicates;
end intrinsic;




intrinsic MaintainSmallFusionSystems()
	{Performs some maintenance tasks and status tasks}
	all_list := GetAllpn();
	for p in Keys(all_list) do  
		n_list := all_list[p];
		for n in n_list do 
			printf "Checking (p,n) = (%o, %o) \n", p,n;
			pp := StringToInteger(p);
			nn := StringToInteger(n);
			m := NumberSmallFusionSystems(pp^nn: almost_reduced := false);
			// Check that core_trivial or pPerfect has been assigned to all or none, partially assigned implies something has gone wrong
			flags_op := {};
			flags_pperf := {};
			for i in [1..m] do 
				F := SmallFusionSystemRecord(pp^nn,i);
				Include(~flags_op, assigned F`core_trivial);
				Include(~flags_pperf, assigned F`pPerfect);
			end for;
			if #flags_op gt 1 or #flags_pperf gt 1 then
				message := Sprintf("Error: Partially assigned core_trivial or pPerfect in p_%o/n_%o, you should update these attributes for all FS", p,n);
				ErrorLog(message);
				print message cat "\n";
			elif flags_op eq {false} then 
				message := Sprintf("Advisory: core_trivial has not been assigned for p_%o/n_%o", p,n);
				ErrorLog(message);
				print message cat "\n";
			elif flags_pperf eq {false} then 
				message := Sprintf("Advisory: pPerfect has not been assigned for p_%o/n_%o", p,n);
				ErrorLog(message);
				print message cat "\n";
			end if;
		end for;
	end for;
end intrinsic;



procedure UpdateIndexMigrationYAML(dir, mapping, order)
	date := Trim(Pipe("date '+%Y-%m-%d %H:%M:%S'", ""));
	filename := dir cat "/index_migration.yaml";
	F := Open(filename, "a");
	fprintf F, "  - migration_id: %o \n", date;
	fprintf F, "    mapping:\n";
	for k in Keys(mapping) do 
		fprintf F, "      FS_%o : FS_%o \n", GetSmallFusionSystemFileName(order,k), GetSmallFusionSystemFileName(order,mapping[k]);
	end for;
	fprintf F, "\n";
	delete F;
end procedure;



intrinsic GroupByIsomorphismClass(order::RngIntElt)
	{A procedure that rearranges the directories according to isomorphism classes of the underlying groups}
	p := Factorisation(order)[1][1];
	n := Factorisation(order)[1][2];
	m := NumberSmallFusionSystems(p^n: almost_reduced := false);
	// Classes is the equivalence class of {1..m} under i ~ j iff FS_i`group ~ FS_j`group
	classes := [];
	temp := {1..m};
	while not IsEmpty(temp) do 
		print temp;
		S := SmallFusionSystemRecord(p^n, Minimum(temp))`S;
		k, class := NumberSmallFusionSystems(S: almost_reduced := false);
		Append(~classes, class);
		temp := temp diff Set(class);
	end while;
	print classes;
	// Now we need to write all the files, we save them to a new directory rather than overwriting
	new_dir := Sprintf("data/SmallFusionSystems/rearranged/p_%o/n_%o", p, n);
	System(Sprintf("mkdir -p %o", new_dir));
	start_index := 1;
	// Mapping keeps track of which indices have been changed
	mapping := AssociativeArray();
	for class in classes do 
		for i in [1..#class] do 
			F := SmallFusionSystem(p^n, class[i]);
			k := start_index + i - 1;
			mapping[class[i]] := k;
			file := new_dir cat "/" cat GetSmallFusionSystemFileName(order,k);
			WriteFusionRecord(file, F);
			print k;
		end for;
		start_index := k + 1;
	end for;
	if forall{mapping[i] eq i : i in [1..#mapping]} then
		print "No changes made";
	end if;
	// Now update the YAML file
	UpdateIndexMigrationYAML(new_dir, mapping, order);
	UpdateLog("Migrated indices following isomorphism classes");
end intrinsic;





