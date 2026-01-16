import "small-fusion-systems.m" : ErrorLog, UpdateLog, AddToVerificationQueue, 
									GetAllpn, GetSmallFusionSystemFilePath, GetSmallFusionSystemFileName,
									GetAllIndices;



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


intrinsic UpdateSmallFusionSystemAttributes(order :: RngIntElt, i::RngIntElt, options::SeqEnum[MonStgElt]: fusion_group := false, overwrite := false, factors := [])
	{Updates a given attribute e.g. core in a fusion systems record}
	// Check first if we actually need to do anything
	R := SmallFusionSystemRecord(order, i);
	need_update := NeedsUpdate(R,options,overwrite);
	if not need_update then
		printf "Record (%o,%o) does not need updating \n", order, i;
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
	if "fusion_group" in options and ISA(Type(fusion_group), Grp) then
		F`fusion_group := fusion_group;
		F`fusion_group_name := GroupName(fusion_group);
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



intrinsic UpdateSmallFusionSystemAttribute(order :: RngIntElt, i::RngIntElt, option::MonStgElt : fusion_group := false, overwrite := false, factors := [])
	{Updates a given attribute e.g. core in a fusion systems record, single argument version}
	UpdateSmallFusionSystemAttributes(order, i, [option] : fusion_group := fusion_group, overwrite := overwrite, factors := factors);
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



intrinsic UpdateAllSmallFusionSystemsAttributes(options::SeqEnum[MonStgElt])
	{Runs UpdateAllSmallFusionSystemsAttributes on all orders}
	pn := GetAllpn();
	for p in Keys(pn) do 
		for n in pn[p] do 
			pp := StringToInteger(p);
			nn := StringToInteger(n);
			UpdateAllSmallFusionSystemsAttributes(pp^nn, options);
		end for;
	end for;
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


intrinsic CheckDuplicatesAll()
	{Run check duplicates on all fusion systems}
	pn := GetAllpn();
	for pp in Keys(pn) do  
		for nn in pn[pp] do 
			p := StringToInteger(pp);
			n := StringToInteger(nn);
			dup := CheckDuplicatesSmallFusionSystem(p^n:almost_reduced:=false);
			if not IsEmpty(dup) then 
				message := Sprintf("(%o,%o) contains duplicates", p, n);
				print message;
				ErrorLog(message);
			end if;
		end for;
	end for;
end intrinsic;



intrinsic TestIsomorphismWorking() -> BoolElt
	{test}
	pn := GetAllpn();
	for pp in Keys(pn) do 
		for nn in pn[pp] do
			p := StringToInteger(pp);
			n := StringToInteger(nn);
			print p,n;
			indices := [1..NumberSmallFusionSystems(p^n:almost_reduced := false)];
			for i in indices do 
				for j in [i+1..#indices] do  
					print i,j;
					F := SmallFusionSystem(p^n, i);
					FF := SmallFusionSystem(p^n, j);
					R := SmallFusionSystemRecord(p^n, i);
					RR := SmallFusionSystemRecord(p^n, j);
					a := IsIsomorphic(F,FF);
					b := IsIsomorphicFusionRecords(R,RR);
					if not a eq b then
						print p,n, i,j;
						return false;
					end if;
				end for;
			end for;
		end for;
	end for;
	return true;
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
