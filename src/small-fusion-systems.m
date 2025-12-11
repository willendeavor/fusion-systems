// Implements a database similar to SmallGroups

procedure UpdateLog(entry)
	log_file := Open("data/update.log", "a");
	date := Trim(Pipe("date '+%Y-%m-%d %H:%M:%S'", ""));
	fprintf log_file, "\n %o: %o", date, entry;
	delete log_file;
end procedure;



intrinsic SetSmallFusionSystemDirectory() -> MonStgElt
	{Returns the path to the database}
	return GetCurrentDirectory();
end intrinsic



intrinsic SmallFusionSystem(S_order::RngIntElt, i::RngIntElt) -> FusionSystem
	{Return the i-th fusion system on a group of order S_order}
	// Recall that loading the fusion system record does not load the fusion system
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	filename := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, i);
	return LoadFusionSystem(filename);
end intrinsic;



intrinsic SmallFusionSystemRecord(S_order::RngIntElt, i::RngIntElt) -> Rec 
	{Return the record only for a small fusion system}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	filename := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, i);
	return LoadFusionSystemRecord(filename);
end intrinsic;



intrinsic IdentifyFusionSystem(F::FusionSystem) -> SeqEnum
	{If F is a small fusion system return its identifying pair}
	S := F`group;
	m := NumberSmallFusionSystems(#S);
	for i in [1..m] do 
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


intrinsic AddSmallFusionSystem(F::FusionSystem)
	{Given a fusion system check if it is already in the database, otherwise add it}
	S := F`group;
	m, indices := NumberSmallFusionSystems(S);
	new := true;
	for i in indices do 
		F_i := SmallFusionSystem(#S, i);
		printf "Checking if F is isomorphic to fusion system %o", i;
		if IsIsomorphic(F_i, F) then
			print "Fusion system is already in database \n";
			new := false;
			break;
		end if;
	end for;

	if new then
		p := FactoredOrder(S)[1][1];
		n := FactoredOrder(S)[1][2];
		filepath := Sprintf("data/SmallFusionSystems/p_%o/n_%o", p, n);
		System(Sprintf("mkdir -p %o", filepath));
		filename := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, NumberSmallFusionSystems(#S) + 1);
		WriteFusionRecord(filename, F);
		print "Successfully added new fusion system \n";
		UpdateLog(Sprintf(
			"Added SmallFusionSystem(%o^%o, %o)", p, n, NumberSmallFusionSystems(#S) + 1));
	end if;
end intrinsic;


intrinsic AddSmallFusionSystems(FS::SeqEnum)
	{Given a list of fusion systems, add them to the database}
	for F in FS do 
		AddSmallFusionSystem(F);
	end for;
end intrinsic;


intrinsic AllSmallFusionSystems(S::Grp) -> SeqEnum
	{Given a group S return all small fusion systems over S}
	m, indices := NumberSmallFusionSystems(S);
	FS := [LoadFusionSystem(SmallFusionSystemRecord(#S, i)) : i in indices ];
	return(FS);
end intrinsic;


intrinsic AllSmallFusionSystems(S_order::RngIntElt) -> SeqEnum
	{Return all small fusion systems on a p-group of S_order}
	FS := [SmallFusionSystem(S_order,i) : i in [1..NumberSmallFusionSystems(S_order)]];
	return(FS);
end intrinsic;



intrinsic NumberSmallFusionSystems(S_order::RngIntElt) -> RngIntElt
	{Returns the number of small fusion systems over a group of order S_order}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	path := Sprintf(" data/SmallFusionSystems/p_%o/n_%o/", p, n);
	try 
		files := Pipe("ls" cat path, "");
	catch e
		return 0;
	end try;
    filelist := Split(files, "\n");
    count := #[s : s in filelist | Split(s, "_")[1] eq "FS" and #Split(s, ".") eq 1];
    return(count);
end intrinsic;



intrinsic NumberSmallFusionSystems(S::Grp) -> RngIntElt, SeqEnum
	{Returns the number of small fusion systems over S and the indices of them}
	p := FactoredOrder(S)[1][1];
	n := FactoredOrder(S)[1][2];
	indices := [];
	m := NumberSmallFusionSystems(#S);
	for i in [1..m] do 
		R := SmallFusionSystemRecord(#S, i);
		if IsIsomorphic(S, R`S) then 
			Append(~indices, i);
		end if;
	end for;
	return #indices, indices;
end intrinsic;



intrinsic AllSmallFusionSystemsGroups(S_order::RngIntElt) -> SeqEnum
	{Given S_order return a list of all groups which have a small fusion system}
	grps := [];
	m := NumberSmallFusionSystems(S_order);
	for i in [1..m] do 
		R := SmallFusionSystemRecord(S_order,i);
		S := R`S;
		if forall{not IsIsomorphic(S,T) : T in grps} then
			Append(~grps, S);
		end if;
	end for;
	return grps;
end intrinsic;



intrinsic UpdateSmallFusionSystems(S_order::RngIntElt)
	{Update the files in the SmallFusionSystems S_order database}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	path := Sprintf("data/SmallFusionSystems/p_%o/n_%o/", p, n);
	F_list := Split(Pipe("ls " cat path, ""), "\n");
	// Get only file names with no extension
	F_list := [x : x in F_list | #Split(x, ".") eq 1];
	for i in F_list do 
		filename := path cat i;
		UpdateFusionRecord(filename);
		printf "Updated %o \n", i;
	end for;
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
			// Get only file names with no extension
			F_list := [x : x in F_list | #Split(x, ".") eq 1];
			for i in F_list do 
				filename := n_path cat i;
				UpdateFusionRecord(filename);
				printf "Updated %o \n", i;
			end for;
		end for;
	end for;
end intrinsic;



intrinsic VerifyAllSmallFusionSystemRecords()
	{Check that every fusion record at least returns a fusion system}
	p_list := Pipe("ls " cat "data/SmallFusionSystems", "");
	p_list := Split(p_list, "\n");
	errors := [];
	for p in p_list do 
		path := Sprintf("data/SmallFusionSystems/%o", p);
		n_list := Pipe("ls " cat path, "");
		n_list := Split(n_list, "\n");
		for n in n_list do 
			n_path := path cat Sprintf("/%o/", n);
			F_list := Split(Pipe("ls " cat n_path, ""), "\n");
			// Get only file names with no extension
			F_list := [x : x in F_list | #Split(x, ".") eq 1];
			for i in F_list do 
				filename := n_path cat i;
				try 
					F := LoadFusionSystem(filename);
					printf "Verified %o \n", filename;
				catch e
					printf "Failed to load %o \n", filename;
					Append(~errors);
				end try;
			end for;
		end for;
	end for;
	print errors;
end intrinsic;
