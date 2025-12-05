// Implements a database similar to SmallGroups


intrinsic GetSmallFusionSystemDirectory() -> MonStgElt
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


intrinsic FusionRecordTemp() -> Rec
	{dummy intrinsic, yes really this is the workaround}
end intrinsic;


intrinsic LoadFusionSystemRecord(filename:: MonStgElt) -> Rec 
	{Loads a fusion system record given the file path}
	Attach(filename);
	R := FusionRecordTemp();
	return R;
end intrinsic;


intrinsic SmallFusionSystemRecord(S_order::RngIntElt, i::RngIntElt) -> Rec 
	{Return the record only for a small fusion system}
	p := Factorisation(S_order)[1][1];
	n := Factorisation(S_order)[1][2];
	filename := Sprintf("data/SmallFusionSystems/p_%o/n_%o/FS_%o", p, n, i);
	return LoadFusionSystemRecord(filename);
end intrinsic;


intrinsic LoadFusionSystem(R::Rec) -> FusionSystem
	{Creates a fusion system from a fusion system record}
	S := R`S;
	Autos := [];
	for E_rec in R`EssentialData do 
		E := E_rec`E;
		AE := AutomorphismGroup(E);
		gens := [];
		for alpha in E_rec`AutFE_gens do
			Append(~gens, AE!hom<E -> E | alpha>);
		end for;
		A := sub<AE | gens>;
		Append(~Autos, A);
	end for;
	return(CreateFusionSystem(Autos));
end intrinsic;


intrinsic LoadFusionSystem(filename::MonStgElt) -> FusionSystem
	{Creates a fusion system from a database entry}
	R := LoadFusionSystemRecord(filename);
	return(LoadFusionSystem(R));
end intrinsic;


intrinsic IdentifyFusionSystem(F::FusionSystem) -> SeqEnum
	{If F is a small fusion system return its identifying pair}
	S := F`group;
	m := NumberSmallFusionSystems(#S);
	for i in [1..m] do 
		F_i := SmallFusionSystem(#S, i);
		if IsIsomorphic(F_i, F) then
			index := <#S, i>;
			printf "Input fusion system is small fusion system <%o, %o> \n";
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


