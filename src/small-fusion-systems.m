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
	print "Fusion system is not a small fusion system";
	return <0,0>;
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
	{Given a group fusion system find it in the SmallFusionSystem library and add the fusion_group}
	require assigned F`fusion_group : "F is not a group fusion system (or at least it is not assigned)";
	pair := IdentifyFusionSystem(F);
	G := F`fusion_group;
	// Replace G by G/O_{p'}(G)
	if pair eq <0,0> then
		message := Sprintf("Adding group fusion system of %o", GroupName(G));
		UpdateLog(message);
		AddSmallFusionSystem(F);
	else
		R := SmallFusionSystemRecord(pair[1], pair[2]);
		if (assigned R`fusion_group and overwrite eq true) or not assigned R`fusion_group then
			UpdateSmallFusionSystemAttributes(pair[1], pair[2], ["fusion_group"] : fusion_group := G);
			message := Sprintf("Added fusion_group to SmallFusionSystem(%o, %o)", pair[1], pair[2]);
			UpdateLog(message);
		else
			printf "SmallFusionSystem(%o, %o) already has group %o attached \n", pair[1], pair[2], R`fusion_group_name;
		end if;
	end if;
end intrinsic;


intrinsic AddAllGroupFusionSystems(G::Grp) 
	{Given a group G add every group fusion system it yields}
	bounds := [
		[2,3], [2,4], [2,5], [2,6], [2,7], [2,8],
		[3,3], [3,4], [3,5], [3,6], [3,7],
		[5,3], [5,4], [5,5], [5,6],
		[7,3], [7,4], [7,5]
		];
	divisors := FactoredOrder(G);
	for factor in divisors do 
		p := factor[1];
		n := factor[2];
		if [p,n] in bounds then 
			printf "Making the fusion system over (p,n) = (%o,%o) \n", p,n;
			F := GroupFusionSystem(G,p);
			AddGroupFusionSystem(F);
		end if; 
	end for;
end intrinsic;


intrinsic AddAllSimpleGroupFusionSystems(resume::RngIntElt: skips := false)
	{Add every possible group fusion system from the simple groups database}
	for i in [resume..NumberOfSimpleGroups()] do 
		printf "Adding SimpleGroupId(%o) \n", i;
		try
			G := SimpleGroup(SimpleGroupId(i));
			name := GroupName(G);
			print name;
			if "PSL(2," in name
					or "2A(2," in name and skips then
				continue;
			end if;
			message := Sprintf("Making all fusion systems of SimpleGroup(%o): %o", i, name);
			print message;
			UpdateLog(message);
		catch e 
			message := Sprintf("Could not load SimpleGroupId(%o)", i);
			print message;
			ErrorLog(message);
			continue;
		end try;
		AddAllGroupFusionSystems(G);
	end for;
end intrinsic;


intrinsic AddAllGroupFusionSystemsLieType(min_order, max_order)
	{Adds all group fusion systems from groups of lie type of bounded order}
	bounds := [
		[2,3], [2,4], [2,5], [2,6], [2,7], [2,8],
		[3,3], [3,4], [3,5], [3,6], [3,7],
		[5,3], [5,4], [5,5], [5,6],
		[7,3], [7,4], [7,5]
		];
	ns := [2,3,4,5];
	lies := ["B", "C", "D", "E", "F", "G", "2A", "2B", "2C", "2D", "2E", "2F", "2G", "3D"];
	for lie in lies do 
		for bound in bounds do  
			for n in ns do 
				q := bound[1]^bound[2];
				name := lie cat Sprintf("(%o, %o)", n,q);
				try 				
					G := SimpleGroup(name);
				catch e 
					continue;
				end try;
				if #G ge max_order or #G le min_order then
					continue;
				end if;
				message := Sprintf("Adding all fusion systems of %o", name);
				print(message);
				UpdateLog(message);
				AddAllGroupFusionSystems(G);
			end for;
		end for;
	end for;
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
			printf "Calculating direct product of (%o, %o) and (%o, %o)", order_1,i, order_2, j;
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




























































