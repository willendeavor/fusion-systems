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


// Returns an associate array of p : [n_1, n_2, ..] as strings
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


// Return associate array p:[n_1,...] as integers
function GetAllpnIntegers()
	pn := GetAllpn();
	p_ints := [StringToInteger(x) : x in Keys(pn)];
	pn_int := AssociativeArray(p_ints);
	for p in Keys(pn) do 
		n_ints := [StringToInteger(x) : x in pn[p]];
		pn_int[StringToInteger(p)] := n_ints;
	end for;
	return(pn_int);
end function;


procedure AddToVerificationQueue(order,i)
	filename := "data/verification_queue.log";
	F := Open(filename, "a");
	fprintf F, " \n %o : %o", order,i;
	delete F; 
end procedure;








//////////////////////// Loading SmallFusionSystems //////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic SmallFusionSystem(order::RngIntElt, i::RngIntElt :load_group := false) -> FusionSystem
	{Return the i-th fusion system on a group of given order}
	// Recall that loading the fusion system record does not load the fusion system
	F := LoadFusionSystem(GetSmallFusionSystemFilePath(order, i) :load_group := load_group);
	F`small_id := <order, i>;
	return F;
end intrinsic;



intrinsic SmallFusionSystemRecord(order::RngIntElt, i::RngIntElt: load_group := false) -> Rec 
	{Return the record only for a small fusion system}
	return LoadFusionSystemRecord(GetSmallFusionSystemFilePath(order, i):load_group := load_group);
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
    fs_files := [s: s in filelist | Split(s, "_")[1] eq "FS" and Split(s, ".")[2] eq "m"];
    indices := [Split(s, ".m")[1] : s in fs_files];
    all_indices := [StringToInteger(Split(s, "_")[4]) : s in indices];
    if almost_reduced then
    	indices := [];
    	for i in all_indices do  
    		R := SmallFusionSystemRecord(S_order, i);
    		if not assigned R`core_trivial or not assigned R`pPerfect then
    			continue;
    		end if;
    		if R`core_trivial eq true and R`pPerfect eq true then 
    			Append(~indices, i);
    		end if;
    	end for;
    	return #indices, indices;
    end if;
    return #all_indices, all_indices;
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


intrinsic NumberGroupFusionSystems(order::RngIntElt) -> RngIntElt, SeqEnum
	{Returns the number of fusion systems that have a group attached}
	p := Factorisation(order)[1][1];
	n := Factorisation(order)[1][2];
	indices := [];
	for i in [1..NumberSmallFusionSystems(order: almost_reduced:=false)] do  
		R := SmallFusionSystemRecord(order,i);
		if assigned R`fusion_group_name then 
			Append(~indices, i);
		end if;
	end for;
	return #indices, indices;
	end intrinsic;


intrinsic AllSmallFusionSystems(S::Grp: almost_reduced := true) -> SeqEnum
	{Given a group S return all small fusion systems over S}
	m, indices := NumberSmallFusionSystems(S:almost_reduced := almost_reduced);
	FS := [SmallFusionSystem(#S,i) : i in indices];
	return(FS);
end intrinsic;


intrinsic AllSmallFusionSystems(S_order::RngIntElt: almost_reduced := true) -> SeqEnum
	{Return all small fusion systems on a p-group of S_order}
	m, indices := NumberSmallFusionSystems(S_order:almost_reduced := almost_reduced);
	FS := [SmallFusionSystem(S_order,i) : i in indices];
	return(FS);
end intrinsic;


intrinsic AllSmallFusionSystemsRecords(S::Grp: almost_reduced := true) -> SeqEnum
	{Given a group S return all small fusion systems over S}
	m, indices := NumberSmallFusionSystems(S:almost_reduced := almost_reduced);
	FS := [SmallFusionSystemRecord(#S,i) : i in indices];
	return(FS);
end intrinsic;


intrinsic AllSmallFusionSystemsRecords(S_order::RngIntElt: almost_reduced := true) -> SeqEnum
	{Return all small fusion systems on a p-group of S_order}
	m, indices := NumberSmallFusionSystems(S_order:almost_reduced := almost_reduced);
	FS := [SmallFusionSystemRecord(S_order,i) : i in indices];
	return(FS);
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
	print "(p,n) : Almost reduced (Total) [Groups] \n";
	for pp in Keys(pn) do 
		for nn in pn[pp] do  
			p := StringToInteger(pp);
			n := StringToInteger(nn);
			printf "(%o, %o) : %o (%o) [%o] \n", 
				p,n, NumberSmallFusionSystems(p^n), NumberSmallFusionSystems(p^n : almost_reduced := false), NumberGroupFusionSystems(p^n);
		end for;
	end for;
end intrinsic




intrinsic NumberSmallFusionSystemsWithAttribute(attribute::MonStgElt) -> RngIntElt, SeqEnum
	{Returns the number of SmallFusionSystems which have attribute assigned}
	pn := GetAllpn();
	sfs := [];
	for pp in Keys(pn) do 
		for nn in pn[pp] do 
			p := StringToInteger(pp);
			n := StringToInteger(nn);
			m, indices := NumberSmallFusionSystems(p^n : almost_reduced := false);
			for i in indices do 
				R := SmallFusionSystemRecord(p^n, i);
				try
					if assigned R``attribute then
						Append(~sfs, <p,n,i>);
					end if;
				catch e
					continue;
				end try;
			end for;
		end for;
	end for;
	return #sfs, sfs;
end intrinsic;



intrinsic CalculateAllIndecomposableSFS(order::RngIntElt: almost_reduced := true) -> RngIntElt, SeqEnum
	{Calculates all indecomposable fusion systems on a group of given order}
	m, indices := NumberSmallFusionSystems(order);
	indecomposables := [];
	for i in indices do 
		F := SmallFusionSystem(order,i);
		if IsIndecomposable(F: strong_check := true) then
			printf "SmallFusionSystem(%o, %o) is indecomposable \n", order, i;
			Append(~indecomposables, i);
		end if;
	end for;
	printf "Of the %o fusion systems %o are decomposable", m, m - #indecomposables;
	return #indecomposables, indecomposables;
end intrinsic;



intrinsic NumberReducedSmallFusionSystems(order::RngIntElt) -> RngIntElt, SeqEnum
	{returns all reduced fusion systems (assuming the residual calculation is correct)}
	m, indices := NumberSmallFusionSystems(order);
	reduced := [];
	for i in indices do 
		F := SmallFusionSystem(order,i);
		if IsResidual(F) then
			Append(~reduced, i);
		end if;
	end for;
	return #reduced, reduced;
end intrinsic;





////////////////////////////// Adding fusion systems /////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic AddSmallFusionSystem(F::FusionSystem) -> BoolElt, SeqEnum
	{Given a fusion system check if it is already in the database, otherwise add it, returns whether a new one has been added}
	S := F`group;
	m, indices := NumberSmallFusionSystems(S:almost_reduced := false);
	// Compare records only for a drastic improvement in speed in certain cases
	temp_name := Sprintf("temp_candidate_%o_%o", Random(10^12), Cputime());
	temp_file := Sprintf("%o.m", temp_name);
	WriteFusionRecord(temp_name, F);
	R := LoadFusionSystemRecord(temp_name);
	for i in indices do 
		R_i := SmallFusionSystemRecord(#S, i);
		printf "Checking if F is isomorphic to fusion system %o \n", i;
		if IsIsomorphicFusionRecords(R_i, R: preloaded := F) then
			delete R;
			com := Sprintf("rm %o.*", temp_name);
			System(com);
			print "Fusion system is already in database \n";
			return false, [#S, i];
			break;
		end if;
	end for;
	com := Sprintf("rm %o", temp_name);
	System(com);
	p := FactoredOrder(S)[1][1];
	n := FactoredOrder(S)[1][2];
	filepath := Sprintf("data/SmallFusionSystems/p_%o/n_%o", p, n);
	System(Sprintf("mkdir -p %o", filepath));
	m, indices := NumberSmallFusionSystems(#S:almost_reduced := false);
	// Get the next available indice, accounting for gaps
	i := Minimum({1..m + 1} diff SequenceToSet(indices));
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
		elif not assigned R`fusion_group_name then 
			UpdateSmallFusionSystemAttributes(pair[1], pair[2], ["fusion_group"] : fusion_group := G);
			message := Sprintf("Added fusion_group_name to SmallFusionSystem(%o, %o)", pair[1], pair[2]);
			UpdateLog(message);
		else
			printf "SmallFusionSystem(%o, %o) already has group %o attached \n", pair[1], pair[2], R`fusion_group_name;
		end if;
	end if;
end intrinsic;


intrinsic AddAllGroupFusionSystems(G::Grp) 
	{Given a group G add every group fusion system it yields}
	bounds := [
		[2,3], [2,4], [2,5], [2,6], [2,7], [2,8], [2,9], [2,10],
		[3,3], [3,4], [3,5], [3,6], [3,7], [3,8],
		[5,3], [5,4], [5,5], [5,6], [5,7],
		[7,3], [7,4], [7,5]
		];
	divisors := FactoredOrder(G);
	for factor in divisors do 
		p := factor[1];
		n := factor[2];
		if [p,n] in bounds then 
			printf "Making the fusion system over (p,n) = (%o,%o) \n", p,n;
			F := GroupFusionSystem(G,p);
			print "made";
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




function GetAlmostSimpleGroups(S)
	// Given S simple get all the almost simple groups S < G < Aut(S)
	MakeAutos(S);
	I := sub<S`autoperm | {S`autopermmap(x) : x in Generators(Inn(S))}>;
	OutS, pi := S`autoperm/I;
	GroupName(OutS);
	CC := SubgroupClasses(OutS);
	subs := [Inverse(pi)(C`subgroup) : C in CC];
	return subs;
end function;





intrinsic AddAllOuterAutomorphismGroupFusionSystems(G::Grp)
	{Add all group fusion systems of H where G < H < Aut(G)}
	almost_simples := GetAlmostSimpleGroups(G);
	almost_simples;
	for H in almost_simples do 
		GroupName(H);
		AddAllGroupFusionSystems(H);
	end for;
end intrinsic;



intrinsic AddAllAlmostSimpleGroupFusionSystems(resume::RngIntElt: skips := false)
	{Add every possible group fusion system from almost simple groups}
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
			message := Sprintf("Making all fusion systems over Almost Simple groups of SimpleGroup(%o): %o", i, name);
			print message;
			UpdateLog(message);
		catch e 
			message := Sprintf("Could not load SimpleGroupId(%o)", i);
			print message;
			ErrorLog(message);
			continue;
		end try;
		almost_simples := GetAlmostSimpleGroups(G);
		for H in almost_simples do 
			printf "Doing it for %o", GroupName(H);
			AddAllGroupFusionSystems(H);
		end for;
	end for;
end intrinsic;






intrinsic AddAllGroupFusionSystemsLieType(min_order, max_order)
	{Adds all group fusion systems from groups of lie type of bounded order}
	bounds := [
		[2,3], [2,4], [2,5], [2,6], [2,7], [2,8], [2,9], [2,10],
		[3,3], [3,4], [3,5], [3,6], [3,7], [3,8],
		[5,3], [5,4], [5,5], [5,6], [5,7],
		[7,3], [7,4], [7,5]
		];
	qs := [x : x in [1..100] | #Factorisation(x) eq 1];
	ns := [2,3,4,5];
	lies := ["B", "C", "D", "E", "F", "G", "2A", "2B", "2C", "2D", "2E", "2F", "2G", "3D"];
	for n in ns do 
		for q in qs do  
			for lie in lies do 
				completed_log := Open("data/lie_added.info", "r");
				lines := [];
				while true do
				    line := Gets(completed_log); 
				    if IsEof(line) then
				        break;
				    end if;
				    Append(~lines, line);
				end while;
				delete completed_log;
				name := lie cat Sprintf("(%o, %o)", n,q);
				if name in lines then
					continue;
				end if;
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
				completed_log := Open("data/lie_added.info", "a");
				fprintf completed_log, "%o\n", name;
				delete completed_log;
			end for;
		end for;
	end for;
end intrinsic;



intrinsic AddAllFusionSystems(order::RngIntElt : resume := 1, OpTriv := true, pPerfect := true, id_list := [])
    {Add all fusion systems over a group of given order}
    if resume eq 1 and id_list eq [] then
    	UpdateLog(Sprintf("Attempting to add all fusion systems of order %o", order));
    end if;

    if id_list eq [] then
    	id_list := [resume..NumberOfSmallGroups(order)];
    end if;
    print "hey";
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



intrinsic AddAllDirectProducts(order_1::RngIntElt, order_2::RngIntElt : resume := [1,1], almost_reduced := false)
	{Create all direct products of all small fs starting at SFS(order_1, resume[1]) and SFS(order_2, resume[2])}
	m,indices := NumberSmallFusionSystems(order_1:almost_reduced := almost_reduced);
	factors_1 := [x : x in indices | x ge resume[1]];

	for i in factors_1 do 
		if order_1 eq order_2 then
			if i eq resume[1] then
				range := [x : x in indices | x ge resume[2]];
			else
				range := [x : x in indices | x ge i];
			end if;
			
		else
			m, indices := NumberSmallFusionSystems(order_2 : almost_reduced := almost_reduced);
			if i eq resume[1] then
				range := [x : x in indices | x ge resume[2]];
			else
				range := indices;
			end if;
		end if;
		for j in range do  
			F_1 := SmallFusionSystem(order_1, i);
			F_2 := SmallFusionSystem(order_2, j);
			message := Sprintf("Calculating direct product of (%o, %o) and (%o, %o)", order_1,i, order_2, j);
			print message;
			UpdateLog(message);
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





/*
intrinsic CreateList()
{}
	F := Open("data/to_update.info", "a");
	pn := GetAllpnIntegers();
	for p in Keys(pn) do
		for n in pn[p] do
			m, indices := NumberSmallFusionSystems(p^n : almost_reduced := false);
			for i in [1..m] do  
				fprintf F, "%o : %o \n", p^n, i;
			end for;
		end for;
	end for;
	delete F;
end intrinsic;
*/





























































