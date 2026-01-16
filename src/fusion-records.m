// Functions that convert a fusion system to an entry in the SmallFusionSystems database
// and generally work directly with the record files


function GetOptionalArgs()
	optional := [
    		"core",
    		"core_trivial",
    		"pPerfect",
    		"focal_subgroup",
    		"fusion_group",
    		"fusion_group_name",
    		"indecomposable",
    		"factors"
    	];
	return optional;
end function;



// Given S and a subgroup of S return the string sub<S | gens >;
function SubgroupToString(S,T)
	rel := {S!w:w in PCGenerators(T)};
	return Sprintf("sub<S | %o>", rel);
end function;


// Function that takes a fusion system and returns a completed fusion record
// Idea is that the record does not do any major computations but stores enough to
// compare different fusion systems
function FusionToRecord(FS)
	FusionRecord := recformat<
		p : RngIntElt,
		S : Grp, 
		S_order: RngIntElt,
		S_name : MonStgElt,
		S_small_group_id : Tup, 
		EssentialData : SeqEnum,
		core: Grp, 
		core_trivial : BoolElt,
		pPerfect: BoolElt,
		focal_subgroup : Grp,
		fusion_group_name : MonStgElt,
		fusion_group : Grp,
		indecomposable : BoolElt,
		factors : SeqEnum
		>;

	EssentialRecord := recformat< 
		E : Grp, 
		E_order : RngIntElt,
		E_name : MonStgElt,
		AutFE_order : RngIntElt,
		AutFE_name : MonStgElt,
		AutFE_gens : SeqEnum
		>;
	S := PCGroup(FS`group);
	p := FactoredOrder(S)[1][1];
	S_order := #S;
	S_name := GroupName(S);
	try 
		S_small_group_id := IdentifyGroup(S);
	catch e
		S_small_group_id := <0,0>;
	end try;
	EssentialSeq := [];
    for i in [1..#FS`essentials] do
    	AutFE := FS`essentialautos[i];
        E := Group(AutFE);
        R := {S!w:w in PCGenerators(E)};
	    E:=sub<S|R>;
	    E_gens := SetToSequence(PCGenerators(E));
	    image_gens := [];
	    for alpha in Generators(AutFE) do 
	    	pairs := [<g, E!alpha(g)> : g in E_gens];
	    	Append(~image_gens, pairs);
	    end for;
        Append(~EssentialSeq,
            rec< EssentialRecord |
                E   := E,
                E_order := #E,
                E_name := GroupName(E),
                AutFE_order := #AutFE,
                AutFE_name := GroupName(AutFE),
                AutFE_gens  := image_gens
            >
        );
    end for;
    // Add the minimum record information
    R := rec< FusionRecord |
        p                := p,
        S                := S,
        S_order          := S_order,
        S_name           := S_name,
        S_small_group_id := S_small_group_id,
        EssentialData    := EssentialSeq
    >;

    // Now check any additional info
    optional := GetOptionalArgs();
    for x in optional do  
    	// We deal with this outside this loop
    	if x eq "fusion_group_name" or x eq "fusion_group" then 
    		continue;
    	end if;
    	if assigned FS``x then
    		// If FS``x is supposed to store a subgroup of S then get the PC presentation
    		if ISA(Type(FS``x), Grp) then
    			FS``x := sub<S | {S!w : w in PCGenerators(FS``x)}>;
    		end if;
    		R``x := FS``x;
    	end if;
    end for;

    // For backwards compatability check for both and separate from other optionals
    if assigned FS`grpsystem or assigned FS`fusion_group then
    	if assigned FS`grpsystem then
    		R`fusion_group := FS`grpsystem;
    	end if;
    	if assigned FS`fusion_group then 
    		R`fusion_group := FS`fusion_group;
    	end if;
    	if assigned FS`fusion_group_name then 
    		R`fusion_group_name := FS`fusion_group_name;
    	end if;
    end if;
    return R;
end function;


function WriteFusionYAML(filename, R)
	F := Open(filename cat ".yaml");
end function;




/* 
A VERY VERY ugly intrinsic that creates a file which can be loaded.
However MAGMA is very very awkward about loading files, ideally we would have 
just used load filename but MAGMA does not like this so instead what we do
is create a file which contains a temporary intrinsic which is then called to create
the record. From the record it is fairly straightforward to recover F
Ideally at some point we would remove the duplicate definition of FusionRecord
and EssentialRecord but for now, this works, although I don't like it
*/
intrinsic WriteFusionRecord(filename::MonStgElt, FS::FusionSystem)
	{Outputs a fusion record to a file}
    R := FusionToRecord(FS);
    F := Open(filename, "w");
    fprintf F, "intrinsic FusionRecordTemp() -> Rec \n {} \n";
    fprintf F, "
    FusionRecord := recformat<
		p : RngIntElt,
		S : Grp, 
		S_order: RngIntElt,
		S_name : MonStgElt,
		S_small_group_id : Tup, 
		EssentialData : SeqEnum,
		core: Grp, 
		core_trivial : BoolElt,
		pPerfect: BoolElt,
		focal_subgroup : Grp,
		fusion_group_name : MonStgElt,
		fusion_group : Grp,
		indecomposable : BoolElt,
		factors : SeqEnum
		>;

	EssentialRecord := recformat< 
		E : Grp, 
		E_order : RngIntElt,
		E_name : MonStgElt,
		AutFE_order : RngIntElt,
		AutFE_name : MonStgElt,
		AutFE_gens : SeqEnum
		>; \n";
    S := R`S;
    // Print S as a PCGroup with generators that can be loaded
    fprintf F, "\n";
    fprintf F, "  S :=";
    delete F;
    PrintFileMagma(filename, S);
    F := Open(filename, "a");
    fprintf F, "; \n";
    fprintf F, "";
    // Need to create the essential records before assigning then
    fprintf F, "EssentialData := [];\n";
    for i in [1..#R`EssentialData] do
    	ER := R`EssentialData[i];
    	E := ER`E;
    	A := ER`AutFE_gens;
    	// We have to define E outside of the record otherwise we lost subgroup information
    	fprintf F, "\n";
    	fprintf F, "E := %o; \n", SubgroupToString(S,E);
        fprintf F, "ER := rec< EssentialRecord |\n";
   		fprintf F, "E := %o, \n", SubgroupToString(S,E);
   		fprintf F, "E_order := %o, \n", ER`E_order;
   		fprintf F, "E_name := \"%o\", \n", ER`E_name;
   		fprintf F, "AutFE_order := %o, \n", ER`AutFE_order;
	    fprintf F, "AutFE_gens := %o, \n", A;
	    fprintf F, "AutFE_name := \"%o\" \n", ER`AutFE_name;
        fprintf F, "	>; \n";
        fprintf F, "Append(~EssentialData, ER); \n";
    end for;

    
   

    fprintf F, "R := rec< FusionRecord |\n";
    fprintf F, "p := %o,\n", R`p;
    fprintf F, "S := S, \n";
    fprintf F, "S_order := %o,\n", R`S_order;
    fprintf F, "S_name := \"%o\",\n", R`S_name;
    fprintf F, "S_small_group_id := %o,\n", R`S_small_group_id;

    // Essentials
    fprintf F, "EssentialData := EssentialData";


    // Optional info
    optional := GetOptionalArgs();
    // If no optionals defined closed records assignment
    if forall{x : x in optional | not assigned R``x} then 
    	fprintf F, ">;\n";
    // Otherwise add the optionals
    else 
    	options := [x : x in optional | assigned R``x];
    	fprintf F, ", \n";
    	// Get a list of values so we can change types if necessary e.g. group to string
    	// Not using an actual list since types vary
    	info := AssociativeArray(options);
    	for i in options do
    		// Deal with groups
    		if ISA(Type(R``i), Grp) then
    			// If subgroup of S then we save it as a subgroup construction
    			if ISA(Type(R``i), GrpPC) and R``i subset S then 
    				info[i] := SubgroupToString(S,R``i);
    			// Otherwise it must be the fusion_group and we save it how MAGMA likes			
    			else
    				// We want it as a string so create a temp file
    				PrintFileMagma("temp_fusion_group.m", R``i);
    				info[i] := Read("temp_fusion_group.m");
    				System("rm temp_fusion_group.m");
    			end if;

    		// If string then surround in quotes so is string when defined
			elif ISA(Type(R``i), MonStgElt) then
				info[i] := Sprintf("\"%o\"", R``i);
    		// Otherwise straightforward saving	
    		else
    			info[i] := R``i;
    		end if;
    	end for;
    	for i in [1..#options -1] do 
    		x := options[i];
    		fprintf F, "%o := %o, \n", x, info[x];
    	end for;
    	// Save last one so trailing comma is not added
    	fprintf F, "%o := %o >; \n", options[#options], info[options[#options]];
    end if;

    fprintf F, "return R; \n";
    fprintf F, "end intrinsic;";
    delete F;
end intrinsic;



intrinsic FusionRecordTemp() -> Rec
	{dummy intrinsic, yes really this is the workaround}
end intrinsic;


intrinsic LoadFusionSystemRecord(filename:: MonStgElt) -> Rec 
	{Loads a fusion system record given the file path}
	Attach(filename);
	R := FusionRecordTemp();
	Detach(filename);
	return R;
end intrinsic;


intrinsic LoadFusionSystem(R::Rec : load_group := false) -> FusionSystem
	{Creates a fusion system from a fusion system record}
	S := R`S;
	PS := PowerGroup(S);
	Autos := [];
	for E_rec in R`EssentialData do 
		E := PS!E_rec`E;
		AE := AutomorphismGroup(E);
		A := sub<AE | >;
		gens := [];
		for alpha in E_rec`AutFE_gens do
			phi := AE!hom<E -> E | alpha>;
			Append(~gens, phi);
		end for;
		A := sub<AE | gens>;
		Append(~Autos, A);
	end for;
	F := CreateFusionSystem(Autos);
	// If we can assign the optionals then do so
	optional := GetOptionalArgs();
	for x in optional do 
		if x in GetAttributes(FusionSystem) and x in Names(R) then
			if assigned R``x then
				// If want a subgroup of S we need to transport it to the Borel group
				if ISA(Type(R``x), Grp) and not x eq "fusion_group" and R``x subset S then
					F``x := F`borelmap(R``x);
				elif x eq "fusion_group" then
					if load_group then
						F``x := R``x;
					end if;
				else
					F``x := R``x;
				end if;
			end if; 
		end if;
	end for;
	return F;
end intrinsic;



intrinsic LoadFusionSystem(filename::MonStgElt: load_group := false) -> FusionSystem
	{Creates a fusion system from a database entry}
	R := LoadFusionSystemRecord(filename);
	return(LoadFusionSystem(R: load_group:=load_group));
end intrinsic;



intrinsic UpdateFusionRecord(filename::MonStgElt)
	{Given filename rewrite the record to reflect any changes made}
	F := LoadFusionSystem(filename);
	WriteFusionRecord(filename, F);
end intrinsic;



// Preloaded if you already have a fusion system loaded, helpful to avoid calling subgroups many times, corresponds to second entry
intrinsic IsIsomorphicFusionRecords(R_1::Rec, R_2::Rec : preloaded := 0, printing := false) -> Bool
	{Given two fusion records return if they are potentially isomorphic without constructing the fusion systems}
	// Trivial case
	if R_1 cmpeq R_2 then 
		return true;
	end if;

	// Check orders of everything first
	if not #R_1`EssentialData eq #R_2`EssentialData then 
		if printing then 
			print "Different number of essentials";
		end if;
		return false;
	end if;
	// We've already checked they have the same number of essentials so worry about duplicate orders
	orders_1 := {X`E_order : X in R_1`EssentialData};
	orders_2 := {X`E_order : X in R_2`EssentialData};
	if not orders_1 eq orders_2 then 
		if printing then 
			print "Essentials have different orders";
		end if;
		return false;
	end if;
	// Now check isomorphism of the essential subgroups
	for E_1 in R_1`EssentialData do 
		E := E_1`E;
		if not exists{E_2`E : E_2 in R_2`EssentialData | IsIsomorphic(E, E_2`E)} then
			if printing then 
				print "Non isomorphic essentials [1]";
			end if;
			return false;
		end if;
	end for;

	for E_2 in R_2`EssentialData do 
		E := E_2`E;
		if not exists{E_1`E : E_1 in R_1`EssentialData | IsIsomorphic(E, E_1`E)} then 
			if printing then 
				print "Non isomorphic essentials [2]";
			end if;
			return false;
		end if;
	end for;

	// Finally perform isomorphism test of the fusion systems
	if preloaded cmpeq 0 then
		F_2 := LoadFusionSystem(R_2);
	else
		F_2 := preloaded;
	end if;
	F_1 := LoadFusionSystem(R_1);
	return IsIsomorphic(F_1, F_2);
end intrinsic;












/* 
A one time intrinsic that is no longer needed
intrinsic ConvertDirectory(p::RngIntElt,n::RngIntElt)
	{Converts a directory in database p_i n_j to the new format}
	base_in := Sprintf("database/p_%o/n_%o", p,n);
	base_out := Sprintf("database/SmallFusionSystems/p_%o/n_%o", p, n);
	System(Sprintf("mkdir -p %o", base_out));
	files := Pipe("ls" cat base_in cat "/FS_*.m", "");
    filelist := Split(files, "\n");

    for fname in filelist do
        if fname eq "" then
            continue;
        end if;

        printf "Processing %o...\n", fname;

        // input and output paths
        inpath  := Sprintf("%o/%o", base_in, fname);
        outpath := Sprintf("%o/%o", base_out, fname);


        // Load FS from file
        FS := 0;
        Attach(inpath); 

        // Convert & write
        WriteFusionRecord(outpath, FS);
    end for;
end intrinsic;
*/


