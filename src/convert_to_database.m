// Functions that convert a fusion system to an entry in the SmallFusionSystems database

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
		OpTriv: Bool, 
		pPerfect: Bool
		>;

	EssentialRecord := recformat< 
		E : Grp, 
		E_name : MonStgElt,
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
        E := FS`essentials[i];
        R := [S!w:w in PCGenerators(E)];
	    E:=sub<S|R>;
	    E_gens := SetToSequence(PCGenerators(E));
	    image_gens := [];
	    for alpha in Generators(AutFE) do 
	    	pairs := [<S!g, S!alpha(g)> : g in E_gens];
	    	Append(~image_gens, pairs);
	    end for;
        Append(~EssentialSeq,
            rec< EssentialRecord |
                E   := E,
                E_name := GroupName(E),
                AutFE_name := GroupName(AutFE),
                AutFE_gens  := image_gens
            >
        );
    end for;
    return rec< FusionRecord |
        p                := p,
        S   := S ,
        S_order          := S_order,
        S_name           := S_name,
        S_small_group_id := S_small_group_id,
        EssentialData    := EssentialSeq
    >;
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
		OpTriv: Bool, 
		pPerfect: Bool
		>;

	EssentialRecord := recformat< 
		E : Grp, 
		E_name : MonStgElt,
		AutFE_name : MonStgElt,
		AutFE_gens : SeqEnum
		>; \n";
    S := R`S;
    // Print S as a PCGroup with generators that can be loaded
    fprintf F, "  S :=";
    delete F;
    PrintFileMagma(filename, S);
    F := Open(filename, "a");
    fprintf F, "; \n";
    fprintf F, "";
    // Need to create the essential records before assigning then
    fprintf F, "  EssentialData := [];\n";
    for i in [1..#R`EssentialData] do
    	ER := R`EssentialData[i];
    	E := ER`E;
    	A := ER`AutFE_gens;
    	rel := [S!w:w in PCGenerators(E)];
    	fprintf F, " E := sub<S| %o>; \n", rel;
        fprintf F, "    ER := rec< EssentialRecord |\n";
   		fprintf F, " E := sub<S| %o>, \n", rel;
   		fprintf F, "E_name := \"%o\", \n", ER`E_name;
	    fprintf F, "AutFE_gens := %o, \n", A;
	    fprintf F, "AutFE_name := \"%o\" \n", ER`AutFE_name;
        fprintf F, "	>; \n";
        fprintf F, "Append(~EssentialData, ER);";
    end for;

    fprintf F, "R := rec< FusionRecord |\n";
    fprintf F, "  p := %o,\n", R`p;
    fprintf F, "  S := S, \n";
    fprintf F, "  S_order := %o,\n", R`S_order;
    fprintf F, "  S_name := \"%o\",\n", R`S_name;
    fprintf F, "  S_small_group_id := %o,\n", R`S_small_group_id;

    // Essentials
    fprintf F, "  EssentialData := EssentialData";
    if assigned(R`OpTriv) then
    	fprintf F, "  , OpTriv := %o,\n", R`OpTriv;
    end if;
    if assigned(R`pPerfect) then 
    	fprintf F, "  pPerfect := %o\n", R`pPerfect;
    end if;
    fprintf F, ">;\n";
    fprintf F, "return R; \n";
    fprintf F, "end intrinsic;";
    delete F;
end intrinsic;




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



