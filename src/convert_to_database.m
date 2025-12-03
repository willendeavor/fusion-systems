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
		AutFE_gens : MonStgElt
		>;
	S := PCGroup(FS`group);
	p := FactoredOrder(S)[1][1];
	S_order := #S;
	S_name := GroupName(S);
	S_small_group_id := IdentifyGroup(S);
	EssentialSeq := [];
    for i in [1..#FS`essentials] do
    	AutFE := FS`essentialautos[i];
        E := FS`essentials[i];
        R := [S!w:w in PCGenerators(E)];
	    E:=sub<S|R>;
	    E_gens := SetToSequence(PCGenerators(E));
	    image_gens := [];
	    for alpha in Generators(AutFE) do 
	    	for x in E_gens do
	    		y := E!x;
	    		Append(~image_gens, <x, E!alpha(x)>);
	    	end for;
	    end for;
        Append(~EssentialSeq,
            rec< EssentialRecord |
                E   := E,
                E_name := GroupName(E),
                AutFE_name := GroupName(AutFE),
                AutFE_gens  := Sprint(image_gens)
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
the record.
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
		AutFE_gens : MonStgElt
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
    fprintf F, "  EssentialData := [\n";
    for i in [1..#R`EssentialData] do
    	ER := R`EssentialData[i];
    	E := ER`E;
    	A := ER`AutFE_gens;
    	rel := [S!w:w in PCGenerators(E)];
        fprintf F, "    rec< EssentialRecord |\n";
   		fprintf F, " E := sub<S| %o>, \n", rel;
   		fprintf F, "E_name := \"%o\", \n", ER`E_name;
	    fprintf F, "AutFE_gens := \"%o\", \n", A;
	    fprintf F, "AutFE_name := \"%o\" \n", ER`AutFE_name;
	    if i eq #R`EssentialData then
	    	fprintf F, "    >\n"; // Final line
	    	continue;
	    end if;
        fprintf F, "	>, \n"; // Continue listing otherwise
    end for;
    fprintf F, "  ];\n"; // Close EssentialData

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



