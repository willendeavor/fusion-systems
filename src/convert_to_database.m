FusionRecord := recformat<
	p : RngIntElt,
	S_presentation : MonStgElt, 
	S_order: RngIntElt,
	S_name : MonStgElt,
	S_small_group_id : SeqEnum, 
	EssentialData : SeqEnum,
	OpTriv: Bool, 
	pPerfect: Bool
	>;

EssentialRecord := recformat< 
	E_presentation : MonStgElt, 
	AutE_generators : SeqEnum
	>;


function FusionToRecord(FS)
	S := PCGroup(FS`group);
	S_presentation := Sprint(S); 
	p := GetPrime(S);
	S_order := #S;
	S_name := GroupName(S);
	S_small_group_id := IdentifyGroup(S);
	EssentialSeq := [];
    for i in [1..#FS`essentials] do
        E := FS`essentials[i];
        EP := PCGroup(E);
        E_pres := Sprint(EP);

        A := FS`essentialautos[i];
        gens := [];

        // Each generator is stored as a sequence of strings
        for phi in Generators(A) do
            imgs := [ Sprint(phi(EP.j)) : j in [1..NPCgens(EP)] ];
            Append(~gens, imgs);
        end for;

        Append(~EssentialSeq,
            rec< EssentialRecord |
                E_presentation   := E_pres,
                AutE_generators  := gens
            >
        );
    end for;
    return rec< FusionRecord |
        p                := p,
        S_presentation   := S_presentation,
        S_order          := S_order,
        S_name           := S_name,
        S_small_group_id := S_small_group_id,
        EssentialData    := EssentialSeq
    >;
end function;


procedure WriteRecord(filename, FS)
    R := FusionToRecord(FS);
    F := Open(filename, "w");

    fprintf F, "rec< FusionRecord |\n";
    fprintf F, "  p := %o,\n", R`p;
    fprintf F, "  S_presentation := \"%o\",\n", R`S_presentation;
    fprintf F, "  S_order := %o,\n", R`S_order;
    fprintf F, "  S_name := \"%o\",\n", R`S_name;
    fprintf F, "  S_small_group_id := %o,\n", R`S_small_group_id;

    // Essentials
    fprintf F, "  EssentialData := [\n";
    for ER in R`EssentialData do
        fprintf F, "    rec< EssentialRecord |\n";
        fprintf F, "      E_presentation := \"%o\",\n", ER`E_presentation;
        fprintf F, "      AutE_generators := [\n";

        for gen in ER`AutE_generators do
            fprintf F, "        [ %o ],\n",
                Join([ "\"" cat x cat "\"" : x in gen ], ", ");
        end for;

        fprintf F, "      ]\n";
        fprintf F, "    >,\n";
    end for;
    fprintf F, "  ],\n";

    fprintf F, "  OpTriv := %o,\n", R`OpTriv;
    fprintf F, "  pPerfect := %o\n", R`pPerfect;
    fprintf F, ">;\n";

    delete F;
end procedure;




intrinsic ConvertDirectory(p::RngIntElt,n::RngIntElt)
	{Converts a directory in database p_i n_j to the new format}
	base_in := Sprintf("database/p_%o/n_%o", p,n);
	base_out := Sprintf("database/SmallFusionSystems/p_%o/n_%o", p, n);
	System(Sprintf("mkdir -p %o", base_out));
	files := Pipe("ls ",  base_in cat "/FS_*.m");
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
        eval Sprintf("load \"%o\";", inpath); 

        // Convert & write
        WriteRecord(outpath, FS);
    end for;
end intrinsic;



