// Functions that deal with printing, saving fusion systems



intrinsic Print(F::FusionSystem)
	{Print F}

	E:= [(#F`essentialautos[i]*#Centre(F`essentials[i]))/#F`essentials[i]:i in [2.. #F`essentialautos]];
	E1:= [#F`essentials[i]:i in [2.. #F`essentials]];
	printf "Fusion System with %o", #F`essentials-1; printf "\ F-classes of essential subgroups", "\n"; 
	printf "\nThey have orders: %o", E1, "\n"; 
	printf "\Out_F(E)  have orders: %o", E; printf 
	"\nOut_\F(S) has order  %o", #F`essentialautos[1]/#Inn(F`group);
	if assigned(F`grpsystem) then
	printf "\nThis is a group fusion system\n"; end if;
end intrinsic;



intrinsic SaveFS(FileName::MonStgElt, F::FusionSystem)
	{Saves fusion system to FileName so that it can be loaded}

	S:=Group(F`essentialautos[1]);
	PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
	PrintFile (FileName, "Autos:=[];\n");
	for k := 1 to #F`essentials do
	    A:=F`essentialautos[k];
	    E:= Group(A);
	    R := [S!w:w in PCGenerators(E)];
	    PrintFile(FileName,"E:=sub<S|");
	    PrintFile(FileName,R);
	    PrintFile(FileName,">;\n");
	    E:=sub<S|R>;
	    PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
	    PrintFile(FileName,"A:=sub<AE|>;\n");
	    for ii := 1 to #Generators(A) do
	        alpha:=A.ii;
	        PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
	        gens:=SetToSequence(PCGenerators(E));
	        for i in [1..#gens-1] do
	            x:= E!gens[i];
	            PrintFile(FileName,"<");
	            PrintFile(FileName,x);
	            PrintFile(FileName,",");
	            PrintFile(FileName,E!alpha(x));
	            PrintFile(FileName,">");
	            PrintFile(FileName,",");
	        end for;
	        x:= gens[#gens];
	        PrintFile(FileName,"<");
	        PrintFile(FileName,x);
	        PrintFile(FileName,",");
	        PrintFile(FileName,E!alpha(x));
	        PrintFile(FileName,">");
	        PrintFile(FileName," ]>>;\n");
	    end for;
	PrintFile(FileName,"Autos[");
	PrintFile(FileName,k);
	PrintFile(FileName,"]:=A;\n");
	end for;
	PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
	PrintFile(FileName,"FS;");
end intrinsic;




intrinsic SaveFS(FileName::MonStgElt, FF::SeqEnum)
	{Saves sequence of fusion systems to FileName so that it can be loaded}


	PrintFile(FileName,"FFS:=[];");

	for F in FF do      
	    S:=Group(F`essentialautos[1]);
	    PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
	    PrintFile (FileName, "Autos:=[];\n");
	    for k := 1 to #F`essentials do
	        A:=F`essentialautos[k];
	        E:= Group(A);
	        R := [S!w:w in PCGenerators(E)];
	        PrintFile(FileName,"E:=sub<S|");
	        PrintFile(FileName,R);
	        PrintFile(FileName,">;\n");
	        E:=sub<S|R>;
	        PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
	        PrintFile(FileName,"A:=sub<AE|>;\n");
	        for ii := 1 to #Generators(A) do
	            alpha:=A.ii;
	            PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
	            gens:=SetToSequence(PCGenerators(E));
	            for i in [1..#gens-1] do
	                x:= E!gens[i];
	                PrintFile(FileName,"<");
	                PrintFile(FileName,x);
	                PrintFile(FileName,",");
	                PrintFile(FileName,E!alpha(x));
	                PrintFile(FileName,">");
	                PrintFile(FileName,",");
	            end for;
	            x:= gens[#gens];
	            PrintFile(FileName,"<");
	            PrintFile(FileName,x);
	            PrintFile(FileName,",");
	            PrintFile(FileName,E!alpha(x));
	            PrintFile(FileName,">");
	            PrintFile(FileName," ]>>;\n");
	        end for;
	    PrintFile(FileName,"Autos[");
	    PrintFile(FileName,k);
	    PrintFile(FileName,"]:=A;\n");
	    end for;
	    PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
	    PrintFile(FileName, "FFS:=Append(FFS,FS);");
	end for;
	PrintFile(FileName,"FFS;");
end intrinsic;