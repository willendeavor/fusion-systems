// Functions that deal with printing, saving fusion systems



intrinsic Print(F::FusionSystem)
	{Print F}

	E:= [(#F`essentialautos[i]*#Centre(F`essentials[i]))/#F`essentials[i]:i in [2.. #F`essentialautos]];
	E1:= [#F`essentials[i]:i in [2.. #F`essentials]];
	S := F`group;
	try 
		S_name := IdentifyGroup(F`group);
	catch e
		S_name := <0,0>;
	end try;
 
	if assigned F`saturated and F`saturated eq true then
		printf "Saturated fusion system F over a p-group S of order %o^%o \n", FactoredOrder(S)[1][1], FactoredOrder(S)[1][2]; 
	else
		printf "Fusion system F over a p-group S of order %o^%o \n", FactoredOrder(S)[1][1], FactoredOrder(S)[1][2];
	end if;
	
	if not S_name eq <0,0> then
		printf "S is SmallGroup(%o, %o) and isomorphic to %o \n", S_name[1], S_name[2], GroupName(S); 
	else
		printf "S is isomorphic to %o \n", GroupName(S);
	end if;

	printf "F has %o classes of essential subgroups \n", #F`essentials-1;
	printf "The orders of the essential subgroups are %o \n", E1;
	printf "The orders of the Out_F(E) are %o \n", E;
	printf "The order of Out_F(S) is %o", #F`essentialautos[1]/#Inn(F`group);
	if assigned(F`fusion_group) then
		printf "\n F is isomorphic to the group fusion system of %o", GroupName(F`fusion_group); 
	end if;
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




intrinsic SaveAsGo(  count::RngIntElt, F::FusionSystem)
	{}
	grp:= #F`group;
	bor:= #F`borel;
	FileName:="F" cat IntegerToString(grp) cat "-" cat IntegerToString(bor) cat "-" 
	cat IntegerToString(count);
	              SaveFS(FileName, [F]);
end intrinsic;