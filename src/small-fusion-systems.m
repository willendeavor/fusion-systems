// Implements a database similar to SmallGroups


intrinsic SmallFusionSystem(S::Grp, i::RngIntElt) -> FusionSystem
	{Return the i-th fusion system on S}
end intrinsic;


intrinsic IdentifyFusionSystem(F::FusionSystem) -> SeqEnum
	{If F is a small fusion system return its identifying pair}
end intrinsic;


intrinsic AddSmallFusionSystem(F::FusionSystem)
	{Given a fusion system check if it is already in the database, otherwise add it}
	S := F`group;
	m := NumberSmallFusionSystems(#S);
	new := true;
	for i in [1..m] do 
		F_i := SmallFusionSystem(S, i);
		if not IsIsomorphic(S, F_i`group) then 
			continue;
		end if;
		if not #F_i`essentials eq #F`essentials then
			continue;
		end if;
		if IsIsomorphic(F_i, F) then
			new := false;
			break;
		end if;
	end for;

	if new then
		p := FactoredOrder(S)[1][1];
		n := FactoredOrder(S)[1][2];
		filename := Sprintf("/data/SmallFusionSystem/p_%o/n_%o/FS_%o", p, n, m + 1)
		WriteFusionRecord(filename, F);
	end if;
end intrinsic;


intrinsic AllSmallFusionSystems(S::Grp) -> SeqEnum
	{Given a group S return all small fusion systems over S}
end intrinsic;



intrinsic NumberSmallFusionSystems(S_order::RngIntElt) -> RngIntElt
	{Returns the number of small fusion systems over a group of order S_order}
	p := Factorisation(S_order)[1];
	n := Factorisation(S_order)[2];
	path := Sprintf("/data/SmallFusionSystem/p_%o/n_%o", p, n);
	files := Pipe("ls" cat base_in cat "/FS_*.m", "");
    filelist := Split(files, "\n");
    return(#filelist);
end intrinsic;


