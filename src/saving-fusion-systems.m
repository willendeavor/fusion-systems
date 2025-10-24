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