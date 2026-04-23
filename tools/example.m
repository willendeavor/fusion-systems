G_1 := PGL(3,4);
G_2 := PGL(3,4);
G := MakeDirectProductGroup(G_1, G_2);
order := #G`group/3;
subs := [H`subgroup : H in Subgroups(G) | #H`subgroup eq order];
for H in subs do 
	if (not Image(G`embed[1]) subset H) and (not Image(G`embed[2]) subset H) then
		GG := H;
		break;
	end if;
end for;

F := GroupFusionSystem(GG, 2);
IdentifyFusionSystem(F);