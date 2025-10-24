// Functions related to properties of a subgroup within the fusion system


intrinsic IdentifyBClass(F::FusionSystem,P::Grp)->RngIntElt,GrpElt
    {Identifies a AutFS-conjugacy class}
     
     SS:= F`subgroups; B:= F`borel;
     for ii := 1 to #SS do 
        aa,bbb:=IsConjugate(B,P,SS[ii]);
        if aa then return ii,bbb; end if; 
     end for;
end intrinsic;


intrinsic IdentifyBClass(B::Grp,SS::SeqEnum,P::Grp)->RngIntElt,GrpElt
     {Identifies a AutFS-conjugacy class}
     
     for ii := 1 to #SS do 
        aa,bbb:=IsConjugate(B,P,SS[ii]);
        if aa then return ii,bbb; end if; 
     end for;
end intrinsic;