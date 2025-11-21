# all-fusion-systems.m

Contains the functionality for generating all fusion systems over a given $p$-group. This is the major WIP in terms of refactoring so currently only contains one intrinsic.


### AllFusionSystems

`AllFusionSystems(S::Grp:SaveEach:=false,Printing:=false,OutFSOrders:=[],OpTriv:=true,pPerfect:= true)-> SeqEnum`

A currently very large intrinsic which given a p-group S will return a list of all saturated fusion systems over S such that O^p(F) = F and O_p(F) = 1, this can be changed with the optional arguments. 
This is perhaps the most important function to be rewritten so I expect many changes to be made in the future.