// Testing IsResidual
flag := true;
// Residual example: F_S(PSU(4,p))
F := GroupFusionSystem(PSU(4,5),5);
if IsResidual(F) eq false then
	flag := false;
	print "Test failed: PSU(4,5)";
end if;

// Non-residual example: 