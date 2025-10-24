freeze;

declare type FusionSystem;
declare attributes  FusionSystem: prime, group, subgroups, borel, centrics, 
essentials, essentialautos, fusiongraph, maps, classes, AutF, saturated,
grpsystem, grppgrp, mapbackgrp;

declare attributes GrpMat: autogrp,  autoperm, autopermmap,autF;
declare attributes GrpPerm: autogrp, autoperm, autopermmap, autF;
declare attributes GrpPC: autogrp, autoperm, autopermmap, autF;

Attach("general-group.m");
Attach("general-fusion-system.m");
Attach("properties-fusion-systems.m");
Attach("group-properties-fusion-system.m");
Attach("generating-fusion-systems.m");
Attach("saving-fusion-system.m");