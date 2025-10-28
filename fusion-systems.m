freeze;

declare type FusionSystem;
declare attributes  FusionSystem: prime, group, subgroups, borel, centrics, 
essentials, essentialautos, fusiongraph, maps, classes, AutF, saturated,
grpsystem, grppgrp, mapbackgrp;

declare attributes GrpMat: autogrp,  autoperm, autopermmap,autF;
declare attributes GrpPerm: autogrp, autoperm, autopermmap, autF;
declare attributes GrpPC: autogrp, autoperm, autopermmap, autF;

Attach("src/general-group.m");
Attach("src/general-fusion-system.m");
Attach("src/properties-fusion-systems.m");
Attach("src/group-properties-fusion-system.m");
Attach("src/generating-fusion-systems.m");
Attach("src/saving-fusion-system.m");
Attach("src/all-fusion-systems.m");