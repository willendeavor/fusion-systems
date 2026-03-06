Updating and Verification

#### UpdateSmallFusionSystems

`UpdateSmallFusionSystems(S_order::RngIntElt)`

Calls `UpdateFusionRecord` on every small fusion system over a group of the given order

---

#### UpdateAllSmallFusionSystems

`UpdateAllSmallFusionSystems()`

Calls `UpdateFusionRecord` on every fusion system in the SmallFusionSystems database so changes made to the fusion record format can be reflected on every file.

#### UpdateSmallFusionSystemAttributes

`UpdateSmallFusionSystemAttributes(order :: RngIntElt, i::RngIntElt, options::SeqEnum[MonStgElt] : FusionGroup := false)`

Updates the given options from the small fusion systems record, options should be a sublist of ["Core", "OpTriv", "FocalSubgroup", "pPerfect", "FusionGroup"], if "FusionGroup" is passed then FusionGroup should be passed with the group.

---

#### UpdateSmallFusionSystemAttribute

`UpdateSmallFusionSystemAttribute(order :: RngIntElt, i::RngIntElt, option::MonStgElt : FusionGroup := false)`

Updates the given option from the small fusion systems record i.e. option is one of ["Core", "OpTriv", "FocalSubgroup", "pPerfect", "FusionGroup"], if "FusionGroup" is passed then FusionGroup should be passed with the group.

---

#### UpdateAllSmallFusionSystemsAttributes

`UpdateAllSmallFusionSystemsAttributes(order::RngIntElt, options::SeqEnum[MonStgElt] : resume := 1)`

Calls UpdateSmallFusionSystemAttributes on every small fusion system over a group of the given order, note "FusionGroup" is not an option here.

---

#### VerifyAllSmallFusionSystemRecords

`VerifyAllSmallFusionSystemRecords(resume::SeqEnum)`

Checks that every file in the SmallFusionSystems database successfully returns a fusion system. Resume should be a list [p,n,i] such that fusion systems from then on are verified.

#### CheckDuplicatesSmallFusionSystem

`CheckDuplicatesSmallFusionSystem(order::RngIntElt: resume := 1) -> SeqEnum`

Checks if there are duplicate isomorphic fusion systems over groups of the given order, resume allows you to start checking from SmallFusionSystem(order, i). Returns a list of duplicates if there are any.
