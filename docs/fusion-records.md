# Documentation: `small-fusion-systems.m`


## FusionRecordTemp

`FusionRecordTemp() -> Rec`  

A dummy intrinsic overwritten when loading a record file. Each file has its own definition of FusionRecordTemp(), this is defined only so the name is defined.

---

## LoadFusionSystemRecord

`LoadFusionSystemRecord(filename::MonStgElt) -> Rec`  

Loads the fusion system file `filename` and returns the record it constructs.

---

## LoadFusionSystem (record version)

`LoadFusionSystem(R::Rec) -> FusionSystem`  

Reconstructs a FusionSystem from a given FusionRecord.

---

## LoadFusionSystem (filename version)

`LoadFusionSystem(filename::MonStgElt) -> FusionSystem`  

Loads the record using `LoadFusionSystemRecord`, then reconstructs the FusionSystem.

---