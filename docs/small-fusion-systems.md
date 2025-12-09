# Documentation: `small-fusion-systems.m`

## Overview:

This file contains commands for accessing specifically the SmallFusionSystem database, convert-to-database contains commands for generally saving a fusion system record and maintaining the database. 


## SmallFusionSystem

`SmallFusionSystem(S_order::RngIntElt, i::RngIntElt) -> FusionSystem`  

Loads the *i-th* small fusion system on a group of order `S_order`.

---

## SmallFusionSystemRecord

`SmallFusionSystemRecord(S_order::RngIntElt, i::RngIntElt) -> Rec`  

Returns only the FusionRecord (not the fusion system) for the specified small fusion system.

---

## IdentifyFusionSystem

`IdentifyFusionSystem(F::FusionSystem) -> SeqEnum`  

Determines whether `F` matches one of the known small fusion systems (via isomorphism).  
Returns `<|S|, index>` or `<0,0>` if not in the database.

---

## AddSmallFusionSystem

`AddSmallFusionSystem(F::FusionSystem)`  

Checks whether `F` is already stored.  
If not writes it to the SmallFusionSystems database in the next open index.

---

## AddSmallFusionSystems

`AddSmallFusionSystems(FS::SeqEnum)`  

Calls `AddSmallFusionSystem` on every fusion system in the given list.

---

## AllSmallFusionSystems (group version)

`AllSmallFusionSystems(S::Grp) -> SeqEnum`  

Returns all small fusion systems whose underlying group is isomorphic to `S`.

---

## AllSmallFusionSystems (order version)

`AllSmallFusionSystems(S_order::RngIntElt) -> SeqEnum`  

Returns all small fusion systems over groups of order `S_order`.

---

## NumberSmallFusionSystems (order version)

`NumberSmallFusionSystems(S_order::RngIntElt) -> RngIntElt`  

Returns the number of fusion systems stored in the database on groups of order `S_order`.

---

## NumberSmallFusionSystems (group version)

`NumberSmallFusionSystems(S::Grp) -> RngIntElt, SeqEnum`  

Returns the count and list of indices of fusion systems whose Sylow p-subgroup is isomorphic to `S`.


## UpdateSmallFusionSystems

`UpdateSmallFusionSystems()`

Calls `UpdateFusionRecord` on every fusion system in the SmallFusionSystems database.

---

## VerifyAllSmallFusionSystemRecords

`VerifyAllSmallFusionSystemRecords()`

Checks that every file in the SmallFusionSystems database successfully returns a fusion system.