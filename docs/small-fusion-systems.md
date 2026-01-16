## Documentation: `small-fusion-systems.m`

### Overview v.2.5.1

This file contains commands for accessing specifically the SmallFusionSystem database, fusion-records.m contains commands for generally saving a fusion system record and maintaining the database. The following table lists the orders that are currently available, whether they include fusion systems that do not have trivial core and are not perfect and whether all possible direct products that can be built from these fusion systems have been added (of course in theory for example all 2^3 x 2^3 should already be in the database), note as well that the core and focal subgroup are only really interesting to run once the non pPerfect and non OpTriv have been added.

Also note that as detailed in [#92](https://github.com/willendeavor/fusion-systems/issues/92) running AllFusionSystems(S:OpTriv := false, pPerfect := false) does not quite return all fusion systems, in particular if S is abelian then it returns with no fusion systems. I will work on fixing this but it is important to note that while the list of almost_reduced fusion systems is complete it is unlikely that the list of ALL saturated fusion systems will be ever complete. I would like to fix this so if subsystems and direct products are added then we can recognise them quickly by just checking the library.


| $p$ 	| $n$ 	| Number | Grouped by isomorphism class 	| Added non-almost-reduced 						| Added direct products 	| Added core and focal subgroup |
|-----	|-----	|--------|------------------------------	|----------------------------------------------------------------------	|-----------------------	| ----------------|
| 2   	| 3   	| 2      |	+Y			| Y                                                                    	|                       	| Y
|     	| 4   	| 7      |	+Y			| Y                                                                    	|                       	| Y
|     	| 5   	| 37     |	+Y			| Y                                                                    	|                       	| Y
|     	| 6   	| 209    |	+Y			| Y                                                                    	|                       	| Y
|     	| 7   	| 487    |				| Up to SmallGroup(2^7, 1000)                                           |                       	| + Y
|	| 8	| +?	 |				| + Reduced up to SmallGroup(2^8, 8000)					|				|
| 3   	| 3   	| 6      |	+Y			| Y                                                                     |                       	| Y
|     	| 4   	| 28     |	+Y			| Y                                                                     |                       	| Y
|     	| 5   	| 194    |	+Y			| Y                                                                     |                       	| Y
|     	| 6   	| 70     |				| + Up to SmallGroup(3^6, 276)                                          |                       	| + Y
|     	| 7   	| 88     |				|                                                                      	|                       	| + Y
| 5   	| 3   	| 6      |	+Y			| Y                                                                     |                       	| Y
|     	| 4   	| 43     |	+Y			| Y                                                                     |                       	| Y
|     	| 5   	| 58     |				|                                                                      	|                       	| + Y
|     	| 6   	| 37     |				|                                                                      	|                       	| + Y
| 7     | 3     | 17      |	+Y			| Y                                                                     |                        	| Y
|       | 4     | 24      |	+Y			| Y                                                                     |                        	| Y
|       | 5     | 11      |				| + Up to SmallGroup(7^5,40)     		                        |                        	|

---

### Storing Fusion Systems
A basic overview of how the fusion systems are stored is that each FS_i file contains an intrinsic that is attached when loaded. This intrinsic does not return a fusion system but rather a record of the format `FusionRecord` (details included in [fusion-records](https://github.com/willendeavor/fusion-systems/blob/main/docs/fusion-records.md)). This format is determined by a function when saving a new fusion record but for backwards compatibility each intrinsic actually contains the definition of the FusionRecord as of when the file was created. Therefore even if the format has since between updated and extended there is no issues with loading fusion systems saved using an older version of code.

### Intrinsics

### Loading

#### SmallFusionSystem

`SmallFusionSystem(S_order::RngIntElt, i::RngIntElt) -> FusionSystem`  

Loads the *i-th* small fusion system on a group of order `S_order`.

---

#### SmallFusionSystemRecord

`SmallFusionSystemRecord(S_order::RngIntElt, i::RngIntElt) -> Rec`  

Returns only the FusionRecord (not the fusion system) for the specified small fusion system.

---

#### IdentifyFusionSystem

`IdentifyFusionSystem(F::FusionSystem) -> SeqEnum`  

Determines whether `F` matches one of the known small fusion systems (via isomorphism).  
Returns `<|S|, index>` or `<0,0>` if not in the database.

---

### Adding

#### AddSmallFusionSystem

`AddSmallFusionSystem(F::FusionSystem)`  

Checks whether `F` is already stored.  
If not writes it to the SmallFusionSystems database in the next open index.

---

#### AddSmallFusionSystems

`AddSmallFusionSystems(FS::SeqEnum)`  

Calls `AddSmallFusionSystem` on every fusion system in the given list.



#### AllSmallFusionSystems (group version)

`AllSmallFusionSystems(S::Grp: almost_reduced := false) -> SeqEnum`  

Returns all small fusion systems whose underlying group is isomorphic to `S`. If `almost_reduced := true` then returns only those that satisfy $O_p(\mathcal{F}) = 1$ and $O^p(\mathcal{F}) = \mathcal{F}$.

---

#### AllSmallFusionSystems (order version)

`AllSmallFusionSystems(S_order::RngIntElt: almost_reduced := false) -> SeqEnum`  

Returns all small fusion systems over groups of order `S_order`. If `almost_reduced := true` then returns only those that satisfy $O_p(\mathcal{F}) = 1$ and $O^p(\mathcal{F}) = \mathcal{F}$.

---

#### AddAllFusionSystems (order version)

`AddAllFusionSystems(order::RngIntElt: resume := 1)`  

Adds all small fusion systems (including those without trivial core or p-perfect) over groups of order `order` to the library by using `AllFusionSystems`. The options resume can be used to start adding groups from SmallGroups(order, i) upwards.

---

#### AddAllFusionSystems (group version)

`AddAllFusionSystems(S::Grp)`  

Adds all small fusion systems (including those without trivial core or p-perfect) over the group `S` to the library by using `AllFusionSystems`.

---

### Accessing information

#### NumberSmallFusionSystems (order version)

`NumberSmallFusionSystems(S_order::RngIntElt : almost_reduced := false) -> RngIntElt`  

Returns the number of fusion systems stored in the database on groups of order `S_order`.

---

#### NumberSmallFusionSystems (group version)

`NumberSmallFusionSystems(S::Grp : almost_reduced := false) -> RngIntElt, SeqEnum`  

Returns the count and list of indices of fusion systems whose Sylow p-subgroup is isomorphic to `S`.

---

### Updating and Verification

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


#### AddGroupFusionSysten

`AddGroupFusionSystem(F::FusionSystem : overwrite := false)`

Given a group fusion system checks if it is in the database already and if so add the group to a fusion systems record. Otherwise add it to the database. If a fusion system already has a group attached then does nothing unless overwrite is set to true.



