# Documentation: `fusion-records.m`


### Record Formats

#### FusionRecord
| Entry            	| Type      	| Description                                                	|
|------------------	|-----------	|------------------------------------------------------------	|
| p                	| RngIntElt 	| Prime divisor of S                                         	|
| S                	| Grp       	| Underlying p-group of the fusion system                    	|
| S_order          	| RngIntElt 	| Order of S                                                 	|
| S_name           	| MonStgElt 	| GroupName of S                                             	|
| S_small_group_id 	| Tup       	| If S is in the SmallGroup database then this is <order, i> 	|
| EssentialData    	| SeqEnum   	| A list of records of the format EssentialRecord            	|
| core             	| Grp       	| The F-core                                                 	|
| core_trivial           	| BoolElt   	| Stores whether Core is trivial or not                      	|
| focal_subgroup    	| Grp       	| The focal subgroup of F                                    	|
| pPerfect         	| BoolElt   	| Stores whether O^p(F) = F or not                           	|
| fusion_group      	| Grp       	| If F is a group fusion system F_S(G) then this stores G    	|
| fusion_group_name 	| MonStgElt 	| GroupName of FusionGroup                                   	|
---

#### EssentialRecord
| Entry       	| Type      	| Description                                                                     	|
|-------------	|-----------	|---------------------------------------------------------------------------------	|
| E           	| Grp       	| The essential subgroup E, stored as a true subgroup of S                        	|
| E_order     	| RngIntElt 	| The order of E                                                                  	|
| E_name      	| MonStgElt 	| GroupName of E                                                                  	|
| AutFE_order 	| RngIntElt 	| The order of AutFE                                                              	|
| AutFE_name  	| MonStgElt 	| GroupName of AutFE                                                              	|
| AutFE_gens  	| SeqEnum   	| A list of generators of AutFE of the form <g, phi(g)> for each generator g of E 	|
---

### Intrinsics

#### FusionRecordTemp

`FusionRecordTemp() -> Rec`  

A dummy intrinsic overwritten when loading a record file. Each file has its own definition of FusionRecordTemp(), this is defined only so the name is defined at runtime.

---

#### LoadFusionSystemRecord

`LoadFusionSystemRecord(filename::MonStgElt) -> Rec`  

Loads the fusion system file `filename` and returns the record it constructs.

---

#### LoadFusionSystem (record version)

`LoadFusionSystem(R::Rec) -> FusionSystem`  

Reconstructs a FusionSystem from a given FusionRecord.

---

#### LoadFusionSystem (filename version)

`LoadFusionSystem(filename::MonStgElt) -> FusionSystem`  

Loads the record using `LoadFusionSystemRecord`, then reconstructs the FusionSystem.

---

#### UpdateFusionRecord

`UpdateFusionRecord(filename::MonStgElt)`

Given a filename rewrite the fusion record to reflect any changes made to the saving format since the file was originally written.


#### IsIsomorphicFusionRecords

`IsIsomorphicFusionRecords(R_1::Rec, R_2::Rec) -> Bool`

Given two fusion records determine if they represent isomorphic fusion systems using `IsIsomorphic` only as a last resort, the idea being that we can quickly rule out isomorphism without loading the fusion systems.
