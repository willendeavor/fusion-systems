# types-attributes.m

Contains the definition of all new types and attributes, the most important of course being the FusionSystem type.


### FusionSystem

The fusion system has the following attributes

| Attribute        | Type                                  | Purpose                                                                                           |
| ---------------- | ------------------------------------- | ------------------------------------------------------------------------------------------------- |
| `prime`          | `RngIntElt`                           | The prime of the $p$-group $S$                                                      |
| `group`          | `Grp`     							   | The underlying $p$-group $S$ on which the fusion system is defined                           |
| `borel`          | `Grp`                                 | The Borel subgroup $B$, a group such that $\mathrm{Aut}_B(S) = \mathrm{Aut}_{\mathcal{F}}(S)$     |
| `subgroups`      | `SeqEnum[Grp]`                        | All subgroups of $S$, up to $B$-conjugacy												              |
| `centrics`       | `SetEnum[Grp]`                        | The set of $\mathcal{F}$-centric subgroups                                  |
| `essentials`     | `SeqEnum[Grp]`                        | The essential subgroups of $\mathcal{F}$, including the Sylow subgroup $S$ as the first item |
| `essentialautos` | `SeqEnum[GrpAuto]`            | The list of $\mathrm{Aut}_{\mathcal F}(E)$ for each essential subgroup $E$ in same order as `essentials` |
| `fusiongraph`    | `GrphUnd`                             | The fusion graph whose vertices are subgroups and edges encode fusion induced by essentials     |
| `maps`           | `Assoc` (associative array)           | Maps corresponding to the edges in the fusion graph, transporting between subgroups            |
| `classes`        | `SeqEnum[SetEnum]`                    | Connected components of the fusion graph, equivalent to $\mathcal{F}$-conjugacy classes of subgroups        |
| `AutF`           | `Assoc` mapping `Grp → GrpAuto`       | Stores $\mathrm{Aut}_{\mathcal{F}}(P)$ for a subgroup $P$ once computed                   |
| `saturated`      | `BoolElt`                             | Boolean indicating whether the fusion system is saturated once computed     |
| `grpsystem`      | `Grp` 								   | The group $G$ if $\mathcal{F} = \mathcal{F}_S(G)$                          |


### Group Attributes

For GrpMat, GrpPerm and GrpPC there are new attributes declared as follows

| Attribute     | Type          | Purpose                                                                 |
|---------------|---------------|-------------------------------------------------------------------------|
| `autogrp`       | `GrpAuto`       | Stores the full automorphism group $\mathrm{Aut}(X)$ of the group $X$               |
| `autoperm`      | `GrpPerm`       | The GrpPerm version of `autogrp`                       |
| `autopermmap`   | `Map`           | The map `autogrp -> autoperm` that maps an element to its permutation representation         |
| `autF`          | `GrpAuto`       | An auxilliary attribute storing $\mathrm{Aut}_{\mathcal{F}}(X)$ for some $\mathcal{F}$ |
