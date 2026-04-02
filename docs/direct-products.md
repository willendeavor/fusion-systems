### Types and Attributes

This MAGMA file also defines a new `DirectProductGroup` type, this is used to compile all relevant information about a particular decomposition of a group.

| Type                 | Attribute          | Attribute Type                | Attribute Description                                                                                                                                  |
| -------------------- | ------------------ | ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `DirectProductGroup` | `group`            | `Grp`                         | Stores the underlying group $D = \prod_{i = 1}^n D_i                                                                                                   |
|                      | `embed`            | `SeqEnum[map]`                | Stores a list `[iota_1, ..., iota_n]` of all of the embedding homomorphisms from the external subgroups to the internal subgroups $\iota_i: D_i \to D$ |
|                      | `proj`             | `SeqEnum[map]`                | Stores a list `[pi_1,...,pi_n]` of all of the projection homomorphisms from the internal subgroup to the external subgroup $\pi_i:D \to D_i$           |
|                      | `factors`          | `SeqEnum[Grp]`                | Stores a list of the **external** groups $D_i$                                                                                                         |
| `FusionSystems`      | `directproductgrp` | `DirectProductGroup`          | If a fusion system has been constructed as a direct product stores the underlying group as a DirectProductGroup type                                   |
|                      | `factors`          | `SeqEnum[SeqEnum[RngIntElt]]` | Stores the SmallFusionSystem ids of the factors of the fusion system (if constructed as such)                                                          |

## Intrinsics

#### MakeDirectProductGroup

`MakeDirectProductGroup(G_factors::SeqEnum[Grp]) -> DirectProductGroup`

Given a list of groups `G_factors` create a `DirectProductGroup` object and populate the attributes

#### MakeDirectProductGroup

`MakeDirectProductGroup(G_1::Grp, G_2::Grp) -> DirectProductGroup`

Two argument version

#### AutEltRestriction

`AutEltRestriction(phi::GrpAutoElt, H::Grp) -> GrpAutoElt`

Given an automorphism $\phi \in \mathrm{Aut}(G)$ such that $\phi(H) = H$ return $\phi|_H \in \mathrm{Aut}(H)$

#### AutRestriction

`AutRestriction(A::GrpAuto, H::Grp) -> GrpAuto`

Given $A \leq N_{\mathrm{Aut}(G)}(H)$ return $\langle \phi|_H \ | \ \phi \in A \rangle \leq \mathrm{Aut}(H)$

#### AutDirectProduct

`AutDirectProduct(a::GrpAutoElt, b::GrpAutoElt) -> GrpAutoElt`

Given $a \in \mathrm{Aut}(G)$ and $b \in \mathrm{Aut}(H)$ return $a \times b \in \mathrm{Aut}(G \times H)$

#### AutDirectProduct

`AutDirectProduct(A_1::GrpAuto, A_2::GrpAuto : Overgroup := false) -> GrpAuto`

Given $A \leq \mathrm{Aut}(G)$, $B \leq \mathrm{Aut}(H)$ return $A \times B \leq \mathrm{Aut}(G \times H)$, the option `Overgroup` is a `DirectProductGroup` that should be $G \times H$, this ensures that the automorphisms are in the right place

#### AutDirectProduct (deprecated)

`AutDirectProduct(A_list::SeqEnum[GrpAuto] : Overgroup := false) -> GrpAuto`

Given a list $A_i \leq \mathrm{Aut}(G_i)$ return $A_1 \times \ldots \times A_n \leq \mathrm{Aut}(G_1 \times \ldots \times G_n)$

#### FusionDirectProduct

`FusionDirectProduct(F_1::FusionSystem, F_2:: FusionSystem) -> FusionSystem`

Given fusion systems $\mathcal{F}_1, \mathcal{F}_2$ return $\mathcal{F}_1 \times \mathcal{F}_2$ and make the associated `DirectProductGroup` and assign to the attribute ``F`directproductgrp`` 

#### FusionDirectProduct

`FusionDirectProduct(F_factors::SeqEnum[FusionSystem]) -> FusionSystem`

Given a list of fusion systems $\mathcal{F}_i$ return $\mathcal{F}_1 \times \ldots \times \mathcal{F}_n$

#### OneSidedFusionSystem

`OneSidedFusionSystem(F::FusionSystem, S_factors::SeqEnum, i ::RngIntElt) -> FusionSystem`

Given a list of groups $S_i$ and a fusion system $\mathcal{F}$ over $S = \prod S_i$ return the fusion subsystem $\mathcal{F}_i^\bullet = \langle \mathrm{Aut}_\mathcal{F}(S), \mathrm{Aut}_\mathcal{F}(E) \ | \ E = E_i S_i^* \in \mathcal{E}(\mathcal{F}) \rangle$ where $S_i^* = \prod_{j \neq i} S_j$.  By results in my thesis more often than not $\mathcal{F} = \langle \mathcal{F}_1, \ldots, \mathcal{F}_n \rangle$.

#### GroupDecomposition

`GroupDecomposition(G::Grp) -> BoolElt, SeqEnum`

Given a group $G$ either return true if $G$ is indecomposable or else return false and a pair `[G_1, G_2]` such that $G = G_1 \times G_2$.

#### AllSplittings

`AllSplittings(S::Grp) -> SeqEnum`

Given a group $S$ return a list of all possible pairs `[S_1, S_2]` such that $S = S_1 \times S_2$.

#### FusionSystemDecomposition

`FusionSystemDecomposition(F::FusionSystem, S_factors::SeqEnum : return_decomposition := false) -> Bool, SeqEnum`

Given a list of groups $S_i$ and a fusion system $\mathcal{F}$ over $S = \prod S_i$  satisfying $O^{p'}(\mathcal{F}) = \mathcal{F}$ determine if $\mathcal{F}$ splits, if `return_decomposition := true` it will return the decomposition as  a list of fusion systems.

#### IsIndecomposable

`IsIndecomposable(F::FusionSystem: return_decomposition := false, recalculate := false, strong_check:= false) -> Bool, SeqEnum`

Given a fusion system satisfying $O^{p'}(\mathcal{F}) = \mathcal{F}$ determine if it is indecomposable.  As above `return_decomposition` controls whether a decomposition is returned, `recalculate` will ignore ``F`indecomposable`` attribute, and `strong_check` will check manually that $\mathcal{F}$ is indeed the direct product of the factors found.

Note that if a fusion system $O^{p'}(\mathcal{F}) \subset \mathcal{F}$ and the strong check is disabled then this may provide a false negative in that really it checks if $\mathcal{F} \subseteq \mathcal{F}_1 \times \mathcal{F}_2$ so if `IsIndecomposable` returns false that does not mean a fusion system is decomposable but rather that it is a subsystem of the direct product. If strong_check is set to true however than it really does check $\mathcal{F} = \mathcal{F_1} \times \mathcal{F}_2$.
