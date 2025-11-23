# Current Features and Dream Features
A table keeping track of what features currently work and future features that would be nice to implement and their tracked issues (if any).

## Current Features
|Feature| Description|Relevant Functions| Issues|
|---------|--------------|--------------|--------|
|Calculate $P^\mathcal{F}$ | Functions that calculate the $\mathcal{F}$-orbit of a subgroup of $S$,  | `ConjugacyClass` `IsConjugate` `FConjugacyClass` | 
|$P \in \mathcal{F}^{fn/fc/c,fa}$? | Functions that determine if a given subgroup is fully-normalised, fully-centralised, centric, fully-automised | `IsCentric`, `IsFullyNormalized`, `IsFullyCentralised`, `IsFullyAutomised` | 
|Surjectivity property| Determines if $P$ has the surjectivity property | `SurjectivityProperty` |
|Weakly/Strongly closed | Determine if a subgroup is weakly or strongly closed in a fusion system | `IsStronglyClosed`, `IsWeaklyClosed` | 
|$O_p(\mathcal{F})$| Can calculate the core of a fusion system and the automorphism group if wanted | `AutFCore`, `Core`, `FCoreTest` | Some duplication in code see [#55](https://github.com/willendeavor/fusion-systems/issues/55) |
| $\mathfrak{foc}(\mathcal{F})$| Calculate the focal subgroup | `FocalSubgroup`, `FocalSubgroupTest` | 


## Feature Wishlist

| Feature | Description | Progress | Issues |
|----------|---------------|------------|-----------|
|Subsystem support| Add basic functionality to work with subsystems, at least asking if something is a subsystem. Start by doing it in a very slow, dumb way then perhaps think about doing it via essential subgroups. | Not started | 
|Calculate $O^{p'}(\mathcal{F})$ | Add a function to calculate the residual subsystem, currently unsure of how to do this in general cases but we can at least calculate $O^{p'}_*(\mathcal{F})$, the not necessarily saturated system containing all $O^{p'}(\mathrm{Aut}_\mathcal{F}(E))$ and $\mathrm{Aut}_\mathcal{F}^E(S)$ |In progress | [#48](https://github.com/willendeavor/fusion-systems/issues/48) 
| Calculate $O^p(\mathcal{F})$ | Function that calculates the hyperfocal subsystem $O^p(\mathcal{F})$, should be more straightforward than the residual subsystem. | Not started|
| Direct products $\mathcal{F}_1 \times \mathcal{F}_2$| Add support for constructing direct products, to start with probably easier to work with internal direct products first. For external I think would require some thinking about, perhaps similar to my AutoMatrix package defining a direct product type that can keep track of everything is needed. | Not started | 
|Quotients of a strongly closed subgroup| Add support for working with quotient fusion systems. This will be easiest in the case where the strongly closed subgroup is central since we calculate the essential subgroups straight away | Not started| |
| Normal subgroups $P \lhd \mathcal{F}$ | Add a function to determine if a subgroup is normal in $\mathcal{F}$, should be easy using the equivalence from [AKO] | In progress | |
| Central subgroups| Determine if a subgroup is central in the fusion system | Not started|
|Calculate $\mathfrak{hyp}(\mathcal{F})$ | Calculate the hyperfocal subgroup, of course we could calculate the focal subgroup from this so once done perhaps do some testing to see which is quicker, I imagine it'd be slower | In progress
