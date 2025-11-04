# general-group.m

Contains all the general group functions that are used elsewhere in the code, for example there are functions to determine if a group contains a strongly $p$-embedded subgroup.

### SubInvMap

`SubInvMap(j::Map, K::Grp, W::Grp)-> Grp`

For $j: K \to K$ and $W \leq K$ returns $j^{-1}(W)$. 

### SubMap

`SubMap(j::Map,K::Grp,W::Grp)-> Grp`

For $j: K \to K$ and $W \leq K$ returns $j(W)$. 

### ConjtoHom

`ConjtoHom(X::Grp, Y::Grp, g::GrpElt)->GrpHom`

Given $X^g \leq Y$ return the homomorphism $c_g:X \to Y$ 

### ConjtoAuto

`ConjtoAuto(X::Grp, g::GrpElt, AA::GrpAuto)->GrpAutoElt`

Given $X^g = X$ return the automorphism $c_g \in \mathrm{Aut}(X)$. First uses `MakeAutos` on $X$.
 
### MakeAutos

`MakeAutos(x::Grp)`

Given a group $x$ assigns the attributes `autogrp`, `autopermmap`, and `autoperm`


### AutYX

`AutYX(Y::Grp,X::Grp)-> GrpAuto`

Creates $\mathrm{Aut}_Y(X) \leq \mathrm{Aut}(X)$ where $Y$ normalises $X$. Note calls `MakeAutos` first.


### Inn

`Inn(X::Grp)-> GrpAuto`

Calls `AutYX` to create $\mathrm{Inn}(X) = \mathrm{Aut}_X(X)$.


### Automiser/Automizer

`Automiser(G::Grp,P::Grp)->GrpAuto`

Given $P \leq G$ returns $\mathrm{Aut}_G(P) \cong N_G(P)/C_G(P)$ via `AutYX(Normaliser(G,P), P)`.

### AutomiserGens

`AutomiserGens(G::Grp,P::Grp)->SetEnum`

Given $P \leq G$ returns a set of automorphisms that generates $\mathrm{Aut}_G(P)$ by calling `ConjtoHom`

### IsCharacteristic

`IsCharacteristic(G::Grp,H::Grp)->Bool`

Given $H \leq G$ determine if $H$ is characteristic in $G$.

### IsInvariant

`IsInvariant(A::GrpAuto,G::Grp,H::Grp)->Bool`

Given $H \leq G$ and $A \leq \mathrm{Aut}(G)$, determine if $H$ is $A$-invariant.

### IsStronglypEmbeddedMod

`IsStronglypEmbeddedMod(G::Grp, ker::Grp, p::RngIntElt)->Bool`

Given ($N = ker$)  $N \trianglelefteq G$ and $p$ determine if $G/N$ contains a strongly $p$-embedded subgroup

Does this differently than `IsStronglypEmbedded` for some reason and does not just call it on $G/N$? Must be more to what ker is supposed to represent?

### IsStronglypEmbedded

`IsStronglypEmbedded(G::Grp,p::RngIntElt)->Bool`

Given $G$ and $p$ determine if $G$ contains a strongly $p$-embedded subgroup
Uses properties of groups containing a strongly $p$-embedded subgroup to save some calculations.


### RandomAuto

`RandomAuto(A::GrpAuto)->Map`

Given an automorphism group picks a random element.

### AutOrbit

`AutOrbit(P::Grp,Q::Grp,AFP::GrpAuto:Printing:=false)->SeqEnum,Grp,SeqEnum`

Given $Q \leq P$ and $AFP \leq \mathrm{Aut}(P)$ determines the orbits of AFP on $Q$, also returns the stabiliser and a set of representatives.

The first return value is an array `Orb` of subgroups of $P$ representing the orbits and has as its first element $Q$, followed by $Q^n$ for representatives of $n \in N_P(Q)$ and then the other orbits.

The second return value `StB` is the stabiliser $N_{AFP}(Q)$.

The third return value is an array `Elt` of elements in `AFP` representative of each orbit i.e. `Orb[i]` is the image of $Q$ under `Elt[i]`.

`AutOrbit(P::Grp,Q::GrpElt,AFP::GrpAuto)->SeqEnum,Grp,SeqEnum`

As above but for a single element $Q \in P$.


### IsSCentric

`IsSCentric(S::Grp,P::Grp)->Bool`

Given $P \leq Q$ returns true if $C_S(P) \leq P$, false otherwise.


### IsStronglypSylow

`IsStronglypSylow(Q::Grp)->Bool, Bool`

Given a $p$-group $Q$ determines if $Q$ can be the Sylow $p$-subgroup of a group that contains a strongly $p$-embedded subgroup.
