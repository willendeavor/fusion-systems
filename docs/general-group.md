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


### IsRadical

`IsRadical(S::Grp, P::Grp) -> Bool`

Given $P \leq S$ determine if $P$ is radical i.e. if $O_p(N_S(P)/P) = 1$.


### NormalizerTower

`NormalizerTower(S::Grp, E::Grp) -> SeqEnum`

Given $E \leq S$ return the sequence defined by $N_S^i(E) = N_S(N_S^{i-1}(E))$.


### AllMaximalSubgroups

`AllMaximalSubgroups(G) -> SeqEnum`

Create the entire list of maximal subgroups of $G$, not just the classes.


### MaximalOvergroups

`MaximalOvergroups(G::Grp, H::Grp, p::RngIntElt) -> SeqEnum`

Given a $p$-group $H \leq G$ return up to $G$-conjugacy all overgroups of $H$ that contain $H$ as a Sylow $p$-subgroup.


### Overgroups

`Overgroups(G::Grp, H::Grp) -> SeqEnum`

Given $H \leq G$ return up to $G$-conjugacy all overgroups of $H$.


### SubgroupsAutClasses

`SubgroupsAutClasses(S::PCGrp) -> SeqEnum`

Given a group $S$ calculate all centric subgroups up to $\mathrm{Aut}(S)$-conjugacy.


### SemiDirectProduct

`SemiDirectProduct(V::ModGrp : Perm := false) -> Grp`

Given a $G$-module $V$ return the group $K = V \rtimes G$. The optional parameter `Perm` determines if $K$ is returned as a subgroup of $\mathrm{GL}_n(F)$ (the default option) or is returned as a permutation group as the image in $\mathrm{GL}_n(F)$ given by the action of $\mathrm{GL}_n(F)$ on $K$. 


### Blackburn

`Blackburn(p::RngIntElt, n::RngIntElt, alpha::RngIntElt, beta::RngIntElt, gamma::RngIntElt, delta::RngIntElt) -> Grp`

Constructs the Blackburn group denoted $B(p,n; \alpha, \beta, \gamma, \delta)$, see Appendix A of Parker + Semeraro for details.


### homeq

`homeq(x::Map, y::Map) -> Bool`

Determine if two homomorphisms are equal.


### IsQuaternionOrCyclic

`IsQuaternionOrCyclic(G::Grp) -> Bool`

Return true if $G$ is a quaternion or cyclic group.


### piResidual

`piResidual(G::Grp, pi::SeqEnum) -> Grp`

Calculate $O^\pi(G)$


### pResidual

`pResidual(G::Grp, p::RngIntElt) -> Grp`

Calculate $O^p(G)$


### piprimeResidual

`piprimeResidual(G::Grp, pi::SeqEnum) -> Grp`

Calculate $O^{\pi'}(G)$


### pprimeResidual

`pprimeResidual(G::Grp, p::RngIntElt) -> Grp`

Calculate $O^{p'}(G)$


### IsMaximalClass

`IsMaximalClass(G::Grp) -> Bool`

Return if $G$ is a maximal class $p$-group.


### MaximalAbelian

`MaximalAbelian(G::Grp) -> Bool`

Determine if $G$ possesses a maximal subgroup that is abelian.


### SubnormalClosure

`SubnormalClosure(G::Grp, T::Grp) -> Grp`

Given $T \leq G$ return the smallest subnormal subgroup of $G$ containing $T$.


### Centralizer

`Centralizer(G::Grp,A::Grp,B:Grp)->Grp`

Given $B \normal G$ and $B \leq A$ return $C_G(A/B)$.