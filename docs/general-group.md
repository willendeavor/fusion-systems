# general-group.m

Contains all the general group functions that are used elsewhere in the code, for example there are functions to determine if a group contains a strongly $p$-embedded subgroup

###### `SubInvMap(j::Map, K::Grp, W::Grp)-> Grp`

    For $j: K \to K$ and $W \leq K$ returns $j^{-1}(W)$. 
    
###### `SubMap(j::Map,K::Grp,W::Grp)-> Grp`

    For $j: K \to K$ and $W \leq K$ returns $j(W)$. 

###### `ConjtoHom(X::Grp, Y::Grp, g::GrpElt)->GrpHom`

    Given $X^g \leq Y$ return the homomorphism $c_g:X \to Y$ 
    
###### `ConjtoAuto(X::Grp, g::GrpElt, AA::GrpAuto)->GrpAutoElt`

    Given $X^g = X$ return the automorphism $c_g \in \mathrm{Aut}(X)$. First uses MakeAutos on $X$.
    
##### `MakeAutos(x::Grp)`

    Given a group $x$ assigns the attributes [[autogrp]], [[autopermmap]], and [[autoperm]]