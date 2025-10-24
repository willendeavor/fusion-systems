# general-group.m
Contains all the general group functions that are used elsewhere in the code, for example there are functions to determine if a group contains a strongly $p$-embedded subgroup

## `SubInvMap(j::Map, K::Grp, W::Grp)-> Grp

For $j: K \to K$ and $W \leq K$ returns $j^{-1}(W)$. 