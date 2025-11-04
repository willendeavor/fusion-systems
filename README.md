## Fusion Systems

A refactoring of the MAGMA package written by Chris Parker and Jason Semeraro, with the aim of making the code more readable and with relatively in-depth documentation and usage. 

### Installation and execution

Run `load "fusion-systems.m"` from the root directory


### Usage and an example

The main functionality of this package is to create fusion systems, to this end a `FusionSystem` type is defined and various attributes along with it. By Alperin's fusion theorem a fusion system is determined by its essential subgroups and their automorphism groups along with the automorphism group of the underlying $p$-group, indeed this is how the fusion systems are created. 
#### The `FusionSystem` type
To demonstrate the `FusionSystem` type we can look at the easiest fusion systems to create, group fusion systems. The following code creates the group fusion system of $\mathcal{F}_S(G) = \mathcal{F}_{3^{1+2}_+}(\mathrm{SL}(3,3))$ (i.e. $p = 3$) and saves it as `F`.
`F := GroupFusionSystem(SL(3,3),3);`
We expect $\mathcal{F}$ to have 2 classes of essential subgroups, all of the form $3 \times 3$ and the automiser of each essential subgroup should be $\mathrm{GL}_{2}(3)$. We also should have that $\mathrm{Out}_\mathcal{F}(S) \cong (p-1)^2$ and indeed by calling the implicit printing function we find
```
> F;
Fusion System with 2 F-classes of essential subgroups
They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
Out_F(S) has order  4
This is a group fusion system
```
Let's check the essentials in more detail, the attribute `essentials` should be a list of all essential subgroups.
```
> F`essentials;
[
    GrpPC of order 27 = 3^3
    PC-Relations:
        $.2^$.1 = $.2 * $.3,

    GrpPC of order 9 = 3^2
    PC-Relations:
        $.1^3 = Id($),
        $.2^3 = Id($),

    GrpPC of order 9 = 3^2
    PC-Relations:
        $.1^3 = Id($),
        $.2^3 = Id($)
]
```
Notice that the first entry is in fact $S$, which is never an essential subgroup but since we need $\mathrm{Out}_\mathcal{F}(S)$ it is stored here. In fact ``F`essentials[1]`` is always $S$. 
Now let us look at their automorphisms, these are stored in the attribute `essentialautos` such that `essentialautos[i]` is the automorphism group of `essentials[i]` so let us check that in this case `essentialautos[2]` is $\mathrm{GL}_2(3)$.
```
> EA := F`essentialautos;
> GroupName(EA[2]);
GL(2,3)
```
Lastly notice that printing `F` also showed that it is a group fusion system $\mathcal{F}_S(G)$, there is an attribute `grpsystem` that stores the group $G$.

#### Creating fusion systems
In order to create a fusion system we need an _automiser sequence_, this is a list of automorphism groups, the first must be $\mathrm{Aut}_\mathcal{F}(S)$. Let us use `F` to create the fusion system again and check it is isomorphic to the one we created using the `GroupFusionSystem` function.
```
> FF := CreateFusionSystem(EA);
> FF;
Fusion System with 2 F-classes of essential subgroups
They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
Out_F(S) has order  4
> IsIsomorphic(FF,F);
true
```
Note that we have not been told it is a group fusion system. Since `FF` is a group fusion system it is saturated but this information has not yet been stored, since `F` was created with `GroupFusionSystem` it has been stored in the attribute ``F`saturated``:
```
> F`saturated;
true
> FF`saturated;
>> FF`saturated;
     ^
Runtime error in `: Attribute 'saturated' for this structure is valid but not
assigned
```
Fortunately we can rectify this using the `IsSaturated` function.
```
> IsSaturated(FF);
true
> FF`saturated;
true
```

####  Properties of a fusion system
The package provides functionality for computing various properties of a fusion system, for example the core and focal subgroups can be generated, in our particular case we have $O_p(\mathcal{F}) = 1$ and $\mathfrak{foc}(\mathcal{F}) = S$.
```
> Core(F);
true
GrpPC of order 1
PC-Relations:
> FocalSubgroup(F);
GrpPC of order 27 = 3^3
PC-Relations:
    $.2^$.1 = $.2 * $.3
```
####  Subgroups in a fusion system
There is functionality for computing properties of a subgroup $P \leq S$ in relation to a fusion system, such as tests for if $P$ is fully centralised/normalised/automised,  strongly/weakly closed etc. Importantly we can also calculate $\mathrm{Aut}_\mathcal{F}(P)$.
```
> Z := Center(F`group);
> GroupName(AutomorphismGroup(F,Z));
C2
```
####  All fusion systems over a $p$-group

