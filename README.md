# Fusion Systems

A modest refactoring of the MAGMA package written by Chris Parker and Jason Semeraro and detailed in the paper "Algorithms for fusion systems with applications to $p$-groups of small order", with the aim of making the code more readable and with relatively in-depth documentation and usage. 
I have no plans currently to extend or seriously modify the functionality and with some perhaps small exceptions there shouldn't be any compatibility issues between this package and https://github.com/chris1961parker/Fusion-Systems
This is mostly a project to bring myself up to speed with Git and writing documentation etc.

## Installation and execution

Run `load "fusion-systems.m"` from the root directory


## Usage and an example (v.1.0.0)

The main functionality of this package is to create fusion systems, to this end a `FusionSystem` type is defined and various attributes along with it. By Alperin's fusion theorem a fusion system is determined by its essential subgroups and their automorphism groups along with the automorphism group of the underlying $p$-group, indeed this is how the fusion systems are created. 
### The `FusionSystem` type
To demonstrate the `FusionSystem` type we can look at the easiest fusion systems to create, group fusion systems. The following code creates the group fusion system of $`\mathcal{F}_S(G) = \mathcal{F}_{3^{1+2}_+}(\mathrm{SL}(3,3))`$ (i.e. $p = 3$) and saves it as `F`.
```
F := GroupFusionSystem(SL(3,3),3);
```
We expect $\mathcal{F}$ to have 2 classes of essential subgroups, all of the form $3 \times 3$ and the automiser of each essential subgroup should be $`\mathrm{GL}_{2}(3)`$. We also should have that $`\mathrm{Out}_\mathcal{F}(S) \cong (p-1)^2`$ and indeed by calling the implicit printing function we find
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
Lastly notice that printing `F` also showed that it is a group fusion system $`\mathcal{F}_S(G)`$, there is an attribute `grpsystem` that stores the group $G$.

### Creating fusion systems
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
###  All fusion systems over a $p$-group
The most significant function in the package is the `AllFusionSystems` command, given a $p$-group $S$ this returns all possible saturated fusion systems on $S$. Unless specified otherwise it actually returns all fusion systems with $`O_p(\mathcal{F}) = 1`$ and $`O^p(\mathcal{F}) = \mathcal{F}`$. 
```
> FS := AllFusionSystems(ExtraSpecialGroup(3,1));
> FS;
[
    Fusion System with 2 F-classes of essential subgroups
    They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
    Out_F(S) has order  4,
    Fusion System with 2 F-classes of essential subgroups
    They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
    Out_F(S) has order  8,
    Fusion System with 1 F-classes of essential subgroups
    They have orders: [ 9 ]Out_F(E)  have orders: [ 48 ]
    Out_F(S) has order  8,
    Fusion System with 1 F-classes of essential subgroups
    They have orders: [ 9 ]Out_F(E)  have orders: [ 48 ]
    Out_F(S) has order  16
]
> IsIsomorphic(FS[1],F);
true
```
In order to produce the list including those with $O_p(\mathcal{F}) \neq 1$ or $O^p(\mathcal{F}) \neq \mathcal{F}$ we specify the optional parameters `OpTriv` and `pPerfect`:
```
> FSS := AllFusionSystems(ExtraSpecialGroup(3,1):OpTriv:=false, pPerfect := false);
> #FS,#FSS;
4 6
``` 


### Saving fusion systems
It is possible to save a fusion system or even a sequence of fusion systems to a file that can be loaded as needed. This is done using the `SaveFS` command which given a file name and a fusion system (or sequence of them) will output a file in the directory containing a sequence of commands that can be loaded. 
```
> SaveFS("examplefs", F);
> load "examplefs";
Loading "examplefs"
Fusion System with 2 F-classes of essential subgroups
They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
Out_F(S) has order  4
> FS;
Fusion System with 2 F-classes of essential subgroups
They have orders: [ 9, 9 ]Out_F(E)  have orders: [ 48, 48 ]
Out_F(S) has order  4
```
There are some caveats here, one is that the file runs a series of commands and will set `FS` to be the fusion system saved in the file rather than _returning_ a fusion system type. Secondly the command for saving is not currently robust, it does not check if any such file already exists and as such will write multiple times.
 
The repository https://github.com/chris1961parker/Fusion-Systems includes a folder AllFusionSystemsFound containing many already computed fusion systems.

###  Properties of a fusion system
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
###  Subgroups in a fusion system
There is functionality for computing properties of a subgroup $P \leq S$ in relation to a fusion system, such as tests for if $P$ is fully centralised/normalised/automised,  strongly/weakly closed etc. Importantly we can also calculate $\mathrm{Aut}_\mathcal{F}(P)$.
```
> Z := Center(F`group);
> GroupName(AutomorphismGroup(F,Z));
C2
```


## Further details
Documentation for each intrinsic defined by the package can be found in the docs folder, currently a work-in-progress. 


