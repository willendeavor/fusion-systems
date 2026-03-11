# Fusion Systems

A modest refactoring of the MAGMA package written by Chris Parker and Jason Semeraro and detailed in the paper "Algorithms for fusion systems with applications to $p$-groups of small order", with the aim of making the code more readable and with relatively in-depth documentation and usage. Originally I planned this to be backwards compatible with the original code and this is mostly still true but increasingly the functionality is changing enough that this may not be true. There is also extended functionality, to see a complete table of what this package can do see [Features](docs/features-wishlist.md)

This is mostly a project to bring myself up to speed with Git and writing documentation, tests etc but the library [SmallFusionSystems](docs/small-fusion-systems.md) is perhaps actually useful for playing around with fusion systems without having to wait a long time to build them.

## Installation and execution

For the most recent code clone the main branch, extract the data.zip to the root directory so the directory at a minimum looks like
```
.
└── fusion-systems/
    ├── -src/
    ├── -data/
    │   └── SmallFusionSystems/
    └── -spec
```
and run `AttachSpec("spec")` from the root directory `fusion-systems/`, otherwise the releases should be fairly stable and tested and the code can be downloaded there. Importantly the SmallFusionSystems functionality references paths from the root directory, at some point I will add the option to set a directory but for now MAGMA must be run from the root directory. Note as well this uses OS commands that may or may not be specific to the OS.


## Usage and an example (v.2.7.2)

The main functionality of this package is to create fusion systems, to this end a `FusionSystem` type is defined and various attributes along with it. By Alperin's fusion theorem a fusion system is determined by its essential subgroups and their automorphism groups along with the automorphism group of the underlying $p$-group, indeed this is how the fusion systems are created. 
### The `FusionSystem` type
To demonstrate the `FusionSystem` type we can look at the easiest fusion systems to create, group fusion systems. The following code creates the group fusion system of $`\mathcal{F}_S(G) = \mathcal{F}_{3^{1+2}_+}(\mathrm{SL}(3,3))`$ (i.e. $p = 3$) and saves it as `F`.
```
F := GroupFusionSystem(SL(3,3),3);
```
We expect $\mathcal{F}$ to have 2 classes of essential subgroups, all of the form $3 \times 3$ and the automiser of each essential subgroup should be $`\mathrm{GL}_{2}(3)`$. We also should have that $`\mathrm{Out}_\mathcal{F}(S) \cong (p-1)^2`$ and indeed by calling the implicit printing function we find
```
> F;
Saturated fusion system F over a p-group S of order 3^3
S is SmallGroup(27, 3) and isomorphic to He3
F has 2 classes of essential subgroups
The orders of the essential subgroups are [ 9, 9 ]
The orders of the Out_F(E) are [ 48, 48 ]
The order of Out_F(S) is 4
F is isomorphic to the group fusion system of PSL(3,3)
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
Lastly notice that printing `F` also showed that it is a group fusion system $`\mathcal{F}_S(G)`$, there is an attribute `fusion_group` that stores the group $G$ while `fusion_group_name` stores just the GroupName.

### Creating fusion systems
In order to create a fusion system we need an _automiser sequence_, this is a list of automorphism groups, the first must be $\mathrm{Aut}_\mathcal{F}(S)$. Let us use `F` to create the fusion system again and check it is isomorphic to the one we created using the `GroupFusionSystem` function.
```
> FF := CreateFusionSystem(EA);
> FF;
Fusion system F over a p-group S of order 3^3
S is SmallGroup(27, 3) and isomorphic to He3
F has 2 classes of essential subgroups
The orders of the essential subgroups are [ 9, 9 ]
The orders of the Out_F(E) are [ 48, 48 ]
The order of Out_F(S) is 4
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

### SmallFusionSystems
As of v2.0.0 the best way to save and load fusion systems is using the commands `WriteFusionRecord(file)` and `LoadFusionSystem(file)`. Included now is the library SmallFusionSystems, details of its use can be found in the documentation but in essence `SmallFusionSystem(order, i)` returns the ith small fusion systems over a group of order `order` and `AllSmallFusionSystems(order)` or `AllSmallFusionSystems(S)` will return all fusion systems over a group of order `order` or over `S` respectively. Currently all the fusion systems saved in https://github.com/chris1961parker/Fusion-Systems have been added and over time more will be added. There is a command `AddSmallFusionSystem(F)` that will check if a fusion system is already in the library and if not add it. As of right now (v2.7.2) there is not a particularly robust management or maintenance of the library but I plan to add this.

Here are some examples of useful functions. First let us call a fusion system almost reduced if $O_p(\mathcal{F}) = 1$ and $O^p(\mathcal{F}) = \mathcal{F}$. Due to the large number of fusion systems which are not almost reduced (and in any case are not particularly interesting) by default any function that returns a collection of fusion systems will only return almost reduced ones. However this can be controlled by the optional argument `almost_reduced`.

First let us return to our example `F`, this fusion system (should) already in the library and we can check its id by running the following
```
> IdentifyFusionSystem(F);
Input fusion system is small fusion system <27, 1>
<27, 1>
```
This fusion system can therefore be retrieved by `SmallFusionSystem(27,1)`. We know that this is a group fusion system but the library will only know this if it is told i.e. just because a fusion system does not say it is a group fusion system it certainly does not mean it is exotic (hopefully exotic will be its own attribute one day). In this case however it has been saved (and indeed has been for most small groups of Lie type and almost simple groups). When loading the fusion system by default the group is not loaded, only the name, this is due to the disparity in speed in loading a group fusion system vs loading the entire group. This can be rectified by the argument `load_group`:
```
> SF := SmallFusionSystem(27,1);
> SF`fusion_group;

>> SF`fusion_group;
     ^
Runtime error in `: Attribute 'fusion_group' for this structure is valid but not
assigned

> SF`fusion_group_name;
PSL(3,3)

> SF := SmallFusionSystem(27,1: load_group := true);
> SF`fusion_group;
Permutation group acting on a set of cardinality 13
Order = 5616 = 2^4 * 3^3 * 13
    (1, 10, 4)(6, 9, 7)(8, 12, 13)
    (1, 3, 2)(4, 9, 5)(7, 8, 12)(10, 13, 11)
>
```
Since loading fusion systems can be slow there is a way of accessing all the pertinent information without actually loading it, this is done by the `SmallFusionSystemRecord(order,i)` command, this returns a record with a bunch of attributes that gives a near enough complete picture of the fusion system.
Other attributes can be stored such as the core, focal subgroup, if the fusion system is indecomposable etc. These can be updated using the relevant commands but of course hopefully in complete datasets this won't be necessary, likewise we will not demonstrate how to add fusion systems to the dataset.
Finally we look at return complete lists. Often we are interested in a fusion system over a particular $p$-group and we can return all the fusion systems supported on some $S$ as follows:
```
> AllSmallFusionSystems(S);
[
    F is SmallFusionSystem(27, 1)
    Fusion system F over a p-group S of order 3^3
    S is SmallGroup(27, 3) and isomorphic to He3
    F has 2 classes of essential subgroups
    The orders of the essential subgroups are [ 9, 9 ]
    The orders of the Out_F(E) are [ 48, 48 ]
    The order of Out_F(S) is 4
    F is isomorphic to the group fusion system of PSL(3,3),
    F is SmallFusionSystem(27, 2)
    Fusion system F over a p-group S of order 3^3
    S is SmallGroup(27, 3) and isomorphic to He3
    F has 2 classes of essential subgroups
    The orders of the essential subgroups are [ 9, 9 ]
    The orders of the Out_F(E) are [ 48, 48 ]
    The order of Out_F(S) is 8,
    F is SmallFusionSystem(27, 3)
    Fusion system F over a p-group S of order 3^3
    S is SmallGroup(27, 3) and isomorphic to He3
    F has 1 classes of essential subgroups
    The orders of the essential subgroups are [ 9 ]
    The orders of the Out_F(E) are [ 48 ]
    The order of Out_F(S) is 8
    F is isomorphic to the group fusion system of PSL(3,3).C2,
    F is SmallFusionSystem(27, 4)
    Fusion system F over a p-group S of order 3^3
    S is SmallGroup(27, 3) and isomorphic to He3
    F has 1 classes of essential subgroups
    The orders of the essential subgroups are [ 9 ]
    The orders of the Out_F(E) are [ 48 ]
    The order of Out_F(S) is 16
]

> #AllSmallFusionSystems(S:almost_reduced := false);
8
> #AllSmallFusionSystems(S);
4
```
We can also use `AllSmallFusionSystems(order)` to obtain all those over a group of order `order`. If we want to count or obtain the indices of these we can use `NumberSmallFusionSystems`:
```
> NumberSmallFusionSystems(3^3:almost_reduced := false);
10 [ 1 .. 10 ]
> NumberSmallFusionSystems(S);
4 [ 1, 2, 3, 4 ]
```


### Saving fusion systems (legacy)
This method of saving and loading has been replaced by the above.
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


