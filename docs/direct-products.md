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

### Intrinsics


