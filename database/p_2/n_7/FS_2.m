S:=
PCGroup(\[ 7, -2, 2, -2, -2, -2, -2, -2, 85, 254, 135, 142, 675, 346, 192, 1684,
851, 242, 4037, 2028, 124 ])
;
Autos:=[];

E:=sub<S|
{ S.4, S.7, S.6, S.2, S.1, S.3, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1
>
,
<
E.2
,
E.2 * E.3
>
,
<
E.3
,
E.3 * E.4
>
,
<
E.4
,
E.4 * E.5
>
,
<
E.5
,
E.5 * E.6
>
,
<
E.6
,
E.6 * E.7
>
,
<
E.7
,
E.7
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3 * E.4
>
,
<
E.2
,
E.2
>
,
<
E.3
,
E.3 * E.4
>
,
<
E.4
,
E.4 * E.5
>
,
<
E.5
,
E.5 * E.6
>
,
<
E.6
,
E.6 * E.7
>
,
<
E.7
,
E.7
>
 ]>>;

Autos[
1
]:=A;

E:=sub<S|
{ S.7, S.2 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2
>
,
<
E.2
,
E.1
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2
>
,
<
E.2
,
E.1
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.1, S.7 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2
>
,
<
E.2
,
E.1 * E.2
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2
>
,
<
E.2
,
E.2
>
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);