S:=
PCGroup(\[ 6, -2, 2, -2, -2, -2, -2, 192, 73, 218, 116, 122, 579, 297, 165, 1444, 730, 88 ])
;
Autos:=[];

E:=sub<S|
{ S.1, S.3, S.6, S.2, S.4, S.5 }
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
E.6
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
E.6
>
 ]>>;

Autos[
1
]:=A;

E:=sub<S|
{ S.1, S.6, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3
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
E.3
>
 ]>>;

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
E.3
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
E.1
>
,
<
E.3
,
E.3
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
E.1 * E.3
>
,
<
E.3
,
E.3
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.6, S.2 }
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
3
]:=A;

FS:=CreateFusionSystem(Autos);