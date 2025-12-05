S:=
PCGroup(\[ 6, -2, 2, 2, 2, -2, 2, 96, 217, 103, 650, 476, 1347, 297 ])
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
E.1 * E.5
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
E.3 * E.5 * E.6
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
E.5
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
E.2 * E.5
>
,
<
E.2
,
E.1 * E.2
>
,
<
E.3
,
E.3 * E.4 * E.6
>
,
<
E.4
,
E.3
>
,
<
E.5
,
E.5
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
E.1
>
,
<
E.2
,
E.2 * E.6
>
,
<
E.3
,
E.3 * E.5 * E.6
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
E.5
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
E.1 * E.2 * E.4
>
,
<
E.2
,
E.1 * E.3 * E.6
>
,
<
E.3
,
E.3 * E.5 * E.6
>
,
<
E.4
,
E.4 * E.5 * E.6
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
E.5
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
E.2 * E.5
>
,
<
E.3
,
E.3 * E.6
>
,
<
E.4
,
E.4 * E.5 * E.6
>
,
<
E.5
,
E.5
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
E.1 * E.6
>
,
<
E.2
,
E.2 * E.6
>
,
<
E.3
,
E.3 * E.6
>
,
<
E.4
,
E.4 * E.5 * E.6
>
,
<
E.5
,
E.5
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
E.1
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
E.3
>
,
<
E.4
,
E.4
>
,
<
E.5
,
E.5
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
{ S.3 * S.6, S.3, S.5, S.4 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2 * E.3 * E.4
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
E.1 * E.4
>
,
<
E.4
,
E.2 * E.3
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2 * E.3 * E.4
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
,
<
E.4
,
E.4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2 * E.4
>
,
<
E.2
,
E.1 * E.2 * E.3
>
,
<
E.3
,
E.4
>
,
<
E.4
,
E.3 * E.4
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.1 * S.3 * S.4, S.2 * S.4, S.6, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2 * E.4
>
,
<
E.2
,
E.1 * E.4
>
,
<
E.3
,
E.3
>
,
<
E.4
,
E.4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2 * E.4
>
,
<
E.2
,
E.1 * E.2 * E.3
>
,
<
E.3
,
E.4
>
,
<
E.4
,
E.3 * E.4
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
E.3 * E.4
>
,
<
E.3
,
E.1 * E.3
>
,
<
E.4
,
E.2
>
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);