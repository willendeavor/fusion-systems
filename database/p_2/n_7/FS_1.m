S:=
PCGroup(\[ 7, -2, 2, -2, 2, -2, 2, -2, 56, 85, 422, 219, 436, 136, 2804, 1411, 
172, 124 ])
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
E.3 * E.5
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
E.5 * E.7
>
,
<
E.6
,
E.6
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
E.1 * E.3 * E.5
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
E.3 * E.5
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
E.5 * E.7
>
,
<
E.6
,
E.6
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
{ S.3 * S.4 * S.5, S.4, S.5 * S.6, S.1 * S.2, S.7, S.6 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2 * E.3 * E.5
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
E.3 * E.4 * E.5
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
E.1 * E.2 * E.4 * E.6
>
,
<
E.2
,
E.1 * E.3 * E.4 * E.6
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
E.3 * E.5 * E.6
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

Autos[
2
]:=A;

E:=sub<S|
{ S.4, S.5, S.7, S.2, S.6 }
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
E.2
>
,
<
E.3
,
E.3 * E.5
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
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3 * E.5
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
E.1 * E.4 * E.5
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
E.1 * E.3 * E.4
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
 ]>>;

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
E.3 * E.5
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
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);