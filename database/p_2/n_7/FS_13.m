S:=
PCGroup(\[ 7, -2, 2, 2, 2, -2, 2, -2, 253, 456, 758, 2019, 346, 2804, 1411, 375,
172 ])
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
E.4 * E.7
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
E.1 * E.6
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
E.1 * E.7
>
,
<
E.2
,
E.2 * E.5 * E.7
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
E.1 * E.5 * E.7
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
E.4 * E.5
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
{ S.3, S.4, S.5, S.7, S.2, S.6 }
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
E.1 * E.2 * E.4
>
,
<
E.2
,
E.2 * E.4
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
E.2
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
E.1 * E.5 * E.6
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
E.1 * E.2 * E.4
>
,
<
E.2
,
E.4
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
E.2
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
2
]:=A;

E:=sub<S|
{ S.1, S.4, S.5, S.7, S.2, S.6 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.5 * E.6
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
E.1 * E.4
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
E.1 * E.6
>
,
<
E.2
,
E.2 * E.5 * E.6
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
E.1 * E.4
>
,
<
E.2
,
E.1 * E.2 * E.3 * E.4 * E.6
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
E.1 * E.3 * E.5 * E.6
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
3
]:=A;

E:=sub<S|
{ S.1 * S.4, S.3, S.5, S.7, S.2, S.6 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2 * E.5 * E.6
>
,
<
E.2
,
E.4 * E.5 * E.6
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
E.2 * E.4 * E.5
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
E.2 * E.4
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
E.4 * E.6
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
4
]:=A;

E:=sub<S|
{ S.3, S.4, S.1 * S.5, S.7, S.6 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

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
E.4
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
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.4
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
E.3
>
,
<
E.5
,
E.5
>
 ]>>;

Autos[
5
]:=A;

FS:=CreateFusionSystem(Autos);