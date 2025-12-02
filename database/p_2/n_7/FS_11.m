S:=
PCGroup(\[ 7, -2, 2, 2, -2, 2, -2, -2, 422, 471, 2915, 1018, 248, 2804, 851, 
718, 375, 172, 1027 ])
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
E.1 * E.5 * E.6 * E.7
>
,
<
E.2
,
E.2 * E.4 * E.6
>
,
<
E.3
,
E.3 * E.7
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
E.4 * E.6
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
,
<
E.4
,
E.5
>
,
<
E.5
,
E.4 * E.5 * E.6 * E.7
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
E.1 * E.5
>
,
<
E.2
,
E.2 * E.4 * E.6 * E.7
>
,
<
E.3
,
E.3 * E.7
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
E.1 * E.5 * E.6
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
E.3 * E.7
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
E.5
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
E.3 * E.4
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
E.5 * E.6 * E.7
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
E.2 * E.4 * E.7
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
{ S.1, S.5 * S.7, S.4 * S.5, S.7, S.2, S.6 }
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
E.1 * E.6
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
E.2
>
,
<
E.3
,
E.1 * E.3 * E.4 * E.5
>
,
<
E.4
,
E.2 * E.3 * E.5 * E.6
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
E.2 * E.5 * E.6
>
,
<
E.2
,
E.1 * E.2 * E.6
>
,
<
E.3
,
E.2 * E.3
>
,
<
E.4
,
E.1 * E.2 * E.4
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
E.1 * E.4 * E.6
>
,
<
E.2
,
E.2 * E.3 * E.4
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
2
]:=A;

E:=sub<S|
{ S.3, S.4 * S.5 * S.7, S.5 * S.7, S.7, S.6 }
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
E.5
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.4 * E.5
>
,
<
E.2
,
E.1 * E.3 * E.4
>
,
<
E.3
,
E.1 * E.2 * E.4
>
,
<
E.4
,
E.1 * E.5
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
E.4 * E.5
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
E.2 * E.4
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
E.3 * E.5
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
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);