S:=
PCGroup(\[ 6, -3, 3, -3, -3, -3, -3, 810, 145, 3302, 662, 873, 237, 5680 ])
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
E.1 * E.3^2 * E.5^2 * E.6^2
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
E.3 * E.4^2 * E.6
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
E.5 * E.6^2
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
E.1 * E.3^2 * E.5^2 * E.6^2
>
,
<
E.2
,
E.2 * E.4 * E.5
>
,
<
E.3
,
E.3 * E.4^2 * E.6
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
E.5 * E.6^2
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
E.2 * E.5^2 * E.6
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
E.2 * E.3
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
E.1^2 * E.4 * E.5^2
>
,
<
E.2
,
E.2^2
>
,
<
E.3
,
E.3 * E.4 * E.5^2
>
,
<
E.4
,
E.4^2 * E.5^2 * E.6^2
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
E.6^2
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
E.2^2
>
,
<
E.3
,
E.3^2 * E.4^2 * E.6
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
E.5^2
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
1
]:=A;

E:=sub<S|
{ S.2 * S.3 * S.4 * S.6^2, S.6, S.5 }
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
E.2
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
E.1 * E.2^2 * E.3
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
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2^2 * E.3
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
E.1^2 * E.3
>
,
<
E.2
,
E.2^2
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
E.1^2 * E.2^2 * E.3
>
,
<
E.2
,
E.1^2 * E.2 * E.3^2
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
E.1^2
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
E.3^2
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
E.2 * E.3^2
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
{ S.6, S.1 * S.2 * S.3 * S.4^2 * S.6^2 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^2 * E.2^2
>
,
<
E.2
,
E.1^2 * E.2
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
E.1^2
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^2
>
,
<
E.2
,
E.2^2
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^2 * E.2^2
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