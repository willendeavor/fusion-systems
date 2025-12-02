S:=
PCGroup(\[ 5, -3, 3, 3, -3, -3, 301, 2163 ])
;
Autos:=[];

E:=sub<S|
{ S.5, S.1, S.4, S.2, S.3 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.4^2
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
E.3
>
,
<
E.4
,
E.4^2 * E.5
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
E.2^2
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
E.4^2
>
,
<
E.5
,
E.5^2
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
E.3^2
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
1
]:=A;

E:=sub<S|
{ S.5, S.4, S.2, S.3 }
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
E.3^2 * E.4
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
E.1^2
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
E.3^2
>
,
<
E.4
,
E.4^2
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2 * E.4^2
>
,
<
E.2
,
E.1^2 * E.2^2 * E.3 * E.4^2
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
E.1 * E.2^2 * E.3^2
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.1 * S.5, S.5, S.4, S.3 }
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
E.3 * E.4
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
E.1^2 * E.3^2 * E.4^2
>
,
<
E.4
,
E.4^2
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
E.4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3^2
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
E.1^2 * E.3^2 * E.4
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
E.3^2 * E.4^2
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
E.3 * E.4
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
E.1^2 * E.4^2
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
E.3
>
,
<
E.4
,
E.4
>
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);