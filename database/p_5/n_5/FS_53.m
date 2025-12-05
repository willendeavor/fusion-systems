S:=
PCGroup(\[ 5, -5, 5, -5, -5, -5, 301, 21002, 27503 ])
;
Autos:=[];

E:=sub<S|
{ S.1, S.3, S.4, S.2, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.5^2
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
E.4 * E.5^2
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
E.2^2
>
,
<
E.3
,
E.3^4 * E.4^2
>
,
<
E.4
,
E.4^3 * E.5
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
E.1^4
>
,
<
E.2
,
E.2^4
>
,
<
E.3
,
E.3 * E.4^4 * E.5^2
>
,
<
E.4
,
E.4^4 * E.5^4
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
E.1 * E.5^3
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
E.3^2 * E.4
>
,
<
E.4
,
E.4^4 * E.5^3
>
,
<
E.5
,
E.5^3
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3^4
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
E.1^4
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
E.3^4 * E.4 * E.5^3
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
E.5^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.4 * E.5^2
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
E.4 * E.5^2
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
{ S.3, S.4, S.2, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^3
>
,
<
E.2
,
E.2^3
>
,
<
E.3
,
E.3^3
>
,
<
E.4
,
E.4^3
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
E.2^3 * E.3 * E.4^2
>
,
<
E.4
,
E.2^2 * E.4^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.2^4 * E.3
>
,
<
E.2
,
E.2^3 * E.4^2
>
,
<
E.3
,
E.2^4 * E.3^4 * E.4^2
>
,
<
E.4
,
E.2^2 * E.3^4 * E.4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^4
>
,
<
E.2
,
E.2^4
>
,
<
E.3
,
E.3^4
>
,
<
E.4
,
E.4^4
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.1 * S.3^4 * S.4^4 * S.5^2, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^3
>
,
<
E.2
,
E.2^3
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.2^3
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
E.1^4
>
,
<
E.2
,
E.2^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^4 * E.2^4
>
,
<
E.2
,
E.1^4 * E.2^2
>
 ]>>;

Autos[
3
]:=A;

FS:=CreateFusionSystem(Autos);