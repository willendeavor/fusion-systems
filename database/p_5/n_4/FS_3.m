S:=
PCGroup(\[ 4, -5, 5, -5, -5, 241, 6302 ])
;
Autos:=[];

E:=sub<S|
{ S.4, S.1, S.2, S.3 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

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
E.3^4 * E.4^3
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
E.3 * E.4
>
,
<
E.4
,
E.4^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.4^4
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
E.3 * E.4^4
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
E.2 * E.3
>
,
<
E.3
,
E.3 * E.4^4
>
,
<
E.4
,
E.4
>
 ]>>;

Autos[
1
]:=A;

E:=sub<S|
{ S.4, S.1 * S.2^4 * S.3^4 * S.4^2 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

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
E.1^3 * E.2^4
>
,
<
E.2
,
E.1^3 * E.2
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
E.1^3 * E.2^4
>
 ]>>;

Autos[
2
]:=A;

E:=sub<S|
{ S.1 * S.2^2 * S.3^3 * S.4^2, S.4 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^2 * E.2
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
E.2
>
,
<
E.2
,
E.1^4 * E.2
>
 ]>>;

Autos[
3
]:=A;

E:=sub<S|
{ S.1 * S.2^3 * S.3 * S.4, S.4 }
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
E.1^4 * E.2^4
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
E.1^2 * E.2
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

Autos[
4
]:=A;

E:=sub<S|
{ S.4, S.1 * S.3^4 * S.4 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

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
E.2^3
>
,
<
E.2
,
E.1^3
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^2 * E.2^4
>
,
<
E.2
,
E.1^2 * E.2^2
>
 ]>>;

Autos[
5
]:=A;

E:=sub<S|
{ S.1 * S.2 * S.4, S.4 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

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
E.1^3 * E.2
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
E.1^3
>
,
<
E.2
,
E.1^2 * E.2^2
>
 ]>>;

Autos[
6
]:=A;

FS:=CreateFusionSystem(Autos);