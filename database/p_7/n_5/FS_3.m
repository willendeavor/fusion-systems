S:=
PCGroup(\[ 5, -7, 7, -7, -7, -7, 561, 4522, 7848 ])
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
E.1 * E.3^6
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
E.3 * E.4^6
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
E.1^6
>
,
<
E.2
,
E.2^6
>
,
<
E.3
,
E.3 * E.4 * E.5^6
>
,
<
E.4
,
E.4^6 * E.5^2
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
E.1^6
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
E.3^6
>
,
<
E.4
,
E.4^6
>
,
<
E.5
,
E.5^6
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3^6
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
E.3 * E.4^6
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
E.2^2
>
,
<
E.3
,
E.3 * E.4^3
>
,
<
E.4
,
E.4^2 * E.5^2
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
E.2 * E.5^6
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

Autos[
1
]:=A;

E:=sub<S|
{ S.2 * S.3 * S.4^6 * S.5^4, S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^3 * E.2^3
>
,
<
E.2
,
E.1^6 * E.2^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^5 * E.2
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
E.1^6
>
,
<
E.2
,
E.2^6
>
 ]>>;

Autos[
2
]:=A;

FS:=CreateFusionSystem(Autos);