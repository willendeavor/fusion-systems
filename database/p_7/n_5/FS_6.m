S:=
PCGroup(\[ 5, -7, 7, -7, -7, -7, 52011, 35392, 14708 ])
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
E.2
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
E.1^2 * E.3^4 * E.4^6 * E.5^5
>
,
<
E.2
,
E.1 * E.2^3 * E.3^2 * E.4^2 * E.5^5
>
,
<
E.3
,
E.3^6 * E.4^6 * E.5^5
>
,
<
E.4
,
E.4^4
>
,
<
E.5
,
E.5^5
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3 * E.4 * E.5^5
>
,
<
E.2
,
E.1 * E.2^2 * E.5^4
>
,
<
E.3
,
E.3^2 * E.4 * E.5^5
>
,
<
E.4
,
E.4^4
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
E.2 * E.4^5 * E.5^6
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
E.1 * E.3^5 * E.4
>
,
<
E.2
,
E.2 * E.3^5 * E.5^2
>
,
<
E.3
,
E.3 * E.4^5 * E.5^5
>
,
<
E.4
,
E.4 * E.5^4
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
E.1^4 * E.3^4 * E.4^4 * E.5^6
>
,
<
E.2
,
E.1^5 * E.2^2 * E.3^3 * E.4
>
,
<
E.3
,
E.3 * E.4^4 * E.5^6
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
E.2 * E.4^5
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
E.2 * E.4^5 * E.5^2
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
{ S.5, S.1 * S.2 * S.3^6 * S.5 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^4 * E.2
>
,
<
E.2
,
E.1^2 * E.2^6
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
E.2^3
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
E.1 * E.2^6
>
,
<
E.2
,
E.1^3 * E.2^6
>
 ]>>;

Autos[
2
]:=A;

FS:=CreateFusionSystem(Autos);