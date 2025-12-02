S:=
PCGroup(\[ 4, -7, 7, -7, -7, 449, 25286 ])
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
E.2 * E.3
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
E.2
>
,
<
E.3
,
E.3^4 * E.4
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
E.1
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
E.3^6
>
,
<
E.4
,
E.4^6
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
E.3^6 * E.4^6
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
E.1 * E.4^6
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
E.3 * E.4^6
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
{ S.1 * S.3^6 * S.4^6, S.4 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^5 * E.2^3
>
,
<
E.2
,
E.1^3 * E.2^2
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
E.1^5 * E.2^6
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