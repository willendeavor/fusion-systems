S:=
PCGroup(\[ 3, -7, 7, -7, 631 ])
;
Autos:=[];

E:=sub<S|
{ S.3, S.2, S.1 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^6 * E.3
>
,
<
E.2
,
E.2^6 * E.3
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
E.1^6
>
,
<
E.2
,
E.2 * E.3^6
>
,
<
E.3
,
E.3^6
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
E.2^2 * E.3
>
,
<
E.3
,
E.3^4
>
 ]>>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1 * E.3^5
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
E.1
>
,
<
E.2
,
E.2 * E.3^5
>
,
<
E.3
,
E.3
>
 ]>>;

Autos[
1
]:=A;

E:=sub<S|
{ S.3, S.1 }
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
E.1^6 * E.2^3
>
 ]>>;

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
E.1^2 * E.2^5
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

E:=sub<S|
{ S.2, S.2^5 * S.3 }
>;

AE:= AutomorphismGroup(E);

A:=sub<AE|>;

A:=sub<AE|A, hom<E -> E |[ 
<
E.1
,
E.1^6 * E.2^6
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
E.1^4 * E.2^5
>
,
<
E.2
,
E.2^5
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
3
]:=A;

FS:=CreateFusionSystem(Autos);