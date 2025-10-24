//This file is created by Parker and Semeraro.
//It contains programs designed to calculate with fusion systems.  
//It also has programs to find all saturated fusion systems on 
//a given p-group with trivial $p$-core and $p$-quotient. 
//It can be easilly modified to find all saturated fusion systems if 
//so desired. Details can be found in  
//``Algorithms for fusion systems with applications 
//to $p$-groups of small order" by Parker and  Semeraro
//It also contains other functions that we found useful.
//It works on Magma V2.25-4.  Load the file by Attach("FusionSystems.m");

freeze;
declare type FusionSystem;
declare attributes  FusionSystem: prime, group, subgroups, borel, centrics, 
essentials, essentialautos, fusiongraph, maps, classes, AutF, saturated,
grpsystem, grppgrp, mapbackgrp;

declare attributes GrpMat: autogrp,  autoperm, autopermmap,autF;
declare attributes GrpPerm: autogrp, autoperm, autopermmap, autF;
declare attributes GrpPC: autogrp, autoperm, autopermmap, autF;
//////




/






///////////////////////////////////////
////// IsStronglypEmbeddedMod(G,Ker,p): 
//////does G contain a Strongly p-embedded subgroup?
////////////////////////





 
//////////////////////////////////////////////////////////////////////////////
////// IsStronglypEmbedded(G,p): does G contain a Strongly p-embedded subgroup?
////USES GLS2 Proposition 17.11
///////////////////////////////////////////////////////////////////////////



//////////////////////////////////
/////Selects a  random automorphism in Aut(Q). 
///////////////////////////////////





////////////////////////////////////////////////////////////////////////////
/////// This makes orbits of automorphism group on subgroups.
///////Here Q is a subgroup of P and AFP \le Aut(P). We 
///////determine Q^A=[Q,Q2,\dots Qs] and N_A(Q)
////// Elt is a sequence of elements [w1,w2, dots, ws] 
////// which map elements of the Q to the corresponding element Qi.
///////////////////////////////////////////////////////////////////////////




////////////////
/// IsSCentric(S,P)
//////////////////



///////////////////



//////////////////////////////

//////////////////////////////


///////////////////////////////



/////////////////////////////////
/////////////AutFPCandidates.
/////////////////




//////////////////////////////////////////////////////
////We now start to make some functions specific for fusion systems
//////////////////////////////////////////////////////////////////






//////////////////////////////////////////////////////////////////////////
 //Given a subgroup Q and a morphism Q -> S in F, calculate NPhi. 
////Requires various functions already to be loaded.
//////////////////////////////////////////////////////////////////////////



 

//
///////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
/////FocalSubgroup #Uses 1.8 from AOV to determine the focal subgroup. 
///////////////////////////////////////////////////////////////////////



 

//////////////////////////////////////////////////////
///////////////////////////////////////////////
//This determines a graph with edges AB   for A and B 
// subgroups of an essential subgroup E with A and B Aut_F(E) 
//conjugate. The connects components are the S-classes which have 
//union the p-class. It then completes the connected components to complete 
//graphs Maps contains and element 
//Maps[i,j]:SS[i]->SS[j]
///////////////////////////////////////////////







//////////////////////////////////////////////
//Identifies the B-Class of an arbitrary subgroup.
/////////////////////////////////////////

 
 
 
//////////////////////////////////////
////Identify the F-orbit as a connected component of the fusion graph. 
///P is in SS
///////////////////////////////

  


//////////////////////////////////////////
////Suppose that P \le S. Determine the F-class of P
/////////////////////////////




   //////////////////////////////////////////
////Suppose that P,Q \le S. Are P and Q F-conjugate? V:= Vertices(Gamma);
///Returns true or false and if true a map in F
/////////////////////////////



///////////////////////
/////// F-conjugacy class
///////////////////////////////


/////////////////////////
// SizeFConjugacyClass
/////////////////////////


/////////////////////////////////////
/// FConjugacyClasses
///////////////////////////////////




/////////////////////////////////////
///Number  FConjugacyClasses
///////////////////////////////////




///////////////////////////////////
///////IsCentric(P).
///////////////////////////////////




///////////////////////////////////
///////IsFullyNormalized(P).
///////////////////////////////////




/////////////////////////////////////
/////////IsFullyCentralized(P).
/////////////////////////////////////




//////////////////////////////////////////////////////////////////////
///Transports for ww in SS and x B-conjugate to AutF(ww) to AutF(x). 
///The second one transports with known origin and X in SS.  
//So AY= AutF[SS[ii]] is known and X is F-conjugate to Y=SS[ii]
//////////////////////////////////////////////////////////////////////

intrinsic TransportAutomorphismsYtoX(F::FusionSystem,AutF::Assoc,Y::Grp,X::Grp)
                ->GrpAuto
{Transports the automorphism group of the first group to 
the second assuming they are F-conjugate}
require IsConjugate(F,Y,X):"The groups are not F-conjugate";
 MakeAutos(X);


    Ax:= X`autogrp;
    AY:= AutF[Y];
    SS:= F`subgroups; S:= F`group; B:= F`borel; 
if assigned(F`fusiongraph) eq false then 
    F`fusiongraph,F`maps:= FusionGraph(F);  
   
end if; F`classes:= ConnectedComponents(F`fusiongraph); 
    V:= Vertices(F`fusiongraph);
    Maps:=F`maps;
    jj:= Index(SS,X);
    ii:= Index(SS,Y);

    Geo:=Geodesic(V!ii,V!jj);
    alpha:= Identity(AY);
    beta:= Identity(Ax);
        for iii:= 1 to #Geo-1 do
            alpha:= alpha*Maps[[Index(Geo[iii]),Index(Geo[iii+1])]];
        end for;
        for iii:= #Geo to 2 by -1 do
            beta:= beta*Maps[[Index(Geo[iii]),Index(Geo[iii-1])]];
        end for;
    AutX:= sub<Ax|{beta*gen*alpha:gen in Generators(AY)}>;
return AutX;
end intrinsic;

/////////////////////////////////////////////////////////
////////////Making AutF[X] more generally for F-centric X. We do this on connected components.
////////////////////////////////////////////////////////
//
intrinsic MakeAllAutFCentric(FF::FusionSystem:saturationtest)->Assoc, Bool
{Makes all AutF for centric subgroups unless parameter saturated test eq true in which case it stops early when the system is not saturated .}

ZZ:=Integers();
SS:= FF`subgroups;
S:= FF`group; 
B:= FF`borel; 
AutF:= FF`AutF; 
Essentials:= FF`essentials; 

if assigned(FF`fusiongraph) eq false then FF`fusiongraph,FF`maps:= FusionGraph(FF);
   
end if;
 FF`classes:= ConnectedComponents(FF`fusiongraph);
if assigned(FF`centrics) eq false then FF`centrics:={x:x in FF`subgroups|IsCentric(FF,x)}; end if;
Maps:= FF`maps;  
ConComp:= FF`classes; 
Fac:= FactoredOrder(S);
ExpS:=Fac[1][2]; p:= FF`prime;
expP:= ExpS-1;

 
for x in SS do   
    if #x eq p^expP and ((x in Essentials) eq false) then
    	AutF[x]:= AutYX(Normalizer(B,x),x);
    end if;
end for;

  TTTn:={x:x in FF`centrics|   IsFullyNormalized(FF,x) and (x in Essentials) eq false};
for subexponent:=ExpS-2 to 2 by -1 do
  
    TTT :={x: x in TTTn|#x eq p^subexponent };
  
 
    while  #TTT ne 0 do 
        P:= Random(TTT);
	//If P is F-conjugate to a member of Essentials, then Aut_F(P) is F-conjugate to Aut_F(E). Transfer the data and move to next P.

        for E in Essentials do 
            aa,bb:=IsConjugate(FF,P,E); 
            aa,bbb:=IsConjugate(FF,E,P); 
            if aa  then  //bbb:= Inverse(bb);
                AutF[P]:=  sub<P`autogrp|{hom<P->P|gg:->bbb(hh(bb(gg)))> :hh in Generators(AutF[E])}>;
                TTT:= TTT diff {P};continue; 
            end if; 
        end for; //E
        
	///Now P is not F-conjugate to E.

           NBP:=Normalizer(B,P);
           AutF[P] :=  AutYX(NBP,P); 
	   AFSP:=AutF[P];
          
	   NBPoverP, a := NBP/P;
		///TTTS contains representative of all non-trivial $p$-subgroups in N_S(P)/P
 
            TTTS:= [sub<NBP|SubInvMap(a, NBP, x`subgroup),P>:x in Subgroups(NBPoverP:OrderDividing:=#S)|x`order ne 1];
                for ccc:= 1 to #TTTS do
                 x := TTTS[ccc]; 
                    MakeAutos(x);

                    if x in SS then
                        AutFx := AutF[x];
                        j:= x`autopermmap;  Ap:=x`autoperm;
                    else  
                           Ax:=x`autogrp;
                            for ww in SS do
                            aa, bb := IsConjugate(B,ww,x);
                                if aa then
                                    bbb:= ConjtoHom(ww,x,bb);  bbb1:= ConjtoHom(x,ww,bb^-1);
                                    AutFx:= sub<Ax|{bbb1*gen*bbb : gen in Generators(AutF[ww])}>; break ww;
                                end if;
                             end for;//for ww
                    j:=x`autopermmap; Ap:= x`autoperm; 
                    end if;// if x in ss, then, else, end if
                AFp:= sub<Ap|{j(pp):pp in Generators(AutFx)}>;
                jinverse:=Inverse(j);
                AA, NN, Elt:= AutOrbit(x,P,AutFx);
                MM:= sub<Ap|{j(n):n in Generators(NN)}>;
                Trp := Transversal(AFp,MM);
                Tr:= {jinverse(t):t in Trp};
                ////////////////////////////////
                //We look at maps between TTTS[ccc] and TTTS[ddd] that are extensions of maps in AutF[P].  
                ///We don't need to do it both ways around as adding an element is the same as adding its inverse.
                //////////////////////////////////////////////////
                    for ddd:= ccc to #TTTS do  
                        y := TTTS[ddd]; W:={};
                        if x eq y then 
                                for nn in Generators(NN) do  mmP:= iso<P->P| w:->nn(w)>; 
                                W:= W join {mmP};
                            end for;
                            AutF[P]:=sub<P`autogrp|AutF[P],W>;
                        else
                        aa, bb:= IsConjugate(FF,x,y);
                            if aa then 
                            W:={alpha*bb:alpha in Tr |(alpha*bb)(P) eq P}; 
                            AutF[P]:=sub<P`autogrp|AutF[P],W>;
                            end if;
                        end if;
                    end for;//ddd
                     if saturationtest then 
                        if ZZ!(#AutF[P]/#AFSP) mod p eq 0 then  
                        return AutF, false;
                        end if;  
                     end if; 
                end for; //ccc
                
              isp:=Index(SS,P);

                for C in FF`classes do
                    if isp  in C then D:= C; break; end if;
                end for;
                //Check that calculated data coincides with information from essentials. 
                //I.e if P if F-conjugate to some F`essential, then auto groups should be the same.
                
                 for iiii in [1..#Essentials] do E:= Essentials[iiii];
                    mm:= Index(SS,E); 
                    if mm in D then
                     TransP:=TransportAutomorphismsYtoX(FF,AutF,P,E);
                     if TransP ne FF`essentialautos[iiii] then 
                     if saturationtest then
                        return AutF, false; 
                      else print "the automiser sequence is not consistent in this system"; return AutF,_;
                      end if;
                      end if;
                     end if;
                end for;
                 //we now can define AutF for  all the F-conjugates of P
                 for kk in D do jj:= Index(kk); 
                    if jj eq isp then  TTT:= TTT diff {P};   continue; end if;
                    AutF[SS[jj]]:= TransportAutomorphismsYtoX(FF,AutF,P,SS[jj]);  
                    TTT:= TTT diff {SS[jj]};
                end for;  //
                
           end while; //TTT
     end for;//subexponent
delete TTT; delete TTTS;

return AutF, _;

end intrinsic;

////////////////////////////


intrinsic SurjectivityProperty(F::FusionSystem,P::Grp:saturationtest)->Bool, Bool
{Determines whether the surjectivity property hold for P}

if saturationtest and assigned(F`saturated) then 
return F`saturated, F`saturated; end if;

require IsCentric(F,P):"subgroup not F-centric";

SS:= F`subgroups; 
S:= F`group; 
B:= F`borel; 
Essentials:= F`essentials;

Maps:= F`maps; 
ConComp:= F`classes; 
AutF:= F`AutF;

 
 
SurP:= true;
NSP:= Normalizer(S,P);

NSPoverP, a := NSP/P; 
SSP:= [sub<NSP|SubInvMap(a, NSP, x`subgroup),P>:x in Subgroups(NSPoverP)|x`order ne 1];
   for OverGrpP in SSP do 
        BClassOverGrpP, alpha:= IdentifyBClass(F,OverGrpP);
        RepOverGrpP:= SS[BClassOverGrpP];
        MakeAutos(OverGrpP);
        Ax:=  OverGrpP`autogrp;
        beta:= ConjtoHom(RepOverGrpP,OverGrpP,alpha^-1);
        beta1:= ConjtoHom(OverGrpP,RepOverGrpP,alpha); 
        AutFx:= sub<Ax|{beta1*gen*beta : gen in Generators(AutF[RepOverGrpP])}>;      
        AA:= AutF[P]; 
        MakeAutos(P);
        AAp:= sub<P`autoperm|{P`autopermmap(gAA):gAA in Generators(AA)}>;
        action := AutYX (OverGrpP,P);
        actionp:= SubMap(P`autopermmap,AAp,action);
        Naction:= Normalizer(AAp,actionp);
        NBB:= SubInvMap(P`autopermmap,P`autogrp,Naction);
        Orb,NN, Elts:= AutOrbit(OverGrpP,P,AutFx);
        ResNN:=sub<P`autogrp|Generators(NN)>;
        if ResNN ne NBB then  SurP := false; break; end if;
    end for;
    if assigned(F`saturated) then
 return SurP, F`saturated; else return SurP, _;end if; 
 
 end intrinsic;
/////////////////////////
 /////////////////IsSaturated(F)
////////////////////////////////
 
intrinsic IsSaturated(F::FusionSystem)-> Bool{Determines if F is saturated}

if assigned(F`saturated) then return F`saturated; end if;
 
SS:= F`subgroups; 
S:= F`group; 
B:= F`borel; 
Essentials:= F`essentials;
 

if assigned(F`fusiongraph) eq false then  
F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
end if;
F`classes:= ConnectedComponents(F`fusiongraph);

Maps:= F`maps; 
AutF:= F`AutF;

ConComp:= F`classes; 
 
 
for x in F`essentials do 
    if IsCentric(F,x) eq false then 
    F`saturated := false; return F`saturated; 
    end if; 
     if IsFullyNormalized(F,x) eq false then 
    F`saturated := false; return F`saturated; 
    end if; 
end for;

 

if assigned(F`centrics) eq false then F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if;
  
    W:= {x: x in F`centrics|IsDefined(F`AutF,x) };
    i:=0;
     for x in Reverse(Setseq(F`centrics)) do  
        if x in W then continue; end if; 
        for w in W do
            a,b:=IsConjugate(F,x,w);
            if a then    aa,cc:=IsConjugate(F,w,x);    
            F`AutF[x] := sub<x`autogrp| {b*gamma*cc: gamma in Generators(F`AutF[w])} >; 
             W:= W join{x}; continue x; 
        end if;
        end for;
        
       F`AutF[x]:= AutomorphismGroup(F,x);  
       if IsFullyNormalized(F,x) then 
            if not IsFullyAutomised(F,x) then return false; end if;
       end if; 
       W:= W join{x};
     end for;
 

Saturated:= true;
for C in ConComp do
    for vv in C do
        PP:= SS[Index(vv)];
            if PP eq S then continue C; end if;
            if IsCentric(F,PP) eq false then continue C; end if;
            if IsFullyNormalized(F,PP) eq false then continue vv; end if;
            if RadicalTest(S,PP) eq false then   continue vv; end if;
            if IsFullyAutomised(F,PP) eq false then return false; end if;
        Saturated, sat := SurjectivityProperty(F,PP:saturationtest:=true);
        if  assigned(sat) then  return sat; end if;
            if Saturated then continue C; end if;
    end for;
    if Saturated eq false then break C; end if;
end for; 
delete F`fusiongraph;//This is a fix to make sure that IsConjugate works for non-centric subgroups



F`saturated := Saturated;
return Saturated;
end intrinsic;



//////////////////////////////////
intrinsic IsFullyAutomised(F::FusionSystem,P::Grp)->Bool{Is P fully F-automised}

 
 S:= F`group;   
 p:= F`prime;
 require #P gt 1 : "We require P non-trivial";
 
if  IsDefined(F`AutF,P) eq false then 
    F`AutF[P]:=  AutomorphismGroup(F,P);
end if;

ZZ:= Integers();
m:= #Normalizer(S,P)/#Centralizer(S,P);
m:= ZZ!m;
F:= FactoredOrder(F`AutF[P]); q:=1;
for x in F do 
    if x[1] eq p then q:= p^x[2]; end if; 
end for;
if q eq m then FA:= true; else FA:= false; end if;
return FA;
end intrinsic;
////////////////////////////////////////


intrinsic IsIsomorphic (F1::FusionSystem,F2::FusionSystem)->Bool{}

a, theta := IsIsomorphic(F1`borel,F2`borel);
if a eq false then return false; end if; 
p:= F1`prime;
bounds:=[8,6,6,6];
primes:=[2,3,4,4];

if p in primes and #F1`group le p^bounds[Index(primes,p)]  then
RO1:=[IdentifyGroup( x):x in F1`essentials];
RO2:=[IdentifyGroup(x):x in F2`essentials];
else
RO1:=[#x:x in F1`essentials];
RO2:=[#x:x in F2`essentials];
end if; 
if  RO1 ne RO2 then   return false; end if; 

 

//The automisers should have the same orders.
RO1:=[#x :x in F1`essentialautos];
RO2:=[#x :x in F2`essentialautos];
Sort(~RO1);
Sort(~RO2);
if RO1 ne RO2 then   return false; end if; 
 
 

AutBp:=(F2`essentials[1])`autoperm;

alpha:= (F2`essentials[1])`autopermmap;

NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp);
TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
Trans:=[Inverse(alpha)(xxx):xxx in TNB];
 

//transfer to same group. And make an image for each transversal map.
ImEssentials:=[];

for mu in Trans do
ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1`essentials] ); 
end for;

ImAutEssentials:= AssociativeArray({1..#Trans});

for zz in [1..#ImEssentials] do 
    ImEssentialsCalc:= ImEssentials[zz]; 
    mu:= Trans[zz];// theta. mu maps xin F1 essentials to a subgroup of F2`group
       //Initialize the automorphism group of the images
        for ii in [1..#ImEssentialsCalc] do  
            x:= ImEssentialsCalc[ii]; 
            x`autogrp :=AutomorphismGroup(x); 
            x`autopermmap, x`autoperm:= PermutationRepresentation(x`autogrp); 
        end for;     
    ImAutEssentialsCalc:=[];
    for x in ImEssentialsCalc do 
            AutF1:= F1`essentialautos[Index(ImEssentialsCalc,x)];
            XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
            ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
    end for;
    
ImAutEssentials[zz]:=ImAutEssentialsCalc;
 
end for;

for XXct in [1..#ImEssentials] do XX:=ImEssentials[XXct];
    for ii in [1..#XX] do e:= XX[ii]; if e in F2`subgroups then continue; end if;
            jj:= IdentifyBClass(F2,e);
            P:= F2`subgroups[jj];
            MakeAutos(P);
            a,b :=IsConjugate(F2`borel,e,P);
            bb:= ConjtoHom(e,P,b); 
            bbb:= ConjtoHom(P,e,b^-1);    
            XX[ii]:=P;
            ImAutEssentials[XXct][ii]:= sub<P`autogrp|
                {hom<P->P|gg:-> bb(gen(bbb(gg)))>:
                gen in  Generators(ImAutEssentials[XXct][ii])}>;
    end for;
end for;
            
 
        jj:= {1..#F2`essentials};
        for ii in [1..#ImAutEssentials] do 
            kk:= jj;
            for mm in ImAutEssentials[ii] do
                for aa in jj do
                    if mm eq F2`essentialautos[aa] then kk:= kk diff {aa}; end if;
                end for; 
             if #kk eq 0 then return true;end if;
            end for;
        end for; 
 return false;
end intrinsic;


//////////////////////////////////////////////////////////////
intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
{checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    
    return Eq;
end intrinsic;

/////////////////////////////////////
///////Make a fusion system from a specifeid p-subgroup S of a group G
////////////////////////////////////

intrinsic  GroupFusionSystem(G::Grp,T::Grp)->FusionSystem
{Creates the fusion system on the p-subgroup S of G}
p:= FactoredOrder(T)[1][1];
ZZ:= Integers();
B1:= Normalizer(G,T); T1:= Sylow(B1,p);
require  T1 eq sub<G|T,Centralizer(T1,T)>:"system cannot be saturated";   
 Testers:= {Sylow(SL(2,p^2), p),Sylow(SL(2,p^3), p),Sylow(SL(2,p^4), p),Sylow(SL(2,p^5), p),
Sylow(SL(2,p^6), p), Sylow(SU(3,p), p),Sylow(SU(3,p^2), p)};// Add more?
		



B2, PhiB:= PCGroup(B1);

SST:= [SubInvMap(PhiB,B1,x`subgroup):x in Subgroups(B2:OrderDividing:=#T)];
 
SS:= [x:x in SST|IsSCentric(T,x)];

EE:=[T];
GrpEssentialAutos:=AssociativeArray(SS);
GrpEssentialAutos[T]:=AutomiserGens(B1,T);

for x in SS do 

if x eq T then continue; end if;

NTx:= Normalizer(T,x);
Q:=NTx/x;
QC:= IsQuaternionOrCyclic(Q);
    if QC eq false then 
            if #Q le p^6 then TesT:= false;
               for SP in Testers do
                 if IsIsomorphic(Q,SP) then TesT := true; break; end if;
                end for;
             if TesT eq false  then continue; end if;
        end if;
    end if;  
    Nx:= Normalizer(G,x);
    
    if Index(Nx,NTx) mod p eq 0 then continue; end if;  
    kk := sub<G|Centralizer(G,x), x>;

    if QC eq false and #Factorisation(ZZ!(#Nx/#kk)) le 2 then continue; end if;


   ISPE:=IsStronglypEmbeddedMod(Nx,kk,p);
    if ISPE then 
    EE:= Append(EE,x);
 
    GrpEssentialAutos[x]:= AutomiserGens(Nx,x);
    
 
    end if; 
end for; 
 
 
 

B2, PhiB:= PCGroup(B1);
EEPC:=[SubMap(PhiB,B2,x):x in EE];
EEAA:=[];
for i := 1 to #EEPC do
Es:= EEPC[i];
MakeAutos(Es);
EEAA[i]:= sub<Es`autogrp|[Inverse(PhiB)*gamma*PhiB:gamma in GrpEssentialAutos[EE[i]]]>; 
end for;

F:=CreateFusionSystem(EEAA);
 
F`grpsystem:=G;
F`grppgrp:=T;
F`saturated := true;
return F;
end intrinsic
//////////////////////////////////////////////////////////////////////
intrinsic  GroupFusionSystem(G::Grp, p::RngIntElt)->FusionSystem
{Makes the group fusion system on the Sylow p-subgroup}
T:= Sylow(G,p);F:= GroupFusionSystem(G,T);F`saturated:= true;

return F;
end intrinsic;
//////////////////////////////////////////////////////////////////////////
intrinsic IsWeaklyClosed(F::FusionSystem, P::Grp)->Bool
{Returns true if the subgroups is weakly closed}
WC:= false;
if IsNormal(F`borel,P) eq false then return false; end if;
if #ConjugacyClass(F,P) eq 1 then WC := true; end if;
return WC;
end intrinsic;
/////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
intrinsic IsStronglyClosed(F::FusionSystem, P::Grp)->Bool
{Returns true if the subgroups is strongly closed}
SC:= true;
if IsWeaklyClosed(F,P) eq false then return false; end if;

X:= {x`subgroup: x in Subgroups(P)};
for x in X do 
    xC:= ConjugacyClass(F,x);  
    for w in xC do
        if w subset P eq false then return false; end if; 
    end for;
end for; 
return SC;
end intrinsic;

/////////////////////////////////////
intrinsic IsGroupFusionSystem(F::FusionSystem)->Bool
{Return true if F is constructed from G }
if assigned(F`grpsystem) then return true; end if;
return false; 
end intrinsic;
/////////////////////////////
//////////////////////////////////
////Given an automiser sequence Autos with Borel B, and a Fusion system F
////Check is the automniser sequence of F and the fusion system of EssA are
///Isomorphic 
/////////////////////////////////////
intrinsic IsIsomorphic(B::Grp,Autos::SeqEnum,F2::FusionSystem)->Bool{}


a, theta := IsIsomorphic(B,F2`borel);
if a eq false then return false; end if; 
p:= F2`prime;
bounds:=[8,8,6,6];
primes:=[2,3,4,4];



/////////////////////////////////////////////////////////
///F2 has its automiser sequence in the canonical order.
///We should reorder Autos.
//////////////////////////////////////////////////////////
if p in primes and #F2`group le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
  
  
  
F1essentials := [Group(x):x in Autos];

if p in primes and #F2`group le p^bounds[Index(primes,p)]  then
RO1:=[IdentifyGroup( x):x in F1essentials];
RO2:=[IdentifyGroup(x):x in F2`essentials];
else
RO1:=[#x:x in F1essentials];
RO2:=[#x:x in F2`essentials];
end if; 
if  RO1 ne RO2 then return false; end if; 

//The automisers should have the same orders.
RO1:=[#x :x in Autos];
RO2:=[#x :x in F2`essentialautos];
Sort(~RO1);
Sort(~RO2);
if RO1 ne RO2 then return false; end if; 
 
 
 
    


AutBp:= (F2`essentials[1])`autoperm;

alpha:= (F2`essentials[1])`autopermmap;

NAutBp:= Normalizer(AutBp, SubMap(alpha,AutBp,F2`essentialautos[1]));
NAutB:= SubInvMap(alpha,F2`essentials[1]`autogrp,NAutBp); 
TNB:= Transversal(NAutBp,SubMap(alpha,AutBp,F2`essentialautos[1]));
Trans:=[Inverse(alpha)(xxx):xxx in TNB];
 

//transfer to same group. And make an image for each transversal map.
ImEssentials:=[];

for mu in Trans do
ImEssentials:= Append(ImEssentials,[mu(theta(x)):x in F1essentials] ); 
end for;

ImAutEssentials:= AssociativeArray({1..#Trans});

for zz in [1..#ImEssentials] do 
    ImEssentialsCalc:= ImEssentials[zz]; 
    mu:= Trans[zz];// theta. mu maps x in F1essentials to a subgroup of F2`group
       //Initialize the automorphism group of the images
        for ii in [1..#ImEssentialsCalc] do  
            x:= ImEssentialsCalc[ii];
            MakeAutos(x); 
        end for;     
    ImAutEssentialsCalc:=[];
    for x in ImEssentialsCalc do 
            AutF1:= Autos[Index(ImEssentialsCalc,x)];
            XX:=[Inverse(mu)*Inverse(theta)*gen*theta*mu:gen in Generators(AutF1)];
            ImAutEssentialsCalc:=Append(ImAutEssentialsCalc, sub<x`autogrp| XX>); 
    end for;
     
ImAutEssentials[zz]:=ImAutEssentialsCalc;
 
end for;

for XXct in [1..#ImEssentials] do 
    XX:=ImEssentials[XXct];
    for ii in [1..#XX] do 
    e:= XX[ii]; 
     if e in F2`subgroups then continue; end if;
        jj:= IdentifyBClass(F2,e);
        P:= F2`subgroups[jj];
        MakeAutos(P);
        a,b :=IsConjugate(F2`borel,e,P);
        bb:= ConjtoHom(e,P,b); 
        bbb:= ConjtoHom(P,e,b^-1);    
        XX[ii]:=P;
        ImAutEssentials[XXct][ii]:= sub<P`autogrp|
            {hom<P->P|gg:-> bb(gen(bbb(gg)))>:
            gen in  Generators(ImAutEssentials[XXct][ii])}>;
end for;
end for;
            
 
        jj:= {1..#F2`essentials};
        for ii in [1..#ImAutEssentials] do 
            kk:= jj;
            for mm in ImAutEssentials[ii] do
                for aa in jj do
                    if mm eq F2`essentialautos[aa] then kk:= kk diff {aa}; end if;
                end for; 
             if #kk eq 0 then return true;end if;
            end for;
        end for; 
 return false;
end intrinsic;
////////////////////////////////////////////
intrinsic NormalizerTower(S::Grp,E::Grp)->SeqEnum
{Creates a normalizer tower}

NT:= [Normalizer(S,E)];
while NT[#NT] ne S do Append(~NT,Normalizer(S,NT[#NT])); end while;
return NT;
end intrinsic; 

 ///////////////////////////////////////////
 intrinsic FusionTower(F::FusionSystem,P::GrpPC, AFP::GrpAuto)-> SeqEnum
 {Determines the fusion systems on normalizer tower when possible}
 S:= F`group;
 B:= F`borel; 
 NBP:=Normalizer(B,P);
 L:=Random(Complements(NBP,Normalizer(S,P)));
 AFPS:=AutYX(NBP,P);
 
 
 require  {x in AFP: x in  Generators(AFPS)} eq {true}: "the system F isn't saturated"; 
 AFPS:= sub<AFP|Generators(AFPS)>;
 AFPp:= SubMap(P`autopermmap,P`autoperm, AFP);
 AFPSp:= SubMap(P`autopermmap,P`autoperm, AFPS);
 ASp:= SubMap(P`autopermmap,P`autoperm,AutYX(Normalizer(S,P), P));
 

 InnSp:=SubMap(S`autopermmap,S`autoperm,Inn(S));
 
if not AFPSp eq Normalizer(AFPp,ASp) then print "construction not applicable"; return []; end if;

Tower :=  NormalizerTower(S,P);
FF:=[];

for T in Tower do BT:= sub<B|L,T>; Autos:=[AutYX(BT,T),AFP]; 
Append(~FF,CreateFusionSystem(Autos));
end for;
return FF;
 
end intrinsic;
 
 ////////////////////////////////////////////
////////////////////////////////////////////////////////////
intrinsic SaveFS(FileName::MonStgElt, F::FusionSystem)
{Saves fusion system to FileName so that it can be loaded}

S:=Group(F`essentialautos[1]);
PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
PrintFile (FileName, "Autos:=[];\n");
for k := 1 to #F`essentials do
    A:=F`essentialautos[k];
    E:= Group(A);
    R := [S!w:w in PCGenerators(E)];
    PrintFile(FileName,"E:=sub<S|");
    PrintFile(FileName,R);
    PrintFile(FileName,">;\n");
    E:=sub<S|R>;
    PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
    PrintFile(FileName,"A:=sub<AE|>;\n");
    for ii := 1 to #Generators(A) do
        alpha:=A.ii;
        PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
        gens:=SetToSequence(PCGenerators(E));
        for i in [1..#gens-1] do
            x:= E!gens[i];
            PrintFile(FileName,"<");
            PrintFile(FileName,x);
            PrintFile(FileName,",");
            PrintFile(FileName,E!alpha(x));
            PrintFile(FileName,">");
            PrintFile(FileName,",");
        end for;
        x:= gens[#gens];
        PrintFile(FileName,"<");
        PrintFile(FileName,x);
        PrintFile(FileName,",");
        PrintFile(FileName,E!alpha(x));
        PrintFile(FileName,">");
        PrintFile(FileName," ]>>;\n");
    end for;
PrintFile(FileName,"Autos[");
PrintFile(FileName,k);
PrintFile(FileName,"]:=A;\n");
end for;
PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
PrintFile(FileName,"FS;");
end intrinsic;



intrinsic SaveFS(FileName::MonStgElt, FF::SeqEnum)
{Saves sequence of fusion systems to FileName so that it can be loaded}


PrintFile(FileName,"FFS:=[];");

for F in FF do      
    S:=Group(F`essentialautos[1]);
    PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
    PrintFile (FileName, "Autos:=[];\n");
    for k := 1 to #F`essentials do
        A:=F`essentialautos[k];
        E:= Group(A);
        R := [S!w:w in PCGenerators(E)];
        PrintFile(FileName,"E:=sub<S|");
        PrintFile(FileName,R);
        PrintFile(FileName,">;\n");
        E:=sub<S|R>;
        PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
        PrintFile(FileName,"A:=sub<AE|>;\n");
        for ii := 1 to #Generators(A) do
            alpha:=A.ii;
            PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
            gens:=SetToSequence(PCGenerators(E));
            for i in [1..#gens-1] do
                x:= E!gens[i];
                PrintFile(FileName,"<");
                PrintFile(FileName,x);
                PrintFile(FileName,",");
                PrintFile(FileName,E!alpha(x));
                PrintFile(FileName,">");
                PrintFile(FileName,",");
            end for;
            x:= gens[#gens];
            PrintFile(FileName,"<");
            PrintFile(FileName,x);
            PrintFile(FileName,",");
            PrintFile(FileName,E!alpha(x));
            PrintFile(FileName,">");
            PrintFile(FileName," ]>>;\n");
        end for;
    PrintFile(FileName,"Autos[");
    PrintFile(FileName,k);
    PrintFile(FileName,"]:=A;\n");
    end for;
    PrintFile(FileName,"FS:=CreateFusionSystem(Autos);");
    PrintFile(FileName, "FFS:=Append(FFS,FS);");
end for;
PrintFile(FileName,"FFS;");
end intrinsic;

//////////////////////////////////////////////////////////
intrinsic CharSbgrpTest(ProtoEssentials::SeqEnum,S::Grp)->Bool                     
{Checks if theres a characteristic subgroups of all essentials 
and S contained in the intersection of protop essentials}

Q:= S; 
for xx in ProtoEssentials do 
	Q := Q meet xx; 
end for;

QQ:= NormalSubgroups(Q);
SProtoEssentials := Append(ProtoEssentials,S);
for w in QQ do 
	ww:= w`subgroup;
	if #ww ne 1 then 
		for xx in SProtoEssentials do 
		wwChar := IsCharacteristic (xx,ww);
			if wwChar eq false then  continue w; end if; 
		end for;
		if wwChar eq true  then return true;end if;
	end if; 
end for;
return false;
end intrinsic; 

 
 
 /////////////////////////////////////

intrinsic AllMaximalSubgroups(G)-> SeqEnum
{Creates all maximal subgroups of G}
 
M:= MaximalSubgroups(G);
AM:=[];
for x in M do 
	m:= x`subgroup;Index(G,m); t:= Transversal(G,m); 
	for y in t do Append(~AM,m^y); end for;
end for; 
return AM;

end intrinsic;




intrinsic MaximalOverGroups(G::Grp,H::Grp, p::RngIntElt)-> SeqEnum
{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}
 
 
M:= MaximalSubgroups(G);
AM:=[];
for x in M do 
	m:= x`subgroup; Cm:= ConjugacyClasses(Sylow(m,p)); J:= Sylow(H,p);
	
	if #m mod #H eq 0 then  W:={xx[3]:xx in Cm|IsConjugate(G,xx[3],J.1)}; if #W ne 0 then
		t:= Transversal(G,m); 
		for y in t do Append(~AM,m^y); end for;
	end if; end if;
end for; 





AMH:=[];
for x in AM do
	if H subset x then Append(~AMH, x);end if;
end for;
return Set(AMH);
end intrinsic;


intrinsic OverGroups(G::Grp,H::Grp)-> SeqEnum
{Creates overgrps of H in G up to G conjugacy which have H as a sylow p-sugroup}

AllOvers:={};
ONew:={G};
while ONew ne {H} do 
	AllOvers := AllOvers join ONew;#AllOvers;
	Overs := ONew; 
	ONew:={H};
		for x in Overs do
			ONew:= ONew join MaximalOverGroups(x,H); 
		end for;
end while;

return AllOvers;


end intrinsic;


intrinsic OverGroupsSylowEmbedded(G::Grp,H::Grp,INN::Grp,p::RngIntElt)-> SeqEnum
{Creates overgrps of H in G which have H as a sylow p-subgroup and such that they are generated by conjugates of H. To get the full list we will use the Fratinni argument}

require IsPrime(p):"p is not a prime";
require #H mod p eq 0 :"H does not have order divisible by p";
require IsNormal(G,INN) :"Inn not normal in G";

J:= Sylow(H,p);
JJ, mp:= J/INN;

require IsCyclic(JJ) :"H/Inn does not have cyclic sylow subgroups";

NGH:= Normalizer(G,J);


JJJ:= Generators(JJ); JJJ:= {j: j in JJJ|Order(j) eq #JJ};
J1:= Inverse(mp)(Rep(JJJ)); // So J1 generates J mod INN and it is an element



AllOvers:={};
ONew:={SubnormalClosure(G,H)};
while ONew ne {H} do 
    Overs := ONew diff AllOvers;  j:= 0;
	AllOvers := AllOvers join ONew; 
	ONew:={H};
		for x in Overs do  j:= j+1;  
			  y:=SubnormalClosure(x,H); 
			M:= MaximalSubgroups(y);
			AM:=[];
			for mm in M do 
				m:= mm`subgroup; 
				if INN subset m then 
				    if #m mod #H eq 0 then  
					Cm:= ConjugacyClasses(m);
					for cc in Cm do  
						aa, bb := IsConjugate(y,cc[3],J1); 
						
						if aa then  mbb:= m^bb;  
							for am in AM do 
                                aaa, bbb := IsConjugate(NGH,am,mbb); 
                                if aaa then continue cc;  end if;
							end for;  
							AM:= AM cat [SubnormalClosure(mbb,H)]; 
						end if; 
					end for;//cc		 
				    end if;//#m mod #H
				end if;//II subset m
			end for; //mm in M

		 
	AM:= Seqset(AM);
			 
		for xx in AM do 
			xxin := false;
			for yy in ONew do 
				if xx subset yy then 
					xxin := true; 
					continue xx; 
				end if; 
			end for;
			if xxin eq false then
				ONew := ONew join {xx}; end if;
		end for; 

		ONew1 :={Rep(ONew)};
			for on in ONew do OUT := true;
				for on1 in ONew1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
			if OUT then ONew1 := ONew1 join{on}; end if;
			end for;
ONew :=ONew1;
 
		end for;
end while;
 




AllOvers1:= {Rep(AllOvers)};


for on in AllOvers do OUT := true;
				for on1 in AllOvers1 do  if IsConjugate(NGH,on,on1) then OUT := false; continue on; end if; end for;
			if OUT then AllOvers1 := AllOvers1 join{on}; end if;
			end for;
AllOvers:= AllOvers1;

AAM:=[x: x in AllOvers|Index(x,H) mod p ne 0];
return AAM;
end intrinsic;



////////////////////////////////////////////////////////////////////////

intrinsic AutomorphismGroup(F::FusionSystem,P::Grp)-> GrpAuto
{Calculates the automorphism group of P}
SS:= F`subgroups;
Essentials:= F`essentials;
B:= F`borel;
S:= F`group;
if assigned(F`fusiongraph) eq false then 
          F`fusiongraph, F`maps:= FusionGraph(F); 
      end if; 
Gamma:= F`fusiongraph;
Theta := F`maps; 

V:= Vertices(Gamma);
IP:= V!Index(SS,P);

ComponentP:= Setseq(IdentifyFOrbit(F,P));
 
for x in ComponentP do MakeAutos(SS[Index(x)]); end for;

AutP:= P`autogrp;

AP := sub<AutP|>;


//First we make all the maps between members of ComponentP
 


for v in ComponentP do 
Theta[[Index(v),Index(v)]]:= Identity(SS[Index(v)]`autogrp); 
end for;

for i in[1.. #ComponentP] do
    for j in [i+1.. #ComponentP] do
        ii:= ComponentP[i];jj:= ComponentP[j]; 
        Geo:=Geodesic(ii,jj); 
        gg := Identity(SS[Index(ii)]`autogrp); 
        for iii:= 1 to #Geo-1 do 
            gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii+1])]];  
        end for;
         Theta[[Index(ii),Index(jj)]]:= gg;
        gg := Identity(SS[Index(jj)]`autogrp); 
        
        for iii:= #Geo to 2 by -1 do 
            gg:= gg*Theta[[Index(Geo[iii]),Index(Geo[iii-1])]];  
        end for;
        Theta[[Index(jj),Index(ii)]]:= gg; 
    end for;
end for;

TranB:= AssociativeArray(ComponentP);
for x in ComponentP do
    TranB[x]:= Transversal(B,Normalizer(B,SS[Index(x)])); 
end for;



CP:= CartesianProduct(Essentials,ComponentP);
PsinEs:=AssociativeArray(CP);
for E in Essentials do 
    if E eq S then continue; end if;
    for xx in  ComponentP do 
            PsinEs[<E,xx>]:= [b:b in TranB[xx]|SS[Index(xx)]^b subset E]; 
    end for;
end for;


 





//Now we start building AP=Aut_F(P)

AP:= AutYX(Normalizer(B,P),P);

for ii in ComponentP do
    R := SS[Index(ii)]; 
    if R eq P then continue; end if; 
    AR := AutYX(Normalizer(B,R),R);
        AP := sub<AutP|AP,{Theta[[Index(IP),Index(ii)]]*gg*Theta[[Index(ii),Index(IP)]]: gg in Generators(AR) }>; 
end for;
 
for ii in ComponentP do R := SS[Index(ii)]; 
    if R eq P then continue ii; end if; 
    for jj in ComponentP do T := SS[Index(jj)]; 
    if T in {P, R} then continue jj; end if; 
    AP := sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*Theta[[Index(ii),Index(jj)]]*Theta[[Index(jj),Index(IP)]]>;
    end for;
end for;
    
 
  
 
    for ee in [2..#Essentials ] do 
         E:= Essentials[ee]; 
         AE:= F`essentialautos[ee];
Done:={};
         for ii in ComponentP do 
            R:= SS[Index(ii)];
            for b in PsinEs[<E,ii>] do
                Rb:= R^b; if Rb in Done then continue b; end if;
                cb:=ConjtoHom(R,Rb,b);
                cb1:=ConjtoHom(Rb,R,b^-1);
                OO,AFRb, TT:= AutOrbit(E,Rb,AE); 
                gamma:= {Theta[[Index(IP),Index(ii)]]*cb*gg*cb1*Theta[[Index(ii),Index(IP)]]:gg in Generators(AFRb)};
                AP:=sub<AutP|AP,gamma>;
                for tt in TT do
                    Rbtt:= SubMap(tt,S,Rb);
                    for jj in ComponentP do a,d:=IsConjugate(B,Rbtt,SS[Index(jj)]); 
                    if a then kk:= jj;break; end if; 
                    end for; //jj
                    cd1:= ConjtoHom(SS[Index(kk)], Rbtt, d^-1);
                    ThetaRbtoRbtt:= cb1*Theta[[Index(ii),Index(kk)]]*cd1;
                AP:=sub<AutP|AP, Theta[[Index(IP),Index(ii)]]*cb*ThetaRbtoRbtt*tt^-1*cb1*Theta[[Index(ii),Index(IP)]]>;
                end for; //tt
                Done := Done join Seqset(OO);
            end for; //b
        end for; //ii
    end for;//ee
    return AP;
end intrinsic;
  
/////////////////////////////////////////////////////////////////////
intrinsic SubgroupsAutClasses(S::PCGrp)-> SeqEnum
{Calculates centric subgroups of S up to Aut(S) conjugacy}
SS:= [x`subgroup:x in Subgroups(S)|IsSCentric(S,x`subgroup)];
A,beta:= Holomorph(S);
SSb :=[SubMap(beta,A,x):x in SS];
TT:=[];K:={1};k:=1;
for i := 1 to #SSb do T:= SSb[i]; if #K ne 0 then k:= Min(K); end if; K:={};
    for j := k to i-1 do print i,j;
        if #T ne #SSb[j] then continue j; else K:= K join {j};end if;
        if IsConjugate(A, T,SSb[j]) eq true then continue i; end if;
    end for;
    Append(~TT,SS[i]);
end for;
return TT;
end intrinsic;
//////////////////////////////////////////
intrinsic SemiDirectProduct(V::ModGrp:Perm:= false)-> Grp
{Constructs the semidirect product of a module and the module for the group}
G:= Group(V);
F:= Field(V);
T:= TrivialModule(G,F);
W:= DirectSum(T,V);
G1:= MatrixGroup(W);
n:= Dimension(W);
H:= GL(n,F);
K:= sub<H|G1>;

for k in [1..n-1] do J:= Identity(H);J:= Eltseq(J);
J[k*n+1]:= Identity(F);J:= H!J;  
K:= sub<H|J,K>;

end for;if Perm then K:= CosetImage(K,G1); end if;
return K;
end intrinsic;
//////////////////////////////////////////
intrinsic AutFCore(Es::SeqEnum,AutE::SeqEnum)->Grp,GrpAuto
{calculates F core and action on it}
F:= Es[1];
for i := 2 to #Es do  F:= F meet Es[i];end for; 
 Fn:= sub<F|>;
 while F ne Fn do
 Fn:= F;
 for i := 1 to #Es do
    A:= AutOrbit(Es[i],F,AutE[i]);
    for x in A do F := F meet x; end for;
 end for;
 end while;
MakeAutos(F); K:= Inn(F); 
    for i := 1 to #Es do  K:=  sub<F`autogrp|K,Generators(AutE[i])>; end for;
    return F,K;
end intrinsic;
 
////////////////////////////////////////////////
intrinsic AllProtoEssentials(S::Grp:OpTriv:=false, pPerfect:= false,Printing:= false)-> SeqEnum
{Makes all protosessentials up to automorphisms of S the parameters ask for  O_p(F)=1 and O^p(\F)= \F}

 
 
ZZ:= Integers(); //Integer Ring
 
p:= FactoredOrder(S)[1][1]; 
 nn:= Valuation(#S,p);



//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);
Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 


///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups 
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need 
///to calculate in some circumstances.
/////////////////////////////////////

ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then 
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then 
        Append(~T,C); end if; 
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
     cat 
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
      TT:=[];
     for x in T do 
            Nx:=Normalizer(S,x);
        	A:=AutYX(Nx,x);
        	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        	Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
        	Append(~TT,x);
     end for;         
       ProtoEssentials:=   TT;
end if; 
        
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do   
	if x eq S then continue x; end if; 
	if IsCyclic(x) then  continue x; end if;
	Nx:=Normalizer(S,x);
	A:=AutYX(Nx,x);
	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
	Inner:= Inn(x);
	Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
	P:= Index(Ap,Innerp);
	Frat:=FrattiniSubgroup(x);
	FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
 	if FQTest eq false then continue x; end if; 
	SylTest, QC:=IsStronglypSylow(Ap/Innerp);print "here";
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
        //Here we check that the Sylow $p$-subgroup is compatible with this.
	if SylTest eq false   then continue x; end if; 
	if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
	ProtoEssentials:= Append(ProtoEssentials,x); 
end for;
end if;
////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
if  #ProtoEssentials eq 0 then return []; end if; 


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
  
if OpTriv then if CharSbgrpTest(ProtoEssentials,S) eq true then return []; end if; end if;
   
 
    ///This test takes Q as the intersection of all the members of the members 
    //of ProtoEssentials and checks if any of them are characteristic in all members 
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F. 
   
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials 
///////and check that they have strongly p-embedded subgroups.
///////////////////



for i in [1..#ProtoEssentialAutClasses] do 
	P:= ProtoEssentialAutClasses[i];
	MakeAutos(P);
	AutP:=P`autogrp;
	mapP:= P`autopermmap;
	AutPp:= P`autoperm;
	InnP:=Inn(P);
	InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
	AutSP:=AutYX(Normalizer(S,P),P );
	AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;	
	Q:= AutSPp/InnPp;

	M:=SubnormalClosure(AutPp,AutSPp);
	
	Candidates :=[];
    	pVal:=Valuation(#AutPp,p);
    	NormVal:=Valuation(#AutSPp,p);
       
        QC:=IsQuaternionOrCyclic(Q); 
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	    end if;//QC
                
    	if QC and IsCyclic(Q)  then
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p);
        end if;  
	
	    if QC and not IsAbelian(Q) then  
		Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
              	AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	end if;
        
	P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

       	for GG in AutPCandidates do
		if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)| 
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
            	for GGs in NGGsubs do 
            		Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>); 
		        end for; 
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if Printing then 
	print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  
end if;
if Printing then 
	for x in ProtoEssentialAutClasses do  
		print "the protoessential aut class  representaive have ", #x`autF, "potential automorphism groups"; 
	 end for; 
end if;

 

return ProtoEssentialAutClasses;
end intrinsic;

/////////
/////////////////////////////////////
///////////////////////////////////////


intrinsic Blackburn(p::RngIntElt,n::RngIntElt,alpha::RngIntElt,beta::RngIntElt,gamma::RngIntElt,delta::RngIntElt)->Grp
{constructs Blackburns metaabelian maximal class group of order p^n}
require IsPrime(p) : "the first element must be a prime"; 
require n eq 6:"this is only implemented for n=6";


        S<s, s1,s2,s3,s4,s5> := Group<s, s1,s2,s3,s4,s5|
        (s1,s)*s2^(-1),
        (s2,s)*s3^(-1),
        (s3,s)*s4^(-1),
        (s4,s)*s5^(-1),
         (s,s5), 
        
        //(32) from Blackburn.
        (s1,s2)*s5^(-beta)*s4^(-alpha),//(33)
        (s1,s3)*s5^(-alpha),//(34)
        (s1,s4),//(35)
        (s1,s5),//(35)

        s^p*s5^(-delta),//(36)


        s1^p*s2^Binomial(p,2)*s3^Binomial(p,3)*s4^Binomial(p,4)*s5^Binomial(p,5)*s5^(-gamma),//(37)
        //s2^p,s3^p,s4^p, 
        
       s2^p*s3^Binomial(p,2)*s4^Binomial(p,3)*s5^Binomial(p,4),

        s3^p*s4^Binomial(p,2)*s5^Binomial(p,3),

        s4^p*s5^Binomial(p,2),

        s5^p>;S:= PCGroup(S);
 return S;
 
 end intrinsic;


/////////////////////////
/////We need to be able to detect when two homomorphisms are equal: 
//////////////////////

intrinsic homeq(x::Map,y::Map)->Bool{checks if two maps are equal}
 X:=Domain(x); X1:= Image(x);
Y:=Domain(y); Y1 := Image(y);
    if X ne Y  or X1 ne Y1 then return false; end if;
gens:=Generators(X);
     for gg in gens do
        if x(gg) ne y(gg) then return false; end if;
     end for;
 return true;
 end intrinsic;
 
 //////////
 intrinsic IsQuaternionOrCyclic(G::Grp)->Bool
 {Is a quaternion or a cyclic group}
 if #G eq 1 then return true;end if; 
 p:= FactoredOrder(G)[1][1];
 C:= ConjugacyClasses(G);
 if # {x: x in C|x[1] eq p} eq p-1 then return true; end if;
 return false;
 end intrinsic;
 
 ////////////////////////////////////////////////////////////////////////////////
///Functions which creates $O^pi(G)$.
///for various pi
///////////////////////////////////////////////////////////////////////
intrinsic piResidual(G::Grp, pi::SeqEnum)-> Grp
{Determine O^\pi(G)}
JJ:= PrimeFactors(#G);
Resid:=sub<G|>;
for x in JJ do 	
	if x in pi then continue x; end if;
	P:= Sylow(G,x);
	N:= NormalClosure(G,P);
	Resid:= sub<G|Resid,N>;
end for;
return Resid;

end intrinsic;
//////////////////////////////////////////////////////////////

intrinsic pResidual(G::Grp, p::RngIntElt)-> Grp
{Determine O^p(G)}
R:=piResidual(G,[p]);
return R;
end intrinsic;

intrinsic piprimeResidual(G::Grp, pi :: SeqEnum)-> Grp
{Determine O^p(G)}
 JJ:= PrimeFactors(#G);
pistar:= {w: w in JJ| (w in pi) eq false};
R:=piResidual(G,pistar);
return R;
end intrinsic;

intrinsic pprimeResidual(G::Grp, p::RngIntElt)-> Grp
{Determine O^p(G)}
P:= Sylow(G,p);
return NormalClosure(G,P);
end intrinsic;
/////////////////////////////
//// Is the p-group Maximal class
/////////////////////////////

intrinsic IsMaximalClass(G::Grp)-> Bool
{Check if G is maximal class}
f:= FactoredOrder(G);
require #f eq 1 : "the group  is not a p-group"; 
 n:= NilpotencyClass(G);

return n eq (f[1][2]-1);
end intrinsic;
/////////////////////////////
//// Does the p-group have an abelian subgroup of index p
/////////////////////////////

intrinsic  MaximalAbelian(G::Grp)-> Bool
{Check if G gas a maximal abelian subgroup}
f:= FactoredOrder(G);
require #f eq 1:"the group  is not a p-group"; 
M:= MaximalSubgroups(G);
for x in M do 
    y:= x`subgroup; 
    if IsAbelian(y) then return true; end if; 
end for;

return  false;
end intrinsic;

///////////////////////////////////////////////
/////sub normal closure of a subgroup
////////////////////////////////////////////////
intrinsic SubnormalClosure(G::Grp,T::Grp)-> Grp
{Determines the subnormal closure of $T$ in G}

SNew:= NormalClosure(G,T);
SN:= G;
while SN ne SNew do
SN:= SNew;
SNew:= NormalClosure(SN,T);
end while;
return SN;
end intrinsic;



////////////////////////////
////// IdentifyGroup3to7(S::GRP)->
////// 
////////////////////////


intrinsic IdentifyGroup3to7(S::Grp)->RngIntElt
{Identifies Group of Order 3^7}
require #S eq 3^7:"Group doesn't have order 3^7";
for i in [1..NumberOfSmallGroups(3^7)] do
        if IsIsomorphic(S,SmallGroup(3^7,i) ) then return i; end if;
end for; 
end intrinsic;

//////////////////////////////////////////////////////////
intrinsic AllFusionSystems(S::Grp:SaveEach:=false,Printing:=false,OutFSOrders:=[],OpTriv:=true,pPerfect:= true)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F}
 
 
 
FNumber:=0; //This is to help when saving fusion systems
ZZ:= Integers(); //Integer Ring
FF:=[]; //We will put the possible systems in here  

p:= FactoredOrder(S)[1][1]; 
 nn:= Valuation(#S,p);



//Use that we know fusion systems with an abelian subgroup

if IsAbelian(S) then return FF; end if;

///Lemma~7.1 shows that $S:Z(S) \gt p^2 or |S|\le p^3

if Index(S,Centre(S)) le p^2 and #S ge p^4  then return FF; end if; 
 
 

//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);

//We use Cor 6.2 from ANTONIO Diaz, ADAM GLESSER, NADIA MAZZA, AND SEJONG PARK
if p ge 5 and #FactoredOrder(S`autogrp) eq 1 then return []; end if; 


Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 
 
 
 
///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups 
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need 
///to calculate in some circumstances.
/////////////////////////////////////

ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then 
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then 
        Append(~T,C); end if; 
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ] 
     cat 
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ]; 
      TT:=[];
     for x in T do 
            Nx:=Normalizer(S,x);
        	A:=AutYX(Nx,x);
        	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
        	Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
        	Append(~TT,x);
     end for;         
       ProtoEssentials:=   TT;
end if; 

        
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do   
	if x eq S then continue x; end if; 
	if IsCyclic(x) then  continue x; end if;
	Nx:=Normalizer(S,x);
	A:=AutYX(Nx,x);
	Ap:= SubMap(x`autopermmap,x`autoperm ,A);
	Inner:= Inn(x);
	Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
	P:= Index(Ap,Innerp);
	Frat:=FrattiniSubgroup(x);
	FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
 	if FQTest eq false then continue x; end if; 
	SylTest, QC:=IsStronglypSylow(Ap/Innerp);
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded. 
        //Here we check that the Sylow $p$-subgroup is compatible with this.
	if SylTest eq false   then continue x; end if; 
	if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if; 
	ProtoEssentials:= Append(ProtoEssentials,x); 
end for;
end if;
////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
 


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
  
if OpTriv and  CharSbgrpTest(ProtoEssentials,S)   then return FF; end if;  
   
 
    ///This test takes Q as the intersection of all the members of the members 
    //of ProtoEssentials and checks if any of them are characteristic in all members 
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>; 
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F. 
     
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials 
///////and check that they have strongly p-embedded subgroups.
///////////////////


for i in [1..#ProtoEssentialAutClasses] do 
	P:= ProtoEssentialAutClasses[i];
	MakeAutos(P);
	AutP:=P`autogrp;
	mapP:= P`autopermmap;
	AutPp:= P`autoperm;
	InnP:=Inn(P);
	InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
	AutSP:=AutYX(Normalizer(S,P),P );
	AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;	
	Q:= AutSPp/InnPp;

	M:=SubnormalClosure(AutPp,AutSPp);
	
	Candidates :=[];
    	pVal:=Valuation(#AutPp,p);
    	NormVal:=Valuation(#AutSPp,p);
      
        QC:=IsQuaternionOrCyclic(Q); 
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	    end if;//QC
                
    	if QC and IsCyclic(Q)  then  
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p);
        end if;  
	
	    if QC and not IsAbelian(Q) then  
		Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
              	AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
		APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
		for kk in [1..#AutPCandidates] do  
            		GG:= AutPCandidates[kk];
           		Sylow:=SylowSubgroup(GG,p);
            		a,b:=IsConjugate(AutPp,Sylow,AutSPp);
			if a then Append(~APC,GG^b); end if; 
		end for;
		AutPCandidates:= APC;
	end if;
        
	P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

       	for GG in AutPCandidates do
		if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)| 
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
            	for GGs in NGGsubs do 
            		Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>); 
		        end for; 
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if #ProtoEssentialAutClasses eq 0 then return []; end if;
 
 

if OpTriv and CharSbgrpTest(ProtoEssentialAutClasses,S)   then return []; end if;  
if Printing then print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  end if;


//We calculate the possible Borel subgroups and S pairs.


pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
BorelsandS:=[];
if m ne 1  then
    if IsSoluble(AutSp) then 
        PAut, tt:= PCGroup(AutSp); 
        H:=HallSubgroup(PAut,-p); 
        K:=[];
        if OutFSOrders eq [] then 
         K:= [wx`subgroup:wx in Subgroups(H)];
         else  
        for x in OutFSOrders do K:= K cat [wx`subgroup:wx in 
        Subgroups(H:OrderEqual:=x)]; 
        end for; 
        end if;
        BCand:=[]; 
       
    for k:= 1 to #K do  
        K1:= K[k]; 
            for K2 in BCand do 
            if IsConjugate(PAut,K1,K2) then   continue k;   end if;
            end for; 
        Append(~BCand,K1); 
    end for;
    BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
 else
  if OutFSOrders eq [] then OutFSOrders:= [1..m]; end if;
    SubsAutS:= Subgroups(AutSp:OrderDividing:=m);   
    BCand:=  [sub<AutSp|x`subgroup,InnSp>: x in SubsAutS|Index(x`subgroup,InnSp meet x`subgroup) mod p ne 0];
    BCand:= [Random(Complements(AA,InnSp)):AA in BCand];
    BCand:=[ AA:AA in BCand| #AA in OutFSOrders]; 
 end if;
 

 
    for CC in BCand do
    if not IsSoluble(CC) then print "Execution failed: The Borel group is not soluble ";   return []; end if;
        f:=hom<CC->AutS|g:->Inverse(map) (g)>;
        C:= SubMap(f,AutS,CC);  
        if #C ne 1 then B,phiB:= Holomorph(GrpFP,S, sub<AutS|C>); else B,phiB:= Holomorph(S, sub<AutS|C>);  end if; 
       // B,phiB:= Holomorph(S, sub<AutS|C>);  
        T:= phiB(S);  
       
         B, theta := PCGroup(B); T:= theta(T); ///This will not work if B is not soluble.
        BB:=[B,T];
        
        a, alpha:= IsIsomorphic(S,T); //phiB*theta does not work when Holomorph is calculcated with FP group
          for x in ProtoEssentialAutClasses do Append(~BB,SubMap(alpha,T,x)); end for;
        for ii in [3..#BB] do 
        xx:= BB[ii];
        yy:= ProtoEssentialAutClasses[ii-2];
        MakeAutos(xx);
          
            WW:=[];
            for jj in   [1..#yy`autF] do 
		    Wx:= yy`autF[jj]; 
		    WGens :=[
		    Inverse(alpha)*gamma*alpha: gamma in  Generators(Wx)];
		    WW[jj]:=sub<xx`autogrp|WGens>; 
            end for;
            xx`autF:= WW;
        end for;
     Append(~BorelsandS,BB);
end for;
else
 T, theta := PCGroup(S);
    BB:=[T,T];
    for x in ProtoEssentialAutClasses do Append(~BB,SubMap( theta,T,x)); end for;
        for ii in [3..#BB] do 
            xx:= BB[ii];yy:= ProtoEssentialAutClasses[ii-2]; MakeAutos(xx);WW:=[];
            for jj in   [1..#yy`autF] do 
                WGens:=[]; Wx:= yy`autF[jj]; 
                    for gamma in Generators(Wx) do  
                        Append(~WGens,Inverse( theta)*gamma* theta); 
                    end for;
                WW[jj]:=sub<xx`autogrp|WGens>; 
            end for;
            xx`autF:= WW; 
        end for;
     Append(~BorelsandS,BB);
end if;








if Printing then print "This group has ", #BorelsandS, " Borel groups";end if;

count:=0;
for Bor in BorelsandS do
   

    count := count+1;  
print "**********************************************";
print " Borel", count, "of", #BorelsandS, FactoredOrder(Bor[1]);
print "**********************************************";
 
  B:= Bor[1];    
S:= Bor[2];  

//We use the fact that if $B=S$ and p ge 5 then $O^p(\F)<\F$.
if p ge 5 and B eq S then continue; end if;
MakeAutos(S);
    
    	Bbar, bar:= B/Centre(S);
	subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
	subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
	SS:= [x:x in subsBS|IsSCentric(S,x)]; 
    AutFS:=AutYX(B,S);
    InnS:=Inn(S);
    AutS:= S`autogrp;
    alpha:= S`autopermmap;
    AutSp:= S`autoperm; 
    InnSp:= SubMap(alpha,AutSp, InnS);
    AutBS:= AutYX(B,S);
    AutBp:= SubMap(alpha,AutSp, AutBS);
 
    NAutBp:= Normalizer(AutSp,AutBp);
    NAutB:= SubInvMap(alpha,AutS,NAutBp);
    ProtoEssentialAutClasses:=[Bor[j]:j in [3 ..#Bor]];

//We explode the autclasses to get all protoessentials and ajoin their potential autogrps.
ProtoEssentials:=[];
for x in ProtoEssentialAutClasses do
    Xx, Stx, Rx := AutOrbit(S,x,S`autogrp); 
    PNew := [];
    for y in SS do
        if y in Xx then 
            MakeAutos(y); 
            Append(~ProtoEssentials,y); 
            Append(~PNew,y);
        end if; 
    end for;
    
    if #PNew ne 0 then 
        for j := 1 to #PNew do
            y:= PNew[j];
            y`autF:=[];
            for AP in x`autF do
                        y`autF := Append(y`autF, sub<y`autogrp|[Inverse(Rx[Index(Xx,y)])*gamma*Rx[Index(Xx,y)]: gamma in Generators(AP)]>);
            end for;
        end for; 
    end if;
end for;//x


if OpTriv then 
//The next test uses Lemma 4.10 to show that P1 and P2 are not both essential.
// If P1 is essential, then P1' ne 1 and is normalized by Aut_\F(S) and Aut_F(E_1). This gives O_p(F) ne 1.
	if #ProtoEssentials eq 2 and p ge 5 and #S lt p^(p+3) then 
	    P1:= ProtoEssentials[1]; 
	    P2:= ProtoEssentials[2]; 
	    	if #P1 le #P2 then PP:= P2; P2:= P1; P2:= PP; end if; 
	    NSP2:= Normalizer(S,P2);  
	    PC:= Core(S,P2);
	 	if IsConjugate(B,P1,NSP2) and Index(NSP2,P2) eq p and Index(S,NSP2) eq p and 
	    Index(P2,PC) eq p and IsCharacteristic(NSP2,PC) and IsNormal(B,DerivedSubgroup(P1)) then 		ProtoEssentials:=[P2];
	    	end if;
	end if;    
end if; //OpTriv
    








Candidates:= AssociativeArray(ProtoEssentials);

for x in ProtoEssentials do Candidates[x]:= x`autF; end for; 

if pPerfect then 
//The next check is a preliminary focal subgroup check using that we know the Borel  subgroup. 
//This often gets rid of the case when $B=S$
	SB:= CommutatorSubgroup(S,B);
	S1:= sub<S|SB,ProtoEssentials>;
	if S1 ne S then   continue Bor; end if;
end if;

if OpTriv   and #ProtoEssentials eq 1   and IsNormal(B,ProtoEssentials[1]) then continue Bor; end if; 
  


if Printing then print "There are", #ProtoEssentials, "proto-essential subgroups before the extension test.\nThey have orders", 
 Explode([#ProtoEssentials[i]: i in [1..#ProtoEssentials]]);end if;

//We now make all the candidates for Aut_F(E) given our class representatives in 
//E`autF. This means that we check if the automorphisms in $Aut(N_B(E),E)$ restrict to members of $\Aut_\F(E)$.

FirstTime := true;
ProtoEssentialsT:= ProtoEssentials;
ProtoEssentialsTT:= [];

while #ProtoEssentialsT ne #ProtoEssentialsTT  do
    ProtoEssentialsTT:= ProtoEssentialsT; 
    
	if #ProtoEssentialsT eq 0 then
    if Printing then	print #ProtoEssentialsT, "proto-essentials which pass the  strongly p-embedded and extension test";
    end if;	continue Bor; 
    end if;
 
    Candidates1:=AssociativeArray(ProtoEssentialsT);
    
    Done :={};
    for i in [1..#ProtoEssentialsT] do
        P:=ProtoEssentialsT[i];
        if P in Done then continue i; end if;
        MakeAutos(P);
         if Printing then print "About to Apply AutFPC"; end if;
        Candidates1[P]:=AutFPCandidates(B,S,P,ProtoEssentialsT,Candidates,FirstTime:Printing:= Printing); 
        //next we transfer the automorphisms to everything in the AutOrbit.
         if Printing then print "AutFPC complete"; end if;
        OrbP, SSt, Repp:= AutOrbit(S,P, NAutB);
        if Printing then print "the set Repp has", #Repp, "Members"; end if;
        for nn in [2..#Repp] do
            P1:=OrbP[nn];
            MakeAutos(P1);
            beta:= Repp[nn]; 
            Candidates1[P1]:= [];
            for AP in Candidates1[P] do
                Append(~Candidates1[OrbP[nn]],
                        sub<P1`autogrp|[Inverse(beta)*theta*beta: theta in Generators(AP)]>);
            end for;
        end for;
    Done := Done join Seqset(OrbP);
     if Printing then print "the set Done", #Done, "Members"; end if;
    end for; //i
  ProtoEssentialsT:=[ProtoEssentialsT[Index(ProtoEssentialsT,x)]:x in ProtoEssentialsT| #Candidates1[x] ne 0];
Candidates:= Candidates1; FirstTime:=false;
end while;     

 

ProtoEssentials:= ProtoEssentialsT;
if #ProtoEssentials eq 0 then continue Bor; end if;

if Printing then print  #ProtoEssentialsT, 
"proto-essentials which pass both the  strongly p-embedded 
and extension test";end if;


D:= Subsets({1..#ProtoEssentials});



////////////////////////////////
///We look at the orbits of $N_Aut(S)(Aut_\F(S))$ on D. 
///As we will consider all possible automisers of members of protoessentials
///It suffices to look at $N_Aut(S)(Aut_\F(S))$ orbits and this will give us all 
///automorphism classes of fusion systems
//////////////////////////

NN:= NAutBp;
for Pr in ProtoEssentials do 
a, NNN:= AutOrbit(S,Pr,NAutB);
NN := NN meet SubMap(alpha,AutSp,NNN);
end for;

   // NN:= sub<NAutBp|NN>; 
TNB:= Transversal(NAutBp,NN);
TransAutSB:=[Inverse(alpha)(xxx):xxx in TNB];

DD:= D;
DNew:={};
while #DD ne 0 do 
    x:= Rep(DD); 
    DNew:= DNew join{x}; 
    DDD:={x};
   
    for beta in TransAutSB do 
	xnew := {beta(ProtoEssentials[w]):w in x};
   	L:={};
	for ll in xnew do
		for Proto in ProtoEssentials do 
		aa, bb:= IsConjugate(B, ll, Proto);
			if aa then L:= L join{Index(ProtoEssentials,Proto)}; end if;
		end for;
	end for;
  

DDD:= DDD join {L};   
   end for; //beta
DD := DD diff DDD;
end while; 

 
D:= DNew;
 
D:= Setseq(D);
 D1:= [#x:x in D];
ParallelSort(~D1,~D);
D:=Reverse(D);

 // this tests if there is a conjugate of essential x  which is $B$ conjugate to a subgroup of essential $y$ which using all posibilities for Aut_\F(y) is we can see $x$ is not fully Normalized
 Forbiddenpairs :={};
 
 for x in ProtoEssentials do 
    NSx := Normalizer(S,x);
    for y in ProtoEssentials do
         
        if exists(tt){ tt: tt in Conjugates(B,x)|tt subset y} then 
            if forall{w:w in Candidates[y]| exists{cc:cc in AutOrbit(y,tt,w)|#Normaliser(S,cc) gt #NSx}} 
            then Forbiddenpairs:= Forbiddenpairs join{{x,y}}; 
            end if;
        end if;
    end for;
end for;
if Printing then print "The number of forbidden pairs of essential subgroups is ", #Forbiddenpairs;end if;
/////


////////////////Main Search starts here. 



for ss in [1..#D] do//This is the main loop considering all subsets of ProtoEssentials
    EssSup:= D[ss];//This set specifies which essential subgroups we select from ProtoEssentials.

    if #EssSup eq 0 then continue ss;
    end if; //the fusion system must have rank at least one
    ssSequence:=SetToSequence(EssSup);
    
 	Essentials:=[ProtoEssentials[i]: i in EssSup];
   if OpTriv then if #EssSup eq 1 and IsNormal(B,Essentials[1]) then continue ss; end if;end if;
    if exists{w: w in Forbiddenpairs| w subset Essentials} then continue ss; end if;

  max:= Max({#e: e in Essentials});
Candidates1:=Candidates; 
Maxes:= {e:e in Essentials|#e eq max};

 
FLAG := false;
for P in Essentials do 
    if p*#P ge max and IsNormal(S,P) eq false  then  
         PB:= Conjugates(B,P); 
         Tst:={};  
         for M in Maxes do 
            Tst := Tst join {x subset M:x in PB};
         end for;
          if Tst eq {false} or P in Maxes then 
            MakeAutos(P);
            AutP:=P`autogrp;
            mapP:= P`autopermmap;
            AutPp:= P`autoperm;
            InnP:=AutYX(P,P);
            InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
            AutSP:=AutYX(Normalizer(S,P),P );
            AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;
            AutBP:=AutYX(Normalizer(B,P),P );
            AutBPp:=sub<P`autoperm|{mapP(g): g in Generators(AutBP)}>;
            for II in [1.. #Candidates[P]] do AP:= Candidates[P][II]; 
                APp:=SubMap(P`autopermmap, P `autoperm,AP);
                 if Normalizer(APp,AutSPp) ne AutBPp then 
                     Candidates1[P][II]:=sub<AP|>; FLAG:= true; 
                 end if;
            end for;//II
        end if;// #Tst;
    end if;
end for;            
        
        
if FLAG then 
CandidatesNew:=AssociativeArray(ProtoEssentials); 
for x in ProtoEssentials do
CandidatesNew[x]:=[];
for y in Candidates1[x] do if #y ne 1 then Append(~CandidatesNew[x],y); end if; end for;
end for;
else CandidatesNew:=Candidates;
end if;
  

 
////This next test makes sure that if we have essential subgroups x<y then 
////|N_S(x)|\ge  N_S(x\alpha) for all alpha in $\Aut_F(y)$
Candidates1 := CandidatesNew;

FLAG := false;
for x in Essentials do 
    for y in Essentials do 
    if x subset y and x ne y then 
        for II in [1..#CandidatesNew[y]] do AutFy:= CandidatesNew[y][II];
            xOrb:= AutOrbit(y,x,AutFy);
            for w in xOrb do  
                if #Normalizer(S,w) gt #Normalizer(S,x) then     
                    Candidates1[y][II]:=sub<AutFy|>; FLAG:= true;
                end if;
            end for;
        end for;
    end if; 
    end for;
end for; 


if FLAG then 
CandidatesNew:=AssociativeArray(ProtoEssentials); 
for x in ProtoEssentials do
    CandidatesNew[x]:=[]; 
    for y in Candidates1[x] do 
        if #y ne 1 then Append(~CandidatesNew[x],y); 
        end if; 
    end for;
end for;
end if;
  
  
  
 
CandidatesNewp:= AssociativeArray(ProtoEssentials);


for xP in ProtoEssentials do
    CandidatesNewp[xP]:=[ SubMap(xP`autopermmap, xP`autoperm,CandidatesNew[xP][kk]): kk in [1..#CandidatesNew[xP]]];
    
end for;

 
 

 
 
  Cart:=[];
  for e in EssSup do
    Cart:=Append(Cart,[1..#CandidatesNew[ProtoEssentials[e]]]);
  end for;

 CPCart:=CartesianProduct(Cart);

     // now run through all possible fusion systems on the chosen set of essential subgoups
 
if Printing then print "Checking", #CPCart, "automizer sequences with", #EssSup, 
"essentials of orders:", Explode([#ProtoEssentials[i]: i in EssSup]);end if;


/////////////////////////////////////////////////////////////////////////////////
/////for each subset we make a cartesian product, where each element gives a
///// potential fusion system
///// The set EssSup, Essentials support, defines the essentials subgroups of the fusion system
/////  For each EssSup we run through the various assignments of automisers to the essentials
//////For example if EssSup<--> [S,E_1,dots, E_k] then we run through all the possibilities for
//// Aut_F(E_1) ...
/////////////////////////////////////////////////////////////////////////////////
 

//First we make the subgroup of Aut(S) which normalizes all the essential subgroups and B.

NAutBQp:=NAutBp;

for Q in Essentials do
Orb, NN:=AutOrbit(S, Q,NAutB);
NAutBQp:= NAutBQp meet SubMap(S`autopermmap, S`autoperm,NN);
end for;


T2:= Transversal(NAutBp,NAutBQp);
L:= Set(Essentials);
T3:= {y: y in T2|{Inverse(alpha)(y)(x): x in L} eq  L};
NAutBQp:= sub<NAutBp|NAutBQp,T3>;


NAutBQ:= SubInvMap( alpha, S`autogrp,NAutBQp); 


CPCart:= Set(CPCart); 

cpc:= #CPCart; 
 
//This defines an action of CPCart 
  alpha:=S`autopermmap;
  function Act(x)
     tup:= x[1];ff:= x[1];
     theta := x[2];
     for i in [1..#Essentials] do 
            	ee:= Essentials[i];  
            	jj:= Index(Essentials,SubMap(theta,S,ee));
            	eee:= Essentials[jj];  
                J:= sub<eee`autogrp|[Inverse(theta)*gen*theta:gen in 
                Generators(CandidatesNew[ee][ff[i]])]>; 
                Jp:= SubMap(eee`autopermmap, eee`autoperm,J);
                kk:= Index(CandidatesNewp[eee],Jp); 
                jjj:= Index(Essentials,eee);
                tup[jjj]:=kk;
            end for;
            return tup;
 end function;

  
  
  
  
  
  while #CPCart ne 0 do  
   Bob:= false; 
   possFSys:=Rep(CPCart); 
 
  //POrb is a partial orbit.  This speeds things up as finding large  full orbits seems to be more time consuming. This routine will with high probability find small orbits anyway. The strange choice to perform it twice is to get a balance between speed and getting enough elements of the orbit.

     POrb:= {possFSys, Act(<possFSys,NAutBQ.1>)  };
     for i:= 1 to 2 do 
      POrb2:= POrb;
     	for x in Generators(NAutBQ) do;
     		for ff in POrb2 do
	     		z:= Act(<ff,x>);
	     		if not z in CPCart then Bob := true; break i; end if;
	     		POrb:= POrb join {z};
	     	end for;
	end for;
     end for;
     if Bob then CPCart:= CPCart diff POrb;continue; end if;//continues while
   Bob:= false;
     POrb2:= POrb;
     for j := 1 to 3 do 
     	x:= Random(Generators(NAutBQ));
     	POrb2:= POrb;
     	for ff in POrb2 do
	     		z:= Act(<ff,x>);
	     		if not z in CPCart then Bob := true; break j; end if;
	     		POrb:= POrb join {z};
	     	end for;
     end for;
  
 
 	CPCart:= CPCart diff POrb; //removes the partial orbit
   if Bob then continue; end if;//continues while
   Bob:= false;
   
    AutF:=AssociativeArray(ProtoEssentials); //this is the fusion system we will make
    AutF[S]:=AutFS; // this was fixed at the start it is Aut_B(S)
    ////We now populate AutF with the appropriate candidate automisers
    for k in [1..#possFSys] do
       AutF[ProtoEssentials[ssSequence[k]]]:=CandidatesNew[ProtoEssentials[ssSequence[k]]][possFSys[k]];
    end for;
    Autos:=[AutF[S]]; ///Autos is the automiser sequence.
           
	for e in Essentials do 
        	Autos:= Append(Autos,AutF[e]);    
   	end for;
     
 	if Printing then print "Remains to do",#CPCart, "of",cpc; end if; 
     
	if pPerfect and not FocalSubgroupTest(B,S, Essentials,AutF) then  continue; //while
 	end if;  
 	
 	
  	if OpTriv and  not FCoreTest(S,Essentials,AutF) then  continue; end if;   


  //    This next test checks that if P is normal in S that its "obvious" automiser has $\Aut_S(P) as a Sylow.
    
    for xx in SS do 
        if IsNormal(S,xx) eq false or #xx eq 1 then continue xx; end if;
        Exx:={w:w in Essentials|xx subset w};
        if #Exx ne 0 then 
            MakeAutos(xx);
            Axx:= sub<xx`autogrp|AutYX(Normalizer(B,xx),xx)>;
            for yy in Exx do
                Oxx,xxStab := AutOrbit(yy, xx,AutF[yy]);
                Axx:= sub<xx`autogrp|Axx,Generators(xxStab)>;
            end for;
            if ZZ!(#Axx/#AutYX(S,xx)) mod p eq 0 then Bob:= true; break xx; end if;
        end if;
    end for;
   if Bob then continue; end if;//continues while
   Bob:= false;
     
//    

  
    N:= {1..#Essentials}; 
	NN:= Subsets(N);
	NN:= Setseq(NN);
	RO:=[#x:x in NN];
    	ParallelSort(~RO,~NN);
	NN:= Reverse(NN);
        
		for sNN in NN do
                    if #sNN eq 0 or #sNN eq #Essentials then continue sNN; end if;
                    Es:=[Essentials[ww]: ww in sNN];Append(~Es,S);
                    AutE:= [Autos[ww+1]:ww in sNN];Append(~AutE,AutF[S]);
                    Cor,AutCor:= AutFCore(Es,AutE);
                    n:=ZZ!(#AutCor/#AutYX(S,Cor));
                    if n mod p eq 0 then  Bob:=true; break sNN; end if;///Tests if Aut_S(x) a sylow p of AutCore.
        end for;//sNN
           
           if Bob then continue; end if;//continues while
            Bob:=false;
           
           
           
//We now create the fusion system. We don't use the standard call as we have already done most of the calculation



bounds:=[8,6,6,6];
primes:=[2,3,4,4]; 
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
if p in primes and #S le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
    
F:= New(FusionSystem);
F`prime:=p;
F`group:= S;    
F`borel:= B;
F`subgroups:=[x:x in subsBS];
F`essentialautos:= Autos;
F`essentials := [];
for x in Autos do
Append(~F`essentials, Group(x)); end for;
F`AutF:= AssociativeArray(F`subgroups);
for x in F`essentials do 
F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
end for; 
       //We only need  to check saturation on centrics. So we make a partial fusion graph.       
if assigned(F`fusiongraph) eq false then  
    F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
end if;
F`classes:= ConnectedComponents(F`fusiongraph);
        
        if assigned(F`centrics) eq false then 
            F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if; 

                  for G in FF do 
                          if IsIsomorphic(F,G) then delete F; Bob:= true; break; end if; 
                  end for;
                  if Bob then continue; end if;Bob:=false;
            IS:= IsSaturated(F);
            if Printing then print "Executed saturation test: result is",IS; end if; 
                if assigned(F`essentials) and IS then  
                	if SaveEach then FNumber:= FNumber +1; 
                        SaveAsGo(FNumber, F);   
                	       else    
                        Append(~FF,F);
                    end if; 
                end if; 
 delete F; 
   end while; //  possFSys
 
end for;//ss
end for;//Bor

GG:= FF;
if #FF le 1 then return FF; end if; 
FF:= [FF[1]];
 for i in [2.. #GG] do
 	x:= GG[i];  
 	for y in FF do 
 		if IsIsomorphic(x,y) then continue i; end if;
 	end for; 
 	Append(~FF,x); 
 end for; 
 
return FF;
end intrinsic;

///////////////////////////////////////

intrinsic AllFusionSystems(ordergrp::RngIntElt)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n}
 range:=[1..NumberOfSmallGroups(ordergrp)];
SatFS:=[];
for count in range do 
print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
S:= SmallGroup(ordergrp,count);
if IsAbelian(S) eq false then
SatFS := SatFS cat AllFusionSystems(S:SaveEach:=false);
end if;
end for;
return SatFS;
end intrinsic;

///////////////////////////////////////////////////////////

intrinsic AllFusionSystems(ordergrp::RngIntElt, range::SeqEnum:Printing:=false)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F on all groups of order n from small groups library in the asserted range}
  
SatFS:=[];
for count in range do 
print "testing group ", count, "of ", NumberOfSmallGroups(ordergrp);
S:= SmallGroup(ordergrp,count);
if IsAbelian(S) eq false then
AA:=AllFusionSystems(S:Printing:=Printing,SaveEach:=false);
if #AA ne 0 then 
 FileName:="F" cat IntegerToString(#S) cat "-" cat IntegerToString(count)cat "-" cat IntegerToString(range[1]) cat "-" cat IntegerToString(range[#range]);
              SaveFS(FileName, AA);
              end if; 

 
end if;
end for;
return SatFS;
end intrinsic;

intrinsic SaveAsGo(  count::RngIntElt, F::FusionSystem)
{}
grp:= #F`group;
bor:= #F`borel;
FileName:="F" cat IntegerToString(grp) cat "-" cat IntegerToString(bor) cat "-" 
cat IntegerToString(count);
              SaveFS(FileName, [F]);
end intrinsic;



intrinsic Centralizer(G::Grp,A::Grp,B:Grp)->Grp
{Return the centralizer in G of the the quotient A/B}
require IsNormal(G,B): "B is not normalized by G"; 
K:= Normalizer(G,A);
 Q,a:= K/B;
C:= Centralizer(Q,a(A));
C:= SubInvMap(a,K,C); 
return C;
end intrinsic;





intrinsic AbelianPearls(S::Grp:fusion:=true)->SeqEnum
{Returns all fusion systems with just abelian Pearls provide anu such exists}
S:= PCGroup(S);

require IsMaximalClass(S): "S does not have maximal class";
p:= FactoredOrder(S)[1][1];
ZZ:= Integers();
 
L:= LowerCentralSeries(S);
gamma1:= Centralizer(S,L[2],L[4]);
Z2:= L[#L-2]; 
SS:= Subgroups(S:OrderEqual:=p^2);
PotPearls:= {x`subgroup: x in SS| Normalizer(S,x`subgroup) eq sub<S|Z2,x`subgroup> and Exponent(x`subgroup) eq p};
if #PotPearls eq 0 then return[]; end if;  
MakeAutos(S);
AutS:= S`autogrp;
AutSp:= S`autoperm;
map:= S`autopermmap;
pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
BorelsandS:=[];
if m lt p-1 then return[]; end if;
        
PAut, tt:= PCGroup(AutSp); 
H:=HallSubgroup(PAut,-p); 
K:= [wx`subgroup:wx in Subgroups(H)|wx`order ge p-1];


BCand:=[];
for k:= 1 to #K do  
	K1:= K[k]; 
    	for K2 in BCand do 
    		if IsConjugate(PAut,K1,K2) then   continue k;   end if;
    	end for; 
	Append(~BCand,K1); 
end for;
BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
Z:= Centre(S);
MakeAutos(Z);
 
BCand:= [k: k in BCand|#sub<Z`autogrp|Generators(  SubInvMap(map, AutS,k))> eq p-1];





for CC in BCand do
         f:=hom<CC->AutS|g:->Inverse(map) (g)>;
          C:= SubMap(f,AutS,CC);  
          B,phiB:=Holomorph(GrpFP,S, sub<AutS|C>); 
        T:= phiB(S);  
         B, theta := PCGroup(B); T:= theta(T);
        BB:=[B,T];
         for x in PotPearls do Append(~BB,SubMap(phiB*theta,T,x)); end for;
     Append(~BorelsandS,BB);
end for;
        
        AllPearls:=[];
        
for Bor in  BorelsandS  do
	B:= Bor[1];
	S:= Bor[2];
	L:= LowerCentralSeries(S);
	PotPearls:=[Bor[j]: j in [3..#Bor]];   

	PotPearls2:=[];

		for PP in PotPearls do 
			for PP1 in PotPearls2 do
				if IsConjugate(B,PP,PP1) then continue PP; end if;
			end for;
			Append(~PotPearls2, PP); 
		end for;
	PotPearls:= PotPearls2;  

	Pearls:=[B];
	for PP in  PotPearls do 
		N:= Normalizer(B,PP); 
		
		MakeAutos(PP);
		AutN:= AutYX(N,PP);
		SL2:= SubInvMap(PP`autopermmap, PP`autogrp,DerivedSubgroup(PP`autoperm));
		AutSPP:= AutYX(Normalizer(S,PP),PP);
		D:=sub<PP`autogrp|AutN,SL2>;
		 if #Normalizer(SubMap(PP`autopermmap, PP`autoperm,D), SubMap(PP`autopermmap, PP`autoperm,AutSPP)) eq #AutN then
		 Append(~Pearls,PP); end if;
	
	end for;
	if #Pearls ne 1 then Append(~AllPearls,Pearls); end if;
end for;


FusSys:=[];
AutomiserSequences:=[];
for FS in AllPearls do
B:= FS[1]; 
S:= pCore(B,p);
A1:= AutYX(B,S);
AutSeq:=[A1];
	for ii in [2..#FS] do
		Pearl:= FS[ii];
		N:= Normalizer(FS[1],Pearl);
		A2:= AutYX(N,Pearl);
		SL2:= SubInvMap(Pearl`autopermmap, 	Pearl`autogrp,DerivedSubgroup(Pearl`autoperm));
		Append(~AutSeq, sub<Pearl`autogrp| SL2,A2>);
	end for;
	Autos:= AutSeq;

Append(~AutomiserSequences,AutSeq);
if fusion then
	
	Bbar, bar:= B/Centre(S);
	subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
	subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
	 
bounds:=[8,6,6,6];
primes:=[2,3,4,4]; 
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
 
 
if p in primes and #S le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos); 
end if; 
    
F:= New(FusionSystem);
F`prime:=p;
F`group:= S;    
F`borel:= B;
F`subgroups:=[x:x in subsBS];
F`essentialautos:= Autos;
F`essentials := [];
for x in Autos do
Append(~F`essentials, Group(x)); end for;
F`AutF:= AssociativeArray(F`subgroups);
for x in F`essentials do 
F`AutF[x] := F`essentialautos[Index(F`essentials,x)]; 
end for; 
	
	
	
	
Append(~FusSys,F);
end if;
end for;
if fusion then
if #FusSys eq 0 then return []; end if;
FusSys1:=[FusSys[1]];
for x in FusSys do 
	for y in FusSys1 do
		if IsIsomorphic(x,y) then continue x; end if;
	end for;
	Append(~FusSys1,x); 
end for;

return FusSys;
else return AutomiserSequences;
end if;


end intrinsic;
         
