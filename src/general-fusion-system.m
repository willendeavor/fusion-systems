// General functions dealing with fusion systems


intrinsic 'eq'(F1::FusionSystem, F2::FusionSystem) -> Bool
    {checks if two fusion systems are equal}
    E1:= F1`essentialautos;
    E2:= F2`essentialautos;
    Eq := true;
    if #E1 ne #E2 then return false; end if; 
    for x in E1 do
        for y in E2 do
            if x eq y then continue x; end if;
        end for;
        Eq:= false;
        if Eq eq false then break x; end if;
    end for;
    
    return Eq;
end intrinsic;




intrinsic NPhi(S::Grp, Q::Grp,phi::Map)->Grp
     {for a subgroup and homomorphism from the second 
     term to the first create the control subgroup}
     P:=Image(phi);
     phii:=iso<Q->P|x:->phi(x)>;
     TSP:= Transversal(Normalizer(S,P),Centralizer(S,P));
     Nphi:= Q;
     T:= Transversal(Normalizer(S,Q),Q);
        for t in T do
                if t in Nphi then continue; end if;
            alpha:=ConjtoHom(Q,Q,t);
            beta :=iso<Q->P|x:-> phii(alpha(x))>;
                for g in TSP do
                    gg:= ConjtoHom(P,P,g);
                    betag :=iso<Q->P|x:-> gg(phii(x))>;
                        if homeq(beta,betag) then   
                            Nphi:= sub<S|Nphi,t>; break; 
                        end if;
                end for;
        end for;
    return Nphi;
end intrinsic;




