rec< FusionRecord |
  p := 2,
  S_presentation := "GrpPC : S of order 128 = 2^7
PC-Relations:
S.4^2 = S.7, 
S.5^2 = S.7, 
S.2^S.1 = S.2 * S.4, 
S.3^S.1 = S.3 * S.4 * S.5, 
S.4^S.1 = S.4 * S.7, 
S.4^S.2 = S.4 * S.7, 
S.4^S.3 = S.4 * S.6 * S.7, 
S.5^S.2 = S.5 * S.6 * S.7, 
S.5^S.3 = S.5 * S.6, 
S.5^S.4 = S.5 * S.7, 
S.6^S.1 = S.6 * S.7",
  S_order := 128,
  S_name := "C4.D4.C2^2",
  S_small_group_id := <128, 934>,
  EssentialData := [
    rec< EssentialRecord |
      E_presentation := "GrpPC : E of order 128 = 2^7
PC-Relations:
E.4^2 = E.7, 
E.5^2 = E.7, 
E.2^E.1 = E.2 * E.4, 
E.3^E.1 = E.3 * E.4 * E.5, 
E.4^E.1 = E.4 * E.7, 
E.4^E.2 = E.4 * E.7, 
E.4^E.3 = E.4 * E.6 * E.7, 
E.5^E.2 = E.5 * E.6 * E.7, 
E.5^E.3 = E.5 * E.6, 
E.5^E.4 = E.5 * E.7, 
E.6^E.1 = E.6 * E.7",
      AutE_generators := [
        [ "E.1 * E.7", "E.2 * E.4 * E.6", "E.3 * E.4 * E.5 * E.6 * E.7", "E.4", "E.5", "E.6 * E.7", "E.7" ],
        [ "E.1 * E.7", "E.2 * E.4 * E.6 * E.7", "E.3 * E.4 * E.5 * E.7", "E.4", "E.5 * E.7", "E.6 * E.7", "E.7" ],
        [ "E.1 * E.4 * E.5 * E.7", "E.2", "E.3", "E.4 * E.6 * E.7", "E.5 * E.6", "E.6", "E.7" ],
        [ "E.1 * E.7", "E.2 * E.4 * E.7", "E.3 * E.4 * E.5 * E.6", "E.4 * E.7", "E.5 * E.7", "E.6 * E.7", "E.7" ],
        [ "E.1 * E.4 * E.7", "E.2", "E.3", "E.4 * E.7", "E.5 * E.6 * E.7", "E.6", "E.7" ],
        [ "E.1", "E.3", "E.2 * E.3", "E.4 * E.5", "E.4 * E.6", "E.6", "E.7" ],
        [ "E.1", "E.2", "E.3", "E.4", "E.5", "E.6", "E.7" ],
        [ "E.1", "E.2 * E.4", "E.3 * E.4 * E.5", "E.4 * E.7", "E.5", "E.6 * E.7", "E.7" ],
      ]
    >,
    rec< EssentialRecord |
      E_presentation := "GrpPC : E of order 64 = 2^6
PC-Relations:
E.1^2 = E.5, 
E.2^2 = E.5, 
E.2^E.1 = E.2 * E.5, 
E.3^E.1 = E.3 * E.6, 
E.3^E.2 = E.3 * E.5 * E.6, 
E.4^E.1 = E.4 * E.5, 
E.4^E.2 = E.4 * E.6",
      AutE_generators := [
        [ "E.1 * E.5", "E.2 * E.6", "E.3", "E.4", "E.5", "E.6" ],
        [ "E.2 * E.3", "E.1 * E.2 * E.4", "E.3", "E.4", "E.6", "E.5 * E.6" ],
        [ "E.1", "E.2 * E.5", "E.3 * E.6", "E.4 * E.5", "E.5", "E.6" ],
        [ "E.1 * E.6", "E.2 * E.5 * E.6", "E.3", "E.4", "E.5", "E.6" ],
        [ "E.1 * E.3 * E.4 * E.5 * E.6", "E.2 * E.3 * E.5 * E.6", "E.3 * E.4 * E.5", "E.3 * E.5 * E.6", "E.6", "E.5 * E.6" ],
        [ "E.1 * E.5", "E.2", "E.3 * E.5 * E.6", "E.4 * E.6", "E.5", "E.6" ],
        [ "E.1 * E.6", "E.2 * E.6", "E.1 * E.2 * E.3", "E.1 * E.4", "E.5", "E.5 * E.6" ],
      ]
    >,
    rec< EssentialRecord |
      E_presentation := "GrpPC : E of order 32 = 2^5
PC-Relations:
E.2^2 = E.5, 
E.3^2 = E.5, 
E.2^E.1 = E.2 * E.5, 
E.3^E.1 = E.3 * E.5, 
E.3^E.2 = E.3 * E.5, 
E.4^E.1 = E.4 * E.5",
      AutE_generators := [
        [ "E.1 * E.5", "E.2", "E.3", "E.4 * E.5", "E.5" ],
        [ "E.1", "E.2 * E.5", "E.3 * E.5", "E.4", "E.5" ],
        [ "E.1 * E.5", "E.2 * E.5", "E.3", "E.4 * E.5", "E.5" ],
        [ "E.4 * E.5", "E.1 * E.3 * E.4", "E.1 * E.2 * E.4", "E.1 * E.5", "E.5" ],
        [ "E.1 * E.2", "E.3 * E.4", "E.2 * E.3 * E.5", "E.4", "E.5" ],
        [ "E.1", "E.2 * E.5", "E.3 * E.5", "E.4 * E.5", "E.5" ],
      ]
    >,
    rec< EssentialRecord |
      E_presentation := "GrpPC : E of order 16 = 2^4
PC-Relations:
E.1^2 = Id(E), 
E.2^2 = Id(E), 
E.3^2 = Id(E), 
E.4^2 = Id(E)",
      AutE_generators := [
        [ "E.2", "E.1 * E.2", "E.3 * E.4", "E.3" ],
        [ "E.1 * E.2 * E.3", "E.1 * E.3 * E.4", "E.3", "E.4" ],
        [ "E.3", "E.3 * E.4", "E.2", "E.1" ],
      ]
    >,
  ],
>;
