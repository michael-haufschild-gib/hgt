import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected8

/-!
# Exact reflected compact source jet of order 10

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 10. -/
def oddCompactReflectedScalar10 (u a w : ℝ) : ℝ :=
  (((((((((-61723566501949440 : ℝ) +
    (288754505946270720 : ℝ)*a^1) +
    ((-525870894807097344 : ℝ)*a^1*w^2 +
    (159377994722672640 : ℝ)*a^1*w^4)) +
    (((-12960492371509248 : ℝ)*a^1*w^6 +
    (326412864847872 : ℝ)*a^1*w^8) +
    ((-2229025112064 : ℝ)*a^1*w^10 +
    ((-185915575102284288 : ℝ)*a^2 +
    (25809895921674240 : ℝ)*a^2*w^2)))) +
    ((((6222134220263424 : ℝ)*a^2*w^4 +
    (-527678159634432 : ℝ)*a^2*w^6) +
    ((7244331614208 : ℝ)*a^2*w^8 +
    (-7429861879155072 : ℝ)*a^3)) +
    (((-4308804857313792 : ℝ)*a^3*w^2 +
    (588741801919488 : ℝ)*a^3*w^4) +
    ((-15420326068224 : ℝ)*a^3*w^6 +
    ((34828517376 : ℝ)*a^3*w^8 +
    (-5574757070288304 : ℝ)*a^4))))) +
    (((((936553185399168 : ℝ)*a^4*w^2 +
    (-123000718482432 : ℝ)*a^4*w^4) +
    ((-132783722496 : ℝ)*a^4*w^6 +
    (44192420639676 : ℝ)*a^5)) +
    (((-64397690542656 : ℝ)*a^5*w^2 +
    (1577214851328 : ℝ)*a^5*w^4) +
    ((-2280934143180 : ℝ)*a^6 +
    ((214940249568 : ℝ)*a^6*w^2 +
    (128583744273 : ℝ)*a^7)))) +
    ((((-4008107864088576 : ℝ)*u^1*a^1*w^1 +
    (-170240602959544320 : ℝ)*u^1*a^1*w^3) +
    ((44673424725639168 : ℝ)*u^1*a^1*w^5 +
    (-2331978209427456 : ℝ)*u^1*a^1*w^7)) +
    (((27119805530112 : ℝ)*u^1*a^1*w^9 +
    (-23312812520964096 : ℝ)*u^1*a^2*w^1) +
    ((-27312354988425216 : ℝ)*u^1*a^2*w^3 +
    ((3951417196118016 : ℝ)*u^1*a^2*w^5 +
    (-98541485162496 : ℝ)*u^1*a^2*w^7)))))) +
    ((((((185752092672 : ℝ)*u^1*a^2*w^9 +
    (-13116628614905856 : ℝ)*u^1*a^3*w^1) +
    ((-3064930208520192 : ℝ)*u^1*a^3*w^3 +
    (172483878739968 : ℝ)*u^1*a^3*w^5)) +
    (((-1126122061824 : ℝ)*u^1*a^3*w^7 +
    (-2773912504700160 : ℝ)*u^1*a^4*w^1) +
    ((105511904999424 : ℝ)*u^1*a^4*w^3 +
    ((2614315585536 : ℝ)*u^1*a^4*w^5 +
    (4732035694560 : ℝ)*u^1*a^5*w^1)))) +
    ((((-41268165120 : ℝ)*u^1*a^5*w^3 +
    (614711427408 : ℝ)*u^1*a^6*w^1) +
    ((64798249783726080 : ℝ)*u^2 +
    (-143296696558725120 : ℝ)*u^2*a^1)) +
    (((150950285382721536 : ℝ)*u^2*a^1*w^2 +
    (-72556354030141440 : ℝ)*u^2*a^1*w^4) +
    ((7732615818313728 : ℝ)*u^2*a^1*w^6 +
    ((-168012767821824 : ℝ)*u^2*a^1*w^8 +
    (247669456896 : ℝ)*u^2*a^1*w^10))))) +
    (((((50182774905696768 : ℝ)*u^2*a^2 +
    (-14717233597095936 : ℝ)*u^2*a^2*w^2) +
    ((-9454863509139456 : ℝ)*u^2*a^2*w^4 +
    (526659425501184 : ℝ)*u^2*a^2*w^6)) +
    (((-3188744257536 : ℝ)*u^2*a^2*w^8 +
    (-14260267032556032 : ℝ)*u^2*a^3) +
    ((-145435453530624 : ℝ)*u^2*a^3*w^2 +
    ((-739142042462208 : ℝ)*u^2*a^3*w^4 +
    (10904228315136 : ℝ)*u^2*a^3*w^6)))) +
    ((((1050785266264848 : ℝ)*u^2*a^4 +
    (-399500916708096 : ℝ)*u^2*a^4*w^2) +
    ((-2101501946880 : ℝ)*u^2*a^4*w^4 +
    (3251419810920 : ℝ)*u^2*a^5)) +
    (((-1015072150464 : ℝ)*u^2*a^5*w^2 +
    (262242041508 : ℝ)*u^2*a^6) +
    ((22015268527693824 : ℝ)*u^3*a^1*w^1 +
    ((29560987910799360 : ℝ)*u^3*a^1*w^3 +
    (-11741838678687744 : ℝ)*u^3*a^1*w^5))))))) +
    (((((((569484957450240 : ℝ)*u^3*a^1*w^7 +
    (-3013311725568 : ℝ)*u^3*a^1*w^9) +
    ((-10151428616257536 : ℝ)*u^3*a^2*w^1 +
    (4189806788050944 : ℝ)*u^3*a^2*w^3)) +
    (((-1380005184208896 : ℝ)*u^3*a^2*w^5 +
    (20494647558144 : ℝ)*u^3*a^2*w^7) +
    ((-3391635366862848 : ℝ)*u^3*a^3*w^1 +
    ((520838628913152 : ℝ)*u^3*a^3*w^3 +
    (-46852256784384 : ℝ)*u^3*a^3*w^5)))) +
    ((((184701825427968 : ℝ)*u^3*a^4*w^1 +
    (-4380613208064 : ℝ)*u^3*a^4*w^3) +
    ((3279999684384 : ℝ)*u^3*a^5*w^1 +
    (-27954856723230720 : ℝ)*u^4)) +
    (((38394461497512960 : ℝ)*u^4*a^1 +
    (-10064466000691200 : ℝ)*u^4*a^1*w^2) +
    ((8108072395407360 : ℝ)*u^4*a^1*w^4 +
    ((-1047057457545216 : ℝ)*u^4*a^1*w^6 +
    (14638296858624 : ℝ)*u^4*a^1*w^8))))) +
    (((((-14481438521435136 : ℝ)*u^4*a^2 +
    (-927377561604096 : ℝ)*u^4*a^2*w^2) +
    ((1047949105213440 : ℝ)*u^4*a^2*w^4 +
    (-62639195996160 : ℝ)*u^4*a^2*w^6)) +
    (((2041202340078336 : ℝ)*u^4*a^3 +
    (-689087184588288 : ℝ)*u^4*a^3*w^2) +
    ((59734730105856 : ℝ)*u^4*a^3*w^4 +
    ((-27066613875984 : ℝ)*u^4*a^4 +
    (4936461128064 : ℝ)*u^4*a^4*w^2)))) +
    ((((15649585884 : ℝ)*u^4*a^5 +
    (-2753828127424512 : ℝ)*u^5*a^1*w^1) +
    ((-1189759352832 : ℝ)*u^5*a^1*w^3 +
    (868716099403776 : ℝ)*u^5*a^1*w^5)) +
    (((-34486251945984 : ℝ)*u^5*a^1*w^7 +
    (-1268750860222464 : ℝ)*u^5*a^2*w^1) +
    ((-453977039536128 : ℝ)*u^5*a^2*w^3 +
    ((72585568419840 : ℝ)*u^5*a^2*w^5 +
    (322316052996096 : ℝ)*u^5*a^3*w^1)))))) +
    ((((((-49297871738880 : ℝ)*u^5*a^3*w^3 +
    (3657456218880 : ℝ)*u^5*a^4*w^1) +
    ((6499279531560960 : ℝ)*u^6 +
    (-6101852532092928 : ℝ)*u^6*a^1)) +
    (((18128279126016 : ℝ)*u^6*a^1*w^2 +
    (-157483089395712 : ℝ)*u^6*a^1*w^4) +
    ((38653777870848 : ℝ)*u^6*a^1*w^6 +
    ((1541309590361088 : ℝ)*u^6*a^2 +
    (-259985285259264 : ℝ)*u^6*a^2*w^2)))) +
    ((((-36274787684352 : ℝ)*u^6*a^2*w^4 +
    (-73900534934016 : ℝ)*u^6*a^3) +
    ((27994542451200 : ℝ)*u^6*a^3*w^2 +
    (-43773184080 : ℝ)*u^6*a^4)) +
    (((-172082174312448 : ℝ)*u^7*a^1*w^1 +
    (-167401142747136 : ℝ)*u^7*a^1*w^3) +
    ((-12843457708032 : ℝ)*u^7*a^1*w^5 +
    ((175717665570816 : ℝ)*u^7*a^2*w^1 +
    (-4723436519424 : ℝ)*u^7*a^2*w^3))))) +
    (((((-2806088417280 : ℝ)*u^7*a^3*w^1 +
    (-885815220326400 : ℝ)*u^8) +
    ((532369904661504 : ℝ)*u^8*a^1 +
    (-21906044559360 : ℝ)*u^8*a^1*w^2)) +
    (((-7364654825472 : ℝ)*u^8*a^1*w^4 +
    (-63332780235264 : ℝ)*u^8*a^2) +
    ((15546737534976 : ℝ)*u^8*a^2*w^2 +
    ((716943934080 : ℝ)*u^8*a^3 +
    (31194216308736 : ℝ)*u^9*a^1*w^1)))) +
    ((((4012119392256 : ℝ)*u^9*a^1*w^3 +
    (-3615641763840 : ℝ)*u^9*a^2*w^1) +
    ((71119196467200 : ℝ)*u^10 +
    ((-23124169009152 : ℝ)*u^10*a^1 +
    (1914513629184 : ℝ)*u^10*a^1*w^2))) +
    (((923124718080 : ℝ)*u^10*a^2 +
    (-851607625728 : ℝ)*u^11*a^1*w^1) +
    ((-3125006438400 : ℝ)*u^12 +
    ((398529637376 : ℝ)*u^12*a^1 +
    (58118860800 : ℝ)*u^14))))))))) / (46438023168 : ℝ)

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar10_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 10) =
      (oddCompactReflectedScalar10 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 10) =
      ((((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar10 u a w +
    (-10 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar9 u a w) +
    ((45 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar8 u a w +
    ((-120 : ℝ)*oddCompactSourceScalar3 u a w*oddCompactSourceScalar7 u a w +
    (210 : ℝ)*oddCompactSourceScalar4 u a w*oddCompactSourceScalar6 u a w))) +
    (((-252 : ℝ)*oddCompactSourceScalar5 u a w*oddCompactSourceScalar5 u a w +
    ((210 : ℝ)*oddCompactSourceScalar6 u a w*oddCompactSourceScalar4 u a w +
    (-120 : ℝ)*oddCompactSourceScalar7 u a w*oddCompactSourceScalar3 u a w)) +
    ((45 : ℝ)*oddCompactSourceScalar8 u a w*oddCompactSourceScalar2 u a w +
    ((-10 : ℝ)*oddCompactSourceScalar9 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar10 u a w*oddCompactSourceScalar0 u a w)))) : ℝ) : ℂ) := by
    as_aux_lemma =>
      rw [eval_oddCompactReflectedJetPolynomial]
      norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
      simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq, oddCompactSourceScalar3_eq, oddCompactSourceScalar4_eq, oddCompactSourceScalar5_eq, oddCompactSourceScalar6_eq, oddCompactSourceScalar7_eq, oddCompactSourceScalar8_eq, oddCompactSourceScalar9_eq, oddCompactSourceScalar10_eq]
      push_cast
      ring
  rw [hf]
  apply congrArg Complex.ofReal
  as_aux_lemma =>
    unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactSourceScalar3 oddCompactSourceScalar4 oddCompactSourceScalar5 oddCompactSourceScalar6 oddCompactSourceScalar7 oddCompactSourceScalar8 oddCompactSourceScalar9 oddCompactSourceScalar10 oddCompactReflectedScalar10
    ring


end
end HTGeometry
