import GaloisForLFunctions.RHTower.WeilWorkPBAPJointJump

/-!
# Exact full-energy modulation increments

For a smooth complex profile supported in `[0,W]` and separated clusters
`L>2W`, paired modulation changes the literal Gamma-plus-both-poles energy by
an explicit positive kernel times the real autocorrelation and cosine defect.
Consequently nonnegative real autocorrelation makes zero a global modulation
minimum. Its value is the original cluster energy and can be negative; this
restricted-profile theorem does not prove full prime-blind positivity.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private def pairGamma (f : JointSmoothTest) (L T : ℝ) : ℝ :=
  testGamma (clusterDifference (cosineProfile f.1.1 T) L)+
    testGamma (clusterDifference (sineProfile f.1.1 T) L)

private theorem pairGamma_jump_integrable (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    IntegrableOn (fun y : ℝ => archJump (2*y)*
      (2*testMass f.1.1-jointPairRealCorr f L T y)) (Ioi 0) := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  have hi := (integrable_testGamma_jump_scaled gc.1).add
    (integrable_testGamma_jump_scaled gs.1)
  apply hi.congr
  filter_upwards with y
  have hm := joint_pair_testMass f hf hWL hL T
  have hc := jointPairRealCorr_eq f L T y
  change archJump (2*y)*(testMass gc.1.1-(EF.weilTest gc.1.1 gc.1.1 y).re)+
    archJump (2*y)*(testMass gs.1.1-(EF.weilTest gs.1.1 gs.1.1 y).re)=_
  change testMass gc.1.1+testMass gs.1.1=2*testMass f.1.1 at hm
  change jointPairRealCorr f L T y=(EF.weilTest gc.1.1 gc.1.1 y).re+
    (EF.weilTest gs.1.1 gs.1.1 y).re at hc
  linear_combination archJump (2*y)*hm+archJump (2*y)*hc

private theorem pairGamma_eq_jump (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    pairGamma f L T =
      2*((Complex.digamma (1/4)).re-Real.log Real.pi)*testMass f.1.1+
      2*∫ y in Ioi (0:ℝ), archJump (2*y)*
        (2*testMass f.1.1-jointPairRealCorr f L T y) := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  have hc := testGamma_eq_jump_scaled gc.1
  have hs := testGamma_eq_jump_scaled gs.1
  have hsum : (∫ y in Ioi (0:ℝ), archJump (2*y)*
        (testMass gc.1.1-(EF.weilTest gc.1.1 gc.1.1 y).re))+
      (∫ y in Ioi (0:ℝ), archJump (2*y)*
        (testMass gs.1.1-(EF.weilTest gs.1.1 gs.1.1 y).re)) =
      ∫ y in Ioi (0:ℝ), archJump (2*y)*
        (2*testMass f.1.1-jointPairRealCorr f L T y) := by
    rw [← integral_add (integrable_testGamma_jump_scaled gc.1)
      (integrable_testGamma_jump_scaled gs.1)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    have hm := joint_pair_testMass f hf hWL hL T
    have hcorr := jointPairRealCorr_eq f L T y
    change testMass gc.1.1+testMass gs.1.1=2*testMass f.1.1 at hm
    change jointPairRealCorr f L T y=(EF.weilTest gc.1.1 gc.1.1 y).re+
      (EF.weilTest gs.1.1 gs.1.1 y).re at hcorr
    linear_combination archJump (2*y)*hm+archJump (2*y)*hcorr
  have hm := joint_pair_testMass f hf hWL hL T
  change testMass gc.1.1+testMass gs.1.1=2*testMass f.1.1 at hm
  change testGamma gc.1.1+testGamma gs.1.1=_
  linear_combination hc+hs+2*hsum+
    ((Complex.digamma (1/4)).re-Real.log Real.pi)*hm

private theorem pairGamma_sub_zero (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    pairGamma f L T-pairGamma f L 0 =
      2*∫ y in Ioi (0:ℝ), archJump (2*y)*
        (jointPairRealCorr f L 0 y-jointPairRealCorr f L T y) := by
  rw [pairGamma_eq_jump f hf hWL hL T, pairGamma_eq_jump f hf hWL hL 0]
  rw [show ∀ a b c : ℝ, (a+2*b)-(a+2*c)=2*(b-c) by intros; ring]
  rw [← integral_sub (pairGamma_jump_integrable f hf hWL hL T)
    (pairGamma_jump_integrable f hf hWL hL 0)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  ring

private theorem shifted_jump_integrable {g : ℝ → ℝ} {L W : ℝ}
    (hc : Continuous g) (hs : tsupport g ⊆ Icc (-W) W) (hWL : W < L) :
    Integrable (fun y : ℝ => archJump (2*(L+y))*g y) := by
  have hgs : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hs
  have hcont : Continuous (fun y : ℝ => archJump (2*(L+y))*g y) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = -L
    · subst x
      have hn : -L ∉ tsupport g := by
        intro h
        have hh := (hs h).1
        linarith
      have he := notMem_tsupport_iff_eventuallyEq.mp hn
      have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (-L) := continuousAt_const
      apply hzero.congr
      filter_upwards [he] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy]
    · have hd : 1-Real.exp (-(2*(L+x))) ≠ 0 := by
        intro h
        have he : Real.exp (-(2*(L+x))) = Real.exp 0 := by
          rw [Real.exp_zero]
          linarith
        have heq := Real.exp_injective he
        exact hx (by linarith)
      unfold archJump
      exact ((by fun_prop : ContinuousAt (fun y : ℝ => Real.exp (-(2*(L+y)/4))) x).div
        (by fun_prop) hd).mul hc.continuousAt
  exact hcont.integrable_of_hasCompactSupport hgs.mul_left

private theorem shifted_jump_fold {g : ℝ → ℝ} {L W : ℝ}
    (hc : Continuous g) (hs : tsupport g ⊆ Icc (-W) W)
    (heven : ∀ y, g (-y)=g y) (hWL : W < L) :
    (∫ y in Ioi (0:ℝ), archJump (2*y)*g (y-L)) =
      ∫ y in Ioi (0:ℝ),
        (archJump (2*(L+y))+archJump (2*(L-y)))*g y := by
  let F : ℝ → ℝ := fun y => archJump (2*(L+y))*g y
  have hi : Integrable F := shifted_jump_integrable hc hs hWL
  have hshift : (∫ y : ℝ, archJump (2*y)*g (y-L)) = ∫ y : ℝ, F y := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) F L
    have hcancel (x : ℝ) : L+(x-L)=x := by ring
    simpa only [F, hcancel] using h
  have hfull : (∫ y in Ioi (0:ℝ), archJump (2*y)*g (y-L)) =
      ∫ y : ℝ, archJump (2*y)*g (y-L) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hy0 : y ≤ 0 := le_of_not_gt hy
    have hz : g (y-L)=0 := image_eq_zero_of_notMem_tsupport (by
      intro h
      have hh := (hs h).1
      linarith)
    simp [hz]
  rw [hfull,hshift]
  have hsplit := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hi
  rw [compl_Ioi, integral_Iic_eq_integral_Iio,
    ← show (∫ y in Ioi (0:ℝ), F (-y)) = ∫ y in Iio (0:ℝ), F y from
      (by simpa only [neg_zero, integral_Iic_eq_integral_Iio] using integral_comp_neg_Ioi 0 F)] at hsplit
  rw [← hsplit, ← integral_add hi.integrableOn hi.comp_neg.integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only [F]
  rw [heven]
  simp only [sub_eq_add_neg]
  ring

private def modulationLagDefect (f : JointSmoothTest) (T y : ℝ) : ℝ :=
  (EF.weilTest f.1.1 f.1.1 y).re*(1-Real.cos (T*y))

private theorem modulationLagDefect_continuous (f : JointSmoothTest) (T : ℝ) :
    Continuous (modulationLagDefect f T) := by
  have hc := (WeilSpectral.admissible_weilTest f.1.2.1 f.1.2.2).cont
  exact (Complex.continuous_re.comp hc).mul (by fun_prop)

private theorem modulationLagDefect_support (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (T : ℝ) :
    tsupport (modulationLagDefect f T) ⊆ Icc (-W) W := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra hn
  have hwy : W < |y| := lt_of_not_ge (fun h => hn (abs_le.mp h))
  have hz := weilTest_eq_zero_outside_interval hf hwy
  exact hy (by simp [modulationLagDefect, hz])

private theorem modulationLagDefect_neg (f : JointSmoothTest) (T y : ℝ) :
    modulationLagDefect f T (-y)=modulationLagDefect f T y := by
  simp only [modulationLagDefect, weilTest_self_neg, Complex.conj_re, mul_neg, Real.cos_neg]

private theorem jointPairRealCorr_defect (f : JointSmoothTest) (L T y : ℝ) :
    jointPairRealCorr f L 0 y-jointPairRealCorr f L T y=
      2*modulationLagDefect f T y-modulationLagDefect f T (y-L)-
        modulationLagDefect f T (y+L) := by
  simp only [jointPairRealCorr, zero_mul, Real.cos_zero, mul_one, modulationLagDefect]
  ring

private theorem folded_jump_integrable {g : ℝ → ℝ} {L W : ℝ}
    (hc : Continuous g) (hs : tsupport g ⊆ Icc (-W) W)
    (heven : ∀ y, g (-y)=g y) (hWL : W < L) :
    Integrable (fun y : ℝ =>
      (archJump (2*(L+y))+archJump (2*(L-y)))*g y) := by
  have hi := shifted_jump_integrable hc hs hWL
  have hj := hi.add hi.comp_neg
  apply hj.congr
  filter_upwards with y
  simp only [Pi.add_apply]
  rw [heven]
  simp only [sub_eq_add_neg]
  ring

private theorem pairGamma_sub_zero_folded (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    pairGamma f L T-pairGamma f L 0=
      ∫ y in Ioi (0:ℝ),
        (4*archJump (2*y)-2*(archJump (2*(L+y))+archJump (2*(L-y))))*
          modulationLagDefect f T y := by
  let g := modulationLagDefect f T
  have hgc : Continuous g := modulationLagDefect_continuous f T
  have hgs : tsupport g ⊆ Icc (-W) W := modulationLagDefect_support f hf T
  have hgn (y : ℝ) : g (-y)=g y := modulationLagDefect_neg f T y
  have hmain : IntegrableOn (fun y : ℝ => archJump (2*y)*g y) (Ioi 0) := by
    simpa only [g, modulationLagDefect, mul_assoc] using integrable_modulation_jump f T
  have hcross : Integrable (fun y : ℝ => archJump (2*y)*g (y-L)) := by
    have h := (shifted_jump_integrable hgc hgs hWL).comp_sub_right L
    have hcancel (x : ℝ) : L+(x-L)=x := by ring
    simpa only [hcancel] using h
  have hfold := folded_jump_integrable hgc hgs hgn hWL
  rw [pairGamma_sub_zero f hf hWL hL T]
  have heq : (∫ y in Ioi (0:ℝ), archJump (2*y)*
      (jointPairRealCorr f L 0 y-jointPairRealCorr f L T y)) =
      2*(∫ y in Ioi (0:ℝ), archJump (2*y)*g y)-
        ∫ y in Ioi (0:ℝ), archJump (2*y)*g (y-L) := by
    rw [← integral_const_mul, ← integral_sub (hmain.const_mul 2) hcross.integrableOn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [jointPairRealCorr_defect]
    have hz : g (y+L)=0 := image_eq_zero_of_notMem_tsupport (by
      intro h
      have hh := (hgs h).2
      linarith [show 0 < y from hy])
    change archJump (2*y)*(2*g y-g (y-L)-g (y+L))=_
    rw [hz]
    ring
  rw [heq, shifted_jump_fold hgc hgs hgn hWL]
  rw [show ∀ a b : ℝ, 2*(2*a-b)=4*a-2*b by intros; ring]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hmain.const_mul 4) (hfold.integrableOn.const_mul 2)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change 4*(archJump (2*y)*g y)-
    2*((archJump (2*(L+y))+archJump (2*(L-y)))*g y)=_
  ring

private theorem testPole_cosh_integrable (f : WeilTestFn) :
    Integrable (fun y : ℝ => 2*Real.cosh (y/2)*(EF.weilTest f.1 f.1 y).re) := by
  have hk := WeilSpectral.admissible_weilTest f.2.1 f.2.2
  have hs : HasCompactSupport (fun y : ℝ => (EF.weilTest f.1 f.1 y).re) := by
    apply HasCompactSupport.intro (K := tsupport (EF.weilTest f.1 f.1)) hk.supp
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact ((by fun_prop : Continuous (fun y : ℝ => 2*Real.cosh (y/2))).mul
    (Complex.continuous_re.comp hk.cont)).integrable_of_hasCompactSupport hs.mul_left

private def pairPole (f : JointSmoothTest) (L T : ℝ) : ℝ :=
  testPole (clusterDifference (cosineProfile f.1.1 T) L)+
    testPole (clusterDifference (sineProfile f.1.1 T) L)

private theorem pairPole_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (fun y : ℝ => 2*Real.cosh (y/2)*jointPairRealCorr f L T y) := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  apply ((testPole_cosh_integrable gc.1).add (testPole_cosh_integrable gs.1)).congr
  filter_upwards with y
  rw [jointPairRealCorr_eq]
  change 2*Real.cosh (y/2)*(EF.weilTest gc.1.1 gc.1.1 y).re+
    2*Real.cosh (y/2)*(EF.weilTest gs.1.1 gs.1.1 y).re=_
  dsimp only [gc,gs,clusterDifferenceTest,cosineProfileTest,sineProfileTest]
  ring

private theorem pairPole_eq_integral (f : JointSmoothTest) (L T : ℝ) :
    pairPole f L T=∫ y : ℝ, 2*Real.cosh (y/2)*jointPairRealCorr f L T y := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  change testPole gc.1.1+testPole gs.1.1=_
  rw [testPole_eq_integral_cosh gc.1, testPole_eq_integral_cosh gs.1,
    ← integral_add (testPole_cosh_integrable gc.1) (testPole_cosh_integrable gs.1)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [jointPairRealCorr_eq]
    change 2*Real.cosh (y/2)*(EF.weilTest gc.1.1 gc.1.1 y).re+
      2*Real.cosh (y/2)*(EF.weilTest gs.1.1 gs.1.1 y).re=_
    dsimp only [gc,gs,clusterDifferenceTest,cosineProfileTest,sineProfileTest]
    ring

private theorem cosh_cluster_integral {g : ℝ → ℝ}
    (hc : Continuous g) (hs : HasCompactSupport g) (L : ℝ) :
    (∫ y : ℝ, 2*Real.cosh (y/2)*(-(2*g y-g (y-L)-g (y+L))))=
      4*(Real.cosh (L/2)-1)*(∫ y : ℝ, Real.cosh (y/2)*g y) := by
  let F0 : ℝ → ℝ := fun y => Real.cosh (y/2)*g y
  let Fm : ℝ → ℝ := fun y => Real.cosh (y/2)*g (y-L)
  let Fp : ℝ → ℝ := fun y => Real.cosh (y/2)*g (y+L)
  have hw : Continuous (fun y : ℝ => Real.cosh (y/2)) := by fun_prop
  have h0 : Integrable F0 := (hw.mul hc).integrable_of_hasCompactSupport hs.mul_left
  have hm : Integrable Fm := (hw.mul (hc.comp
    (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hs.comp_homeomorph (Homeomorph.subRight L)).mul_left
  have hp : Integrable Fp := (hw.mul (hc.comp
    (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hs.comp_homeomorph (Homeomorph.addRight L)).mul_left
  have hmp : Integrable (fun y : ℝ => Real.cosh ((y+L)/2)*g y) :=
    ((by fun_prop : Continuous (fun y : ℝ => Real.cosh ((y+L)/2))).mul hc).integrable_of_hasCompactSupport hs.mul_left
  have hpm : Integrable (fun y : ℝ => Real.cosh ((y-L)/2)*g y) :=
    ((by fun_prop : Continuous (fun y : ℝ => Real.cosh ((y-L)/2))).mul hc).integrable_of_hasCompactSupport hs.mul_left
  have hem : (∫ y : ℝ, Fm y)=∫ y : ℝ, Real.cosh ((y+L)/2)*g y := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ)) Fm L
    simpa only [Fm, add_sub_cancel_right] using h.symm
  have hep : (∫ y : ℝ, Fp y)=∫ y : ℝ, Real.cosh ((y-L)/2)*g y := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) Fp L
    simpa only [Fp, sub_add_cancel] using h.symm
  have hsum : (∫ y : ℝ, Fm y)+(∫ y : ℝ, Fp y)=
      2*Real.cosh (L/2)*(∫ y : ℝ, F0 y) := by
    rw [hem,hep,← integral_add hmp hpm,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only [F0]
      rw [add_div,sub_div,Real.cosh_add,Real.cosh_sub]
      ring
  have heq : (fun y : ℝ => 2*Real.cosh (y/2)*(-(2*g y-g (y-L)-g (y+L))))=
      fun y => -4*F0 y+2*(Fm y+Fp y) := by
    funext y
    dsimp only [F0,Fm,Fp]
    ring
  have hsumI : Integrable (fun y : ℝ => 2*(Fm y+Fp y)) := (hm.add hp).const_mul 2
  rw [heq,integral_add (h0.const_mul (-4)) hsumI,
    integral_const_mul,integral_const_mul,integral_add hm hp,hsum]
  dsimp only [F0]
  ring

private theorem even_integral_half {g : ℝ → ℝ} (hi : Integrable g)
    (he : ∀ y, g (-y)=g y) : (∫ y : ℝ, g y)=2*∫ y in Ioi (0:ℝ), g y := by
  have hsplit := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hi
  have hneg := integral_comp_neg_Ioi 0 g
  simp only [he,neg_zero] at hneg
  rw [compl_Ioi,← hneg] at hsplit
  linarith

private theorem pairPole_sub_zero_folded (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (L T : ℝ) :
    pairPole f L T-pairPole f L 0=
      8*(Real.cosh (L/2)-1)*∫ y in Ioi (0:ℝ),
        Real.cosh (y/2)*modulationLagDefect f T y := by
  let g := modulationLagDefect f T
  have hc : Continuous g := modulationLagDefect_continuous f T
  have hs : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g)
    (modulationLagDefect_support f hf T)
  have hg : Integrable (fun y : ℝ => Real.cosh (y/2)*g y) :=
    ((by fun_prop : Continuous (fun y : ℝ => Real.cosh (y/2))).mul hc).integrable_of_hasCompactSupport hs.mul_left
  rw [pairPole_eq_integral,pairPole_eq_integral,
    ← integral_sub (pairPole_integrable f L T) (pairPole_integrable f L 0)]
  have heq : (∫ y : ℝ,
      2*Real.cosh (y/2)*jointPairRealCorr f L T y-
      2*Real.cosh (y/2)*jointPairRealCorr f L 0 y)=
      ∫ y : ℝ, 2*Real.cosh (y/2)*(-(2*g y-g (y-L)-g (y+L))) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      have h := jointPairRealCorr_defect f L T y
      change jointPairRealCorr f L 0 y-jointPairRealCorr f L T y=
        2*g y-g (y-L)-g (y+L) at h
      linear_combination -2*Real.cosh (y/2)*h
  rw [heq,cosh_cluster_integral hc hs L]
  have heven (y : ℝ) : Real.cosh (-y/2)*g (-y)=Real.cosh (y/2)*g y := by
    dsimp only [g]
    rw [modulationLagDefect_neg,neg_div,Real.cosh_neg]
  rw [even_integral_half hg heven]
  ring

/-- Literal full energy of the actual paired smooth cluster tests. -/
def jointPairFullEnergy (f : JointSmoothTest) (L T : ℝ) : ℝ :=
  weilArchRe (EF.weilTest (clusterDifference (cosineProfile f.1.1 T) L)
    (clusterDifference (cosineProfile f.1.1 T) L))+
  weilArchRe (EF.weilTest (clusterDifference (sineProfile f.1.1 T) L)
    (clusterDifference (sineProfile f.1.1 T) L))

private theorem jointPairFullEnergy_eq_parts (f : JointSmoothTest) (L T : ℝ) :
    jointPairFullEnergy f L T=pairGamma f L T+pairPole f L T := by
  have hc := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (cosineProfileTest f T) L).1
  have hs := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (sineProfileTest f T) L).1
  dsimp only [clusterDifferenceTest,cosineProfileTest,sineProfileTest] at hc hs
  unfold jointPairFullEnergy pairGamma pairPole
  linarith

/-- Exact signed modulation increment, with both poles retained. -/
theorem jointPairFullEnergy_sub_zero (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW : 0 < W) (hL : 2*W < L) (T : ℝ) :
    jointPairFullEnergy f L T-jointPairFullEnergy f L 0=
      ∫ y in Ioi (0:ℝ), jointModulationKernel L y*
        (EF.weilTest f.1.1 f.1.1 y).re*(1-Real.cos (T*y)) := by
  let g := modulationLagDefect f T
  have hgc : Continuous g := modulationLagDefect_continuous f T
  have hgs : tsupport g ⊆ Icc (-W) W := modulationLagDefect_support f hf T
  have hgn (y : ℝ) : g (-y)=g y := modulationLagDefect_neg f T y
  have hcs : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  have hmain : IntegrableOn (fun y : ℝ => archJump (2*y)*g y) (Ioi 0) := by
    simpa only [g,modulationLagDefect,mul_assoc] using integrable_modulation_jump f T
  have hfold := folded_jump_integrable hgc hgs hgn (show W < L by linarith)
  have hgamma : IntegrableOn (fun y : ℝ =>
      (4*archJump (2*y)-2*(archJump (2*(L+y))+archJump (2*(L-y))))*g y)
      (Ioi 0) := by
    apply ((hmain.const_mul 4).sub (hfold.integrableOn.const_mul 2)).congr
    filter_upwards with y
    dsimp only [Pi.sub_apply]
    ring
  have hcosh : Integrable (fun y : ℝ => Real.cosh (y/2)*g y) :=
    ((by fun_prop : Continuous (fun y : ℝ => Real.cosh (y/2))).mul hgc).integrable_of_hasCompactSupport hcs.mul_left
  have he : jointPairFullEnergy f L T-jointPairFullEnergy f L 0=
      (pairGamma f L T-pairGamma f L 0)+(pairPole f L T-pairPole f L 0) := by
    rw [jointPairFullEnergy_eq_parts,jointPairFullEnergy_eq_parts]
    ring
  rw [he,pairGamma_sub_zero_folded f hf (by linarith) (by linarith),
    pairPole_sub_zero_folded f hf L T,← integral_const_mul,
    ← integral_add hgamma (hcosh.integrableOn.const_mul (8*(Real.cosh (L/2)-1)))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only [g,modulationLagDefect,jointModulationKernel]
  ring

/-- Nonnegative real autocorrelation makes zero the global modulation minimum. -/
theorem jointPairFullEnergy_zero_le (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW : 0 < W) (hL : 2*W < L)
    (hcorr : ∀ y ∈ Icc 0 W, 0 ≤ (EF.weilTest f.1.1 f.1.1 y).re) (T : ℝ) :
    jointPairFullEnergy f L 0 ≤ jointPairFullEnergy f L T := by
  apply sub_nonneg.mp
  rw [jointPairFullEnergy_sub_zero f hf hW hL T]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hy
  by_cases hyW : y ≤ W
  · exact mul_nonneg (mul_nonneg (jointModulationKernel_pos hy0 (by linarith)).le
      (hcorr y ⟨hy0.le,hyW⟩)) (by linarith [Real.cos_le_one (T*y)])
  · have hz := weilTest_eq_zero_outside_interval hf
      (show W < |y| by rw [abs_of_pos hy0]; exact lt_of_not_ge hyW)
    simp [hz]

theorem jointPairFullEnergy_zero (f : JointSmoothTest) (L : ℝ) :
    jointPairFullEnergy f L 0=
      weilArchRe (EF.weilTest (clusterDifference f.1.1 L) (clusterDifference f.1.1 L)) := by
  have hc : cosineProfile f.1.1 0=f.1.1 := by funext y; simp [cosineProfile]
  have hs : sineProfile f.1.1 0=0 := by funext y; simp [sineProfile]
  have hz : clusterDifference (0 : ℝ → ℂ) L=0 := by funext y; simp [clusterDifference]
  have hcorr : EF.weilTest (0 : ℝ → ℂ) 0=0 := by
    funext y
    rw [weilTest_apply]
    simp
  rw [jointPairFullEnergy,hc,hs,hz,hcorr]
  simp [weilArchRe,paperFT]

end RHTower.WeilWorkPBAP
