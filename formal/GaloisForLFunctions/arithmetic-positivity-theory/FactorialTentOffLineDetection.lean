import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTranslatedTentApproximation
import GaloisForLFunctions.«arithmetic-positivity-theory».PeriodDifferenceOffLineDetection

/-! A quantitative native factorial-tent detector.
The arithmetic scale may grow above an explicit period-dependent threshold.
One smoothing index gives both literal full Weil approximation and detection of
the complete lattice-plus-reflected-pair model, including diagonal and defect. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported ComplexConjugate Convolution
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.WeilOneSided
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false


theorem factorialSourceRight_nonneg (n : ℕ) (x : ℝ) : 0 ≤ factorialSourceRight n x :=
  mul_nonneg (Real.exp_pos _).le (exponentialTentDensity_nonneg _ _)

theorem factorialSourceRight_integral_lower (n : ℕ) : 1 ≤ ∫ x, factorialSourceRight n x := by
  let d := sourceFactorialWidth (n+1)
  have hd : 0 < d := sourceFactorialWidth_pos (by omega)
  have hden : (∫ x, exponentialTentDensity d x) = 1 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => exponentialTentDensity_zero_of_not_mem d hx)]
    exact integral_Icc_exponentialTentDensity hd
  rw [← hden]
  apply integral_mono
    ((continuous_exponentialTentDensity d).integrable_of_hasCompactSupport (hasCompactSupport_exponentialTentDensity d))
    ((factorialSourceRight n).continuous.integrable_of_hasCompactSupport (factorialSourceRight n).hasCompactSupport)
  intro x
  change exponentialTentDensity d x ≤ Real.exp (x/2)*exponentialTentDensity d x
  by_cases hx : x ∈ Icc 0 (2*d)
  · have he : 1 ≤ Real.exp (x/2) := Real.one_le_exp_iff.mpr (by linarith [hx.1])
    nlinarith [exponentialTentDensity_nonneg d x]
  · rw [exponentialTentDensity_zero_of_not_mem d hx]
    simp

theorem smoothCompactSource_nonneg (f : C_c(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x) (k : ℕ) (x : ℝ) :
    0 ≤ smoothCompactSource f k x :=
  integral_nonneg fun y => mul_nonneg (mollifier_nonneg k y) (hf (x-y))

theorem smoothCompactSource_integral (f : C_c(ℝ, ℝ)) (k : ℕ) :
    (∫ x, smoothCompactSource f k x) = ∫ x, f x := by
  change (∫ x, lineConvolution (CHMDDoobGraph.mollifier k) f x) = _
  change (∫ x, ((CHMDDoobGraph.mollifier k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : ℝ → ℝ)) x) = _
  rw [integral_convolution (f := CHMDDoobGraph.mollifier k) (g := (f : ℝ → ℝ))
    (μ := volume) (ν := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifier_integrable k) (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)]
  simp only [mollifier_integral, ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul]

theorem smoothCompactSource_zero_of_radius (f : C_c(ℝ, ℝ)) {R : ℝ}
    (hf : ∀ x, R < |x| → f x = 0) (k : ℕ) {x : ℝ}
    (hx : R+1/(4*((k : ℝ)+1)) < |x|) : smoothCompactSource f k x = 0 := by
  change (∫ y, CHMDDoobGraph.mollifier k y*f (x-y)) = 0
  have hzero (y : ℝ) : CHMDDoobGraph.mollifier k y*f (x-y) = 0 := by
    by_cases hy : CHMDDoobGraph.mollifier k y = 0
    · simp [hy]
    have hyr : |y| ≤ 1/(4*((k : ℝ)+1)) := by
      have hm : y ∈ Function.support (CHMDDoobGraph.mollifier k) := hy
      rw [CHMDDoobGraph.mollifier, ContDiffBump.support_normed_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs] at hm
      exact hm.le
    have hdist : |x| ≤ |x-y|+|y| := by
      simpa only [sub_add_cancel] using abs_add_le (x-y) y
    rw [hf (x-y) (by linarith), mul_zero]
  simp only [hzero, integral_zero]

theorem factorialSourceRight_zero_of_thin_radius (n : ℕ) {x : ℝ}
    (hx : 2/((n : ℝ)+1) < |x|) : factorialSourceRight n x = 0 := by
  have hd := (sourceFactorialWidth_bounds (by omega : 1 ≤ n+1)).2
  have hN : 0 < (n : ℝ)+1 := by positivity
  have hlarge : sourceFactorialWidth (n+1) ≤ 1/((n : ℝ)+1) := by
    refine hd.trans ?_
    push_cast
    apply (div_le_div_iff₀ (by positivity) hN).2
    nlinarith
  have hout : x ∉ Icc 0 (2*sourceFactorialWidth (n+1)) := by
    intro hm
    rw [abs_of_nonneg hm.1] at hx
    have : 2*sourceFactorialWidth (n+1) ≤ 2/((n : ℝ)+1) := by
      calc
        _ ≤ 2*(1/((n : ℝ)+1)) := mul_le_mul_of_nonneg_left hlarge (by norm_num)
        _ = _ := by ring
    linarith [hm.2]
  change exponentialTentSource (sourceFactorialWidth (n+1)) x = 0
  simp only [exponentialTentSource, exponentialTentDensity_zero_of_not_mem _ hout, mul_zero]

theorem smoothedFactorialTent_thin (n k : ℕ) (hnk : n ≤ k) {x : ℝ}
    (hx : 3/((n : ℝ)+1) < |x|) : smoothCompactSource (factorialSourceRight n) k x = 0 := by
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hr : 1/(4*((k : ℝ)+1)) ≤ 1/((n : ℝ)+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  apply smoothCompactSource_zero_of_radius _ (fun _ => factorialSourceRight_zero_of_thin_radius n) k
  have he : 2/((n : ℝ)+1)+1/((n : ℝ)+1) = 3/((n : ℝ)+1) := by ring
  linarith

/-- Arithmetic scale chosen only from the lattice period. -/
def factorialTentDetectionScale (L : ℝ) : ℕ := ⌈32*Real.pi/L⌉₊

theorem factorialTentDetectionScale_thin {L : ℝ} (hL : 0 < L) :
    (2*Real.pi/L)*(3/((factorialTentDetectionScale L : ℝ)+1)) ≤ 1/4 := by
  have hc := Nat.le_ceil (32*Real.pi/L)
  change 32*Real.pi/L ≤ (factorialTentDetectionScale L : ℝ) at hc
  have h := (div_le_iff₀ hL).mp hc
  calc
    _ = (6*Real.pi)/(L*((factorialTentDetectionScale L : ℝ)+1)) := by
      field_simp [hL.ne', ne_of_gt (by positivity : 0 < (factorialTentDetectionScale L : ℝ)+1)]
      <;> ring
    _ ≤ 1/4 := (div_le_div_iff₀ (mul_pos hL (by positivity)) (by norm_num)).2 (by
      nlinarith [Real.pi_pos])

theorem factorialTentDetectionScale_le_thin {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : factorialTentDetectionScale L ≤ n) :
    (2*Real.pi/L)*(3/((n : ℝ)+1)) ≤ 1/4 := by
  have hn' : (factorialTentDetectionScale L : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hr : 3/((n : ℝ)+1) ≤ 3/((factorialTentDetectionScale L : ℝ)+1) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans (factorialTentDetectionScale_thin hL)

/-- A native two-site pattern, with coefficients `1,-1` and sites `0,-L`. -/
def factorialTentPeriodDifference (n : ℕ) (L : ℝ) : C_c(ℝ, ℝ) :=
  factorialTentPattern {0,1} (fun _ => n) (fun i => if i = 0 then 1 else -1)
    (fun i => if i = 0 then 0 else -L)

@[simp] theorem factorialTentPeriodDifference_apply (n : ℕ) (L x : ℝ) :
    factorialTentPeriodDifference n L x = factorialSourceRight n x-factorialSourceRight n (x-L) := by
  simp [factorialTentPeriodDifference, factorialTentPattern_apply, sub_eq_add_neg]

theorem smooth_factorialTentPeriodDifference (n k : ℕ) (L x : ℝ) :
    smoothCompactSource (factorialTentPeriodDifference n L) k x =
      smoothCompactSource (factorialSourceRight n) k x-
        smoothCompactSource (factorialSourceRight n) k (x-L) := by
  have hi (z : ℝ) : Integrable (fun y => CHMDDoobGraph.mollifier k y*factorialSourceRight n (z-y)) :=
    ((mollifier_contDiff k).continuous.mul
      ((factorialSourceRight n).continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        (mollifier_compact k).mul_right
  change (∫ y, CHMDDoobGraph.mollifier k y*factorialTentPeriodDifference n L (x-y)) =
    (∫ y, CHMDDoobGraph.mollifier k y*factorialSourceRight n (x-y))-
      ∫ y, CHMDDoobGraph.mollifier k y*factorialSourceRight n (x-L-y)
  simp_rw [factorialTentPeriodDifference_apply, show ∀ y : ℝ, x-y-L = x-L-y from fun y => by ring, mul_sub]
  exact integral_sub (hi x) (hi (x-L))

theorem liftC_smooth_factorialTentPeriodDifference (n k : ℕ) (L : ℝ) :
    liftC (smoothCompactSource (factorialTentPeriodDifference n L) k) =
      shiftPair (smoothCompactSource (factorialSourceRight n) k) (-1) L := by
  funext x
  simp only [liftC, shiftPair]
  rw [smooth_factorialTentPeriodDifference]
  push_cast
  ring

/-- One index simultaneously pays the full-form error and preserves a thin detector seed. -/
def factorialTentDetectorSmoothingIndex (n : ℕ) (L : ℝ) (q : ℕ) : ℕ :=
  max n
    (factorialTentPatternSmoothingIndex {0,1} (fun _ => n)
      (fun i => if i = 0 then 1 else -1) (fun i => if i = 0 then 0 else -L) q)

theorem factorialTentDetector_fullWeil_approximation (n : ℕ) (L : ℝ) (q : ℕ) :
    |compactFullWeilEnergy (smoothCompactSource
        (factorialTentPeriodDifference n L)
        (factorialTentDetectorSmoothingIndex n L q))-
      compactFullWeilEnergy (factorialTentPeriodDifference n L)| ≤
        1/((q : ℝ)+1) := by
  refine (factorialTentPattern_fullWeil_smoothing_error {0,1}
    (fun _ => n) (fun i => if i = 0 then 1 else -1)
    (fun i => if i = 0 then 0 else -L) _).trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hc := Nat.le_ceil (((q : ℝ)+1)*compactFullWeilApproximationCost
    (factorialTentPatternRadius {0,1} (fun i => if i = 0 then 0 else -L))
    (factorialTentPatternValueBound {0,1} (fun _ => n) (fun i => if i = 0 then 1 else -1))
    (factorialTentPatternSlopeBound {0,1} (fun _ => n) (fun i => if i = 0 then 1 else -1)))
  have hm : (factorialTentPatternSmoothingIndex {0,1} (fun _ => n)
      (fun i => if i = 0 then 1 else -1) (fun i => if i = 0 then 0 else -L) q : ℝ) ≤
      (factorialTentDetectorSmoothingIndex n L q : ℝ) := by
    apply Nat.cast_le.mpr
    exact le_max_right _ _
  change _ ≤ (factorialTentPatternSmoothingIndex {0,1} (fun _ => n)
    (fun i => if i = 0 then 1 else -1) (fun i => if i = 0 then 0 else -L) q : ℝ) at hc
  nlinarith

/-- The detector belongs to the same smoothed native family used in the full-form estimate. -/
def factorialTentDetector (n : ℕ) (L : ℝ) (q : ℕ) : ℝ → ℂ :=
  liftC (smoothCompactSource (factorialTentPeriodDifference n L)
    (factorialTentDetectorSmoothingIndex n L q))

def factorialTentDetectionMargin (n : ℕ) (L δ : ℝ) : ℝ :=
  (Real.exp (δ*L)-1)*(1-Real.exp (-(δ*L)))*
    Real.exp (-6*δ/((n : ℝ)+1))

theorem factorialTentDetectionMargin_pos (n : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    0 < factorialTentDetectionMargin n L δ := by
  have hp : 0 < Real.exp (δ*L)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hδ hL))
  have hm : 0 < 1-Real.exp (-(δ*L)) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  exact mul_pos (mul_pos hp hm) (Real.exp_pos _)

theorem factorialTentDetector_admissible (n : ℕ) (L : ℝ) (q : ℕ) :
    ContDiff ℝ 2 (factorialTentDetector n L q) ∧ HasCompactSupport (factorialTentDetector n L q) := by
  let f := factorialTentPeriodDifference n L
  let k := factorialTentDetectorSmoothingIndex n L q
  exact ⟨contDiff_liftC (smooth_contDiff (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport) k),
    hasCompactSupport_liftC (smoothCompactSource f k).hasCompactSupport⟩

theorem factorialTentDetector_eq_periodDifference (n : ℕ) (L : ℝ) (q : ℕ) :
    factorialTentDetector n L q = shiftPair
      (smoothCompactSource (factorialSourceRight n)
        (factorialTentDetectorSmoothingIndex n L q)) (-1) L :=
  liftC_smooth_factorialTentPeriodDifference _ _ _

theorem factorialTentDetector_online_zero (n : ℕ) {L : ℝ} (hL : 0 < L) (q : ℕ) (j : ℤ) :
    paperFT (factorialTentDetector n L q) ((((j : ℝ)*(2*Real.pi/L) : ℝ) : ℂ)) = 0 := by
  rw [factorialTentDetector_eq_periodDifference]
  exact periodDifference_online_readout_zero _ hL j

/-- Native detection with an explicit strictly positive margin and no readout premise. -/
theorem factorialTentDetector_negative_margin (n : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (hn : factorialTentDetectionScale L ≤ n) (q : ℕ) :
    ((isolatedPairConfig hL hδ hδ' (2*Real.pi/L)).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤ -factorialTentDetectionMargin n L δ := by
  let k := factorialTentDetectorSmoothingIndex n L q
  have hnk : n ≤ k := le_max_left _ _
  have hmass : 1 ≤ ∫ x, smoothCompactSource (factorialSourceRight n) k x := by
    rw [smoothCompactSource_integral]
    exact factorialSourceRight_integral_lower n
  rw [factorialTentDetector_eq_periodDifference]
  have h := periodDifference_isolatedPair_negative_margin
    (smoothCompactSource (factorialSourceRight n) k)
    (smoothCompactSource_nonneg _ (factorialSourceRight_nonneg n) k)
    (fun x hx => smoothedFactorialTent_thin n k hnk hx) hmass hL hδ hδ'
    (factorialTentDetectionScale_le_thin hL hn)
  convert h using 1 <;> dsimp [factorialTentDetectionMargin, k] <;> congr 3 <;> ring

theorem factorialTentDetector_reflection_gap (n : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (hn : factorialTentDetectionScale L ≤ n) (q : ℕ) :
    factorialTentDetectionMargin n L δ ≤
      configurationReflectionDefect (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (factorialTentDetector n L q)-
        configurationSquareMass (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (factorialTentDetector n L q) := by
  have hW := factorialTentDetector_negative_margin n hL hδ hδ' hn q
  have he := isolatedPair_reflection_identity_of_online_zero hL hδ hδ' (2*Real.pi/L)
    (factorialTentDetector n L q) (factorialTentDetector_online_zero n hL q)
  linarith

/-- The approximation controls the literal arithmetic full form of the very same detector. -/
theorem factorialTentDetector_literal_fullWeil_approximation (n : ℕ) (L : ℝ) (q : ℕ) :
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (factorialTentDetector n L q) (factorialTentDetector n L q))).re-
      compactFullWeilEnergy (factorialTentPeriodDifference n L)| ≤ 1/((q : ℝ)+1) :=
  factorialTentDetector_fullWeil_approximation n L q

/-- A single native C² compact test carries joint full-form control and model detection. -/
theorem factorialTentDetector_spec (n : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (hn : factorialTentDetectionScale L ≤ n) (q : ℕ) :
    ContDiff ℝ 2 (factorialTentDetector n L q) ∧
    HasCompactSupport (factorialTentDetector n L q) ∧
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (factorialTentDetector n L q) (factorialTentDetector n L q))).re-
      compactFullWeilEnergy (factorialTentPeriodDifference n L)| ≤ 1/((q : ℝ)+1) ∧
    0 < factorialTentDetectionMargin n L δ ∧
    ((isolatedPairConfig hL hδ hδ' (2*Real.pi/L)).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤ -factorialTentDetectionMargin n L δ ∧
    factorialTentDetectionMargin n L δ ≤
      configurationReflectionDefect (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (factorialTentDetector n L q)-
        configurationSquareMass (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (factorialTentDetector n L q) :=
  ⟨(factorialTentDetector_admissible n L q).1, (factorialTentDetector_admissible n L q).2,
    factorialTentDetector_literal_fullWeil_approximation n L q,
    factorialTentDetectionMargin_pos n hL hδ,
    factorialTentDetector_negative_margin n hL hδ hδ' hn q,
    factorialTentDetector_reflection_gap n hL hδ hδ' hn q⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
