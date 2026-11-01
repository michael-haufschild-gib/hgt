import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.HalfLogThreeCutoffAndTraceIdentity
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarBumpSources
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFormTranslation
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninSmallSupportDomination

/-!
# Semilocal `{∞, 2}` Positivity Obstructions and Forced Zero Crossings

Question Q6 (Candidate A) asks whether small-aperture Weil positivity through `½ log 3` can be
obtained by rewriting the restricted Weil form as the trace of a positive operator built from the
archimedean Sonin trace identity and a local operator at the prime `2` of logarithmic trace growth.

While `PrimeValuationShellLogTrace` and `HalfLogThreeCutoffAndTraceIdentity` prove that the exact
`{∞, 2}` operator-trace **identity** holds throughout `0 < a ≤ ½ log 3` with a genuine positive
trace-class `2`-adic shell operator `K_2(m)` (`Tr(K_2(m)) = m log 2`), this module proves four
unconditional operator-theoretic obstructions ruling out **positivity** from any semilocal `{∞, 2}`
positive operator trace or tensor factorization:

1. **General positive operator-trace monotonicity:** for every positive operator `P` on a complex
   Hilbert space, `0 ≤ (opTrace P).re`, and for every positive `M` and bounded `Θ, Ψ`,
   `Θ† ∘L M ∘L Θ` and `Ψ ∘L M ∘L Ψ†` are positive with nonnegative real trace.
2. **Non-positivity of the unglued archimedean Sonin generic operator `ccmSoninGenericPartAt 1`:**
   even at cutoff `1`, a smooth nonnegative bump supported inside `(-ε₀, ε₀)` produces a strictly
   negative conjugate scaling trace, proving `¬ IsPositive (ccmSoninGenericPartAt 1)`.
3. **Bilateral indefiniteness of the prime-`p` transport block and multiplicative pure-tensor
   no-go:** for every `p ≥ 2` and `a > ½ log p`, `ccmPrimeTransportOperator a p` takes both
   strictly positive and strictly negative diagonal values on `CCMArchimedeanFormDomain a`, so
   neither `±ccmPrimeTransportOperator a p` (nor `±ccmFinitePrimeOperator a` on `(½ log 2, ½ log 3]`)
   is positive; moreover on `(½ log 2, ½ log 3]`, `ccmRestrictedWeilSourceQuadratic a` admits
   neither a scalar multiple nor a positive-degree homogeneous multiplicative factorization over
   `primeFreeFamily.Q a`.
4. **Exponential ground-energy collapse along the half-integer prime lattice and forced zero
   crossings:** for every `p ≥ 2`, along `b_M = 1/16 + ((2M + 1)/4) log p`, an antisymmetric
   translated bump pair lies in the simultaneous kernel of **all** prime-power shifts `p^k` (`k ≥ 1`)
   while its polar term grows like `-2 (e^{L_M/2} - e^{-L_M/2})^2 m₊ m₋`. Hence both
   `primeFreeFamily.energy` and `(primeSingleSemilocalFamily p).energy` (in particular at `p = 2`)
   collapse exponentially to `-∞`, cross zero unconditionally with a nonzero Friedrichs kernel
   state, and admit **no** positive operator-trace carrier on `CCMArchimedeanFormDomain`.
-/

noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped ENNReal InnerProductSpace
open _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-! ## 1. Positive operator traces have nonnegative real part -/

/-- Sandwiching a positive operator `M` by `Θ†` and `Θ` preserves positivity. -/
theorem isPositive_adjoint_comp_comp {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : H →L[ℂ] H} (hM : ContinuousLinearMap.IsPositive M) (Θ : K →L[ℂ] H) :
    ContinuousLinearMap.IsPositive (ContinuousLinearMap.adjoint Θ ∘L M ∘L Θ) := by
  refine ⟨?_, fun x => ?_⟩
  · intro x y
    have hsym : ⟪M (Θ x), Θ y⟫_ℂ = ⟪Θ x, M (Θ y)⟫_ℂ := hM.1 (Θ x) (Θ y)
    change ⟪ContinuousLinearMap.adjoint Θ (M (Θ x)), y⟫_ℂ =
      ⟪x, ContinuousLinearMap.adjoint Θ (M (Θ y))⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, hsym,
      ContinuousLinearMap.adjoint_inner_right]
  · rw [ContinuousLinearMap.reApplyInnerSelf]
    change 0 ≤ RCLike.re ⟪ContinuousLinearMap.adjoint Θ (M (Θ x)), x⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hM.2 (Θ x)

/-- Sandwiching a positive operator `M` by `Ψ` and `Ψ†` preserves positivity. -/
theorem isPositive_comp_comp_adjoint {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : H →L[ℂ] H} (hM : ContinuousLinearMap.IsPositive M) (Ψ : H →L[ℂ] K) :
    ContinuousLinearMap.IsPositive (Ψ ∘L M ∘L ContinuousLinearMap.adjoint Ψ) := by
  have heq : Ψ ∘L M ∘L ContinuousLinearMap.adjoint Ψ =
      ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint Ψ) ∘L M ∘L
        ContinuousLinearMap.adjoint Ψ := by
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [heq]
  exact isPositive_adjoint_comp_comp hM (ContinuousLinearMap.adjoint Ψ)

/-- Every positive bounded operator on a complex Hilbert space has `0 ≤ (opTrace P).re`. -/
theorem opTrace_re_nonneg_of_isPositive {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {P : H →L[ℂ] H} (hP : ContinuousLinearMap.IsPositive P) :
    0 ≤ (ContinuousLinearMap.opTrace P).re := by
  unfold ContinuousLinearMap.opTrace
  set b := ContinuousLinearMap.hsBasis ℂ H
  by_cases hsum : Summable (fun i => inner ℂ (b i) (P (b i)))
  · rw [Complex.re_tsum hsum]
    refine tsum_nonneg fun i => ?_
    have h1 : 0 ≤ (⟪P (b i), b i⟫_ℂ).re := hP.2 (b i)
    have h2 : ⟪b i, P (b i)⟫_ℂ = starRingEnd ℂ ⟪P (b i), b i⟫_ℂ := (inner_conj_symm _ _).symm
    rw [h2, Complex.conj_re]
    exact h1
  · rw [tsum_eq_zero_of_not_summable hsum, Complex.zero_re]

theorem opTrace_adjoint_comp_comp_re_nonneg {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : H →L[ℂ] H} (hM : ContinuousLinearMap.IsPositive M) (Θ : K →L[ℂ] H) :
    0 ≤ (ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint Θ ∘L M ∘L Θ)).re :=
  opTrace_re_nonneg_of_isPositive (isPositive_adjoint_comp_comp hM Θ)

theorem opTrace_comp_comp_adjoint_re_nonneg {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : H →L[ℂ] H} (hM : ContinuousLinearMap.IsPositive M) (Ψ : H →L[ℂ] K) :
    0 ≤ (ContinuousLinearMap.opTrace (Ψ ∘L M ∘L ContinuousLinearMap.adjoint Ψ)).re :=
  opTrace_re_nonneg_of_isPositive (isPositive_comp_comp_adjoint hM Ψ)

/-! ## 2. Non-positivity of the unglued archimedean Sonin generic operator -/

/-- Explicit small-support nonnegative compact Schwartz logarithmic test inside
`(-ccmSoninSmallSupportRadius, ccmSoninSmallSupportRadius)`. -/
def smallSupportNonnegLogTest : CCMCompactSchwartzLogTest :=
  let ε := min ccmSoninSmallSupportRadius 1
  have hε : 0 < ε := lt_min ccmSoninSmallSupportRadius_pos zero_lt_one
  { toSchwartzMap := suzukiRealTestSchwartz (polarBumpFn 0 ε hε)
      (polarBumpFn 0 ε hε).contDiff (polarBumpFn 0 ε hε).hasCompactSupport
    radius := 2
    one_lt_radius := by norm_num
    eq_zero_of_radius_le_abs := by
      intro x hx
      have hε1 : ε ≤ 1 := min_le_right _ _
      have hnot : x ∉ Function.support (polarBumpFn 0 ε hε) := by
        rw [(polarBumpFn 0 ε hε).support_eq, polarBumpFn_rOut, Metric.mem_ball, Real.dist_eq,
          sub_zero]
        linarith
      have hzero : polarBumpFn 0 ε hε x = 0 := Function.notMem_support.mp hnot
      change ((polarBumpFn 0 ε hε x : ℝ) : ℂ) = 0
      rw [hzero, Complex.ofReal_zero] }

/-- A small-support nonnegative bump yields a strictly negative generic Sonin trace at cutoff `1`. -/
theorem opTrace_ccmSoninGenericPartAt_one_smallSupportNonneg_lt_zero :
    (ContinuousLinearMap.opTrace
      (ccmIntegratedScaling (ccmSchwartzLogKernel smallSupportNonnegLogTest.toSchwartzMap) ∘L
        ccmSoninGenericPartAt 1 ∘L
          ContinuousLinearMap.adjoint
            (ccmIntegratedScaling
              (ccmSchwartzLogKernel smallSupportNonnegLogTest.toSchwartzMap)))).re < 0 := by
  let ε := min ccmSoninSmallSupportRadius 1
  have hε : 0 < ε := lt_min ccmSoninSmallSupportRadius_pos zero_lt_one
  have hε₀ : ε ≤ ccmSoninSmallSupportRadius := min_le_left _ _
  have hsupp : ∀ x, ε ≤ |x| → smallSupportNonnegLogTest x = 0 := by
    intro x hx
    have hnot : x ∉ Function.support (polarBumpFn 0 ε hε) := by
      rw [(polarBumpFn 0 ε hε).support_eq, polarBumpFn_rOut, Metric.mem_ball, Real.dist_eq,
        sub_zero]
      linarith
    have hzero : polarBumpFn 0 ε hε x = 0 := Function.notMem_support.mp hnot
    change ((polarBumpFn 0 ε hε x : ℝ) : ℂ) = 0
    rw [hzero, Complex.ofReal_zero]
  have hreal : ∀ x, (smallSupportNonnegLogTest x).im = 0 := fun x => Complex.ofReal_im _
  have hnonneg : ∀ x, 0 ≤ (smallSupportNonnegLogTest x).re := fun x => by
    change 0 ≤ ((polarBumpFn 0 ε hε x : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact (polarBumpFn 0 ε hε).nonneg
  have hx₀ : smallSupportNonnegLogTest 0 ≠ 0 := by
    change ((polarBumpFn 0 ε hε 0 : ℝ) : ℂ) ≠ 0
    have hone : polarBumpFn 0 ε hε 0 = 1 :=
      (polarBumpFn 0 ε hε).one_of_mem_closedBall
        (Metric.mem_closedBall_self (polarBumpFn 0 ε hε).rIn_pos.le)
    rw [hone, Complex.ofReal_one]
    exact one_ne_zero
  have hfail := not_ccmSoninTraceDomination_of_nonneg smallSupportNonnegLogTest hε hε₀ hsupp
    hreal hnonneg hx₀
  have hiff := (ccmSoninTraceDomination_iff_toeplitz smallSupportNonnegLogTest).not
  rw [not_le, not_le] at hiff
  rw [opTrace_ccmSoninGenericPartAt_eq_toeplitz smallSupportNonnegLogTest one_pos]
  exact hiff.mp hfail

/-- **Unglued archimedean Sonin obstruction:** `ccmSoninGenericPartAt 1` is not positive. -/
theorem not_isPositive_ccmSoninGenericPartAt_one :
    ¬ ContinuousLinearMap.IsPositive (ccmSoninGenericPartAt 1) := by
  intro hpos
  have hge := opTrace_comp_comp_adjoint_re_nonneg hpos
    (ccmIntegratedScaling (ccmSchwartzLogKernel smallSupportNonnegLogTest.toSchwartzMap))
  linarith [opTrace_ccmSoninGenericPartAt_one_smallSupportNonneg_lt_zero]

/-! ## 3. Bilateral indefiniteness of prime transport and multiplicative tensor no-go -/

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : Real.log (Real.exp 1) < Real.log 4 :=
    Real.log_lt_log (Real.exp_pos 1) hexp
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]
    norm_num
  rw [Real.log_exp, hlog4] at hlog
  linarith

theorem half_lt_log_of_two_le {p : ℕ} (hp : 2 ≤ p) : (1 / 2 : ℝ) < Real.log p :=
  lt_of_lt_of_le half_lt_log_two (Real.log_le_log (by norm_num) (by exact_mod_cast hp))

theorem bumpFormVector_aperture_ne_zero (a : SuzukiPositiveAperture) (r : ℝ) (hr : 0 < r)
    (hc : Metric.closedBall (0 : ℝ) r ⊆ Ioo (-a.1) a.1) :
    ccmArchimedeanFormToAperture a (bumpInteriorSource a 0 r hr hc).toCCMFormVector ≠ 0 := by
  intro hzero
  have hm : 0 < polarBumpMoment 0 r hr (1 / 2) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (polarBumpMass_pos 0 r hr))
      (le_polarBumpMoment 0 r hr (1 / 2))
  have hpol := inner_polar_bumpInteriorSource a 0 r hr hc (1 / 2)
  rw [hzero, inner_zero_right] at hpol
  have : polarBumpMoment 0 r hr (1 / 2) = 0 := Complex.ofReal_eq_zero.mp hpol.symm
  linarith

theorem inner_logTranslationCLM_map_map (h : ℝ) (f g : SoninL2) :
    inner ℂ (logTranslationCLM h f) (logTranslationCLM h g) = inner ℂ f g :=
  (MellinL2.additiveTranslationUnitary h).inner_map_map f g

theorem norm_logTranslationCLM (h : ℝ) (f : SoninL2) :
    ‖logTranslationCLM h f‖ = ‖f‖ :=
  (MellinL2.additiveTranslationUnitary h).norm_map f

theorem inner_logTranslation_two_shifts (t c d : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM t (logTranslationCLM c f)) (logTranslationCLM d f) =
      inner ℂ (logTranslationCLM (t + c - d) f) f := by
  calc
    inner ℂ (logTranslationCLM t (logTranslationCLM c f)) (logTranslationCLM d f)
      = inner ℂ (logTranslationCLM t (logTranslationCLM c f)) (logTranslationCLM (- -d) f) := by
          rw [neg_neg]
    _ = inner ℂ (logTranslationCLM (-d) (logTranslationCLM t (logTranslationCLM c f))) f :=
          (inner_logTranslationCLM (-d) _ _).symm
    _ = inner ℂ (logTranslationCLM (-d + t + c) f) f := by
          rw [logTranslationCLM_add_apply, logTranslationCLM_add_apply]
    _ = inner ℂ (logTranslationCLM (t + c - d) f) f := by
          congr 2; ring

theorem inner_logTranslationCLM_eq_zero_of_two_mul_le_abs
    (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 ≤ |h|) :
    inner ℂ (logTranslationCLM h f.1) g.1 = 0 := by
  rcases le_or_gt 0 h with h0 | h0
  · rw [abs_of_nonneg h0] at hh
    exact inner_logTranslationCLM_eq_zero_of_two_mul_le a f g hh
  · rw [abs_of_neg h0] at hh
    simpa using inner_neg_logTranslationCLM_eq_zero_of_two_mul_le a f g (h := -h) hh

/-- **Bilateral indefiniteness of `ccmPrimeTransportOperator a p` beyond `½ log p`.**
Symmetric and antisymmetric pairs of narrow translated bumps at `± ½ log p` give strictly positive
and strictly negative expectation values for `ccmPrimeTransportOperator a p`. -/
theorem exists_pos_and_neg_ccmPrimeTransportOperator {p : ℕ} (hp : 2 ≤ p)
    {a : SuzukiPositiveAperture} (ha : Real.log p / 2 < a.1) :
    ∃ uPos uNeg : CCMArchimedeanFormDomain a,
      0 < (inner ℂ (ccmPrimeTransportOperator a p (ccmArchimedeanFormToAperture a uPos))
          (ccmArchimedeanFormToAperture a uPos)).re ∧
        (inner ℂ (ccmPrimeTransportOperator a p (ccmArchimedeanFormToAperture a uNeg))
          (ccmArchimedeanFormToAperture a uNeg)).re < 0 := by
  have hlogp : 0 < Real.log p := lt_trans (by norm_num) (half_lt_log_of_two_le hp)
  set h₀ : ℝ := Real.log p / 2
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  set r : ℝ := min (Real.log p / 8) ((a.1 - h₀) / 2)
  have hr : 0 < r := lt_min (by positivity) (by linarith)
  have hr1 : r ≤ Real.log p / 8 := min_le_left _ _
  have hr2 : r ≤ (a.1 - h₀) / 2 := min_le_right _ _
  let a_small : SuzukiPositiveAperture := ⟨2 * r, by positivity⟩
  have hc₀ : Metric.closedBall (0 : ℝ) r ⊆ Ioo (-a_small.1) a_small.1 := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    change -(2 * r) < x ∧ x < 2 * r
    constructor <;> linarith [hx.1, hx.2]
  set w₀ := (bumpInteriorSource a_small 0 r hr hc₀).toCCMFormVector
  set f₀ := ccmArchimedeanFormToAperture a_small w₀
  have hf₀_ne : f₀ ≠ 0 := bumpFormVector_aperture_ne_zero a_small r hr hc₀
  have hf₀_norm : 0 < ‖(f₀ : SoninL2)‖ ^ 2 := by
    have : (f₀ : SoninL2) ≠ 0 := Subtype.coe_ne_coe.mpr hf₀_ne
    exact sq_pos_of_pos (norm_pos_iff.mpr this)
  have habPos : a_small.1 + |h₀| ≤ a.1 := by
    rw [abs_of_pos hh₀]; change 2 * r + h₀ ≤ a.1; linarith
  have habNeg : a_small.1 + |-h₀| ≤ a.1 := by
    rw [abs_neg, abs_of_pos hh₀]; change 2 * r + h₀ ≤ a.1; linarith
  set uPos := ccmArchimedeanFormTranslate (-h₀) habNeg w₀ +
    ccmArchimedeanFormTranslate h₀ habPos w₀
  set uNeg := ccmArchimedeanFormTranslate (-h₀) habNeg w₀ -
    ccmArchimedeanFormTranslate h₀ habPos w₀
  set fPos := ccmArchimedeanFormToAperture a uPos
  set fNeg := ccmArchimedeanFormToAperture a uNeg
  have hfPos_coe : (fPos : SoninL2) = logTranslationCLM (-h₀) f₀.1 + logTranslationCLM h₀ f₀.1 := by
    change ((ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormTranslate (-h₀) habNeg w₀ +
        ccmArchimedeanFormTranslate h₀ habPos w₀) : suzukiApertureHilbert a) : SoninL2) = _
    rw [map_add, Submodule.coe_add, ccmArchimedeanFormTranslate_physical,
      ccmArchimedeanFormTranslate_physical]
  have hfNeg_coe : (fNeg : SoninL2) = logTranslationCLM (-h₀) f₀.1 - logTranslationCLM h₀ f₀.1 := by
    change ((ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormTranslate (-h₀) habNeg w₀ -
        ccmArchimedeanFormTranslate h₀ habPos w₀) : suzukiApertureHilbert a) : SoninL2) = _
    rw [map_sub, Submodule.coe_sub, ccmArchimedeanFormTranslate_physical,
      ccmArchimedeanFormTranslate_physical]
  have hz1 : inner ℂ (logTranslationCLM (Real.log p + -h₀ - -h₀) f₀.1) f₀.1 = 0 :=
    inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a_small f₀ f₀ (by
      rw [show Real.log p + -h₀ - -h₀ = Real.log p by ring, abs_of_pos hlogp]
      change 2 * (2 * r) ≤ Real.log p; linarith)
  have hz2 : inner ℂ (logTranslationCLM (Real.log p + h₀ - -h₀) f₀.1) f₀.1 = 0 :=
    inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a_small f₀ f₀ (by
      have h2p : Real.log p + h₀ - -h₀ = 2 * Real.log p := by dsimp [h₀]; ring
      rw [h2p, abs_of_pos (by positivity)]
      change 2 * (2 * r) ≤ 2 * Real.log p; linarith)
  have hz3 : inner ℂ (logTranslationCLM (Real.log p + h₀ - h₀) f₀.1) f₀.1 = 0 :=
    inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a_small f₀ f₀ (by
      rw [show Real.log p + h₀ - h₀ = Real.log p by ring, abs_of_pos hlogp]
      change 2 * (2 * r) ≤ Real.log p; linarith)
  have hmid : inner ℂ (logTranslationCLM (Real.log p) (logTranslationCLM (-h₀) f₀.1))
      (logTranslationCLM h₀ f₀.1) = ((‖f₀.1‖ ^ 2 : ℝ) : ℂ) := by
    have hh : Real.log p + -h₀ = h₀ := by dsimp [h₀]; ring
    rw [logTranslationCLM_add_apply, hh, inner_logTranslationCLM_map_map h₀ f₀.1 f₀.1,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpos_shift : inner ℂ (logTranslationCLM (Real.log p) fPos.1) fPos.1 =
      ((‖f₀.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [hfPos_coe, map_add, inner_add_left, inner_add_right, inner_add_right,
      inner_logTranslation_two_shifts (Real.log p) (-h₀) (-h₀), hz1,
      hmid,
      inner_logTranslation_two_shifts (Real.log p) h₀ (-h₀), hz2,
      inner_logTranslation_two_shifts (Real.log p) h₀ h₀, hz3]
    ring
  have hneg_shift : inner ℂ (logTranslationCLM (Real.log p) fNeg.1) fNeg.1 =
      -((‖f₀.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [hfNeg_coe, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_logTranslation_two_shifts (Real.log p) (-h₀) (-h₀), hz1,
      hmid,
      inner_logTranslation_two_shifts (Real.log p) h₀ (-h₀), hz2,
      inner_logTranslation_two_shifts (Real.log p) h₀ h₀, hz3]
    ring
  have hpos_symm : inner ℂ (logTranslationCLM (-Real.log p) fPos.1) fPos.1 =
      ((‖f₀.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_logTranslationCLM (-Real.log p), neg_neg, ← inner_conj_symm, hpos_shift,
      Complex.conj_ofReal]
  have hneg_symm : inner ℂ (logTranslationCLM (-Real.log p) fNeg.1) fNeg.1 =
      -((‖f₀.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_logTranslationCLM (-Real.log p), neg_neg, ← inner_conj_symm, hneg_shift,
      map_neg, Complex.conj_ofReal]
  have hsqrt_pos : 0 < 1 / Real.sqrt p := by
    have : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
    positivity
  refine ⟨uPos, uNeg, ?_, ?_⟩
  · rw [inner_ccmPrimeTransportOperator, hpos_shift, hpos_symm]
    have hval : (((1 / Real.sqrt p : ℝ) : ℂ) * (((‖f₀.1‖ ^ 2 : ℝ) : ℂ) + ((‖f₀.1‖ ^ 2 : ℝ) : ℂ))).re =
        (1 / Real.sqrt p) * (2 * ‖f₀.1‖ ^ 2) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    rw [hval]
    positivity
  · rw [inner_ccmPrimeTransportOperator, hneg_shift, hneg_symm]
    have hval : (((1 / Real.sqrt p : ℝ) : ℂ) * (-((‖f₀.1‖ ^ 2 : ℝ) : ℂ) + -((‖f₀.1‖ ^ 2 : ℝ) : ℂ))).re =
        -((1 / Real.sqrt p) * (2 * ‖f₀.1‖ ^ 2)) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    rw [hval]
    linarith [mul_pos hsqrt_pos (by positivity : 0 < 2 * ‖f₀.1‖ ^ 2)]

theorem not_isPositive_ccmPrimeTransportOperator {p : ℕ} (hp : 2 ≤ p)
    {a : SuzukiPositiveAperture} (ha : Real.log p / 2 < a.1) :
    ¬ ContinuousLinearMap.IsPositive (ccmPrimeTransportOperator a p) := by
  intro hpos
  obtain ⟨_, uNeg, _, hneg⟩ := exists_pos_and_neg_ccmPrimeTransportOperator hp ha
  have hge := hpos.2 (ccmArchimedeanFormToAperture a uNeg)
  rw [ContinuousLinearMap.reApplyInnerSelf] at hge
  change 0 ≤ (inner ℂ (ccmPrimeTransportOperator a p (ccmArchimedeanFormToAperture a uNeg))
    (ccmArchimedeanFormToAperture a uNeg)).re at hge
  linarith

theorem not_isPositive_neg_ccmPrimeTransportOperator {p : ℕ} (hp : 2 ≤ p)
    {a : SuzukiPositiveAperture} (ha : Real.log p / 2 < a.1) :
    ¬ ContinuousLinearMap.IsPositive (-ccmPrimeTransportOperator a p) := by
  intro hpos
  obtain ⟨uPos, _, hgt, _⟩ := exists_pos_and_neg_ccmPrimeTransportOperator hp ha
  have hge := hpos.2 (ccmArchimedeanFormToAperture a uPos)
  rw [ContinuousLinearMap.reApplyInnerSelf, clm_neg_apply, inner_neg_left] at hge
  change 0 ≤ -(inner ℂ (ccmPrimeTransportOperator a p (ccmArchimedeanFormToAperture a uPos))
    (ccmArchimedeanFormToAperture a uPos)).re at hge
  linarith

/-- On `(½ log 2, ½ log 3]`, neither `ccmFinitePrimeOperator a` nor `-ccmFinitePrimeOperator a` is
a positive operator on `suzukiApertureHilbert a`. -/
theorem neither_sign_isPositive_ccmFinitePrimeOperator_primeTwo_window
    {a : SuzukiPositiveAperture} (ha2 : Real.log 2 / 2 < a.1) (ha3 : a.1 ≤ Real.log 3 / 2) :
    ¬ ContinuousLinearMap.IsPositive (ccmFinitePrimeOperator a) ∧
      ¬ ContinuousLinearMap.IsPositive (-ccmFinitePrimeOperator a) := by
  have hlog2 : 0 < Real.log 2 := lt_trans (by norm_num) half_lt_log_two
  obtain ⟨uPos, uNeg, hgt, hlt⟩ :=
    exists_pos_and_neg_ccmPrimeTransportOperator (by norm_num : 2 ≤ 2) (by simpa using ha2)
  rw [ccmFinitePrimeOperator_eq_primeTwo_of_le_halfLogThree ha3]
  constructor
  · intro hpos
    have hge := hpos.2 (ccmArchimedeanFormToAperture a uNeg)
    rw [ContinuousLinearMap.reApplyInnerSelf, clm_smul_apply, inner_smul_left,
      Complex.conj_ofReal] at hge
    change 0 ≤ ((Real.log 2 : ℂ) *
      inner ℂ (ccmPrimeTransportOperator a 2 (ccmArchimedeanFormToAperture a uNeg))
        (ccmArchimedeanFormToAperture a uNeg)).re at hge
    rw [Complex.re_ofReal_mul] at hge
    nlinarith
  · intro hpos
    have hge := hpos.2 (ccmArchimedeanFormToAperture a uPos)
    rw [ContinuousLinearMap.reApplyInnerSelf, clm_neg_apply,
      clm_smul_apply, inner_neg_left, inner_smul_left, Complex.conj_ofReal] at hge
    change 0 ≤ -((Real.log 2 : ℂ) *
      inner ℂ (ccmPrimeTransportOperator a 2 (ccmArchimedeanFormToAperture a uPos))
        (ccmArchimedeanFormToAperture a uPos)).re at hge
    rw [Complex.re_ofReal_mul] at hge
    nlinarith

/-- **Multiplicative pure-tensor factorization no-go on `(½ log 2, ½ log 3]`.**
At every aperture in `(½ log 2, ½ log 3]` (in particular `halfLogThreeAperture`), the restricted
Weil quadratic form is neither a scalar multiple `c * primeFreeFamily.Q a u` nor a product
`primeFreeFamily.Q a u * τ₂ u` with any positive-degree homogeneous functional `τ₂`. -/
theorem no_multiplicative_tensor_factorization_primeTwo_window
    {a : SuzukiPositiveAperture} (ha2 : Real.log 2 / 2 < a.1) (ha3 : a.1 ≤ Real.log 3 / 2) :
    (¬ ∃ c : ℝ, ∀ u : CCMArchimedeanFormDomain a,
      ccmRestrictedWeilSourceQuadratic a u = primeFreeFamily.Q a u * c) ∧
    (¬ ∃ (d : ℕ) (τ₂ : CCMArchimedeanFormDomain a → ℝ),
      1 ≤ d ∧
      (∀ (t : ℝ) (u : CCMArchimedeanFormDomain a), τ₂ ((t : ℂ) • u) = |t| ^ (2 * d) * τ₂ u) ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u = primeFreeFamily.Q a u * τ₂ u) := by
  obtain ⟨δ, hδ, hpos_small⟩ := exists_small_aperture_primeFree_energy_pos
  have hlog2 : 0 < Real.log 2 := lt_trans (by norm_num) half_lt_log_two
  let a_tiny : SuzukiPositiveAperture :=
    ⟨min (δ / 2) (Real.log 2 / 4), lt_min (by positivity) (by positivity)⟩
  have htiny_le_a : a_tiny.1 ≤ a.1 := le_trans (min_le_right _ _) (by linarith)
  have htiny_le_log2 : a_tiny.1 ≤ Real.log 2 / 2 := le_trans (min_le_right _ _) (by linarith)
  have htiny_lt_δ : a_tiny.1 < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set u_tiny := primeFreeFamily.normalizedGround a_tiny
  obtain ⟨u₀, hu₀_val⟩ := exists_ccmArchimedeanFormDomain_extension htiny_le_a u_tiny
  have hu₀_pf : primeFreeFamily.Q a u₀ = primeFreeFamily.energy a_tiny := by
    rw [primeFreeFamily.Q_eq_of_val_eq htiny_le_a hu₀_val, primeFreeFamily.normalizedGround_Q]
  have hu₀_lit : ccmRestrictedWeilSourceQuadratic a u₀ = primeFreeFamily.energy a_tiny := by
    rw [← primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree ha3 u₀,
      (primeSingleSemilocalFamily 2).Q_eq_of_val_eq htiny_le_a hu₀_val,
      primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree
        (le_trans htiny_le_a ha3) u_tiny,
      ← primeFreeFamily_Q_eq_literal_of_le_halfLogTwo htiny_le_log2 u_tiny,
      primeFreeFamily.normalizedGround_Q]
  have henergy_pos : 0 < primeFreeFamily.energy a_tiny := hpos_small a_tiny htiny_lt_δ
  constructor
  · rintro ⟨c, hc⟩
    have hc1 : c = 1 := by
      have h0 := hc u₀
      rw [hu₀_lit, hu₀_pf] at h0
      nlinarith
    subst hc1
    obtain ⟨uPos, _, hgt, _⟩ :=
      exists_pos_and_neg_ccmPrimeTransportOperator (by norm_num : 2 ≤ 2) (by simpa using ha2)
    have heq := hc uPos
    rw [mul_one] at heq
    have hdiff : primeFreeFamily.Q a uPos = ccmRestrictedWeilSourceQuadratic a uPos +
        (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a uPos))
          (ccmArchimedeanFormToAperture a uPos)).re := by
      rw [CCMRemainderFamily.Q_eq_form_re, ← ccmRestrictedWeilForm_self_re_eq_source]
      show (inner ℂ uPos uPos + inner ℂ (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a uPos) +
        ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a uPos))
        (ccmArchimedeanFormToAperture a uPos)).re = _
      rw [inner_add_left, ← add_assoc, Complex.add_re]
      rfl
    rw [ccmFinitePrimeOperator_eq_primeTwo_of_le_halfLogThree ha3,
      clm_smul_apply, inner_smul_left, Complex.conj_ofReal] at hdiff
    have hre : (((Real.log 2 : ℂ) * inner ℂ (ccmPrimeTransportOperator a 2
        (ccmArchimedeanFormToAperture a uPos)) (ccmArchimedeanFormToAperture a uPos))).re =
        Real.log 2 * (inner ℂ (ccmPrimeTransportOperator a 2
          (ccmArchimedeanFormToAperture a uPos)) (ccmArchimedeanFormToAperture a uPos)).re :=
      Complex.re_ofReal_mul _ _
    nlinarith
  · rintro ⟨d, τ₂, hd, hhom, hfac⟩
    have h1 := hfac u₀
    have h2 := hfac (((2 : ℝ) : ℂ) • u₀)
    rw [← primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree ha3,
      (primeSingleSemilocalFamily 2).Q_smul,
      primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree ha3,
      primeFreeFamily.Q_smul, hhom 2 u₀] at h2
    have hnorm2 : ‖((2 : ℝ) : ℂ)‖ ^ 2 = 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
    have habs2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [hu₀_lit, hu₀_pf] at h1
    rw [hnorm2, habs2, hu₀_lit, hu₀_pf] at h2
    have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * d) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (2 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hτ_one : τ₂ u₀ = 1 := by nlinarith
    rw [hτ_one, mul_one] at h2
    nlinarith

/-! ## 4. Half-integer prime-lattice collapse and forced zero crossings -/

theorem ccmPrimeFreeRemainder_eq_scalar_add_polar (a : SuzukiPositiveAperture) :
    ccmPrimeFreeRemainder a = ccmArchimedeanRemainderScalar • 1 + ccmPolarOperator a := by
  unfold ccmPrimeFreeRemainder ccmRestrictedWeilBoundedRemainder
  exact sub_add_cancel _ _

theorem ccmPrimePowerOperator_eq_zero_of_le_halfLogTwo (p : ℕ) {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 2 / 2) :
    ccmPrimePowerOperator p a = 0 := by
  unfold ccmPrimePowerOperator
  refine Finset.sum_eq_zero fun m _ => ?_
  unfold ccmVisiblePrimeBlock
  split_ifs with hmem
  · have hp2 : 2 ≤ p ^ m := (Finset.mem_Icc.mp hmem).1
    have hlog : Real.log 2 ≤ Real.log ((p ^ m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a (by linarith), clm_smul_zero]
  · rfl

theorem ccmPrimePowerOperator_of_lt_two {p : ℕ} (hp : p < 2) (a : SuzukiPositiveAperture) :
    ccmPrimePowerOperator p a = 0 := by
  unfold ccmPrimePowerOperator
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hnotMem : p ^ m ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
    intro hmem
    have hp2 : 2 ≤ p ^ m := (Finset.mem_Icc.mp hmem).1
    match p with
    | 0 => rw [zero_pow (by omega)] at hp2; omega
    | 1 => rw [one_pow] at hp2; omega
  exact ccmVisiblePrimeBlock_of_invisible a hnotMem

theorem primeSingleSemilocalFamily_energy_eq_primeFree_of_le_halfLogTwo (p : ℕ)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 2 / 2) :
    (primeSingleSemilocalFamily p).energy a = primeFreeFamily.energy a := by
  have he : (primeSingleSemilocalFamily p).B a = ccmRestrictedWeilBoundedRemainder a := by
    change ccmPrimeFreeRemainder a - ccmPrimePowerOperator p a = _
    rw [ccmPrimePowerOperator_eq_zero_of_le_halfLogTwo p ha, sub_zero,
      ccmPrimeFreeRemainder_eq_literal_of_le_halfLogTwo ha]
  rw [ccmRemainderFamily_energy_eq_literal_of_B_eq (primeSingleSemilocalFamily p) a he,
    primeFreeFamily_energy_eq_literal_of_le_halfLogTwo ha]

private theorem clm_zero_apply {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (x : E) :
    (0 : E →L[ℂ] F) x = 0 := rfl

theorem re_inner_ccmPrimePowerOperator_eq_zero_of_transport_zero
    (q : ℕ) (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (hzero : ∀ k : ℕ, 1 ≤ k → inner ℂ (ccmPrimeTransportOperator a (q ^ k) f) f = 0) :
    (inner ℂ (ccmPrimePowerOperator q a f) f).re = 0 := by
  have hterm_zero : ∀ k ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
      (inner ℂ (ccmVisiblePrimeBlock a (q ^ k) f) f).re = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    unfold ccmVisiblePrimeBlock
    split_ifs
    · rw [clm_smul_apply, inner_smul_left, hzero k hk1, mul_zero, Complex.zero_re]
    · rw [clm_zero_apply, inner_zero_left, Complex.zero_re]
  unfold ccmPrimePowerOperator
  revert hterm_zero
  generalize Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))) = s
  intro hterm_zero
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, clm_zero_apply, inner_zero_left, Complex.zero_re]
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk, clm_add_apply, inner_add_left, Complex.add_re,
        hterm_zero k (Finset.mem_insert_self k s),
        ih (fun m hm => hterm_zero m (Finset.mem_insert_of_mem hm)), add_zero]

theorem primeFreeFamily_Q_expand (a : SuzukiPositiveAperture) (v : CCMArchimedeanFormDomain a) :
    primeFreeFamily.Q a v =
      ‖v‖ ^ 2 +
        (ccmArchimedeanRemainderScalar *
          inner ℂ (ccmArchimedeanFormToAperture a v) (ccmArchimedeanFormToAperture a v)).re +
        (inner ℂ (ccmPolarOperator a (ccmArchimedeanFormToAperture a v))
          (ccmArchimedeanFormToAperture a v)).re := by
  unfold CCMRemainderFamily.Q CCMRemainderFamily.diagonal
  change ‖v‖ ^ 2 +
    (inner ℂ (ccmPrimeFreeRemainder a (ccmArchimedeanFormToAperture a v))
      (ccmArchimedeanFormToAperture a v)).re = _
  rw [ccmPrimeFreeRemainder_eq_scalar_add_polar, clm_add_apply, clm_smul_apply, clm_one_apply,
    inner_add_left, inner_smul_left, star_ccmArchimedeanRemainderScalar, Complex.add_re]
  ring

theorem primeSingleSemilocalFamily_Q_eq_primeFree_sub (p : ℕ) (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    (primeSingleSemilocalFamily p).Q a v =
      primeFreeFamily.Q a v -
        (inner ℂ (ccmPrimePowerOperator p a (ccmArchimedeanFormToAperture a v))
          (ccmArchimedeanFormToAperture a v)).re := by
  unfold CCMRemainderFamily.Q CCMRemainderFamily.diagonal
  change ‖v‖ ^ 2 +
    (inner ℂ ((ccmPrimeFreeRemainder a - ccmPrimePowerOperator p a)
      (ccmArchimedeanFormToAperture a v)) (ccmArchimedeanFormToAperture a v)).re =
    ‖v‖ ^ 2 +
      (inner ℂ (ccmPrimeFreeRemainder a (ccmArchimedeanFormToAperture a v))
        (ccmArchimedeanFormToAperture a v)).re - _
  rw [clm_sub_apply, inner_sub_left, Complex.sub_re]
  ring

/-- **Simultaneous prime-power evasion and unbounded negative ground energy.**
Along the half-integer lattice `L_M = ((2M + 1)/4) log p` (`p ≥ 2`), an antisymmetric translated
centre bump annihilates every prime-power shift `p^k` (`k ≥ 1`) simultaneously while driving the
polar form below any real bound `K`. Consequently both `primeFreeFamily.energy` and
`(primeSingleSemilocalFamily p).energy` tend to `-∞` as the aperture grows. -/
theorem exists_aperture_primeFree_and_singleSemilocal_energy_lt (p : ℕ) (K : ℝ) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ b : SuzukiPositiveAperture, A₀ ≤ b.1 →
      primeFreeFamily.energy b < K ∧ (primeSingleSemilocalFamily p).energy b < K := by
  obtain ⟨q, hq_def⟩ : ∃ q : ℕ, q = max p 2 := ⟨_, rfl⟩
  have hq : 2 ≤ q := by rw [hq_def]; exact le_max_right p 2
  have hlogq_half : (1 / 2 : ℝ) < Real.log q := half_lt_log_of_two_le hq
  have hlogq : 0 < Real.log q := lt_trans (by norm_num) hlogq_half
  let a₀ : SuzukiPositiveAperture := ⟨1 / 16, by norm_num⟩
  have hr₀ : (0 : ℝ) < 1 / 32 := by norm_num
  have hc₀ : Metric.closedBall (0 : ℝ) (1 / 32) ⊆ Ioo (-a₀.1) a₀.1 := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    change -(1 / 16 : ℝ) < x ∧ x < 1 / 16
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : CCMArchimedeanFormDomain a₀,
      u₀ = (bumpInteriorSource a₀ 0 (1 / 32) hr₀ hc₀).toCCMFormVector := ⟨_, rfl⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : suzukiApertureHilbert a₀,
      f₀ = ccmArchimedeanFormToAperture a₀ u₀ := ⟨_, rfl⟩
  have hf₀_ne : f₀ ≠ 0 := by
    rw [hf₀, hu₀]
    exact bumpFormVector_aperture_ne_zero a₀ (1 / 32) hr₀ hc₀
  have hf₀_pos : 0 < ‖f₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf₀_ne)
  obtain ⟨mPos, hmPos_def⟩ : ∃ mPos : ℝ, mPos = polarBumpMoment 0 (1 / 32) hr₀ (1 / 2) := ⟨_, rfl⟩
  obtain ⟨mNeg, hmNeg_def⟩ : ∃ mNeg : ℝ, mNeg = polarBumpMoment 0 (1 / 32) hr₀ (-1 / 2) := ⟨_, rfl⟩
  have hmPos : 0 < mPos := by
    rw [hmPos_def]
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (polarBumpMass_pos 0 (1 / 32) hr₀))
      (le_polarBumpMoment 0 (1 / 32) hr₀ (1 / 2))
  have hmNeg : 0 < mNeg := by
    rw [hmNeg_def]
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (polarBumpMass_pos 0 (1 / 32) hr₀))
      (le_polarBumpMoment 0 (1 / 32) hr₀ (-1 / 2))
  have hmprod : 0 < mPos * mNeg := mul_pos hmPos hmNeg
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ,
      C₀ = 4 * ‖u₀‖ ^ 2 + |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨target, htarget_def⟩ : ∃ target : ℝ,
      target = max 1 ((C₀ - K * (2 * ‖f₀‖ ^ 2) + 1) / (2 * (mPos * mNeg))) := ⟨_, rfl⟩
  have htarget_pos : 0 < target := by
    rw [htarget_def]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * Real.sqrt target / Real.log q)
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = ((2 * (M : ℝ) + 1) / 4) * Real.log q := ⟨_, rfl⟩
  have hL_pos : 0 < L := by
    rw [hL_def]
    have : 0 < (2 * (M : ℝ) + 1) / 4 := by positivity
    exact mul_pos this hlogq
  have hL_ge : (1 / 4 : ℝ) * Real.log q ≤ L := by
    rw [hL_def]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have : (1 / 4 : ℝ) ≤ (2 * (M : ℝ) + 1) / 4 := by linarith
    exact mul_le_mul_of_nonneg_right this hlogq.le
  let b₀ : SuzukiPositiveAperture := ⟨a₀.1 + L, by linarith [a₀.2]⟩
  have habPos : a₀.1 + |L| ≤ b₀.1 := by rw [abs_of_pos hL_pos]
  have habNeg : a₀.1 + |-L| ≤ b₀.1 := by rw [abs_neg, abs_of_pos hL_pos]
  obtain ⟨v, hv⟩ : ∃ v : CCMArchimedeanFormDomain b₀,
      v = ccmArchimedeanFormTranslate (-L) habNeg u₀ - ccmArchimedeanFormTranslate L habPos u₀ :=
    ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : suzukiApertureHilbert b₀,
      f = ccmArchimedeanFormToAperture b₀ v := ⟨_, rfl⟩
  have hf_coe : (f : SoninL2) = logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1 := by
    rw [hf, hv, map_sub, Submodule.coe_sub, ccmArchimedeanFormTranslate_physical,
      ccmArchimedeanFormTranslate_physical, ← hf₀]
  -- Exact orthogonality of the two shifted packets gives `‖f‖^2 = 2 ‖f₀‖^2`.
  have horth : inner ℂ (logTranslationCLM (-L) f₀.1) (logTranslationCLM L f₀.1) = 0 := by
    rw [inner_logTranslationCLM (-L), neg_neg, logTranslationCLM_add_apply]
    refine inner_eq_zero_symm.mpr (inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ ?_)
    rw [abs_of_pos (by linarith)]
    change 2 * (1 / 16 : ℝ) ≤ L + L
    linarith
  have hf_norm_sq : ‖f‖ ^ 2 = 2 * ‖f₀‖ ^ 2 := by
    have horth' : inner ℂ (logTranslationCLM L f₀.1) (logTranslationCLM (-L) f₀.1) = 0 :=
      inner_eq_zero_symm.mpr horth
    have hcoe_norm : ‖f‖ = ‖(f : SoninL2)‖ := rfl
    have hcoe_norm₀ : ‖f₀‖ = ‖(f₀ : SoninL2)‖ := rfl
    rw [hcoe_norm, hcoe_norm₀, hf_coe]
    have h1 : ‖logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1‖ ^ 2 =
        (inner ℂ (logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1)
          (logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1)).re :=
      (CCMRemainderFamily.re_inner_self _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, horth, horth',
      sub_zero, zero_sub, sub_neg_eq_add, Complex.add_re,
      CCMRemainderFamily.re_inner_self, CCMRemainderFamily.re_inner_self,
      norm_logTranslationCLM (-L), norm_logTranslationCLM L]
    ring
  -- Every positive power `q^k` (`k ≥ 1`) pairs to zero against `f`.
  have hprime_zero : ∀ k : ℕ, 1 ≤ k →
      inner ℂ (ccmPrimeTransportOperator b₀ (q ^ k) f) f = 0 := by
    intro k hk
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = Real.log ((q ^ k : ℕ) : ℝ) := ⟨_, rfl⟩
    have hh_eq : h = (k : ℝ) * Real.log q := by
      rw [hh_def, Nat.cast_pow, Real.log_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hh_gt : (1 / 2 : ℝ) < h := by
      rw [hh_eq]
      calc (1 / 2 : ℝ) < 1 * Real.log q := by linarith
        _ ≤ (k : ℝ) * Real.log q := mul_le_mul_of_nonneg_right hk1 hlogq.le
    have hshift_zero : inner ℂ (logTranslationCLM h f.1) f.1 = 0 := by
      rw [hf_coe, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
        inner_logTranslation_two_shifts h (-L) (-L),
        inner_logTranslation_two_shifts h (-L) L,
        inner_logTranslation_two_shifts h L (-L),
        inner_logTranslation_two_shifts h L L]
      have z1 : inner ℂ (logTranslationCLM (h + -L - -L) f₀.1) f₀.1 = 0 :=
        inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
          rw [show h + -L - -L = h by ring, abs_of_pos (lt_trans (by norm_num) hh_gt)]
          change 2 * (1 / 16 : ℝ) ≤ h; linarith)
      have z2 : inner ℂ (logTranslationCLM (h + -L - L) f₀.1) f₀.1 = 0 := by
        refine inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ ?_
        have hodd_ne : (2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) ≠ 0 := by omega
        have hodd_abs : (1 : ℝ) ≤ |((2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) : ℝ)| := by
          exact_mod_cast Int.one_le_abs hodd_ne
        have hdiff_eq : h + -L - L =
            (((2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) : ℝ) / 2) * Real.log q := by
          rw [hh_eq, hL_def]; push_cast; ring
        rw [hdiff_eq, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hlogq]
        change 2 * (1 / 16 : ℝ) ≤ |((2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) : ℝ)| / 2 * Real.log q
        have hge1 : (1 / 2 : ℝ) * Real.log q ≤
            |((2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) : ℝ)| / 2 * Real.log q := by
          have : (1 / 2 : ℝ) ≤ |((2 * (k : ℤ) - 2 * (M : ℤ) - 1 : ℤ) : ℝ)| / 2 := by linarith
          exact mul_le_mul_of_nonneg_right this hlogq.le
        linarith
      have z3 : inner ℂ (logTranslationCLM (h + L - -L) f₀.1) f₀.1 = 0 :=
        inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
          rw [abs_of_pos (by linarith)]
          change 2 * (1 / 16 : ℝ) ≤ h + L - -L; linarith)
      have z4 : inner ℂ (logTranslationCLM (h + L - L) f₀.1) f₀.1 = 0 :=
        inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
          rw [show h + L - L = h by ring, abs_of_pos (lt_trans (by norm_num) hh_gt)]
          change 2 * (1 / 16 : ℝ) ≤ h; linarith)
      rw [z1, z2, z3, z4]
      ring
    have hneg_zero : inner ℂ (logTranslationCLM (-h) f.1) f.1 = 0 := by
      rw [inner_logTranslationCLM (-h), neg_neg]
      exact inner_eq_zero_symm.mpr hshift_zero
    rw [inner_ccmPrimeTransportOperator, ← hh_def, hshift_zero, hneg_zero, add_zero, mul_zero]
  have hpower_re_zero : (inner ℂ (ccmPrimePowerOperator q b₀ f) f).re = 0 :=
    re_inner_ccmPrimePowerOperator_eq_zero_of_transport_zero q b₀ f hprime_zero
  -- Polar evaluation on `v` gives `-2 (e^{L/2} - e^{-L/2})^2 mPos mNeg`.
  have hpol₀_plus : inner ℂ (ccmPolarApertureVector a₀ (1 / 2)) f₀ = (mPos : ℂ) := by
    rw [hf₀, hu₀, hmPos_def]
    exact inner_polar_bumpInteriorSource a₀ 0 (1 / 32) hr₀ hc₀ (1 / 2)
  have hpol₀_minus : inner ℂ (ccmPolarApertureVector a₀ (-1 / 2)) f₀ = (mNeg : ℂ) := by
    rw [hf₀, hu₀, hmNeg_def]
    exact inner_polar_bumpInteriorSource a₀ 0 (1 / 32) hr₀ hc₀ (-1 / 2)
  have hpol_plus : inner ℂ (ccmPolarApertureVector b₀ (1 / 2)) f =
      (((Real.exp (L / 2) - Real.exp (-L / 2)) * mPos : ℝ) : ℂ) := by
    rw [hf, hv, map_sub, inner_sub_right,
      inner_polar_ccmArchimedeanFormTranslate (-L) habNeg (1 / 2) u₀,
      inner_polar_ccmArchimedeanFormTranslate L habPos (1 / 2) u₀,
      ← hf₀, hpol₀_plus]
    have h1 : -(1 / 2 : ℝ) * -L = L / 2 := by ring
    have h2 : -(1 / 2 : ℝ) * L = -L / 2 := by ring
    rw [h1, h2]
    push_cast
    ring
  have hpol_minus : inner ℂ (ccmPolarApertureVector b₀ (-1 / 2)) f =
      (((Real.exp (-L / 2) - Real.exp (L / 2)) * mNeg : ℝ) : ℂ) := by
    rw [hf, hv, map_sub, inner_sub_right,
      inner_polar_ccmArchimedeanFormTranslate (-L) habNeg (-1 / 2) u₀,
      inner_polar_ccmArchimedeanFormTranslate L habPos (-1 / 2) u₀,
      ← hf₀, hpol₀_minus]
    have h1 : -(-1 / 2 : ℝ) * -L = -L / 2 := by ring
    have h2 : -(-1 / 2 : ℝ) * L = L / 2 := by ring
    rw [h1, h2]
    push_cast
    ring
  have hpol_re : (inner ℂ (ccmPolarOperator b₀ f) f).re =
      -2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
    rw [inner_ccmPolarOperator, hpol_plus, hpol_minus, Complex.conj_ofReal, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  -- Bound `primeFreeFamily.Q b₀ v` and `(primeSingleSemilocalFamily p).Q b₀ v`.
  have hv_norm : ‖v‖ ^ 2 ≤ 4 * ‖u₀‖ ^ 2 := by
    have htri : ‖v‖ ≤ 2 * ‖u₀‖ := by
      rw [hv]
      calc ‖ccmArchimedeanFormTranslate (-L) habNeg u₀ -
              ccmArchimedeanFormTranslate L habPos u₀‖
          ≤ ‖ccmArchimedeanFormTranslate (-L) habNeg u₀‖ +
              ‖ccmArchimedeanFormTranslate L habPos u₀‖ := norm_sub_le _ _
        _ = ‖u₀‖ + ‖u₀‖ := by
              rw [norm_ccmArchimedeanFormTranslate, norm_ccmArchimedeanFormTranslate]
        _ = 2 * ‖u₀‖ := by ring
    calc ‖v‖ ^ 2 ≤ (2 * ‖u₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ‖u₀‖ ^ 2 := by ring
  have hscal_le : (ccmArchimedeanRemainderScalar * inner ℂ f f).re ≤
      |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2) := by
    rw [ccmArchimedeanRemainderScalar, Complex.re_ofReal_mul, CCMRemainderFamily.re_inner_self,
      hf_norm_sq]
    calc (2 * gammaHardyPhaseRate 0 - 1) * (2 * ‖f₀‖ ^ 2)
        ≤ |2 * gammaHardyPhaseRate 0 - 1| * (2 * ‖f₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hf₀_pos]) (abs_nonneg _)
  have hQ_pf : primeFreeFamily.Q b₀ v ≤
      C₀ - 2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
    have hform := primeFreeFamily_Q_expand b₀ v
    rw [← hf] at hform
    rw [hform, hpol_re, hC₀]
    linarith only [hv_norm, hscal_le]
  -- Compare `Real.exp (L / 2) - Real.exp (-L / 2)` with `L / 2 > Real.sqrt target`.
  have hexp_ge : L / 2 ≤ Real.exp (L / 2) - Real.exp (-L / 2) := by
    have h1 : L / 2 + 1 ≤ Real.exp (L / 2) := Real.add_one_le_exp (L / 2)
    have h2 : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hL_pos])
    linarith only [h1, h2]
  have hL_half_gt : Real.sqrt target < L / 2 := by
    have hM' : 4 * Real.sqrt target < (M : ℝ) * Real.log q := (div_lt_iff₀ hlogq).mp hM
    have hL_eq : L / 2 = ((2 * (M : ℝ) + 1) / 8) * Real.log q := by rw [hL_def]; ring
    rw [hL_eq]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hcoef : (M : ℝ) * Real.log q < (2 * (M : ℝ) + 1) * Real.log q :=
      mul_lt_mul_of_pos_right (by linarith only [hM0]) hlogq
    linarith only [hM', hcoef]
  have hsq_gt : target < (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
    calc target = Real.sqrt target ^ 2 := (Real.sq_sqrt htarget_pos.le).symm
      _ < (L / 2) ^ 2 := pow_lt_pow_left₀ hL_half_gt (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hexp_ge 2
  have htarget_ge : (C₀ - K * (2 * ‖f₀‖ ^ 2) + 1) / (2 * (mPos * mNeg)) ≤ target := by
    rw [htarget_def]
    exact le_max_right _ _
  have hQ_lt : primeFreeFamily.Q b₀ v < K * ‖f‖ ^ 2 := by
    rw [hf_norm_sq]
    have hmul : C₀ - K * (2 * ‖f₀‖ ^ 2) + 1 <
        2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
      have hpos2 : 0 < 2 * (mPos * mNeg) := by positivity
      have h1 : C₀ - K * (2 * ‖f₀‖ ^ 2) + 1 ≤ target * (2 * (mPos * mNeg)) :=
        (div_le_iff₀ hpos2).mp htarget_ge
      have h2 : target * (2 * (mPos * mNeg)) <
          (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (2 * (mPos * mNeg)) :=
        mul_lt_mul_of_pos_right hsq_gt hpos2
      calc C₀ - K * (2 * ‖f₀‖ ^ 2) + 1
          ≤ target * (2 * (mPos * mNeg)) := h1
        _ < (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (2 * (mPos * mNeg)) := h2
        _ = 2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by ring
    linarith only [hQ_pf, hmul]
  have hnorm_pos : 0 < ‖f‖ ^ 2 := by rw [hf_norm_sq]; positivity
  have henergy_pf_lt : primeFreeFamily.energy b₀ < K := by
    have hray := primeFreeFamily.energy_mul_formNorm_sq_le b₀ v
    rw [← hf] at hray
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hray hQ_lt) hnorm_pos.le
  have henergy_single_lt : (primeSingleSemilocalFamily p).energy b₀ < K := by
    have hsub := primeSingleSemilocalFamily_Q_eq_primeFree_sub p b₀ v
    rw [← hf] at hsub
    have hQeq : (primeSingleSemilocalFamily p).Q b₀ v = primeFreeFamily.Q b₀ v := by
      rcases lt_or_ge p 2 with hp2 | hp2
      · rw [ccmPrimePowerOperator_of_lt_two hp2 b₀, clm_zero_apply, inner_zero_left,
          Complex.zero_re, sub_zero] at hsub
        exact hsub
      · have hqp : q = p := by rw [hq_def]; exact max_eq_left hp2
        rw [← hqp, hpower_re_zero, sub_zero] at hsub
        exact hsub
    have hray := (primeSingleSemilocalFamily p).energy_mul_formNorm_sq_le b₀ v
    rw [← hf, hQeq] at hray
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt hray hQ_lt) hnorm_pos.le
  refine ⟨b₀.1, b₀.2, fun b hb => ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt (primeFreeFamily.energy_antitone hb) henergy_pf_lt
  · exact lt_of_le_of_lt ((primeSingleSemilocalFamily p).energy_antitone hb) henergy_single_lt

/-- **Unconditional zero crossing of `primeFreeFamily`:** there is an aperture `a > 0` at which the
prime-free ground energy vanishes and the prime-free Friedrichs operator has a nonzero kernel. -/
theorem exists_primeFree_zero_crossing :
    ∃ a : SuzukiPositiveAperture, primeFreeFamily.energy a = 0 ∧
      ∃ x : (primeFreeFamily.operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ primeFreeFamily.operator a x = 0 := by
  obtain ⟨δ, hδ, hpos⟩ := exists_small_aperture_primeFree_energy_pos
  obtain ⟨A₀, hA₀, hneg⟩ := exists_aperture_primeFree_and_singleSemilocal_energy_lt 2 (-1)
  let a₀ : SuzukiPositiveAperture := ⟨min (δ / 2) A₀, lt_min (by positivity) hA₀⟩
  let a₁ : SuzukiPositiveAperture := ⟨A₀, hA₀⟩
  have h01 : a₀.1 ≤ a₁.1 := min_le_right _ _
  have h0 : 0 < primeFreeFamily.energy a₀ :=
    hpos a₀ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h1 : primeFreeFamily.energy a₁ < 0 := lt_trans (hneg a₁ le_rfl).1 (by norm_num)
  obtain ⟨a, -, -, hzero⟩ := primeFreeFamily.exists_energy_eq_zero h01 h0 h1
  exact ⟨a, hzero, primeFreeFamily.exists_kernel_of_energy_eq_zero hzero⟩

/-- **Unconditional zero crossing of `primeSingleSemilocalFamily p`:** for every `p : ℕ` (and in
particular `p = 2`), retaining only the powers of `p` still forces an aperture zero crossing with a
nonzero Friedrichs kernel state. -/
theorem exists_primeSingleSemilocal_zero_crossing (p : ℕ) :
    ∃ a : SuzukiPositiveAperture, (primeSingleSemilocalFamily p).energy a = 0 ∧
      ∃ x : ((primeSingleSemilocalFamily p).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ (primeSingleSemilocalFamily p).operator a x = 0 := by
  obtain ⟨δ, hδ, hpos⟩ := exists_small_aperture_primeFree_energy_pos
  have hlog2 : 0 < Real.log 2 := lt_trans (by norm_num) half_lt_log_two
  obtain ⟨A₀, hA₀, hneg⟩ := exists_aperture_primeFree_and_singleSemilocal_energy_lt p (-1)
  let a₀ : SuzukiPositiveAperture :=
    ⟨min (min (δ / 2) (Real.log 2 / 2)) A₀,
      lt_min (lt_min (by positivity) (by positivity)) hA₀⟩
  let a₁ : SuzukiPositiveAperture := ⟨A₀, hA₀⟩
  have h01 : a₀.1 ≤ a₁.1 := min_le_right _ _
  have ha₀_log2 : a₀.1 ≤ Real.log 2 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have ha₀_δ : a₀.1 < δ :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have h0 : 0 < (primeSingleSemilocalFamily p).energy a₀ := by
    rw [primeSingleSemilocalFamily_energy_eq_primeFree_of_le_halfLogTwo p ha₀_log2]
    exact hpos a₀ ha₀_δ
  have h1 : (primeSingleSemilocalFamily p).energy a₁ < 0 :=
    lt_trans (hneg a₁ le_rfl).2 (by norm_num)
  obtain ⟨a, -, -, hzero⟩ := (primeSingleSemilocalFamily p).exists_energy_eq_zero h01 h0 h1
  exact ⟨a, hzero, (primeSingleSemilocalFamily p).exists_kernel_of_energy_eq_zero hzero⟩

/-- Specialized `{∞, 2}` zero crossing: the semilocal `{∞, 2}` Friedrichs operator acquires a
nonzero kernel state at a critical aperture `a > 0` and becomes indefinite beyond it. -/
theorem exists_primeTwoSemilocal_zero_crossing :
    ∃ a : SuzukiPositiveAperture, (primeSingleSemilocalFamily 2).energy a = 0 ∧
      ∃ x : ((primeSingleSemilocalFamily 2).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ (primeSingleSemilocalFamily 2).operator a x = 0 :=
  exists_primeSingleSemilocal_zero_crossing 2

/-- **Impossibility of any positive operator-trace carrier for the `{∞, 2}` semilocal form.**
There is no complex Hilbert space `H` and family `R` of positive operators on `H` whose real
operator trace equals `(primeSingleSemilocalFamily 2).Q a u` for all apertures `a` and form vectors
`u`; in particular no Gram trace `Tr(Ψ(a, u) M Ψ(a, u)†)` with `M ≥ 0` can represent the `{∞, 2}`
semilocal Weil form across apertures. -/
theorem no_positive_operator_trace_carrier_for_primeTwoSemilocal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    ¬ ∃ R : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → (H →L[ℂ] H),
      (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
      (∀ a u, (ContinuousLinearMap.opTrace (R a u)).re = (primeSingleSemilocalFamily 2).Q a u) := by
  rintro ⟨R, hpos, htr⟩
  obtain ⟨A₀, hA₀, hneg⟩ := exists_aperture_primeFree_and_singleSemilocal_energy_lt 2 (-1)
  let b : SuzukiPositiveAperture := ⟨A₀, hA₀⟩
  have hb_neg : (primeSingleSemilocalFamily 2).energy b < 0 :=
    lt_trans (hneg b le_rfl).2 (by norm_num)
  let u := (primeSingleSemilocalFamily 2).normalizedGround b
  have hQ_neg : (primeSingleSemilocalFamily 2).Q b u < 0 := by
    rwa [(primeSingleSemilocalFamily 2).normalizedGround_Q]
  have hge := opTrace_re_nonneg_of_isPositive (hpos b u)
  linarith [htr b u]

theorem no_positive_gram_trace_for_primeTwoSemilocal {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    ¬ ∃ (M : H →L[ℂ] H)
        (Ψ : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → (H →L[ℂ] K)),
      ContinuousLinearMap.IsPositive M ∧
      (∀ a u, (ContinuousLinearMap.opTrace (Ψ a u ∘L M ∘L ContinuousLinearMap.adjoint (Ψ a u))).re =
        (primeSingleSemilocalFamily 2).Q a u) := by
  rintro ⟨M, Ψ, hM, htr⟩
  exact no_positive_operator_trace_carrier_for_primeTwoSemilocal
    ⟨fun a u => Ψ a u ∘L M ∘L ContinuousLinearMap.adjoint (Ψ a u),
      fun a u => isPositive_comp_comp_adjoint hM (Ψ a u), htr⟩

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
