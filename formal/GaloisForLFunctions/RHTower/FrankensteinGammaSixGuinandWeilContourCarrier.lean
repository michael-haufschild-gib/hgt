import GaloisForLFunctions.RHTower.FrankensteinGammaSixFiniteLinearFlowSourceCarrier
import GaloisForLFunctions.RHTower.XiGuinandWeilFiniteHermiteCriterion

/-!
# Frankenstein Gamma-six Guinand--Weil contour carrier

This module closes the coefficient-faithful transport gap between a finite Xi divisor pencil and
an actual source expression. Five independent corpus mechanisms are fused:

* Gamma-six Burnol flow converts horizontal displacement into exponential modulus;
* functional-equation reflection retains an expanding orientation of every off-line class;
* multiplicity-copy packets preserve every analytic divisor coefficient;
* finite exponential-pencil mean-square rigidity excludes phase cancellation at maximal modulus;
* Guinand--Weil rectangle residues identify that same pencil with a continued
  prime--archimedean contour, while cofinal admissible symmetric rectangles retain every Xi zero.

For each admissible symmetric rectangle, subexponentiality of the exact source contour is
equivalent to critical-line placement of every enclosed multiplicity copy. Requiring the source
bound on all such rectangles is therefore equivalent to RH. All results are unconditional; the
remaining open producer is the source-side subexponential bound itself.
-/

open Complex Filter Topology intervalIntegral Set

namespace RHTower

noncomputable section

def sourceHorizontalGammaSixCenteredContourWeight (n : ℕ) (z : ℂ) : ℂ :=
  burnolPrimeCharacter ((6 : ℝ) ^ n) (1 / 2 + z * I)

theorem sourceHorizontalGammaSixCenteredContourWeight_analyticOnNhd (n : ℕ) :
    AnalyticOnNhd ℂ (sourceHorizontalGammaSixCenteredContourWeight n) Set.univ := by
  have h6 : (0 : ℝ) < (6 : ℝ) ^ n := pow_pos (by norm_num) _
  rw [show sourceHorizontalGammaSixCenteredContourWeight n =
      fun z => Complex.exp ((1 / 2 + z * I - 1 / 2) * Real.log ((6 : ℝ) ^ n)) by
    funext z
    rw [sourceHorizontalGammaSixCenteredContourWeight,
      burnolPrimeCharacter_eq_exp _ h6]]
  exact (by fun_prop : Differentiable ℂ
    (fun z => Complex.exp ((1 / 2 + z * I - 1 / 2) * Real.log ((6 : ℝ) ^ n)))).differentiableOn.analyticOnNhd
      isOpen_univ

theorem sourceHorizontalGammaSixCenteredContourWeight_spectralPoint
    (n : ℕ) (q : XiZeroCopy) :
    sourceHorizontalGammaSixCenteredContourWeight n (xiSpectralPoint q) =
      sourceHorizontalGammaSixFlowMode q ^ n := by
  rw [sourceHorizontalGammaSixCenteredContourWeight]
  have hcoord : (1 / 2 : ℂ) + xiSpectralPoint q * I = (q.1 : ℂ) := by
    rw [xiSpectralPoint]
    rw [mul_assoc, show (-I) * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]
    ring
  rw [hcoord]
  have h := burnolPrimeCharacter_mul_gammaSixFlow_pow
    (p := (1 : ℝ)) (by norm_num) (q.1 : ℂ) n
  simpa [sourceHorizontalGammaSixFlowMode, burnolPrimeCharacter] using h.symm

def sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent
    (R c : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => sourceHorizontalGammaSixCenteredContourWeight n z *
        continuedPrimeArchSourceRelativeTrace z)
      (symmetricRectangleLower R c) (symmetricRectangleUpper R c)

theorem sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent_eq_copyPencil
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hadm : XiSymmetricRectangleExplicitAdmissible R c) (n : ℕ) :
    sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent R c n =
      ∑ q ∈ xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
          (symmetricRectangleUpper R c),
        sourceHorizontalGammaSixFlowMode q ^ n := by
  let z₁ := symmetricRectangleLower R c
  let z₂ := symmetricRectangleUpper R c
  have hzre : z₁.re < z₂.re := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hzim : z₁.im < z₂.im := by
    dsimp only [z₁, z₂]
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have hbottom : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₁, symmetricRectangleLower, sub_eq_add_neg] using! hadm.1 x hx'
  have htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I) := by
    intro x hx
    have hx' : x ∈ Set.uIcc (-R) R := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hx
    simpa [z₂, symmetricRectangleUpper] using hadm.2.1 x hx'
  have hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₂, symmetricRectangleUpper] using hadm.2.2.1 y hy'
  have hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I) := by
    intro y hy
    have hy' : y ∈ Set.uIcc (-c) c := by
      simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using hy
    simpa [z₁, symmetricRectangleLower] using hadm.2.2.2 y hy'
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (sourceHorizontalGammaSixCenteredContourWeight_analyticOnNhd n)
      hzre hzim hbottom htop hright hleft
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  change (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral
        (fun z => sourceHorizontalGammaSixCenteredContourWeight n z *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂ = _
  rw [hcontour, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [sourceHorizontalGammaSixCenteredContourWeight_spectralPoint]

/-- Subexponentiality of the exact normalized prime--archimedean contour current. -/
def SourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential
    (R c : ℝ) : Prop :=
  ∀ r : ℝ, 1 < r →
    Tendsto
      (fun n : ℕ =>
        sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent R c n /
          (r : ℂ) ^ n)
      atTop (nhds 0)

/-- Any finite packet supported on the critical line has a subexponential Gamma-six pencil. -/
theorem sourceHorizontalGammaSixFiniteCopyPencilSubexponential_of_onLine
    {P : Finset XiZeroCopy}
    (hline : ∀ q ∈ P, (q.1 : ℂ).re = 1 / 2) :
    ∀ r : ℝ, 1 < r →
      Tendsto
        (fun n : ℕ =>
          (∑ q ∈ P, sourceHorizontalGammaSixFlowMode q ^ n) / (r : ℂ) ^ n)
        atTop (nhds 0) := by
  intro r hr
  have hmode : ∀ q ∈ P, ‖sourceHorizontalGammaSixFlowMode q‖ = 1 := by
    intro q hq
    rw [norm_sourceHorizontalGammaSixFlowMode,
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 (hline q hq)]
    norm_num
  have hbound (n : ℕ) :
      ‖∑ q ∈ P, sourceHorizontalGammaSixFlowMode q ^ n‖ ≤ P.card := by
    calc
      ‖∑ q ∈ P, sourceHorizontalGammaSixFlowMode q ^ n‖ ≤
          ∑ q ∈ P, ‖sourceHorizontalGammaSixFlowMode q ^ n‖ := norm_sum_le _ _
      _ = ∑ _q ∈ P, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [norm_pow, hmode q hq, one_pow]
      _ = P.card := by simp
  apply squeeze_zero_norm'
    (a := fun n : ℕ => (P.card : ℝ) / r ^ n)
  · exact Eventually.of_forall fun n => by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hr)]
      exact div_le_div_of_nonneg_right (hbound n) (pow_nonneg (by linarith) n)
  · have hpow : Tendsto (fun n : ℕ => (r ^ n)⁻¹) atTop (nhds 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hr).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using hpow.const_mul (P.card : ℝ)

/-- Symmetric spectral rectangles retain the critical-line reflection of every copied zero. -/
theorem xiZeroCopyClosedSymmetricRectangle_lineConj_closed
    {R c : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) :
    ∀ q ∈ xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
        (symmetricRectangleUpper R c),
      xiZeroCopyLineConjEquiv q ∈
        xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
          (symmetricRectangleUpper R c) := by
  intro q hq
  rw [mem_xiZeroCopyClosedRectangle] at hq ⊢
  rw [xiSpectralPoint_lineConj]
  apply Complex.mem_reProdIm.mpr
  obtain ⟨hqre, hqim⟩ := Complex.mem_reProdIm.mp hq
  have hre : (symmetricRectangleLower R c).re ≤
      (symmetricRectangleUpper R c).re := by
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have him : (symmetricRectangleLower R c).im ≤
      (symmetricRectangleUpper R c).im := by
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  rw [Set.uIcc_of_le hre] at hqre
  rw [Set.uIcc_of_le him] at hqim
  rw [Set.uIcc_of_le hre, Set.uIcc_of_le him]
  have hqre' : -R ≤ (xiSpectralPoint q).re ∧
      (xiSpectralPoint q).re ≤ R := by
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hqre
  have hqim' : -c ≤ (xiSpectralPoint q).im ∧
      (xiSpectralPoint q).im ≤ c := by
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hqim
  constructor
  · simpa [symmetricRectangleLower, symmetricRectangleUpper] using hqre'
  · have hcj : -c ≤ -(xiSpectralPoint q).im ∧
        -(xiSpectralPoint q).im ≤ c := by
      constructor <;> linarith [hqim'.1, hqim'.2]
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hcj

/-- On an admissible symmetric rectangle, source-contour subexponentiality is equivalent to
critical-line placement of every enclosed multiplicity copy. -/
theorem sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_iff
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hadm : XiSymmetricRectangleExplicitAdmissible R c) :
    SourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential R c ↔
      ∀ q ∈ xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
          (symmetricRectangleUpper R c),
        (q.1 : ℂ).re = 1 / 2 := by
  let P := xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
    (symmetricRectangleUpper R c)
  have hcontour (n : ℕ) :
      sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent R c n =
        ∑ q ∈ P, sourceHorizontalGammaSixFlowMode q ^ n := by
    exact sourceHorizontalGammaSixSymmetricPrimeArchContourCurrent_eq_copyPencil
      hR hc hadm n
  constructor
  · intro hsub q hq
    by_contra hoff
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).not.mpr hoff
    have hout : ∃ q' ∈ P, 1 < ‖sourceHorizontalGammaSixFlowMode q'‖ := by
      rcases lt_or_gt_of_ne hrate with hneg | hpos
      · let qr := xiZeroCopyLineConjEquiv q
        have hqr : qr ∈ P :=
          xiZeroCopyClosedSymmetricRectangle_lineConj_closed hR.le hc.le q hq
        refine ⟨qr, hqr, ?_⟩
        rw [norm_sourceHorizontalGammaSixFlowMode,
          show primeDepthBVWoldXiCenteredRate qr.1 =
            -primeDepthBVWoldXiCenteredRate q.1 by
              exact primeDepthBVWoldXiCenteredRate_reflection q.1]
        exact Real.one_lt_rpow (by norm_num) (by linarith)
      · refine ⟨q, hq, ?_⟩
        rw [norm_sourceHorizontalGammaSixFlowMode]
        exact Real.one_lt_rpow (by norm_num) (by linarith)
    apply (not_subexponential_finiteExponentialPencil_of_expanding_mode
      P sourceHorizontalGammaSixFlowMode hout)
    intro r hr
    have hs := hsub r hr
    convert hs using 1
    funext n
    rw [hcontour n]
    simp [finiteExponentialPencil]
  · intro hline
    intro r hr
    have hs := sourceHorizontalGammaSixFiniteCopyPencilSubexponential_of_onLine
      (P := P) hline r hr
    convert hs using 1
    funext n
    rw [hcontour n]

/-- Cofinal exact prime--archimedean Gamma-six contours form a global RH criterion. -/
theorem riemannHypothesis_iff_forall_sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential :
    RiemannHypothesis ↔
      ∀ (R c : ℝ), 0 < R → 0 < c → c < 1 / 2 →
        XiSymmetricRectangleExplicitAdmissible R c →
        SourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential R c := by
  constructor
  · intro hRH R c hR hc hchalf hadm
    apply (sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_iff
      hR hc hadm).2
    intro q hq
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1
  · intro hsource
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    obtain ⟨R, c, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm, _⟩ :=
      exists_admissible_symmetric_rectangle_containing_xiZeroCopy q
    have hqmem : q ∈ xiZeroCopyClosedRectangle (symmetricRectangleLower R c)
        (symmetricRectangleUpper R c) := by
      rw [mem_xiZeroCopyClosedRectangle]
      apply Complex.mem_reProdIm.mpr
      constructor
      · rw [Set.uIcc_of_le]
        · simpa [symmetricRectangleLower, symmetricRectangleUpper] using
            And.intro hqreL.le hqreR.le
        · simp [symmetricRectangleLower, symmetricRectangleUpper]
          linarith
      · rw [Set.uIcc_of_le]
        · simpa [symmetricRectangleLower, symmetricRectangleUpper] using
            And.intro hqimL.le hqimR.le
        · simp [symmetricRectangleLower, symmetricRectangleUpper]
          linarith
    have hline :=
      (sourceHorizontalGammaSixSymmetricPrimeArchContourSubexponential_iff
        hR hc hadm).1 (hsource R c hR hc hchalf hadm) q hqmem
    refine ⟨(xiSpectralPoint q).re, Complex.ext ?_ ?_⟩
    · simp
    · rw [Complex.ofReal_im, xiSpectralPoint_im_eq, hline]
      norm_num

end

end RHTower
