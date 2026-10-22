import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorTwistedTraceReduction
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule

/-!
# Three-point detection: the defect trace of the prime-side reduction detects RH

The twisted-trace reduction writes the mixed (conjugate-twisted) spectral trace as prime data
minus the three-point defect trace.  This file closes that circle: the three-point defect trace
vanishes for all base-point triples **iff** the Riemann hypothesis holds, so under RH — and only
under RH — the non-holomorphic spectral data of the divisor flow is von-Mangoldt-computable.

The detection argument is a simple-pole extraction, easier than the cube case: for a non-real
spectral point `μ₀`, the auxiliary base points `z₂ = μ₀ + I` and `z₃ = μ₀ - I` are
automatically non-spectral — every spectral point has `|Im μ| < 1/2` because the divisor lies
in the open critical strip — their resolvent product against the `μ₀`-block is exactly `1`, and
the block then carries a simple pole in `z₁` at `μ₀` which beats the uniformly majorized tail.

Also included: the honest Euler-half-plane form of the twisted-trace reduction, where the
sources are the actual von-Mangoldt `LSeries` combination (`primeArchSourceRelativeTrace`), and
the unconditional non-vanishing `XiC z ≠ 0` on that half-plane.

Everything is unconditional except where `RiemannHypothesis` is an explicit hypothesis or
conclusion.
-/

noncomputable section

open Complex

namespace RHTower

/-- On the Euler half-plane the centered completed zeta does not vanish. -/
theorem XiC_ne_zero_of_one_lt_re {z : ℂ} (hz : 1 < (1 / 2 + z * Complex.I).re) :
    XiC z ≠ 0 := by
  intro h
  apply xi_ne_zero_of_one_le_re (le_of_lt hz)
  rw [← h, XiC]

/-- Euler-half-plane form of the prime-side reduction: the `μ`-twisted triple resolvent trace
is the corresponding combination of honest von-Mangoldt/archimedean source traces. -/
theorem deningerDivisorTwistedResolventTrace_eq_primeSeries
    {z₁ z₂ z₃ : ℂ}
    (hz₁ : 1 < (1 / 2 + z₁ * Complex.I).re)
    (hz₂ : 1 < (1 / 2 + z₂ * Complex.I).re)
    (hz₃ : 1 < (1 / 2 + z₃ * Complex.I).re)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (∑' q : XiZeroCopy, deningerDivisorTwistedResolventTerm z₁ z₂ z₃ q) =
      -((z₁ / ((z₁ - z₂) * (z₁ - z₃))) * primeArchSourceRelativeTrace z₁ +
        (z₂ / ((z₂ - z₁) * (z₂ - z₃))) * primeArchSourceRelativeTrace z₂ +
        (z₃ / ((z₃ - z₁) * (z₃ - z₂))) * primeArchSourceRelativeTrace z₃) := by
  have hsource : ∀ {z : ℂ}, 1 < (1 / 2 + z * Complex.I).re →
      logDeriv XiC z = primeArchSourceRelativeTrace z := by
    intro z hz
    rw [logDeriv_XiC_eq_relativeResolventTrace (XiC_ne_zero_of_one_lt_re hz),
      ← deningerDivisorRelativeResolventTrace_eq]
    exact deningerResolventLefschetzTrace_primeSeries hz
  rw [deningerDivisorTwistedResolventTrace_eq_logDeriv
    (XiC_ne_zero_of_one_lt_re hz₁) (XiC_ne_zero_of_one_lt_re hz₂)
    (XiC_ne_zero_of_one_lt_re hz₃) h12 h13 h23,
    hsource hz₁, hsource hz₂, hsource hz₃]

private theorem norm_inv_sub_le_of_far {z μ : ℂ} (hfar : 2 * ‖z‖ + 2 ≤ ‖μ‖) :
    ‖(μ - z)⁻¹‖ ≤ 2 / ‖μ‖ := by
  have hμpos : 0 < ‖μ‖ := by
    have : (0 : ℝ) < 2 * ‖z‖ + 2 := by positivity
    linarith
  have hhalf := norm_sub_ge_half_of_far hfar
  rw [norm_inv]
  have hpos2 : (0 : ℝ) < ‖μ‖ / 2 := by positivity
  calc ‖μ - z‖⁻¹ ≤ (‖μ‖ / 2)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hpos2 hhalf
    _ = 2 / ‖μ‖ := by rw [inv_div]

/-- Far-regime majorant for the three-point defect term. -/
theorem norm_threePointDefectTerm_le_of_far (z₁ z₂ z₃ : ℂ) (q : XiZeroCopy)
    (h1 : 2 * ‖z₁‖ + 2 ≤ ‖xiSpectralPoint q‖)
    (h2 : 2 * ‖z₂‖ + 2 ≤ ‖xiSpectralPoint q‖)
    (h3 : 2 * ‖z₃‖ + 2 ≤ ‖xiSpectralPoint q‖) :
    ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖ ≤
      16 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set μ := xiSpectralPoint q with hμ
  have hμpos : 0 < ‖μ‖ := by
    have : (0 : ℝ) < 2 * ‖z₁‖ + 2 := by positivity
    linarith
  have hb1 := norm_inv_sub_le_of_far h1
  have hb2 := norm_inv_sub_le_of_far h2
  have hb3 := norm_inv_sub_le_of_far h3
  calc ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖
      = ‖μ - (starRingEnd ℂ) μ‖ * (‖(μ - z₁)⁻¹‖ *
          (‖(μ - z₂)⁻¹‖ * ‖(μ - z₃)⁻¹‖)) := by
        rw [deningerDivisorThreePointDefectTerm, norm_mul, norm_mul, norm_mul]
    _ ≤ (2 * ‖μ‖) * ((2 / ‖μ‖) * ((2 / ‖μ‖) * (2 / ‖μ‖))) := by
        apply mul_le_mul (norm_defectTwist_le q) _ (by positivity)
          (by positivity)
        apply mul_le_mul hb1 _ (by positivity) (by positivity)
        exact mul_le_mul hb2 hb3 (norm_nonneg _) (by positivity)
    _ = 16 * (1 / ‖μ‖ ^ (2 : ℕ)) := by
        field_simp
        ring

/-- The three-point defect terms are absolutely summable at every base-point triple. -/
theorem summable_norm_threePointDefectTerm (z₁ z₂ z₃ : ℂ) :
    Summable (fun q : XiZeroCopy =>
      ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖) := by
  apply Summable.of_norm_bounded_eventually
    (xiSpectralPoint_inv_sq_summable.mul_left 16)
  set W : ℝ := max ‖z₁‖ (max ‖z₂‖ ‖z₃‖) with hW
  filter_upwards [(finite_setOf_norm_xiSpectralPoint_le
    (2 * W + 2)).eventually_cofinite_notMem] with q hq
  simp only [not_le] at hq
  rw [norm_norm]
  have hW1 : ‖z₁‖ ≤ W := le_max_left _ _
  have hW2 : ‖z₂‖ ≤ W := le_trans (le_max_left _ _) (le_max_right _ _)
  have hW3 : ‖z₃‖ ≤ W := le_trans (le_max_right _ _) (le_max_right _ _)
  exact norm_threePointDefectTerm_le_of_far z₁ z₂ z₃ q
    (by linarith) (by linarith) (by linarith)

theorem summable_threePointDefectTerm (z₁ z₂ z₃ : ℂ) :
    Summable (deningerDivisorThreePointDefectTerm z₁ z₂ z₃) :=
  (summable_norm_threePointDefectTerm z₁ z₂ z₃).of_norm

/-- The three-point defect trace. -/
def deningerDivisorThreePointDefectTrace (z₁ z₂ z₃ : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q

/-- RH kills the three-point defect trace, termwise. -/
theorem deningerDivisorThreePointDefectTrace_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z₁ z₂ z₃ : ℂ) :
    deningerDivisorThreePointDefectTrace z₁ z₂ z₃ = 0 := by
  have hterm : ∀ q : XiZeroCopy,
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q = 0 := by
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [deningerDivisorThreePointDefectTerm, ht]
    simp [Complex.conj_ofReal]
  rw [deningerDivisorThreePointDefectTrace, tsum_congr hterm]
  exact tsum_zero

/-- **Simple-pole extraction: a non-real spectral point makes some three-point defect trace
nonzero.**  The auxiliary points `μ₀ ± I` are non-spectral by the critical strip, their
resolvent product on the block is `1`, and the simple `z₁`-pole at `μ₀` beats the uniform
tail majorant. -/
theorem exists_threePointDefectTrace_ne_zero_of_offline
    (q₀ : XiZeroCopy) (him : (xiSpectralPoint q₀).im ≠ 0) :
    ∃ z₁ z₂ z₃ : ℂ, deningerDivisorThreePointDefectTrace z₁ z₂ z₃ ≠ 0 := by
  classical
  set μ₀ := xiSpectralPoint q₀ with hμ₀
  set c : ℂ := μ₀ - (starRingEnd ℂ) μ₀ with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Complex.sub_conj]
    apply mul_ne_zero _ Complex.I_ne_zero
    rw [Complex.ofReal_ne_zero]
    intro h
    apply him
    linarith
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_xiSpectralPoint_separation μ₀
  -- the uniform strip gap to the auxiliary points
  have hμ₀strip := abs_im_xiSpectralPoint_lt_half q₀
  set g : ℝ := 1 / 2 - |μ₀.im| with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set z₂ : ℂ := μ₀ + Complex.I with hz₂
  set z₃ : ℂ := μ₀ - Complex.I with hz₃
  have hgap₂ : ∀ q : XiZeroCopy, g ≤ ‖xiSpectralPoint q - z₂‖ := by
    intro q
    have hstrip := abs_im_xiSpectralPoint_lt_half q
    have him2 : (xiSpectralPoint q - z₂).im =
        (xiSpectralPoint q).im - (μ₀.im + 1) := by
      rw [hz₂]
      simp
    calc g ≤ |(xiSpectralPoint q - z₂).im| := by
          rw [him2, abs_sub_comm]
          rw [le_abs]
          left
          have h1 : |μ₀.im| ≥ -μ₀.im := neg_le_abs μ₀.im
          have h2 : (xiSpectralPoint q).im ≤ |(xiSpectralPoint q).im| :=
            le_abs_self _
          rw [hg]
          linarith
      _ ≤ ‖xiSpectralPoint q - z₂‖ := Complex.abs_im_le_norm _
  have hgap₃ : ∀ q : XiZeroCopy, g ≤ ‖xiSpectralPoint q - z₃‖ := by
    intro q
    have hstrip := abs_im_xiSpectralPoint_lt_half q
    have him3 : (xiSpectralPoint q - z₃).im =
        (xiSpectralPoint q).im - (μ₀.im - 1) := by
      rw [hz₃]
      simp
    calc g ≤ |(xiSpectralPoint q - z₃).im| := by
          rw [him3]
          rw [le_abs]
          left
          have h1 : |μ₀.im| ≥ μ₀.im := le_abs_self μ₀.im
          have h2 : -(xiSpectralPoint q).im ≤ |(xiSpectralPoint q).im| :=
            neg_le_abs _
          rw [hg]
          linarith
      _ ≤ ‖xiSpectralPoint q - z₃‖ := Complex.abs_im_le_norm _
  set R₀ : ℝ := 2 * ‖μ₀‖ + 4 with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  set C : ℝ := 16 + 2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g))) with hC
  have hCpos : 0 < C := by positivity
  have hCsum : Summable (fun q : XiZeroCopy =>
      C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left C
  set M : ℝ := ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) with hM
  have hM0 : 0 ≤ M := tsum_nonneg (fun q =>
    mul_nonneg (le_of_lt hCpos) (by positivity))
  set t : ℝ := min (δ / 4) (min (1 / 2) (‖c‖ / (2 * (M + 1)))) with ht
  have ht0 : 0 < t := by
    apply lt_min (by positivity)
    apply lt_min (by norm_num)
    exact div_pos hcnorm (by linarith)
  have htδ : t ≤ δ / 4 := min_le_left _ _
  have ht1 : t ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have htc : t ≤ ‖c‖ / (2 * (M + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set z₁ : ℂ := μ₀ + (t : ℂ) with hz₁
  have hμ₀z₁ : μ₀ - z₁ = -(t : ℂ) := by rw [hz₁]; ring
  have hμ₀z₂ : μ₀ - z₂ = -Complex.I := by rw [hz₂]; ring
  have hμ₀z₃ : μ₀ - z₃ = Complex.I := by rw [hz₃]; ring
  refine ⟨z₁, z₂, z₃, ?_⟩
  set v : ℂ := c * ((μ₀ - z₁)⁻¹ * ((μ₀ - z₂)⁻¹ * (μ₀ - z₃)⁻¹)) with hv
  have hv0 : v ≠ 0 := by
    rw [hv, hμ₀z₁, hμ₀z₂, hμ₀z₃]
    apply mul_ne_zero hc0
    apply mul_ne_zero
    · exact inv_ne_zero (neg_ne_zero.mpr
        (Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)))
    · exact mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero))
        (inv_ne_zero Complex.I_ne_zero)
  have hvnorm : ‖v‖ = ‖c‖ / t := by
    rw [hv, hμ₀z₁, hμ₀z₂, hμ₀z₃, norm_mul, norm_mul, norm_mul, norm_inv,
      norm_inv, norm_inv, norm_neg, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    field_simp
  set A : Set XiZeroCopy := {q | xiSpectralPoint q = μ₀} with hA
  have hq₀A : q₀ ∈ A := rfl
  have hsum := summable_threePointDefectTerm z₁ z₂ z₃
  have hsumA : Summable ((deningerDivisorThreePointDefectTerm z₁ z₂ z₃) ∘
      (Subtype.val : A → XiZeroCopy)) := hsum.subtype A
  have hsumAc : Summable ((deningerDivisorThreePointDefectTerm z₁ z₂ z₃) ∘
      (Subtype.val : ↥Aᶜ → XiZeroCopy)) := hsum.subtype Aᶜ
  have htermA : ∀ q : A,
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy) = v := by
    rintro ⟨q, hqA⟩
    have hqval : xiSpectralPoint q = μ₀ := hqA
    simp only [deningerDivisorThreePointDefectTerm, hqval, hv, hc]
  have hAconst : Summable (fun _ : A => v) := hsumA.congr (fun q => by
    rw [Function.comp_apply, htermA q])
  have hfinA : Finite A := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hv0 ((summable_const_iff v).mp hAconst)
  have hcardA : 1 ≤ Nat.card A := by
    haveI := hfinA
    haveI : Nonempty A := ⟨⟨q₀, hq₀A⟩⟩
    exact Nat.card_pos
  have hsumA_eq : (∑' q : A,
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) =
      (Nat.card A) • v :=
    calc (∑' q : A,
        deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy))
        = ∑' _ : A, v := tsum_congr htermA
      _ = (Nat.card A) • v := tsum_const v
  have hnormA : ‖c‖ / t ≤ ‖∑' q : A,
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ := by
    rw [hsumA_eq, nsmul_eq_mul, norm_mul, Complex.norm_natCast, hvnorm]
    have hnn : 0 ≤ ‖c‖ / t := div_nonneg (norm_nonneg c) (le_of_lt ht0)
    calc ‖c‖ / t = 1 * (‖c‖ / t) := (one_mul _).symm
      _ ≤ (Nat.card A : ℝ) * (‖c‖ / t) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcardA) hnn
  have hbound : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ μ₀ →
      ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖ ≤
        C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q hqne
    have hμq0 : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hzn₁ : ‖z₁‖ ≤ ‖μ₀‖ + 1 := by
      rw [hz₁]
      calc ‖μ₀ + (t : ℂ)‖ ≤ ‖μ₀‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖μ₀‖ + 1 := by
            simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
            linarith
    have hzn₂ : ‖z₂‖ ≤ ‖μ₀‖ + 1 := by
      rw [hz₂]
      calc ‖μ₀ + Complex.I‖ ≤ ‖μ₀‖ + ‖Complex.I‖ := norm_add_le _ _
        _ = ‖μ₀‖ + 1 := by rw [Complex.norm_I]
    have hzn₃ : ‖z₃‖ ≤ ‖μ₀‖ + 1 := by
      rw [hz₃]
      calc ‖μ₀ - Complex.I‖ ≤ ‖μ₀‖ + ‖Complex.I‖ := norm_sub_le _ _
        _ = ‖μ₀‖ + 1 := by rw [Complex.norm_I]
    by_cases hreg : R₀ ≤ ‖xiSpectralPoint q‖
    · have hfar : ∀ w : ℂ, ‖w‖ ≤ ‖μ₀‖ + 1 →
          2 * ‖w‖ + 2 ≤ ‖xiSpectralPoint q‖ := by
        intro w hw
        rw [hR₀] at hreg
        linarith
      calc ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖
          ≤ 16 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
            norm_threePointDefectTerm_le_of_far z₁ z₂ z₃ q
              (hfar z₁ hzn₁) (hfar z₂ hzn₂) (hfar z₃ hzn₃)
        _ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hC]
            have h0 : 0 ≤ 2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g))) := by
              positivity
            linarith
    · rw [not_le] at hreg
      have hres₁ : δ / 2 ≤ ‖xiSpectralPoint q - z₁‖ := by
        have hsep := hδ q hqne
        have htri : ‖xiSpectralPoint q - μ₀‖ - ‖z₁ - μ₀‖ ≤
            ‖xiSpectralPoint q - z₁‖ := by
          have h := norm_sub_norm_le (xiSpectralPoint q - μ₀) (z₁ - μ₀)
          calc ‖xiSpectralPoint q - μ₀‖ - ‖z₁ - μ₀‖
              ≤ ‖(xiSpectralPoint q - μ₀) - (z₁ - μ₀)‖ := h
            _ = ‖xiSpectralPoint q - z₁‖ := by ring_nf
        have hz₁dist : ‖z₁ - μ₀‖ = t := by
          rw [hz₁]
          simp [Complex.norm_real, abs_of_pos ht0]
        rw [hz₁dist] at htri
        linarith
      have hinv₁ : ‖(xiSpectralPoint q - z₁)⁻¹‖ ≤ 2 / δ := by
        rw [norm_inv]
        have h2 : (0 : ℝ) < δ / 2 := by positivity
        calc ‖xiSpectralPoint q - z₁‖⁻¹ ≤ (δ / 2)⁻¹ := by
              rw [inv_eq_one_div, inv_eq_one_div]
              exact div_le_div_of_nonneg_left (by norm_num) h2 hres₁
          _ = 2 / δ := by rw [inv_div]
      have hinv₂ : ‖(xiSpectralPoint q - z₂)⁻¹‖ ≤ 1 / g := by
        rw [norm_inv, inv_eq_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hg0 (hgap₂ q)
      have hinv₃ : ‖(xiSpectralPoint q - z₃)⁻¹‖ ≤ 1 / g := by
        rw [norm_inv, inv_eq_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hg0 (hgap₃ q)
      calc ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ q‖
          = ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖ *
              (‖(xiSpectralPoint q - z₁)⁻¹‖ *
                (‖(xiSpectralPoint q - z₂)⁻¹‖ *
                  ‖(xiSpectralPoint q - z₃)⁻¹‖)) := by
            rw [deningerDivisorThreePointDefectTerm, norm_mul, norm_mul,
              norm_mul]
        _ ≤ (2 * R₀) * ((2 / δ) * ((1 / g) * (1 / g))) := by
            apply mul_le_mul _ _ (by positivity) (by positivity)
            · calc ‖xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)‖
                  ≤ 2 * ‖xiSpectralPoint q‖ := norm_defectTwist_le q
                _ ≤ 2 * R₀ := by linarith
            · apply mul_le_mul hinv₁ _ (by positivity) (by positivity)
              exact mul_le_mul hinv₂ hinv₃ (norm_nonneg _) (by positivity)
        _ ≤ (2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g)))) *
              (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
            have hsq : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ R₀ ^ (2 : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hμq0) (le_of_lt hreg) 2
            rw [show (2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g)))) *
                (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) =
                (2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g)))) /
                  ‖xiSpectralPoint q‖ ^ (2 : ℕ) from by ring,
              le_div_iff₀ (by positivity : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ))]
            calc (2 * R₀) * ((2 / δ) * ((1 / g) * (1 / g))) *
                  ‖xiSpectralPoint q‖ ^ (2 : ℕ)
                ≤ (2 * R₀) * ((2 / δ) * ((1 / g) * (1 / g))) * R₀ ^ (2 : ℕ) :=
                  mul_le_mul_of_nonneg_left hsq (by positivity)
              _ = 2 * R₀ ^ (3 : ℕ) * ((2 / δ) * ((1 / g) * (1 / g))) := by ring
        _ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
            rw [hC]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have h16 : (0 : ℝ) ≤ 16 := by norm_num
            linarith
  have hcomplnorm : ‖∑' q : ↥Aᶜ,
      deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ ≤ M := by
    have hsumnormAc : Summable (fun q : ↥Aᶜ =>
        ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖) :=
      (summable_norm_threePointDefectTerm z₁ z₂ z₃).subtype Aᶜ
    calc ‖∑' q : ↥Aᶜ,
        deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖
        ≤ ∑' q : ↥Aᶜ,
            ‖deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ :=
          norm_tsum_le_tsum_norm hsumnormAc
      _ ≤ ∑' q : ↥Aᶜ, C * (1 / ‖xiSpectralPoint (q : XiZeroCopy)‖ ^ (2 : ℕ)) := by
          apply Summable.tsum_le_tsum _ hsumnormAc (hCsum.subtype Aᶜ)
          rintro ⟨q, hqc⟩
          exact hbound q hqc
      _ = ∑' q : XiZeroCopy, (Aᶜ).indicator
            (fun q => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) q :=
          tsum_subtype Aᶜ (fun q => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      _ ≤ M := by
          rw [hM]
          apply Summable.tsum_le_tsum _ (hCsum.indicator Aᶜ) hCsum
          intro q
          exact Set.indicator_le_self' (fun q _ => by positivity) q
  have hsplit := Summable.tsum_add_tsum_compl (s := A) hsumA hsumAc
  have hlow : ‖c‖ / t - M ≤
      ‖deningerDivisorThreePointDefectTrace z₁ z₂ z₃‖ := by
    rw [deningerDivisorThreePointDefectTrace, ← hsplit]
    have htri : ‖∑' q : A,
        deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ -
        ‖∑' q : ↥Aᶜ,
          deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ ≤
        ‖(∑' q : A,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)‖ := by
      have h1 := norm_sub_le
        ((∑' q : A,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy))
        (∑' q : ↥Aᶜ,
          deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy))
      have h2 : ((∑' q : A,
          deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) +
          ∑' q : ↥Aᶜ,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) -
          (∑' q : ↥Aᶜ,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy)) =
          ∑' q : A,
            deningerDivisorThreePointDefectTerm z₁ z₂ z₃ (q : XiZeroCopy) := by
        ring
      rw [h2] at h1
      linarith
    linarith [hnormA, hcomplnorm, htri]
  have hbig : 2 * (M + 1) ≤ ‖c‖ / t := by
    rw [le_div_iff₀ ht0]
    calc 2 * (M + 1) * t ≤ 2 * (M + 1) * (‖c‖ / (2 * (M + 1))) := by
          apply mul_le_mul_of_nonneg_left htc (by linarith)
      _ = ‖c‖ := by field_simp
  intro hzero
  rw [hzero, norm_zero] at hlow
  linarith

/-- **Vanishing of every three-point defect trace forces RH.** -/
theorem riemannHypothesis_of_forall_threePointDefectTrace_eq_zero
    (h : ∀ z₁ z₂ z₃ : ℂ, deningerDivisorThreePointDefectTrace z₁ z₂ z₃ = 0) :
    RiemannHypothesis := by
  by_contra hRH
  rw [rh_iff_xi_ne_zero_right] at hRH
  push Not at hRH
  obtain ⟨s, hs, hzero⟩ := hRH
  have hmem := mem_xi_divisor_support_of_eq_zero hzero
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) s :=
    xi_divisor_pos_on_support ⟨s, hmem⟩
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) s) := by omega
  have him : (xiSpectralPoint (⟨⟨s, hmem⟩, ⟨0, hn⟩⟩ : XiZeroCopy)).im ≠ 0 := by
    rw [xiSpectralPoint_im_divisorDefect]
    have hre := mem_rightHalf.mp hs
    intro heq
    have : (s : ℂ).re = 1 / 2 := by
      have : ((⟨s, hmem⟩ : XiDivisorSupport) : ℂ) = s := rfl
      linarith [heq]
    linarith
  obtain ⟨z₁, z₂, z₃, hz⟩ :=
    exists_threePointDefectTrace_ne_zero_of_offline _ him
  exact hz (h z₁ z₂ z₃)

/-- **The three-point defect trace detects RH**: it vanishes for all base-point triples iff the
Riemann hypothesis holds.  Combined with the twisted-trace reduction, this says the mixed
spectral trace is von-Mangoldt-computable at every admissible triple exactly when RH holds. -/
theorem threePointDefectTrace_eq_zero_iff_riemannHypothesis :
    (∀ z₁ z₂ z₃ : ℂ, deningerDivisorThreePointDefectTrace z₁ z₂ z₃ = 0) ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_forall_threePointDefectTrace_eq_zero,
    fun hRH z₁ z₂ z₃ =>
      deningerDivisorThreePointDefectTrace_eq_zero_of_riemannHypothesis
        hRH z₁ z₂ z₃⟩

end RHTower
