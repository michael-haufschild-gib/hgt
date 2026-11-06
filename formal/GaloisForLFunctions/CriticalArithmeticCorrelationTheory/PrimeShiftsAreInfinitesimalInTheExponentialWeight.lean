import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExponentialSourceMassControlsTheFullPrimeSum

/-!
# Prime shifts are infinitesimal in the terminal exponential weight

The global prime bound uses the weight `exp(2|y|)`. On the negative half-line,
this lower exponential weight is infinitesimal relative to `exp(-8y)`, with
an aperture-independent remainder controlled by ordinary square mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology RHTower
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

/-- Taking absolute values of a test dominates the absolute prime quadratic form. -/
theorem abs_primeSum_le_primeSum_abs {H : ℝ → ℝ}
    (hHc : HasCompactSupport H) :
    |primeSum H| ≤ primeSum (fun y => |H y|) := by
  have hHac : HasCompactSupport (fun y => |H y|) := by
    simpa only [Real.norm_eq_abs] using hHc.norm
  have hterms := summable_primeSum_terms hHc
  have haterms := summable_primeSum_terms hHac
  have hpoint (n : ℕ) :
      |vonMangoldtAtom n * ((∫ y, H y * H (y - Real.log n)) +
        ∫ y, H y * H (y + Real.log n))| ≤
      vonMangoldtAtom n * ((∫ y, |H y| * |H (y - Real.log n)|) +
        ∫ y, |H y| * |H (y + Real.log n)|) := by
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' n)]
    apply mul_le_mul_of_nonneg_left _ (vonMangoldtAtom_nonneg' n)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · simpa only [Real.norm_eq_abs, abs_mul] using
        norm_integral_le_integral_norm (fun y => H y * H (y - Real.log n))
    · simpa only [Real.norm_eq_abs, abs_mul] using
        norm_integral_le_integral_norm (fun y => H y * H (y + Real.log n))
  have htriangle := norm_tsum_le_tsum_norm hterms.norm
  simp only [Real.norm_eq_abs] at htriangle
  exact htriangle.trans (hterms.abs.tsum_le_tsum hpoint haterms)

/-- The absolute prime form obeys the same global exponential bound as its upper part. -/
theorem abs_primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    |primeSum H| ≤ 2 * vonMangoldtThreeHalvesMass * exponentialSourceMass H := by
  have hHac : HasCompactSupport (fun y => |H y|) := by
    simpa only [Real.norm_eq_abs] using hHc.norm
  have h := (abs_primeSum_le_primeSum_abs hHc).trans
    (primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass hH.abs hHac)
  simpa only [exponentialSourceMass, mul_pow, sq_abs] using h

private theorem exists_linear_le_quartic {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → C * t ≤ ε * t ^ 4 + B := by
  let M := max 1 (C / ε)
  have hM : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ ε * M := by
    have h := (div_le_iff₀ hε).mp (le_max_right 1 (C / ε))
    simpa only [mul_comm] using h
  refine ⟨C * M, mul_nonneg hC (zero_le_one.trans hM), ?_⟩
  intro t ht
  by_cases hsmall : t ≤ M
  · exact (mul_le_mul_of_nonneg_left hsmall hC).trans
      (le_add_of_nonneg_left (mul_nonneg hε.le (pow_nonneg ht 4)))
  · have ht1 : 1 ≤ t := hM.trans (le_of_not_ge hsmall)
    have hCt : C ≤ ε * t := hCM.trans (mul_le_mul_of_nonneg_left
      (le_of_not_ge hsmall) hε.le)
    have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
    have ht24 : t ^ 2 ≤ t ^ 4 := by
      have h := mul_le_mul_of_nonneg_left ht2 (sq_nonneg t)
      nlinarith only [h]
    have h := mul_le_mul_of_nonneg_right hCt ht
    have h' := mul_le_mul_of_nonneg_left ht24 hε.le
    have hB : 0 ≤ C * M := mul_nonneg hC (zero_le_one.trans hM)
    nlinarith only [h, h', hB]

/-- Every positive fraction of terminal weighted mass absorbs the prime form,
up to a fixed multiple of ordinary square mass, uniformly over all apertures. -/
theorem exists_abs_primeSum_le_exponential_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {H : ℝ → ℝ}, Continuous H → HasCompactSupport H →
      (∀ y, 0 < y → H y = 0) →
      |primeSum H| ≤ ε * (∫ y, H y ^ 2 * Real.exp (-(8 * y))) + B * ∫ y, H y ^ 2 := by
  let C := 2 * vonMangoldtThreeHalvesMass
  have hC : 0 ≤ C := mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg
  obtain ⟨B, hB, hpoly⟩ := exists_linear_le_quartic hC hε
  refine ⟨B, hB, ?_⟩
  intro H hH hHc hs
  have hpoint (y : ℝ) : C * (Real.exp |y| * H y) ^ 2 ≤
      ε * (H y ^ 2 * Real.exp (-(8 * y))) + B * H y ^ 2 := by
    by_cases hy : y ≤ 0
    · have he2 : (Real.exp |y|) ^ 2 = Real.exp (-(2 * y)) := by
        rw [abs_of_nonpos hy, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have he4 : (Real.exp (-(2 * y))) ^ 4 = Real.exp (-(8 * y)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have h := mul_le_mul_of_nonneg_right
        (hpoly (Real.exp (-(2 * y))) (Real.exp_pos _).le) (sq_nonneg (H y))
      rw [he4] at h
      rw [mul_pow, he2]
      nlinarith only [h]
    · simp only [hs y (lt_of_not_ge hy), mul_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul, add_zero, le_refl]
  have hH2c : HasCompactSupport (fun y => H y ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hHc ⊢
    exact hHc.mono fun y hy => by
      change H y = 0 at hy
      change H y ^ 2 = 0
      rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hic : HasCompactSupport (fun y => (Real.exp |y| * H y) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hH2c ⊢
    exact hH2c.mono fun y hy => by
      change H y ^ 2 = 0 at hy
      change (Real.exp |y| * H y) ^ 2 = 0
      rw [mul_pow, hy, mul_zero]
  have hi : Integrable (fun y => (Real.exp |y| * H y) ^ 2) :=
    (((Real.continuous_exp.comp continuous_abs).mul hH).pow 2).integrable_of_hasCompactSupport hic
  have hi8 : Integrable (fun y => H y ^ 2 * Real.exp (-(8 * y))) :=
    ((hH.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport hH2c.mul_right
  have hi0 : Integrable (fun y => H y ^ 2) :=
    (hH.pow 2).integrable_of_hasCompactSupport hH2c
  have hbound := integral_mono (hi.const_mul C) ((hi8.const_mul ε).add (hi0.const_mul B)) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add (hi8.const_mul ε) (hi0.const_mul B),
    integral_const_mul, integral_const_mul] at hbound
  exact (abs_primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass hH hHc).trans hbound

#print axioms abs_primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass
#print axioms exists_abs_primeSum_le_exponential_mass
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
