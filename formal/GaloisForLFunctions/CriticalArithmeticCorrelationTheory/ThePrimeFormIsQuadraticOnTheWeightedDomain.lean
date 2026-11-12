import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeAndPoleFormsAreContinuousInTheWeightedNorm

/-!
# Exact polarization on the measurable weighted domain

Absolute summability of the mixed prime correlations permits termwise
polarization of the full prime form. The resulting quadratic identity
applies to measurable finite-weight profiles, including half-line states.
-/

noncomputable section
open MeasureTheory Filter RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Scalar multiplication preserves finite exponential source mass. -/
theorem WeightedTwo.const_mul {f : ℝ → ℝ} (hf : WeightedTwo f) (c : ℝ) :
    WeightedTwo (fun t => c * f t) := by
  refine ⟨hf.meas.const_mul c, ?_⟩
  apply (hf.sq.const_mul (c ^ 2)).congr
  exact Eventually.of_forall fun t => by dsimp only; ring

/-- Addition preserves finite exponential source mass. -/
theorem WeightedTwo.add {f g : ℝ → ℝ} (hf : WeightedTwo f) (hg : WeightedTwo g) :
    WeightedTwo (fun t => f t + g t) := by
  have hh := hf.sub (hg.const_mul (-1))
  simpa only [neg_one_mul, sub_neg_eq_add] using hh

/-- The absolutely summable mixed prime form. -/
def primeMixedForm (f g : ℝ → ℝ) : ℝ := ∑' n, primePairTerm f g n

private theorem primePairTerm_add_left {f g h : ℝ → ℝ}
    (hf : WeightedTwo f) (hg : WeightedTwo g) (hh : WeightedTwo h) (n : ℕ) :
    primePairTerm (fun t => f t + g t) h n = primePairTerm f h n + primePairTerm g h n := by
  have hlag (s : ℝ) : (∫ t, (f t + g t) * h (t - s)) =
      (∫ t, f t * h (t - s)) + ∫ t, g t * h (t - s) := by
    simp_rw [add_mul]
    exact integral_add (integrable_mul_shift hf hh s) (integrable_mul_shift hg hh s)
  have hplus := hlag (-Real.log n)
  simp only [sub_neg_eq_add] at hplus
  unfold primePairTerm
  rw [hlag, hplus]
  ring

private theorem primePairTerm_add_right {f g h : ℝ → ℝ}
    (hf : WeightedTwo f) (hg : WeightedTwo g) (hh : WeightedTwo h) (n : ℕ) :
    primePairTerm f (fun t => g t + h t) n = primePairTerm f g n + primePairTerm f h n := by
  have hlag (s : ℝ) : (∫ t, f t * (g (t - s) + h (t - s))) =
      (∫ t, f t * g (t - s)) + ∫ t, f t * h (t - s) := by
    simp_rw [mul_add]
    exact integral_add (integrable_mul_shift hf hg s) (integrable_mul_shift hf hh s)
  have hplus := hlag (-Real.log n)
  simp only [sub_neg_eq_add] at hplus
  unfold primePairTerm
  rw [hlag, hplus]
  ring

theorem primeMixedForm_add_left {f g h : ℝ → ℝ}
    (hf : WeightedTwo f) (hg : WeightedTwo g) (hh : WeightedTwo h) :
    primeMixedForm (fun t => f t + g t) h = primeMixedForm f h + primeMixedForm g h := by
  unfold primeMixedForm
  simp_rw [primePairTerm_add_left hf hg hh]
  exact (summable_primePairTerm hf hh).tsum_add (summable_primePairTerm hg hh)

theorem primeMixedForm_add_right {f g h : ℝ → ℝ}
    (hf : WeightedTwo f) (hg : WeightedTwo g) (hh : WeightedTwo h) :
    primeMixedForm f (fun t => g t + h t) = primeMixedForm f g + primeMixedForm f h := by
  unfold primeMixedForm
  simp_rw [primePairTerm_add_right hf hg hh]
  exact (summable_primePairTerm hf hg).tsum_add (summable_primePairTerm hf hh)

theorem primeMixedForm_const_mul_left (f g : ℝ → ℝ) (c : ℝ) :
    primeMixedForm (fun t => c * f t) g = c * primeMixedForm f g := by
  have hterm (n : ℕ) : primePairTerm (fun t => c * f t) g n = c * primePairTerm f g n := by
    unfold primePairTerm
    simp_rw [mul_assoc, integral_const_mul]
    ring
  unfold primeMixedForm
  simp_rw [hterm]
  exact tsum_mul_left

theorem primeMixedForm_const_mul_right (f g : ℝ → ℝ) (c : ℝ) :
    primeMixedForm f (fun t => c * g t) = c * primeMixedForm f g := by
  have hterm (n : ℕ) : primePairTerm f (fun t => c * g t) n = c * primePairTerm f g n := by
    have hlag (s : ℝ) : (∫ t, f t * (c * g (t - s))) = c * ∫ t, f t * g (t - s) := by
      rw [show (fun t => f t * (c * g (t - s))) =
        (fun t => c * (f t * g (t - s))) from funext fun t => by ring,
        integral_const_mul]
    have hplus := hlag (-Real.log n)
    simp only [sub_neg_eq_add] at hplus
    unfold primePairTerm
    rw [hlag, hplus]
    ring
  unfold primeMixedForm
  simp_rw [hterm]
  exact tsum_mul_left

/-- The full prime sum is an actual quadratic polynomial along every
weighted-domain variation; both mixed correlations retain their literal series. -/
theorem primeSum_add_const_mul {f g : ℝ → ℝ}
    (hf : WeightedTwo f) (hg : WeightedTwo g) (c : ℝ) :
    primeSum (fun t => f t + c * g t) = primeSum f +
      c * (primeMixedForm f g + primeMixedForm g f) + c ^ 2 * primeSum g := by
  change primeMixedForm (fun t => f t + c * g t) (fun t => f t + c * g t) = _
  rw [primeMixedForm_add_left hf (hg.const_mul c) (hf.add (hg.const_mul c)),
    primeMixedForm_add_right hf hf (hg.const_mul c),
    primeMixedForm_add_right (hg.const_mul c) hf (hg.const_mul c)]
  simp only [primeMixedForm_const_mul_left, primeMixedForm_const_mul_right]
  change primeSum f + c * primeMixedForm f g +
    (c * primeMixedForm g f + c * (c * primeSum g)) = _
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
