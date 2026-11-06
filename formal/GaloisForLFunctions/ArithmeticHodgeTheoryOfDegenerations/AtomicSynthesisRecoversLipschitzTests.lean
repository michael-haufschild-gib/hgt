import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive

/-!
# Atomic synthesis recovers Lipschitz tests

Pairing a synthesized source with a Lipschitz test differs from sampling the
centers by at most the atom width times its L¹ mass. On the coefficient ℓ²
scale, the centered source has adjoint error `c/N`, uniformly in its weights.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry

private theorem abs_integral_shift_mul_sub_le {g f : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgs : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {L : NNReal} (hf : LipschitzWith L f) (a : ℝ) :
    |(∫ u, g (u - a) * f u) - (∫ u, g u) * f a| ≤
      (L : ℝ) * w * ∫ u, |g u| := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgs
  have hshift : HasCompactSupport (fun u => g (u - a)) :=
    hgc.comp_homeomorph (Homeomorph.subRight a)
  have hcont : Continuous (fun u => g (u - a)) := hg.comp (continuous_sub_right a)
  have hi : Integrable (fun u => g (u - a) * f u) :=
    (hcont.mul hf.continuous).integrable_of_hasCompactSupport hshift.mul_right
  have hi0 : Integrable (fun u => g (u - a) * f a) :=
    (hcont.integrable_of_hasCompactSupport hshift).mul_const _
  have heq : (∫ u, g (u - a) * f u) - (∫ u, g u) * f a =
      ∫ u, g (u - a) * (f u - f a) := by
    simp_rw [mul_sub]
    rw [integral_sub hi hi0, integral_mul_const, integral_sub_right_eq_self]
  rw [heq]
  apply abs_integral_shift_mul_le hg hgc hgs (hf.continuous.sub continuous_const)
  intro u hu
  have h := hf.dist_le_mul u a
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [hu.2]) L.coe_nonneg)

/-- Atomic synthesis recovers Lipschitz samples with an error controlled by the atom width. -/
theorem abs_integral_atomicTest_mul_sub_le {g f : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgs : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {L : NNReal} (hf : LipschitzWith L f) (N : ℕ) (x : ℕ → ℝ) :
    |(∫ u, atomicTest N x g u * f u) -
        (∫ u, g u) * ∑ n ∈ Icc 1 N, x n * f (Real.log n)| ≤
      ((L : ℝ) * w * ∫ u, |g u|) * ∑ n ∈ Icc 1 N, |x n| := by
  rw [integral_atomicTest_mul hf.continuous hg hgs, mul_sum, ← sum_sub_distrib]
  calc
    |∑ n ∈ Icc 1 N, (x n * (∫ u, g (u - Real.log n) * f u) -
        (∫ u, g u) * (x n * f (Real.log n)))|
      ≤ ∑ n ∈ Icc 1 N, |x n * (∫ u, g (u - Real.log n) * f u) -
        (∫ u, g u) * (x n * f (Real.log n))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, |x n| * ((L : ℝ) * w * ∫ u, |g u|) := by
      apply sum_le_sum
      intro n hn
      rw [show x n * (∫ u, g (u - Real.log n) * f u) -
          (∫ u, g u) * (x n * f (Real.log n)) =
          x n * ((∫ u, g (u - Real.log n) * f u) -
            (∫ u, g u) * f (Real.log n)) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_integral_shift_mul_sub_le hg hgs hf (Real.log n)) (abs_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- Translation of the synthesis estimate to a prescribed center. -/
theorem abs_integral_shift_atomicTest_mul_sub_le {g f : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgs : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {L : NNReal} (hf : LipschitzWith L f) (N : ℕ) (x : ℕ → ℝ) (b : ℝ) :
    |(∫ u, atomicTest N x g (u + b) * f u) -
        (∫ u, g u) * ∑ n ∈ Icc 1 N, x n * f (Real.log n - b)| ≤
      ((L : ℝ) * w * ∫ u, |g u|) * ∑ n ∈ Icc 1 N, |x n| := by
  have hf' : LipschitzWith L (fun u => f (u - b)) := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simpa only [Real.dist_eq, show (u - b) - (v - b) = u - v by ring] using
      hf.dist_le_mul (u - b) (v - b)
  have h := abs_integral_atomicTest_mul_sub_le hg hgs hf' N x
  have he := integral_add_right_eq_self (μ := volume)
    (fun u => atomicTest N x g u * f (u - b)) b
  simp only [add_sub_cancel_right] at he
  rw [← he] at h
  exact h

private theorem sum_abs_le_sqrt_mass (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, |x n| ≤ Real.sqrt N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun _ => (1 : ℝ)) (fun n => |x n|)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs,
    Nat.card_Icc, Nat.add_sub_cancel] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _),
    Real.sqrt_mul (Nat.cast_nonneg N)] at hs
  exact hs

/-- Centered atoms recover samples with an error uniform over the coefficient sphere. -/
theorem abs_integral_centredAtomicTest_mul_sub_le {φ f : ℝ → ℝ}
    (hφ : Continuous φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {L : NNReal} (hf : LipschitzWith L f) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    |(∫ u, centredAtomicTest φ x c N u * f u) -
        (c / N) * (∫ u, φ u) * ∑ n ∈ Icc 1 N, x n * f (Real.log n - Real.log N)| ≤
      ((L : ℝ) * (c / N) ^ 2 * ∫ u, |φ u|) *
        (Real.sqrt N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : Continuous (atomDilate φ (c / N)) := hφ.comp (continuous_id.div_const _)
  have hgs : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    apply hs
    intro hm
    apply hu
    refine ⟨?_, (div_le_one hw).mp hm.2⟩
    simpa only [zero_mul] using (le_div_iff₀ hw).mp hm.1
  have hm : (∫ u, atomDilate φ (c / N) u) = (c / N) * ∫ u, φ u := by
    simpa only [atomDilate, abs_of_pos hw, smul_eq_mul] using
      Measure.integral_comp_div φ (c / N)
  have ha : (∫ u, |atomDilate φ (c / N) u|) = (c / N) * ∫ u, |φ u| := by
    simpa only [atomDilate, abs_of_pos hw, smul_eq_mul] using
      Measure.integral_comp_div (fun u => |φ u|) (c / N)
  have h := abs_integral_shift_atomicTest_mul_sub_le hg hgs hf N x (Real.log N)
  rw [hm, ha] at h
  change |(∫ u, centredAtomicTest φ x c N u * f u) -
    (c / N) * (∫ u, φ u) * ∑ n ∈ Icc 1 N, x n * f (Real.log n - Real.log N)| ≤ _ at h
  refine h.trans ?_
  rw [show (L : ℝ) * (c / N) * ((c / N) * ∫ u, |φ u|) =
    (L : ℝ) * (c / N) ^ 2 * ∫ u, |φ u| by ring]
  exact mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_mass N x)
    (mul_nonneg (mul_nonneg L.coe_nonneg (sq_nonneg _)) (integral_nonneg fun _ => abs_nonneg _))

/-- The centered physical source on the coefficient ℓ² scale. -/
def normalizedCentredAtomicTest (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (u : ℝ) : ℝ := Real.sqrt N / c * centredAtomicTest φ x c N u

/-- After normalization the adjoint synthesis error is at most `c/N` times the
Lipschitz constant, the atom's L¹ mass, and the coefficient ℓ² norm. -/
theorem abs_integral_normalizedCentredAtomicTest_mul_sub_le {φ f : ℝ → ℝ}
    (hφ : Continuous φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {L : NNReal} (hf : LipschitzWith L f) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    |(∫ u, normalizedCentredAtomicTest φ x c N u * f u) -
        (∫ u, φ u) / Real.sqrt N *
          ∑ n ∈ Icc 1 N, x n * f (Real.log n - Real.log N)| ≤
      (c / N) * (L : ℝ) * (∫ u, |φ u|) * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have h := mul_le_mul_of_nonneg_left
    (abs_integral_centredAtomicTest_mul_sub_le hφ hs hf hc hN x)
    (div_nonneg hsqrt.le hc.le)
  have he : (∫ u, normalizedCentredAtomicTest φ x c N u * f u) =
      Real.sqrt N / c * ∫ u, centredAtomicTest φ x c N u * f u := by
    simp only [normalizedCentredAtomicTest, mul_assoc, integral_const_mul]
  have hcoef : Real.sqrt N / c * (c / N) = (Real.sqrt N)⁻¹ := by
    field_simp
    nlinarith only [hsq]
  have hleft : Real.sqrt N / c *
      ((∫ u, centredAtomicTest φ x c N u * f u) -
        (c / N) * (∫ u, φ u) * ∑ n ∈ Icc 1 N, x n * f (Real.log n - Real.log N)) =
      (∫ u, normalizedCentredAtomicTest φ x c N u * f u) -
        (∫ u, φ u) / Real.sqrt N * ∑ n ∈ Icc 1 N, x n * f (Real.log n - Real.log N) := by
    rw [he, mul_sub, ← mul_assoc, ← mul_assoc, hcoef]
    ring
  have hright : Real.sqrt N / c *
      (((L : ℝ) * (c / N) ^ 2 * ∫ u, |φ u|) *
        (Real.sqrt N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2))) =
      (c / N) * (L : ℝ) * (∫ u, |φ u|) * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) := by
    calc
      _ = (Real.sqrt N / c * (c / N)) * Real.sqrt N *
          ((c / N) * (L : ℝ) * (∫ u, |φ u|) * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2)) := by ring
      _ = _ := by rw [hcoef, inv_mul_cancel₀ hsqrt.ne', one_mul]
  rw [← abs_of_pos (div_pos hsqrt hc), ← abs_mul, hleft, abs_of_pos (div_pos hsqrt hc), hright] at h
  exact h

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations


#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_integral_normalizedCentredAtomicTest_mul_sub_le
