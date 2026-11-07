import GaloisForLFunctions.CompletedArithmeticForms.BesselGammaMomentScale
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTail

/-!
# The incomplete-Gamma comparison loses a uniform first-atom reserve

The exact incomplete-Gamma recurrence retains a positive factorial-scale
mass at every degree. Actual integrated first-atom moments lose that scale
geometrically, so they cannot dominate a fixed fraction of even this
weaker Gaussian mixture.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms
open ThetaCuspSections.FifthAtomTail

/-- The radial Gaussian mixture with the first atom's polynomial mass omitted. -/
def integratedGaussianEvenMoment (q : ℝ) (k : ℕ) : ℝ :=
  ((2 * k).factorial : ℝ) / k.factorial * powerTail ((k : ℝ) + 3 / 2) q

/-- Every incomplete-Gamma moment retains the complete initial tail mass. -/
theorem powerTail_factorial_lower {q : ℝ} (hq : 0 < q) (k : ℕ) :
    (k.factorial : ℝ) / (2 : ℝ) ^ k * powerTail (3 / 2) q ≤
      powerTail ((k : ℝ) + 3 / 2) q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hr := powerTail_recurrence (s := ((k + 1 : ℕ) : ℝ) + 3 / 2)
      (by positivity) hq
    have he : ((k + 1 : ℕ) : ℝ) + 3 / 2 - 1 = (k : ℝ) + 3 / 2 := by
      push_cast
      ring
    rw [he] at hr
    have hnn := powerTail_nonneg ((k : ℝ) + 3 / 2) hq.le
    have hbd : 0 ≤ q ^ (((k + 1 : ℕ) : ℝ) + 3 / 2) * Real.exp (-2 * q) / 2 := by
      positivity
    have hstep : ((k : ℝ) + 1) / 2 * powerTail ((k : ℝ) + 3 / 2) q ≤
        powerTail (((k + 1 : ℕ) : ℝ) + 3 / 2) q := by
      push_cast at hr
      nlinarith only [hr, hnn, hbd]
    calc
      _ = ((k : ℝ) + 1) / 2 *
          ((k.factorial : ℝ) / (2 : ℝ) ^ k * powerTail (3 / 2) q) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ ≤ ((k : ℝ) + 1) / 2 * powerTail ((k : ℝ) + 3 / 2) q :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := hstep

theorem powerTail_three_halves_pos {q : ℝ} (hq : 0 < q) :
    0 < powerTail (3 / 2) q := by
  have hh := mul_le_mul_of_nonneg_right (gammaMass_lower hq) (boundary_pos hq).le
  change (1 / 2 : ℝ) * boundary q ≤ powerTail (3 / 2) q / boundary q * boundary q at hh
  rw [div_mul_cancel₀ _ (boundary_pos hq).ne'] at hh
  exact (mul_pos (by norm_num) (boundary_pos hq)).trans_le hh

/-- The Gaussian mixture keeps a fixed positive normalized mass at every degree. -/
theorem integratedGaussianEvenMoment_normalized_lower {q : ℝ} (hq : 0 < q) (k : ℕ) :
    powerTail (3 / 2) q ≤
      ((2 : ℝ) ^ k / (2 * k).factorial) * integratedGaussianEvenMoment q k := by
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hf2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hh := mul_le_mul_of_nonneg_left (powerTail_factorial_lower hq k)
    (by positivity : 0 ≤ (2 : ℝ) ^ k / k.factorial)
  have he : ((2 : ℝ) ^ k / k.factorial) *
      ((k.factorial : ℝ) / (2 : ℝ) ^ k * powerTail (3 / 2) q) =
      powerTail (3 / 2) q := by field_simp [hf.ne', h2]
  rw [he] at hh
  refine hh.trans_eq ?_
  unfold integratedGaussianEvenMoment
  field_simp [hf2]

/-- No positive fraction of the integrated Gaussian comparison pays every actual moment. -/
theorem not_uniform_integratedGaussian_fraction {q : ℝ} (hq : 3 ≤ q) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ,
      c * integratedGaussianEvenMoment q k ≤ besselFirstAtomEvenMoment q k := by
  rintro ⟨c, hc, hpay⟩
  have hq0 : 0 < q := by linarith only [hq]
  apply not_uniform_besselFirstAtomGammaRatio hq
  refine ⟨c * powerTail (3 / 2) q, mul_pos hc (powerTail_three_halves_pos hq0), ?_⟩
  intro k
  have hlo := mul_le_mul_of_nonneg_left (integratedGaussianEvenMoment_normalized_lower hq0 k) hc.le
  have hhi := mul_le_mul_of_nonneg_left (hpay k)
    (by positivity : 0 ≤ (2 : ℝ) ^ k / (2 * k).factorial)
  unfold besselFirstAtomGammaRatio
  calc
    _ ≤ c * (((2 : ℝ) ^ k / (2 * k).factorial) * integratedGaussianEvenMoment q k) := hlo
    _ = ((2 : ℝ) ^ k / (2 * k).factorial) * (c * integratedGaussianEvenMoment q k) := by ring
    _ ≤ _ := hhi

#print axioms powerTail_factorial_lower
#print axioms integratedGaussianEvenMoment_normalized_lower
#print axioms not_uniform_integratedGaussian_fraction

end GaloisForLFunctions.CompletedArithmeticForms
