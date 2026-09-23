/-
Summation of per-mode van der Corput bounds.

The reflected Dirichlet block, after the Euler–Maclaurin sawtooth is Fourier-expanded, becomes a sum
over frequencies `m` of oscillatory integrals `T m`, each bounded by the (weighted) van der Corput
estimate as `‖T m‖ ≤ K/(m+1)²`.  This module supplies the final summation step: such a family is
absolutely summable and `‖∑' m, T m‖ ≤ K·∑' 1/(m+1)²` — a finite constant (`= K·π²/6`).  The
`Σ 1/m²` convergence is what makes the mode sum finite; the `1/m²` per-mode rate comes from the
frequency `2πm` in the phase derivative.
-/
import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace RHTower

/-- **Interval-integral interchange of sum and integral** (absolute convergence).  When the family
`f n` is a.e.-strongly measurable and the integrals of the norms are summable
(`∑' n, ∫⁻ ‖f n‖ ≠ ⊤`), the interval integral commutes with the tsum:
`∫_a^b (∑' n, f n x) dx = ∑' n, ∫_a^b f n x dx`.  This is the interval-integral form of
`MeasureTheory.integral_tsum` (absent from mathlib), the tool that carries the Fourier expansion of
the Euler–Maclaurin sawtooth (via the absolutely summable coefficients of the continuous `B₂`) inside
the integral. -/
theorem intervalIntegral_tsum {a b : ℝ} (hab : a ≤ b) {f : ℤ → ℝ → ℂ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Set.Ioc a b)))
    (hsum : ∑' n : ℤ, ∫⁻ x in Set.Ioc a b, ‖f n x‖ₑ ≠ ⊤) :
    ∫ x in a..b, ∑' n : ℤ, f n x = ∑' n : ℤ, ∫ x in a..b, f n x := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_tsum hmeas hsum]
  exact tsum_congr (fun n => (intervalIntegral.integral_of_le hab).symm)

theorem summable_and_norm_tsum_le_of_mode_bound {T : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : Summable b) (hbound : ∀ m, ‖T m‖ ≤ b m) :
    Summable T ∧ ‖∑' m, T m‖ ≤ ∑' m, b m := by
  have hsummT : Summable (fun m => ‖T m‖) :=
    hb.of_nonneg_of_le (fun m => norm_nonneg _) hbound
  refine ⟨hsummT.of_norm, ?_⟩
  calc ‖∑' m, T m‖ ≤ ∑' m, ‖T m‖ := norm_tsum_le_tsum_norm hsummT
    _ ≤ ∑' m, b m := Summable.tsum_mono hsummT hb hbound

-- specialized to the 1/m^(2 : ℕ) per-mode bound from weighted van der Corput
theorem summable_and_norm_tsum_le_of_inv_sq_bound {T : ℕ → ℂ} {K : ℝ}
    (hbound : ∀ m, ‖T m‖ ≤ K / ((m : ℝ) + 1) ^ (2 : ℕ)) :
    Summable T ∧ ‖∑' m, T m‖ ≤ K * ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
  have hbsum : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ (2 : ℕ)) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact ((summable_nat_add_iff 1).mpr h).congr (fun m => by push_cast; ring)
  have hKbsum : Summable (fun m : ℕ => K / ((m : ℝ) + 1) ^ (2 : ℕ)) :=
    (hbsum.mul_left K).congr (fun m => mul_one_div K _)
  obtain ⟨hsummT, hle⟩ := summable_and_norm_tsum_le_of_mode_bound hKbsum hbound
  refine ⟨hsummT, ?_⟩
  calc ‖∑' m, T m‖ ≤ ∑' m : ℕ, K / ((m : ℝ) + 1) ^ (2 : ℕ) := hle
    _ = K * ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ (2 : ℕ) := by
        rw [show (∑' m : ℕ, K / ((m : ℝ) + 1) ^ (2 : ℕ))
            = ∑' m : ℕ, K * (1 / ((m : ℝ) + 1) ^ (2 : ℕ)) from
              tsum_congr (fun m => (mul_one_div K _).symm)]
        exact tsum_mul_left

end RHTower
