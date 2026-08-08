import Mathlib

/-!
# Weighted valuation shifts are bounded on the lattice energy

A weighted shift `(S_s Z)_ν = α_ν Z_{ν+s}` on a lattice moves no energy: translation by `s` is a
bijection of the index group, so the shifted energy is the original energy, and a uniform bound on
the weights bounds the operator.

This is the elementary half of the `ℓ²(ℤ^d)` weighted-shift stack that the orbit-recurrence cards
name; it needs no `lp` structure, only summability and the translation bijection.
-/

open Filter

set_option maxHeartbeats 800000

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [AddCommGroup G]

/-- Translating the index leaves the lattice energy unchanged. -/
theorem tsum_sq_comp_add (Z : G → ℝ) (s : G) :
    ∑' ν : G, Z (ν + s) ^ 2 = ∑' ν : G, Z ν ^ 2 := by
  simpa [Function.comp_def] using (Equiv.addRight s).tsum_eq fun ν => Z ν ^ 2

theorem summable_sq_comp_add {Z : G → ℝ} (hZ : Summable fun ν => Z ν ^ 2) (s : G) :
    Summable fun ν : G => Z (ν + s) ^ 2 := by
  simpa [Function.comp_def] using (Equiv.summable_iff (Equiv.addRight s)).mpr hZ

/-- **The weighted shift is bounded by the sup of its weights.** -/
theorem tsum_sq_weightedShift_le {α Z : G → ℝ} {M : ℝ}
    (hM : ∀ ν, |α ν| ≤ M) (s : G) (hZ : Summable fun ν => Z ν ^ 2) :
    ∑' ν : G, (α ν * Z (ν + s)) ^ 2 ≤ M ^ 2 * ∑' ν : G, Z ν ^ 2 := by
  have hshift : Summable fun ν : G => Z (ν + s) ^ 2 := summable_sq_comp_add hZ s
  have hdom : Summable fun ν : G => M ^ 2 * Z (ν + s) ^ 2 := hshift.mul_left _
  have hterm : ∀ ν : G, (α ν * Z (ν + s)) ^ 2 ≤ M ^ 2 * Z (ν + s) ^ 2 := by
    intro ν
    have habs : |α ν| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM ν) 2
    calc (α ν * Z (ν + s)) ^ 2 = α ν ^ 2 * Z (ν + s) ^ 2 := by ring
      _ = |α ν| ^ 2 * Z (ν + s) ^ 2 := by rw [sq_abs]
      _ ≤ M ^ 2 * Z (ν + s) ^ 2 :=
          mul_le_mul_of_nonneg_right habs (sq_nonneg _)
  have hsum : Summable fun ν : G => (α ν * Z (ν + s)) ^ 2 :=
    hdom.of_nonneg_of_le (fun ν => sq_nonneg _) hterm
  calc ∑' ν : G, (α ν * Z (ν + s)) ^ 2
      ≤ ∑' ν : G, M ^ 2 * Z (ν + s) ^ 2 := hsum.tsum_le_tsum hterm hdom
    _ = M ^ 2 * ∑' ν : G, Z (ν + s) ^ 2 := tsum_mul_left
    _ = M ^ 2 * ∑' ν : G, Z ν ^ 2 := by rw [tsum_sq_comp_add]

/-- **A finite sum of weighted shifts is bounded by the sum of the weight bounds**, in energy. -/
theorem tsum_sq_weightedShift_le_of_le {α Z : G → ℝ} {M : ℝ}
    (hM : ∀ ν, |α ν| ≤ M) (s : G) (hZ : Summable fun ν => Z ν ^ 2) {E : ℝ}
    (hE : ∑' ν : G, Z ν ^ 2 ≤ E) :
    ∑' ν : G, (α ν * Z (ν + s)) ^ 2 ≤ M ^ 2 * E := by
  refine le_trans (tsum_sq_weightedShift_le hM s hZ) ?_
  exact mul_le_mul_of_nonneg_left hE (by positivity)

end GaloisForLFunctions.HTGeometry
