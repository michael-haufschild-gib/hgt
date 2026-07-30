import GaloisForLFunctions.HTGeometry.BoundedDegreeOperationalHorizonCertificate
import Mathlib.Tactic

/-!
# Noise no-go for finite operational-horizon certification

Exact finite sampling decides whether a bounded-degree response polynomial is
zero.  Without an amplitude normalization or lower margin, no positive noise
floor can do so: scale any nonzero response by a sufficiently small nonzero
constant and every prescribed finite sample falls below that floor while the
response remains nonzero and keeps its disconnected zero.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- **Finite-noise horizon no-go.** At every positive noise floor and every
finite family of coupling samples, there is a nonzero rescaling of any
nonzero disconnected response that lies below the floor at every sample.
The rescaling preserves the zero at disconnection and does not increase
degree. -/
theorem exists_nonzeroPolynomialResponse_below_finiteNoiseFloor
    {ι : Type*} [Fintype ι]
    (sample : ι → ℂ)
    {p : Polynomial ℂ}
    (hp : p ≠ 0)
    (hp0 : p.eval 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Polynomial ℂ,
      q ≠ 0 ∧
      q.eval 0 = 0 ∧
      q.natDegree ≤ p.natDegree ∧
      ∀ i, ‖q.eval (sample i)‖ < δ := by
  let S : ℝ := ∑ i : ι, ‖p.eval (sample i)‖
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  let denom : ℝ := 2 * (S + 1)
  have hdenom : 0 < denom := by
    dsimp [denom]
    positivity
  let c : ℝ := δ / denom
  have hcpos : 0 < c := div_pos hδ hdenom
  have hcne : (c : ℂ) ≠ 0 := by
    exact_mod_cast hcpos.ne'
  let q : Polynomial ℂ := Polynomial.C (c : ℂ) * p
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr hcne) hp
  · simp [q, hp0]
  · calc
      q.natDegree ≤ (Polynomial.C (c : ℂ)).natDegree + p.natDegree :=
        Polynomial.natDegree_mul_le
      _ = p.natDegree := by simp
  · intro i
    have hi : ‖p.eval (sample i)‖ ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (fun j _hj => norm_nonneg (p.eval (sample j)))
        (Finset.mem_univ i)
    have hSdenom : S < denom := by
      dsimp [denom]
      linarith
    have hcdenom : c * denom = δ := by
      dsimp [c]
      exact div_mul_cancel₀ δ hdenom.ne'
    calc
      ‖q.eval (sample i)‖ =
          c * ‖p.eval (sample i)‖ := by
        simp [q, abs_of_pos hcpos]
      _ ≤ c * S := mul_le_mul_of_nonneg_left hi hcpos.le
      _ < c * denom := mul_lt_mul_of_pos_left hSdenom hcpos
      _ = δ := hcdenom

end GaloisForLFunctions.HTGeometry
