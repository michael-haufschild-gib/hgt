import GaloisForLFunctions.HTGeometry.LpSingleAnnihilator
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The prime coefficient tangent space at the Euler boundary

The summable prime-ray topology at the Euler boundary is the weighted `ℓ¹` space of real prime
fields with norm `∑_p |b_p| (log p)/p`.  Carrying the weight inside the generators rather than
inside the norm makes it the plain `ℓ¹` space over the primes, whose coordinate generator at `p` is
the Dirac mass scaled by `(log p)/p`.

The weight never vanishes, so the generators span the same finite-support fields as the unscaled
Dirac masses; a continuous functional killing all of them therefore kills the whole space.

* `HTGeometry.PrimeTangent`, `HTGeometry.primeTangentGen`;
* `HTGeometry.norm_primeTangentGen`;
* `HTGeometry.primeTangent_eq_zero_of_forall_gen`.
-/

namespace HTGeometry

/-- The Banach space of summable real prime coefficient fields. -/
abbrev PrimeTangent : Type := lp (fun _ : Nat.Primes => ℝ) 1

/-- The Euler-boundary weight at a prime. -/
noncomputable def primeTangentWeight (p : Nat.Primes) : ℝ := Real.log (p : ℕ) / (p : ℕ)

theorem primeTangentWeight_pos (p : Nat.Primes) : 0 < primeTangentWeight p := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hpR : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
  have hlog : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hden : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  exact div_pos hlog hden

theorem primeTangentWeight_ne_zero (p : Nat.Primes) : primeTangentWeight p ≠ 0 :=
  (primeTangentWeight_pos p).ne'

/-- The weighted coordinate generator at a prime. -/
noncomputable def primeTangentGen (p : Nat.Primes) : PrimeTangent :=
  lp.single 1 p (primeTangentWeight p)

theorem norm_primeTangentGen (p : Nat.Primes) :
    ‖primeTangentGen p‖ = primeTangentWeight p := by
  rw [primeTangentGen, lp.norm_single (by norm_num)]
  exact Real.norm_of_nonneg (primeTangentWeight_pos p).le

/-- **A continuous functional killing every weighted coordinate generator is zero.** -/
theorem primeTangent_eq_zero_of_forall_gen (f : PrimeTangent →L[ℝ] ℝ)
    (h : ∀ p : Nat.Primes, f (primeTangentGen p) = 0) : ∀ x : PrimeTangent, f x = 0 := by
  classical
  refine eq_zero_of_forall_apply_lp_single (by simp) f ?_
  intro i a
  have hc : primeTangentWeight i ≠ 0 := primeTangentWeight_ne_zero i
  have hrewrite : lp.single 1 i a = (a / primeTangentWeight i) • primeTangentGen i := by
    rw [primeTangentGen, ← lp.single_smul]
    congr 1
    rw [smul_eq_mul, div_mul_cancel₀ _ hc]
  rw [hrewrite, map_smul, h i, smul_zero]

end HTGeometry
