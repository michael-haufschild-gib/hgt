import GaloisForLFunctions.KoszulCohomology

/-!
# Prime-support tomography from Koszul boundary jets

The marked Koszul scalar used by the prime-word selector is usually read only at its terminal
value: support size one survives and every mixed-prime support disappears.  The cancellation is
the boundary value of a canonical positive deformation

`Mₙ(t) = n (1 - t)^(n - 1)`.

For `t < 1`, every nonempty support has positive weight.  At `t = 1`, the zeroth boundary jet is
the existing singleton-support selector.  More strongly, the `r`th boundary jet is nonzero at
exactly support size `r + 1`.  Thus the entire tower of normal jets recovers every mixed-support
stratum that the scalar endpoint discards.

This is finite combinatorial infrastructure, not an RH theorem.  Its RH use is as a positive
successor to the scalar two-sided-ideal no-go: a cofinal Euler--Gamma completion may retain the
full boundary-jet tower before taking the singleton scalar trace.
-/

namespace GaloisForLFunctions.RHTower

open Polynomial

/-- The integral polynomial form of the marked-support deformation.

The sign is chosen so evaluation at `t` is exactly `n * (1 - t)^(n - 1)`. -/
noncomputable def primeSupportMarkedDeformation (n : ℕ) : ℤ[X] :=
  C ((n : ℤ) * (-1 : ℤ) ^ (n - 1)) * (X - C 1) ^ (n - 1)

/-- The real interior weight underlying `primeSupportMarkedDeformation`. -/
def primeSupportMarkedInteriorWeight (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * (1 - t) ^ (n - 1)

/-- Every nonempty prime support has strictly positive weight before the boundary `t = 1`. -/
theorem primeSupportMarkedInteriorWeight_pos {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t < 1) :
    0 < primeSupportMarkedInteriorWeight n t := by
  exact mul_pos (Nat.cast_pos.mpr hn) (pow_pos (sub_pos.mpr ht) _)

/-- Exact evaluation of the integral deformation polynomial. -/
theorem primeSupportMarkedDeformation_eval (n : ℕ) (t : ℤ) :
    (primeSupportMarkedDeformation n).eval t = (n : ℤ) * (1 - t) ^ (n - 1) := by
  simp only [primeSupportMarkedDeformation, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  rw [mul_assoc, ← mul_pow]
  congr 2
  ring

/-- The old singleton-support selector is exactly the zeroth boundary jet of the deformation. -/
theorem primeSupportMarkedDeformation_boundary (n : ℕ) :
    (primeSupportMarkedDeformation n).eval 1 =
      GaloisForLFunctions.koszulSupportMarkedExponent n := by
  rw [primeSupportMarkedDeformation_eval,
    GaloisForLFunctions.koszulSupportMarkedExponent_eq]
  by_cases h : n = 1
  · simp [h]
  · by_cases h0 : n = 0
    · simp [h0]
    · have hm : n - 1 ≠ 0 := by omega
      simp [h, hm]

/-- **Exact support-cardinality tomography.**  The `r`th normal derivative at the cancellation
boundary is nonzero only for words using exactly `r + 1` distinct primes.  Its value there is the
explicit signed factorial `n * (-1)^r * r!`.

Consequently the complete boundary-jet tower retains every mixed-support cardinality even though
the zeroth scalar boundary value factors through the one-prime axes. -/
theorem primeSupportMarkedDeformation_boundaryJet (n r : ℕ) :
    ((derivative^[r]) (primeSupportMarkedDeformation n)).eval 1 =
      if n = r + 1 then (n : ℤ) * (-1 : ℤ) ^ r * (r.factorial : ℤ) else 0 := by
  rw [primeSupportMarkedDeformation, iterate_derivative_C_mul,
    iterate_derivative_X_sub_pow, eval_mul, eval_C, eval_smul, eval_pow,
    eval_sub, eval_X, eval_C, sub_self]
  by_cases h : n = r + 1
  · subst n
    simp [Nat.descFactorial_self]
  · rw [if_neg h]
    by_cases hn0 : n = 0
    · simp [hn0]
    · by_cases hlt : n - 1 < r
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
        simp
      · have hgt : n - 1 - r ≠ 0 := by omega
        rw [zero_pow hgt]
        simp

end GaloisForLFunctions.RHTower
