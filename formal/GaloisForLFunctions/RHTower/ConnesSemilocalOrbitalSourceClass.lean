import GaloisForLFunctions.HTGeometry.QuantizedDifferentialCocycle
import GaloisForLFunctions.RHTower.SoninSemilocalTraceObstruction

/-!
# The degree-one orbital source class is nonzero modulo bounded responses

The nonarchimedean term of the semilocal Weil distribution has prime-power coefficient
`log p · p^{-m/2}`, which splits as `[p^{-m/2}/m] · [m log p]`: an Euler-logarithm amplitude times
the orbital response `m log p`.  Along the powers of any fixed prime that response is unbounded,
while the repository's fixed projection-correction pairing has a uniformly bounded response
(`not_soninSemilocalFluxNormalization`).  Hence, in the quotient of prime-power response
functionals by the uniformly bounded ones, the orbital class does not vanish: no source comparison
preserving the local Weil terms can send it into that pairing.

The factorization-independence half of the same statement is the Leibniz cocycle of
`HTGeometry.QuantizedDifferentialCocycle`.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- Prime-power response functionals. -/
abbrev PrimePowerResponse := Nat.Primes × ℕ → ℝ

/-- The uniformly bounded responses form a submodule. -/
def boundedResponses : Submodule ℝ PrimePowerResponse where
  carrier := {r | ∃ C : ℝ, ∀ x, |r x| ≤ C}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro r s ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun x => ?_⟩
    have habs : |r x + s x| ≤ |r x| + |s x| := abs_add_le (r x) (s x)
    exact habs.trans (add_le_add (hC x) (hD x))
  smul_mem' := by
    rintro c r ⟨C, hC⟩
    refine ⟨|c| * C, fun x => ?_⟩
    have h0 : (0 : ℝ) ≤ |c| := abs_nonneg c
    calc |(c • r) x| = |c| * |r x| := by
          simp [abs_mul]
      _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) h0

/-- `(9)`: the orbital response `m ↦ m log p` of a prime power. -/
def orbitalLogResponse : PrimePowerResponse := fun x => (x.2 : ℝ) * Real.log (x.1 : ℕ)

/-- `(5)`: the nonarchimedean Weil coefficient is the Euler-logarithm amplitude times the orbital
response. -/
theorem weilPrimePowerCoefficient_split (p : ℕ) (m : ℕ) (hm : 0 < m) :
    Real.log p * (p : ℝ) ^ (-(m : ℝ) / 2) =
      ((p : ℝ) ^ (-(m : ℝ) / 2) / (m : ℝ)) * ((m : ℝ) * Real.log p) := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp

/-- **The orbital response is not uniformly bounded.**  Its values along the powers of `2` exceed
every constant. -/
theorem orbitalLogResponse_not_mem_boundedResponses :
    orbitalLogResponse ∉ boundedResponses := by
  rintro ⟨C, hC⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / Real.log 2)
  have hlt : C < (N : ℝ) * Real.log 2 := by
    rwa [div_lt_iff₀ hlog2] at hN
  have hval := hC (⟨2, Nat.prime_two⟩, N)
  have heq : |orbitalLogResponse (⟨2, Nat.prime_two⟩, N)| = (N : ℝ) * Real.log 2 := by
    rw [orbitalLogResponse]
    simp only
    rw [abs_of_nonneg (by positivity)]
    norm_num
  rw [heq] at hval
  linarith

/-- **The degree-one orbital source class is nonzero.**  Its class in the quotient of prime-power
response functionals by the uniformly bounded ones does not vanish, so no comparison whose
response is uniformly bounded can carry it. -/
theorem orbitalLogResponse_class_ne_zero :
    (Submodule.Quotient.mk orbitalLogResponse : PrimePowerResponse ⧸ boundedResponses) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact orbitalLogResponse_not_mem_boundedResponses

/-- The repository's fixed projection-correction pairing has a uniformly bounded response, so its
own class in the quotient is zero and cannot be the orbital class. -/
theorem soninSemilocalGeometricTraceResponse_class_eq_zero {a : ℝ} (ha : 0 < a) :
    (Submodule.Quotient.mk
        (fun pk : Nat.Primes × ℕ => ‖soninSemilocalGeometricTraceResponse a pk‖) :
      PrimePowerResponse ⧸ boundedResponses) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨Real.sqrt (8 * a ^ 2) * Real.sqrt (8192 * a ^ 2), fun pk => ?_⟩
  rw [abs_of_nonneg (norm_nonneg _)]
  exact norm_soninSemilocalGeometricTraceResponse_le_area a ha pk

end

end RHTower
