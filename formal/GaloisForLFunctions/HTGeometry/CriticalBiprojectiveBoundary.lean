import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Boundary exclusion for the critical biprojective fibre

The homogeneous critical equations have no point with either homogenizing coordinate zero, provided
both projective coordinate blocks are nonzero.  This packages the three boundary faces used by the
valuative integrality argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **No projective critical solution lies at infinity.** -/
theorem critical_biprojective_boundary_exclusion
    {K : Type*} [Field K] {m n : ℕ}
    {A B : K[X]} {α β : K}
    (hAdeg : A.natDegree < m) (hBdeg : B.natDegree < n)
    (hleft : A ≠ 0 ∨ α ≠ 0) (hright : B ≠ 0 ∨ β ≠ 0)
    (hdvd : (X : K[X]) ^ (m + n) ∣
      (A + C α * X ^ m) * (B + C β * X ^ n) - C (α * β)) :
    α ≠ 0 ∧ β ≠ 0 := by
  have hα : α ≠ 0 := by
    intro hα
    have hA : A ≠ 0 := hleft.resolve_right (by simpa using hα)
    have hzero : ∀ k < m + n,
        (A * (B + C β * X ^ n)).coeff k = 0 := by
      intro k hk
      have h := Polynomial.X_pow_dvd_iff.mp hdvd k hk
      simpa [hα] using h
    by_cases hβ : β = 0
    · have hB : B ≠ 0 := hright.resolve_right (by simpa using hβ)
      have hbad := exists_low_mul_coeff_ne_zero_of_natDegree_lt hA hB hAdeg hBdeg
      obtain ⟨k, hk, hne⟩ := hbad
      exact hne (by simpa [hβ] using hzero k hk)
    · have hcoeff : (B + C β * X ^ n).coeff n ≠ 0 := by
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_pos rfl, mul_one, Polynomial.coeff_eq_zero_of_natDegree_lt hBdeg, zero_add]
        exact hβ
      exact not_all_low_mul_coeff_zero_of_coeff_ne_zero hA hAdeg hcoeff hzero
  have hβ : β ≠ 0 := by
    intro hβ
    have hB : B ≠ 0 := hright.resolve_right (by simpa using hβ)
    have hzero : ∀ k < n + m,
        (B * (A + C α * X ^ m)).coeff k = 0 := by
      intro k hk
      have h := Polynomial.X_pow_dvd_iff.mp hdvd k (by omega)
      have h' : ((A + C α * X ^ m) * B).coeff k = 0 := by
        simpa [hβ] using h
      rw [mul_comm] at h'
      exact h'
    have hcoeff : (A + C α * X ^ m).coeff m ≠ 0 := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, Polynomial.coeff_eq_zero_of_natDegree_lt hAdeg, zero_add]
      exact hα
    exact not_all_low_mul_coeff_zero_of_coeff_ne_zero hB hBdeg hcoeff hzero
  exact ⟨hα, hβ⟩

end GaloisForLFunctions.HTGeometry
