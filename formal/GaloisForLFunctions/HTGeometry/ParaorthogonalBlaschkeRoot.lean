import GaloisForLFunctions.CayleySchur

/-!
# Finite paraorthogonal Blaschke root location

Let `a_i` lie in the open unit disk and let `tau` be unimodular.  Every solution of

`z * product_i ((z-a_i)/(1-conj(a_i)z)) = tau`

lies on the unit circle.  This is the factorized finite Blaschke form of paraorthogonal OPUC root
location.  The proof treats both sides of the circle: every Blaschke factor is contractive inside
and expansive outside, so the unimodular equation can hold only on the boundary.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- Squared-modulus identity controlling one Blaschke factor on both sides of the unit circle. -/
theorem blaschke_normSq_sub (a z : ℂ) :
    Complex.normSq (z - a) - Complex.normSq (1 - star a * z) =
      (Complex.normSq z - 1) * (1 - Complex.normSq a) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- A disk-root Blaschke factor is strictly expansive outside the unit circle. -/
theorem one_lt_norm_blaschke_of_norm_lt_one_of_one_lt_norm
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : 1 < ‖z‖)
    (hden : 1 - star a * z ≠ 0) :
    1 < ‖(z - a) / (1 - star a * z)‖ := by
  have hsq : ‖1 - star a * z‖ ^ 2 < ‖z - a‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    have hzsq : 1 < Complex.normSq z := by
      rw [← Complex.sq_norm]
      nlinarith [norm_nonneg z]
    have hasq : Complex.normSq a < 1 := by
      rw [← Complex.sq_norm]
      nlinarith [norm_nonneg a]
    nlinarith [blaschke_normSq_sub a z]
  have hlt : ‖1 - star a * z‖ < ‖z - a‖ := by
    nlinarith [norm_nonneg (1 - star a * z), norm_nonneg (z - a)]
  rw [norm_div]
  exact (one_lt_div (norm_pos_iff.mpr hden)).2 hlt

/-- **Finite paraorthogonal root-location theorem.**  A unimodular terminal equation for a finite
Blaschke product with all parameters in the open disk has every solution on the unit circle. -/
theorem finiteBlaschke_paraorthogonal_root_norm_eq_one
    {n : ℕ} (a : Fin n → ℂ) (τ z : ℂ)
    (ha : ∀ i, ‖a i‖ < 1) (hτ : ‖τ‖ = 1)
    (hroot : z * ∏ i, ((z - a i) / (1 - star (a i) * z)) = τ) :
    ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hz | hz | hz
  · have hden : ∀ i, 1 - star (a i) * z ≠ 0 := by
      intro i hi
      have hfac : (z - a i) / (1 - star (a i) * z) = 0 := by rw [hi]; simp
      have hprod : (∏ j, ((z - a j) / (1 - star (a j) * z))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hfac
      rw [hprod, mul_zero] at hroot
      have hnorm := congrArg norm hroot
      simp [hτ] at hnorm
    have hfac : ∀ i, ‖(z - a i) / (1 - star (a i) * z)‖ ≤ 1 := by
      intro i
      exact GaloisForLFunctions.blaschke_schur (a i) z (ha i).le hz.le (hden i)
    have hprod : ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hfac i)
    have hleft : ‖z * ∏ i, ((z - a i) / (1 - star (a i) * z))‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg z,
        norm_nonneg (∏ i, ((z - a i) / (1 - star (a i) * z)))]
    rw [hroot, hτ] at hleft
    exact ((lt_irrefl 1) hleft).elim
  · exact hz
  · have hden : ∀ i, 1 - star (a i) * z ≠ 0 := by
      intro i hi
      have hfac : (z - a i) / (1 - star (a i) * z) = 0 := by rw [hi]; simp
      have hprod : (∏ j, ((z - a j) / (1 - star (a j) * z))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hfac
      rw [hprod, mul_zero] at hroot
      have hnorm := congrArg norm hroot
      simp [hτ] at hnorm
    have hfac : ∀ i, 1 ≤ ‖(z - a i) / (1 - star (a i) * z)‖ := by
      intro i
      exact (one_lt_norm_blaschke_of_norm_lt_one_of_one_lt_norm
        (ha i) hz (hden i)).le
    have hprod : 1 ≤ ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ := by
      rw [norm_prod]
      exact Finset.one_le_prod (fun i _ => hfac i)
    have hleft : 1 < ‖z * ∏ i, ((z - a i) / (1 - star (a i) * z))‖ := by
      rw [norm_mul]
      nlinarith [norm_nonneg z,
        norm_nonneg (∏ i, ((z - a i) / (1 - star (a i) * z)))]
    rw [hroot, hτ] at hleft
    exact ((lt_irrefl 1) hleft).elim

end GaloisForLFunctions.HTGeometry
