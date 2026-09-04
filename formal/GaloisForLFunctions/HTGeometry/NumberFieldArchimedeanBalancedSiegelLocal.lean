import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedEntryComparison
import GaloisForLFunctions.HTGeometry.SiegelIsometryVanishing
import GaloisForLFunctions.HTGeometry.ComplexSiegelIsometryVanishing

/-!
# Local bounded-isometry consumers for number-field Siegel finiteness

These two lemmas isolate the real and Hermitian linear algebra in Siegel's finiteness proof.  The
arithmetic input is an externally established support law for the inverse transition: every
nonzero inverse entry may compare only uniformly comparable source weights.  Over a number field
that support law is supplied globally by the algebraic-integer product formula.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical ComplexOrder

noncomputable section

variable {n : ℕ}

/-- Real bounded-isometry consumer with the inverse support comparison exposed explicitly. -/
theorem real_siegelTransition_entry_bound_of_inverseSupport
    {J J' : JacobiData n} {t u C Q Cu : ℝ}
    (ht : 1 ≤ t) (hC : 0 < C) (hQ : 0 < Q) (hCu : 0 ≤ Cu)
    (hS : J.IsSiegel t u) (hS' : J'.IsSiegel t u)
    {γ δ : Matrix (Fin n) (Fin n) ℝ}
    (hγδ : γ * δ = 1) (hδγ : δ * γ = 1)
    (hform : J'.form = Matrix.transpose γ * J.form * γ)
    (hcmp : ∀ i, J'.d i ≤ C * J.d i)
    (hδ : ∀ a b, δ a b ≠ 0 → J.d a ≤ Q * J.d b)
    (hUinv : ∀ i j, |J.U⁻¹ i j| ≤ Cu)
    (k i : Fin n) :
    |γ k i| ≤
      (n : ℝ) * ((n : ℝ) *
        (Cu * Real.sqrt (C * (t ^ n * (Q * t ^ n)))) * u) := by
  have hUunit : IsUnit J.U.det := by rw [J.det_eq_one]; exact isUnit_one
  have hU'unit : IsUnit J'.U.det := by rw [J'.det_eq_one]; exact isUnit_one
  let M : Matrix (Fin n) (Fin n) ℝ := J.U * γ * J'.U⁻¹
  let P : Matrix (Fin n) (Fin n) ℝ := J'.U * δ * J.U⁻¹
  have hiso : Matrix.transpose M * Matrix.diagonal J.d * M = Matrix.diagonal J'.d :=
    weightedIsometry_congr hform
  have hMP : M * P = 1 := by
    dsimp [M, P]
    calc
      J.U * γ * J'.U⁻¹ * (J'.U * δ * J.U⁻¹) =
          J.U * γ * (J'.U⁻¹ * J'.U) * δ * J.U⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = J.U * γ * δ * J.U⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hU'unit, Matrix.mul_one]
      _ = 1 := by
        rw [Matrix.mul_assoc J.U γ δ, hγδ, Matrix.mul_one,
          Matrix.mul_nonsing_inv _ hUunit]
  have hPeq : isometryInv J J' M = P := isometryInv_eq hiso hMP
  let T : ℝ := t ^ n * (Q * t ^ n)
  have hT : 0 ≤ T := by positivity
  let Bm : ℝ := Real.sqrt (C * T)
  have hMbound : ∀ p q : Fin n, |M p q| ≤ Bm := by
    intro p q
    have hdp : 0 < J.d p := J.pos p
    by_cases hbig : t ^ n * (Q * (t ^ n * J.d p)) < J.d q
    · have hzero : P q p = 0 :=
        triangular_conjugate_entry_zero ht hQ.le hS hδ hbig
      have hval : J.d p * M p q / J'.d q = 0 := by
        have heq := congrFun (congrFun hPeq q) p
        rw [hzero] at heq
        exact heq
      have hMz : M p q = 0 := by
        rcases div_eq_zero_iff.1 hval with hmul | hden
        · exact (mul_eq_zero.mp hmul).resolve_left hdp.ne'
        · exact absurd hden (J'.pos q).ne'
      rw [hMz, abs_zero]
      exact Real.sqrt_nonneg _
    · have hdq : J.d q ≤ T * J.d p := by
        change J.d q ≤ t ^ n * (Q * t ^ n) * J.d p
        nlinarith [not_lt.mp hbig]
      have h1 : J.d p * (M p q) ^ 2 ≤ J'.d q :=
        weightedIsometry_entry_le hiso p q
      have h3 : J.d p * (M p q) ^ 2 ≤ C * (T * J.d p) :=
        h1.trans ((hcmp q).trans (mul_le_mul_of_nonneg_left hdq hC.le))
      have h4 : (M p q) ^ 2 ≤ C * T := by
        apply le_of_mul_le_mul_left (a := J.d p) (b := (M p q) ^ 2) (c := C * T)
        · calc
          J.d p * (M p q) ^ 2 ≤ C * (T * J.d p) := h3
          _ = J.d p * (C * T) := by ring
        · exact hdp
      have hs := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq_eq_abs] at hs
  have hgamma : γ = J.U⁻¹ * M * J'.U := by
    dsimp [M]
    calc
      γ = (J.U⁻¹ * J.U) * γ * (J'.U⁻¹ * J'.U) := by
        rw [Matrix.nonsing_inv_mul _ hUunit, Matrix.nonsing_inv_mul _ hU'unit,
          Matrix.one_mul, Matrix.mul_one]
      _ = J.U⁻¹ * (J.U * γ * J'.U⁻¹) * J'.U := by
        simp only [Matrix.mul_assoc]
  rw [hgamma]
  exact entry_abs_mul_le (fun p q ↦ entry_abs_mul_le hUinv hMbound p q) hS'.2 k i

/-- Hermitian bounded-isometry consumer with the inverse support comparison exposed explicitly. -/
theorem complex_siegelTransition_entry_bound_of_inverseSupport
    {J J' : ComplexJacobiData n} {t u C Q Cu : ℝ}
    (ht : 1 ≤ t) (hC : 0 < C) (hQ : 0 < Q) (hCu : 0 ≤ Cu)
    (hS : J.IsSiegel t u) (hS' : J'.IsSiegel t u)
    {γ δ : Matrix (Fin n) (Fin n) ℂ}
    (hγδ : γ * δ = 1) (hδγ : δ * γ = 1)
    (hform : J'.form = Matrix.conjTranspose γ * J.form * γ)
    (hcmp : ∀ i, J'.d i ≤ C * J.d i)
    (hδ : ∀ a b, δ a b ≠ 0 → J.d a ≤ Q * J.d b)
    (hUinv : ∀ i j, ‖J.U⁻¹ i j‖ ≤ Cu)
    (k i : Fin n) :
    ‖γ k i‖ ≤
      (n : ℝ) * ((n : ℝ) *
        (Cu * Real.sqrt (C * (t ^ n * (Q * t ^ n)))) * u) := by
  have hUunit : IsUnit J.U.det := by rw [J.det_eq_one]; exact isUnit_one
  have hU'unit : IsUnit J'.U.det := by rw [J'.det_eq_one]; exact isUnit_one
  let M : Matrix (Fin n) (Fin n) ℂ := J.U * γ * J'.U⁻¹
  let P : Matrix (Fin n) (Fin n) ℂ := J'.U * δ * J.U⁻¹
  have hiso : Matrix.conjTranspose M * Matrix.diagonal (fun i ↦ (J.d i : ℂ)) * M =
      Matrix.diagonal (fun i ↦ (J'.d i : ℂ)) :=
    complex_weightedIsometry_congr hform
  have hMP : M * P = 1 := by
    dsimp [M, P]
    calc
      J.U * γ * J'.U⁻¹ * (J'.U * δ * J.U⁻¹) =
          J.U * γ * (J'.U⁻¹ * J'.U) * δ * J.U⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = J.U * γ * δ * J.U⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hU'unit, Matrix.mul_one]
      _ = 1 := by
        rw [Matrix.mul_assoc J.U γ δ, hγδ, Matrix.mul_one,
          Matrix.mul_nonsing_inv _ hUunit]
  have hPeq : complexIsometryInv J J' M = P := complexIsometryInv_eq hiso hMP
  let T : ℝ := t ^ n * (Q * t ^ n)
  have hT : 0 ≤ T := by positivity
  let Bm : ℝ := Real.sqrt (C * T)
  have hMbound : ∀ p q : Fin n, ‖M p q‖ ≤ Bm := by
    intro p q
    have hdp : 0 < J.d p := J.pos p
    by_cases hbig : t ^ n * (Q * (t ^ n * J.d p)) < J.d q
    · have hzero : P q p = 0 :=
        complex_triangular_conjugate_entry_zero ht hQ.le hS hδ hbig
      have hval : (J.d p : ℂ) * star (M p q) / (J'.d q : ℂ) = 0 := by
        have heq := congrFun (congrFun hPeq q) p
        rw [hzero] at heq
        exact heq
      have hMz : M p q = 0 := by
        rcases div_eq_zero_iff.1 hval with hmul | hden
        · have hs : star (M p q) = 0 :=
            (mul_eq_zero.mp hmul).resolve_left (Complex.ofReal_ne_zero.mpr hdp.ne')
          exact star_eq_zero.mp hs
        · exact absurd hden (Complex.ofReal_ne_zero.mpr (J'.pos q).ne')
      rw [hMz, norm_zero]
      exact Real.sqrt_nonneg _
    · have hdq : J.d q ≤ T * J.d p := by
        change J.d q ≤ t ^ n * (Q * t ^ n) * J.d p
        nlinarith [not_lt.mp hbig]
      have h1 : J.d p * ‖M p q‖ ^ 2 ≤ J'.d q :=
        complex_weightedIsometry_entry_le hiso p q
      have h3 : J.d p * ‖M p q‖ ^ 2 ≤ C * (T * J.d p) :=
        h1.trans ((hcmp q).trans (mul_le_mul_of_nonneg_left hdq hC.le))
      have h4 : ‖M p q‖ ^ 2 ≤ C * T := by
        apply le_of_mul_le_mul_left (a := J.d p) (b := ‖M p q‖ ^ 2) (c := C * T)
        · calc
          J.d p * ‖M p q‖ ^ 2 ≤ C * (T * J.d p) := h3
          _ = J.d p * (C * T) := by ring
        · exact hdp
      have hs := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  have hgamma : γ = J.U⁻¹ * M * J'.U := by
    dsimp [M]
    calc
      γ = (J.U⁻¹ * J.U) * γ * (J'.U⁻¹ * J'.U) := by
        rw [Matrix.nonsing_inv_mul _ hUunit, Matrix.nonsing_inv_mul _ hU'unit,
          Matrix.one_mul, Matrix.mul_one]
      _ = J.U⁻¹ * (J.U * γ * J'.U⁻¹) * J'.U := by
        simp only [Matrix.mul_assoc]
  rw [hgamma]
  exact complex_entry_norm_mul_le
    (fun p q ↦ complex_entry_norm_mul_le hUinv hMbound p q) hS'.2 k i

end

end GaloisForLFunctions.HTGeometry
