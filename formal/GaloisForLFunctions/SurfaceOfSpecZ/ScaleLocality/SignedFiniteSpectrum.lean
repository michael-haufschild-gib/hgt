import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Finite spectra are detected by signed translations

A polynomial in a sufficiently short translation annihilates all but one
exponent. Its coefficient norm bounds the surviving mode by finitely many
samples. This works for arbitrary complex coefficients and real exponents
as well as nonreal ones; no averaging or conjugation symmetry is used.
-/

open Complex Set
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- A short real step separates the exponential images of any finite spectrum. -/
theorem exists_step_exp_injOn (S : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun z : ℂ => Complex.exp (z * δ)) (S : Set ℂ) := by
  classical
  let B : ℝ := ∑ z ∈ S, |z.im|
  have hB : 0 ≤ B := Finset.sum_nonneg fun z _ => abs_nonneg z.im
  let δ : ℝ := Real.pi / (B + 1)
  have hδ : 0 < δ := div_pos Real.pi_pos (by linarith only [hB])
  have hδid : (B + 1) * δ = Real.pi := by
    dsimp only [δ]
    field_simp [show B + 1 ≠ 0 by linarith only [hB]]
  have hstrip : ∀ z ∈ S, |(z * (δ : ℂ)).im| < Real.pi := by
    intro z hz
    have hzB : |z.im| ≤ B :=
      Finset.single_le_sum (fun w _ => abs_nonneg w.im) hz
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      abs_mul, abs_of_pos hδ]
    calc |z.im| * δ ≤ B * δ := mul_le_mul_of_nonneg_right hzB hδ.le
      _ < (B + 1) * δ := mul_lt_mul_of_pos_right (by linarith only) hδ
      _ = Real.pi := hδid
  refine ⟨δ, hδ, fun z hz w hw he => ?_⟩
  have hz' := abs_lt.mp (hstrip z hz)
  have hw' := abs_lt.mp (hstrip w hw)
  have hzw := Complex.exp_inj_of_neg_pi_lt_of_le_pi hz'.1 hz'.2.le hw'.1 hw'.2.le he
  exact mul_right_cancel₀ (by exact_mod_cast hδ.ne' : (δ : ℂ) ≠ 0) hzw

/-- A polynomial in translation acts diagonally on a finite exponential spectrum. -/
theorem polynomial_translation_cexp (P : Polynomial ℂ) (S : Finset ℂ)
    (c : ℂ → ℂ) (δ T : ℝ) :
    (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j *
      (∑ z ∈ S, c z * Complex.exp (z * ((T + j * δ : ℝ) : ℂ)))) =
      ∑ z ∈ S, c z * Complex.exp (z * T) * P.eval (Complex.exp (z * δ)) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : z * ((T + j * δ : ℝ) : ℂ) = z * T + (j : ℂ) * (z * δ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul]
  ring

/-- Every nonzero coefficient forces a large absolute sample within a fixed distance
of every center, even when the other coefficients have arbitrary phases. -/
theorem finite_spectrum_dense_norm (S : Finset ℂ) (c : ℂ → ℂ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hc₀ : c z₀ ≠ 0) :
    ∃ B η : ℝ, 0 < B ∧ 0 < η ∧ ∀ T : ℝ, ∃ t ∈ Icc T (T + B),
      η * Real.exp (z₀.re * T) ≤ ‖∑ z ∈ S, c z * Complex.exp (z * t)‖ := by
  classical
  obtain ⟨δ, hδ, hinj⟩ := exists_step_exp_injOn S
  let P : Polynomial ℂ := ∏ z ∈ S.erase z₀, Polynomial.X - Polynomial.C (Complex.exp (z * δ))
  have hPkeep : P.eval (Complex.exp (z₀ * δ)) ≠ 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    apply sub_ne_zero.mpr
    intro he
    exact (Finset.mem_erase.mp hz).1 (hinj (Finset.mem_erase.mp hz).2 hz₀ he.symm)
  have hPkill : ∀ z ∈ S, z ≠ z₀ → P.eval (Complex.exp (z * δ)) = 0 := by
    intro z hz hne
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hz⟩)
    exact sub_self _
  have hidentity (T : ℝ) :
      (∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j *
        (∑ z ∈ S, c z * Complex.exp (z * ((T + j * δ : ℝ) : ℂ)))) =
        c z₀ * Complex.exp (z₀ * T) * P.eval (Complex.exp (z₀ * δ)) := by
    rw [polynomial_translation_cexp]
    apply Finset.sum_eq_single z₀
    · intro z hz hne
      rw [hPkill z hz hne, mul_zero]
    · exact fun h => (h hz₀).elim
  let A : ℝ := ‖c z₀‖ * ‖P.eval (Complex.exp (z₀ * δ))‖
  let C : ℝ := (∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖) + 1
  let η : ℝ := A / C
  have hA : 0 < A := mul_pos (norm_pos_iff.mpr hc₀) (norm_pos_iff.mpr hPkeep)
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp only [C]
    linarith only [hs]
  have hη : 0 < η := div_pos hA hC
  have hCη : C * η = A := by
    dsimp only [η]
    field_simp [hC.ne']
  refine ⟨P.natDegree * δ + 1, η, by positivity, hη, fun T => ?_⟩
  have hexists : ∃ j ∈ Finset.range (P.natDegree + 1),
      η * Real.exp (z₀.re * T) ≤
        ‖∑ z ∈ S, c z * Complex.exp (z * ((T + j * δ : ℝ) : ℂ))‖ := by
    by_contra h
    push Not at h
    have he : ‖∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j *
        (∑ z ∈ S, c z * Complex.exp (z * ((T + j * δ : ℝ) : ℂ)))‖ =
        A * Real.exp (z₀.re * T) := by
      rw [hidentity]
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      dsimp only [A]
      ring
    have hu : A * Real.exp (z₀.re * T) ≤
        (∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖) *
          (η * Real.exp (z₀.re * T)) := by
      rw [← he, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (h j hj).le (norm_nonneg _)
    have hlt : (∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖) *
        (η * Real.exp (z₀.re * T)) < C * (η * Real.exp (z₀.re * T)) :=
      mul_lt_mul_of_pos_right (by dsimp only [C]; linarith only)
        (mul_pos hη (Real.exp_pos _))
    rw [← mul_assoc, hCη] at hlt
    exact (not_lt_of_ge hu) hlt
  obtain ⟨j, hj, hlarge⟩ := hexists
  refine ⟨T + j * δ, ⟨?_, ?_⟩, hlarge⟩
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hδ.le)
  · have hj' : (j : ℝ) ≤ P.natDegree := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hm := mul_le_mul_of_nonneg_right hj' hδ.le
    linarith only [hm]

#print axioms finite_spectrum_dense_norm

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
