import GaloisForLFunctions.HTGeometry.SectionValueAnalytic
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumProper

/-!
# The values of a continuous section are polynomials

Each value of the section is entire (`SectionValueAnalytic`) and of polynomial growth, by the Cauchy
bound of `AlgebraSpectrumProper` applied to a monic relation for the element.  Liouville's growth
theorem then makes it a polynomial.  This completes the analytic half of step (c) of the general
simple connectedness of the affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **The values of a continuous section are polynomials.** -/
theorem exists_polynomial_section_apply [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n)
    {σ : ℂ → AlgSpec B} (hσc : Continuous σ) (hσ : ∀ s, AlgSpec.proj B (σ s) = s) (b : B) :
    ∃ Q : ℂ[X], ∀ s : ℂ, σ s b = Q.eval s := by
  classical
  haveI : Algebra.IsIntegral ℂ[X] B := Algebra.IsIntegral.of_finite ℂ[X] B
  obtain ⟨r, hrm, hrz⟩ : ∃ r : ℂ[X][X], r.Monic ∧ Polynomial.aeval b r = 0 := by
    obtain ⟨r, hrm, hrz⟩ := Algebra.IsIntegral.isIntegral (R := ℂ[X]) b
    exact ⟨r, hrm, by simpa [Polynomial.aeval_def] using hrz⟩
  have hdiff : Differentiable ℂ fun s => σ s b := fun s =>
    (analyticAt_section_apply hn e h hσc hσ b s).differentiableAt
  set N : ℕ := (Finset.range r.natDegree).sup fun i => (r.coeff i).natDegree with hN
  set A : ℝ := 1 + ∑ i ∈ Finset.range r.natDegree,
    ∑ j ∈ Finset.range ((r.coeff i).natDegree + 1), ‖(r.coeff i).coeff j‖ with hA
  have hgrowth : ∀ s : ℂ, ‖σ s b‖ ≤ A * (max 1 ‖s‖) ^ N := by
    intro s
    set M : ℝ := max 1 ‖s‖ with hM
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hMN : (1 : ℝ) ≤ M ^ N := one_le_pow₀ hM1
    have hb := AlgSpec.norm_apply_le_of_monic hrm hrz (σ s)
    rw [hσ s] at hb
    refine hb.trans ?_
    have hsum : ∑ i ∈ Finset.range r.natDegree, ‖(r.coeff i).eval s‖ ≤
        (A - 1) * M ^ N := by
      rw [hA]
      simp only [add_sub_cancel_left, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [← Finset.sum_mul]
      refine (norm_eval_le_sum (r.coeff i) s).trans ?_
      have hle : (r.coeff i).natDegree ≤ N := by
        rw [hN]
        exact Finset.le_sup (f := fun k => (r.coeff k).natDegree) hi
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hle)
        (Finset.sum_nonneg fun j _ => norm_nonneg ((r.coeff i).coeff j))
    have hA1 : (1 : ℝ) ≤ A := by
      rw [hA]
      have : (0 : ℝ) ≤ ∑ i ∈ Finset.range r.natDegree,
          ∑ j ∈ Finset.range ((r.coeff i).natDegree + 1), ‖(r.coeff i).coeff j‖ :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
      linarith
    refine max_le ?_ (hsum.trans ?_)
    · nlinarith
    · nlinarith
  obtain ⟨Q, hQ⟩ := Bottcher.exists_polynomial_of_entire_polyGrowth hdiff hgrowth
  exact ⟨Q, hQ⟩

end

end GaloisForLFunctions.HTGeometry
