import GaloisForLFunctions.HTGeometry.FamilyInversionGauge
import GaloisForLFunctions.HTGeometry.HerglotzFullTranslationRegularizedFreeness

/-!
# The Mobius gauge: differential independence under an invertible rational change of variable

A Mobius transformation of each member of a family is a translation, an inversion, a scaling and a
translation.  The corpus already had the affine gauges; with the inversion gauge the whole chain
closes, so a differential relation among Mobius images descends to the family itself.

This is the "maximal differential independence under rational change of variable" layer that the
Hardy-cyclicity and parabolic-orbit cards both name as missing.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The Mobius gauge.**  If the Mobius images `(a g + b) / (c g + d)` of a smooth family satisfy a
differential relation, and the transformation is invertible with nonvanishing denominator, then the
family itself satisfies one. -/
theorem familyDifferentiallyAlgebraicOn_of_mobius {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hden : ∀ i, ∀ w ∈ U, c * g i w + d ≠ 0)
    (h : FamilyDifferentiallyAlgebraicOn (fun i w => (a * g i w + b) / (c * g i w + d)) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  have hgz : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z := fun z hz i => hg i z hz
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : d ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      ring
    have ha : a ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      ring
    refine familyDifferentiallyAlgebraicOn_of_affine g (fun _ => Polynomial.C (a / d))
      (fun _ => Polynomial.C (b / d)) (fun i => ?_) hgz ?_
    · simp only [ne_eq, Polynomial.C_eq_zero, div_eq_zero_iff]
      push Not
      exact ⟨ha, hd⟩
    · refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hU ?_ h
      intro i z hz
      simp only [Polynomial.eval_C, zero_mul, zero_add]
      field_simp
      ring
  · set e : ℂ := (b * c - a * d) / c with he
    have he0 : e ≠ 0 := by
      rw [he]
      refine div_ne_zero (fun h0 => hdet ?_) hc
      linear_combination -h0
    have hsm3 : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => c * g i w + d) z := by
      intro z hz i
      exact (contDiffAt_const.mul (hg i z hz)).add contDiffAt_const
    have hsm2 : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => (c * g i w + d)⁻¹) z := by
      intro z hz i
      exact (hsm3 z hz i).inv (hden i z hz)
    have hsm1 : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => e * (c * g i w + d)⁻¹) z := by
      intro z hz i
      exact contDiffAt_const.mul (hsm2 z hz i)
    -- strip the additive constant
    have h1 : FamilyDifferentiallyAlgebraicOn (fun i w => e * (c * g i w + d)⁻¹) U := by
      refine familyDifferentiallyAlgebraicOn_of_add_polynomial _ (fun _ => Polynomial.C (a / c))
        hsm1 ?_
      refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hU ?_ h
      intro i z hz
      have hne : c * g i z + d ≠ 0 := hden i z hz
      have hne' : g i z * c + d ≠ 0 := by rwa [mul_comm] at hne
      simp only [Polynomial.eval_C, he]
      field_simp
      ring
    -- strip the multiplicative constant
    have h2 : FamilyDifferentiallyAlgebraicOn (fun i w => (c * g i w + d)⁻¹) U := by
      refine familyDifferentiallyAlgebraicOn_of_mul_polynomial _ (fun _ => Polynomial.C e)
        (fun i => by simpa using he0) hsm2 ?_
      refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hU ?_ h1
      intro i z hz
      simp only [Polynomial.eval_C]
    -- invert
    have h3 : FamilyDifferentiallyAlgebraicOn (fun i w => c * g i w + d) U :=
      familyDifferentiallyAlgebraicOn_of_inv hU (fun i w hw => hsm3 w hw i)
        (fun i w hw => hden i w hw) h2
    -- strip the affine change
    refine familyDifferentiallyAlgebraicOn_of_affine g (fun _ => Polynomial.C c)
      (fun _ => Polynomial.C d) (fun i => by simpa using hc) hgz ?_
    refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hU ?_ h3
    intro i z hz
    simp only [Polynomial.eval_C]
    ring

end

end GaloisForLFunctions.HTGeometry
