import GaloisForLFunctions.RHTower.SoninSemilocalGradingNoGo
import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Rank-one incidence commutator energy

For a unit vector and an orthogonal cutoff, the rank-one source projection has exact
Hilbert--Schmidt commutator energy `2 A (1-A)`.  Replacing the cutoff by its clock involution
`2Q-1` multiplies the energy by four, giving `8 A (1-A)`.
-/

open Complex
open scoped BigOperators

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace

/-- The Hilbert--Schmidt norm of a rank-one operator is the product of the vector norms. -/
theorem hsNormSq_rankOne
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (x : E) (y : F) :
    hsNormSq (rankOne ℂ x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  let b := hsBasis ℂ F
  have hHS := isHilbertSchmidt_rankOne x y
  rw [hsNormSq_eq hHS b]
  simp_rw [rankOne_apply, norm_smul, mul_pow]
  rw [tsum_mul_right]
  have hsum : (∑' i, ‖inner ℂ y (b i)‖ ^ 2) = ‖y‖ ^ 2 := by
    calc
      _ = ∑' i, ‖inner ℂ (b i) y‖ ^ 2 := by
        apply tsum_congr
        intro i
        rw [norm_inner_symm]
      _ = _ := b.tsum_norm_inner_sq y
  rw [hsum]
  ring

private theorem crossBoundary_rankOne_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (heAdj : adjoint e = e) (psi : H) :
    crossBoundary e (rankOne ℂ psi psi) =
      rankOne ℂ ((1 - e) psi) (e psi) := by
  unfold crossBoundary
  change ((1 - e) ∘L rankOne ℂ psi psi) ∘L e = _
  rw [comp_rankOne, rankOne_comp, heAdj]

private theorem norm_sq_projection_add_complement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi : H) :
    ‖e psi‖ ^ 2 + ‖(1 - e) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  have hstar : IsStarProjection e := by
    rw [isStarProjection_iff]
    exact ⟨he, by simpa [star_eq_adjoint] using heAdj⟩
  obtain ⟨hRange, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hstar
  letI : e.range.HasOrthogonalProjection := hRange
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection psi e.range
  rw [← heq, Submodule.starProjection_orthogonal', ← heq] at hdecomp
  linarith

/-- Exact cutoff-commutator energy of a rank-one unit projection. -/
theorem hsNormSq_rankOneProjection_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    hsNormSq (ccmCommutator (rankOne ℂ psi psi) e) =
      2 * ‖e psi‖ ^ 2 * (1 - ‖e psi‖ ^ 2) := by
  have hcross := crossBoundary_rankOne_eq e heAdj psi
  have hL : IsHilbertSchmidt (crossBoundary e (rankOne ℂ psi psi)) := by
    rw [hcross]
    exact isHilbertSchmidt_rankOne ((1 - e) psi) (e psi)
  rw [hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    e (rankOne ℂ psi psi) he heAdj (by simp) hL]
  rw [hcross, hsNormSq_rankOne]
  have hdecomp := norm_sq_projection_add_complement e he heAdj psi
  rw [hpsi, one_pow] at hdecomp
  nlinarith

/-- Exact rank-one commutator energy for the clock involution `2Q-1`. -/
theorem hsNormSq_rankOneProjection_clockInvolution_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    hsNormSq (ccmCommutator (rankOne ℂ psi psi) ((2 : ℂ) • e - 1)) =
      8 * ‖e psi‖ ^ 2 * (1 - ‖e psi‖ ^ 2) := by
  let P := rankOne ℂ psi psi
  have hP : IsHilbertSchmidt P := isHilbertSchmidt_rankOne psi psi
  have hcommHS : IsHilbertSchmidt (ccmCommutator P e) := by
    unfold ccmCommutator
    exact (hP.comp_right e).sub (hP.comp_left e)
  have hcomm : ccmCommutator P ((2 : ℂ) • e - 1) =
      (2 : ℂ) • ccmCommutator P e := by
    unfold ccmCommutator
    simp only [two_smul]
    noncomm_ring
  rw [hcomm, hsNormSq_smul_eq hcommHS (2 : ℂ)]
  change ‖(2 : ℂ)‖ ^ 2 * hsNormSq (ccmCommutator P e) = _
  rw [show hsNormSq (ccmCommutator P e) =
      2 * ‖e psi‖ ^ 2 * (1 - ‖e psi‖ ^ 2) by
    simpa [P] using hsNormSq_rankOneProjection_commutator e he heAdj psi hpsi]
  norm_num
  ring

end RHTower
