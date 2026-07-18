import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Pulling degeneracy loci back along a surjective control map

Degeneracy of a finite differential pattern is a polynomial condition on the finite jet vector, and
the zero set of a nonzero polynomial on a finite-dimensional jet space is nowhere dense.  The
Baire argument, however, must run in the infinite-dimensional space of admissible controls, not in
the jet space.

This module supplies the transfer.  A surjective continuous control map is open, so it cannot
squeeze a ball of controls into a set with empty interior.  Consequently the degenerate controls
form a nowhere-dense set, which is exactly the input the countable Baire avoidance backbone
consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A surjective continuous linear map cannot map a ball into a set with empty interior. -/
theorem interior_preimage_eq_empty_of_surjective
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : X →L[ℝ] F) (hL : Function.Surjective L)
    {Z : Set F} (hZ : interior Z = ∅) :
    interior (L ⁻¹' Z) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_interior.mp hu
  have himg : IsOpen (L '' V) := L.isOpenMap hL V hVopen
  have hsub : L '' V ⊆ Z := by
    rintro _ ⟨v, hv, rfl⟩
    exact hVsub hv
  have hmem : (L u) ∈ interior Z :=
    mem_interior.mpr ⟨L '' V, hsub, himg, ⟨u, huV, rfl⟩⟩
  rw [hZ] at hmem
  exact hmem

/-- **Control pullback of nowhere density.**  The preimage of a closed nowhere-dense set under a
surjective continuous control map is nowhere dense. -/
theorem isNowhereDense_preimage_of_surjective
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : X →L[ℝ] F) (hL : Function.Surjective L)
    {Z : Set F} (hZclosed : IsClosed Z) (hZint : interior Z = ∅) :
    IsNowhereDense (L ⁻¹' Z) :=
  isNowhereDense_of_isClosed_of_interior_eq_empty
    (hZclosed.preimage L.continuous)
    (interior_preimage_eq_empty_of_surjective L hL hZint)

/-- **Degenerate controls are nowhere dense.**  If the finite jet vector is fully controllable,
then the controls on which a fixed nonzero polynomial relation degenerates form a nowhere-dense
set.  This is the per-pattern hypothesis of the countable Baire avoidance backbone. -/
theorem isNowhereDense_degenerateControls
    {X σ : Type*} [Fintype σ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (L : X →L[ℝ] (σ → ℂ)) (hL : Function.Surjective L)
    (P : MvPolynomial σ ℂ) (hP : P ≠ 0) :
    IsNowhereDense (L ⁻¹' {x : σ → ℂ | MvPolynomial.eval x P = 0}) := by
  have hnd := mvPolynomial_zero_set_isNowhereDense P hP
  have hclosed := mvPolynomial_zero_set_isClosed P
  apply isNowhereDense_preimage_of_surjective L hL hclosed
  rw [hclosed.isNowhereDense_iff] at hnd
  exact hnd

/-- **Generic controllable nondegeneracy.**  In a Baire control space, the controls avoiding every
member of a countable family of polynomial degeneracies form a dense residual set.  Combining the
pullback with the countable avoidance backbone leaves no per-pattern side condition beyond
controllability and nonvanishing of the pattern polynomial. -/
theorem dense_residual_nondegenerateControls
    {σ : ℕ → Type*} [∀ n, Fintype (σ n)]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : ∀ n, Y →L[ℝ] (σ n → ℂ))
    (hL : ∀ n, Function.Surjective (L n))
    (P : ∀ n, MvPolynomial (σ n) ℂ) (hP : ∀ n, P n ≠ 0) :
    Dense {y : Y | ∀ n, MvPolynomial.eval (L n y) (P n) ≠ 0} := by
  have hnd : ∀ n, IsNowhereDense
      ((L n) ⁻¹' {x : σ n → ℂ | MvPolynomial.eval x (P n) = 0}) :=
    fun n => isNowhereDense_degenerateControls (L n) (hL n) (P n) (hP n)
  have hdense := dense_setOf_forall_notMem_of_isNowhereDense
    (fun n => (L n) ⁻¹' {x : σ n → ℂ | MvPolynomial.eval x (P n) = 0}) hnd
  convert hdense using 2 with y

end

end GaloisForLFunctions.HTGeometry
