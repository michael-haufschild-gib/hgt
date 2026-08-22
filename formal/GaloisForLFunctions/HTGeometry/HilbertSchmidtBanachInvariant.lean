import GaloisForLFunctions.HTGeometry.HilbertSchmidtBanach

/-!
# Banach fixed point on an invariant Hilbert–Schmidt class

A contraction preserving a class of operators that is closed under Hilbert–Schmidt limits has a
fixed point in that class.  No ball has to be prescribed: the geometric series of the increments
supplies its own radius, so the ball version applies with the radius read off from the first step.
-/

open scoped BigOperators
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Hilbert–Schmidt convergence implies operator-norm convergence. -/
lemma tendsto_of_hs_limit {Yn : ℕ → (E →L[ℂ] E)} {Z : E →L[ℂ] E}
    (hHS : ∀ n, IsHilbertSchmidt (Yn n - Z))
    (hlim : Tendsto (fun n => hsNorm (Yn n - Z)) atTop (nhds 0)) :
    Tendsto Yn atTop (nhds Z) := by
  have hnorm : Tendsto (fun n => ‖Yn n - Z‖) atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => norm_le_hsNorm (hHS n)) hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- **Banach fixed point on an invariant class.**  A `θ`-contraction of a class closed under
Hilbert–Schmidt limits, all of whose members differ from a base point by a Hilbert–Schmidt
operator, has a fixed point in the class. -/
theorem exists_fixedPoint_hs_invariant {G : (E →L[ℂ] E) → (E →L[ℂ] E)} {X₀ : E →L[ℂ] E} {θ : ℝ}
    {P : (E →L[ℂ] E) → Prop} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hP0 : P X₀)
    (hPG : ∀ X : E →L[ℂ] E, P X → P (G X))
    (hPHS : ∀ X : E →L[ℂ] E, P X → IsHilbertSchmidt (X - X₀))
    (hPclosed : ∀ (Y : ℕ → (E →L[ℂ] E)) (Z : E →L[ℂ] E), (∀ n, P (Y n)) →
      (∀ n, IsHilbertSchmidt (Y n - Z)) → Tendsto (fun n => hsNorm (Y n - Z)) atTop (nhds 0) →
      P Z)
    (hcontr : ∀ X Y : E →L[ℂ] E, P X → P Y → hsNorm (G X - G Y) ≤ θ * hsNorm (X - Y)) :
    ∃ X : E →L[ℂ] E, P X ∧ IsHilbertSchmidt (X - X₀) ∧ G X = X := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  obtain ⟨X, hP, hHSX, -, hfix⟩ :=
    exists_fixedPoint_hs (G := G) (X₀ := X₀) (r := (1 - θ)⁻¹ * hsNorm (G X₀ - X₀))
      (θ := θ) (P := P) hθ0 hθ1 hP0
      (fun X hX _ _ => hPG X hX)
      hPclosed
      (fun X hX _ _ => hPHS (G X) (hPG X hX))
      (fun X Y hX _ _ hY _ _ => hcontr X Y hX hY)
      (by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h1θ), one_mul])
  exact ⟨X, hP, hHSX, hfix⟩

end

end GaloisForLFunctions.HTGeometry
