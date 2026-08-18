import GaloisForLFunctions.HTGeometry.TensorPolarizationAmplification

/-!
# Amplified realization and port-budget selection

Tensor formation and geometric port fusion are different operations.  This file gives the legal
bridge between them: an injective map preserving a Hermitian quadratic form cannot reduce negative
index.  Combined with tensor-polarization amplification, one target budget strictly below the
previous total tensor rank forces the base packet to have no negative channel.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex

noncomputable section

/-- Negative index cannot decrease under an injective quadratic-form-preserving realization. -/
theorem negIndex_le_of_injective_formEmbedding
    {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I I ℂ) (Q : Matrix J J ℂ)
    (S : (I → ℂ) →ₗ[ℂ] (J → ℂ))
    (hS : Function.Injective S)
    (hform : ∀ x, hermQuad Q (S x) = hermQuad H x) :
    hermNegIndex H ≤ hermNegIndex Q := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hmap : IsPosDefOn (-Q) (W.map S) := by
    rintro y ⟨x, hx, rfl⟩ hy0
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    have hpos := hW x hx hx0
    rw [hermQuad_neg] at hpos ⊢
    rw [hform]
    exact hpos
  have hfinrank : Module.finrank ℂ (W.map S) = Module.finrank ℂ W :=
    ((Submodule.equivMapOfInjective S hS W).symm).finrank_eq
  rw [hermNegIndex, hermNegIndex, ← hrank, ← hfinrank]
  exact finrank_le_posIndex hmap

/-- A single admitted tensor depth with target budget below the previous total tensor rank selects
the positive chamber.  No uniform budget or limiting argument is required. -/
theorem tensorPolar_zero_of_strict_portBudget
    {p q d B : ℕ} (hp : 0 < p)
    (hadmit : tensorPolarNeg p q (d + 1) ≤ B)
    (hsubrank : B < (p + q) ^ d) :
    q = 0 := by
  by_contra hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hfloor := tensorPolar_negative_ge_total_prev hp hqpos d
  omega

/-- Any budget family admitting every tensor depth selects positivity as soon as it is strictly
subrank at one finite depth. -/
theorem tensorPolar_zero_of_eventual_subrankBudget
    {p q : ℕ} (hp : 0 < p) (B : ℕ → ℕ)
    (hadmit : ∀ d, tensorPolarNeg p q d ≤ B d)
    (hsubrank : ∃ d, B (d + 1) < (p + q) ^ d) :
    q = 0 := by
  obtain ⟨d, hd⟩ := hsubrank
  exact tensorPolar_zero_of_strict_portBudget hp (hadmit (d + 1)) hd

/-- **Amplified realization selection.**  A formed source packet whose negative sector embeds
form-preservingly in a port-budgeted target is positive whenever the target budget is strictly
smaller than the previous total tensor rank. -/
theorem tensorPolar_zero_of_formEmbedding_portBudget
    {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I I ℂ) (Q : Matrix J J ℂ)
    (S : (I → ℂ) →ₗ[ℂ] (J → ℂ))
    {p q d B : ℕ} (hp : 0 < p)
    (hformed : tensorPolarNeg p q (d + 1) ≤ hermNegIndex H)
    (hS : Function.Injective S)
    (hform : ∀ x, hermQuad Q (S x) = hermQuad H x)
    (hport : hermNegIndex Q ≤ B)
    (hsubrank : B < (p + q) ^ d) :
    q = 0 := by
  apply tensorPolar_zero_of_strict_portBudget hp
  · exact hformed.trans ((negIndex_le_of_injective_formEmbedding H Q S hS hform).trans hport)
  · exact hsubrank

/-- Closed universal law combining form-embedding inertia monotonicity with strict subrank tensor
selection. -/
def AmplifiedPortBudgetSelectionLaw : Prop :=
  (∀ {I J : Type*} [Fintype I] [Fintype J]
      (H : Matrix I I ℂ) (Q : Matrix J J ℂ)
      (S : (I → ℂ) →ₗ[ℂ] (J → ℂ)),
      Function.Injective S →
      (∀ x, hermQuad Q (S x) = hermQuad H x) →
      hermNegIndex H ≤ hermNegIndex Q) ∧
  (∀ {p q d B : ℕ}, 0 < p →
      tensorPolarNeg p q (d + 1) ≤ B →
      B < (p + q) ^ d → q = 0)

theorem amplifiedPortBudgetSelection_closed :
    AmplifiedPortBudgetSelectionLaw := by
  exact ⟨fun H Q S hS hform =>
      negIndex_le_of_injective_formEmbedding H Q S hS hform,
    fun hp hadmit hsubrank =>
      tensorPolar_zero_of_strict_portBudget hp hadmit hsubrank⟩

end


end GaloisForLFunctions.HTGeometry
