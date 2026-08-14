import GaloisForLFunctions.HTGeometry.CountableMultivariateAffineJetPattern
import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Transfer of jet flatness through an affine frame

A source whose ordered coordinate jets of order `n` all vanish at a point has a vanishing order-`n`
iterated derivative there, because a multilinear form vanishing on every tuple of basis vectors is
zero.  Combined with the exact affine chain rule for polarized jets this shows that flatness at
`σ(x)` kills every mixed jet of the pullback `f ∘ σ` at `x`.  Consequently two sources with the
same coordinate jets at the packet points have the same pulled-back observations, which is what
turns Hermite interpolation into prescription of an affine jet packet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A multilinear form vanishing on every coordinate tuple is zero, so vanishing of all ordered
coordinate jets of one order is vanishing of the iterated derivative of that order. -/
theorem iteratedFDeriv_eq_zero_of_orderedPartialJetEvalCLM_eq_zero
    {d n : ℕ} (x : Fin d → ℂ) (u : MultivariateEntire d)
    (h : ∀ word : Fin n → Fin d, orderedPartialJetEvalCLM x word u = 0) :
    iteratedFDeriv ℂ n u.1 x = 0 := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (fun _ : Fin n ↦ Pi.basisFun ℂ (Fin d)) ?_
  intro v
  have hv := h v
  rw [orderedPartialJetEvalCLM_eq_iteratedFDeriv] at hv
  simpa [coordinateJetDirection, Pi.basisFun_apply] using hv

/-- Flatness in every coordinate direction is flatness in every direction. -/
theorem polarizedJetEvalCLM_eq_zero_of_orderedPartialJetEvalCLM_eq_zero
    {d n : ℕ} (x : Fin d → ℂ) (u : MultivariateEntire d)
    (h : ∀ word : Fin n → Fin d, orderedPartialJetEvalCLM x word u = 0)
    (dirs : Fin n → (Fin d → ℂ)) :
    polarizedJetEvalCLM x dirs u = 0 := by
  rw [polarizedJetEvalCLM_eq_iteratedFDeriv,
    iteratedFDeriv_eq_zero_of_orderedPartialJetEvalCLM_eq_zero x u h]
  simp

/-- **Affine transfer of flatness.**  If every ordered coordinate jet of order below `m` vanishes
at the image point `e x`, then every mixed jet of the affine pullback of total degree below `m`
vanishes at `x`. -/
theorem affineMultiIndexJetEvalCLM_eq_zero_of_flat
    {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) (x : Fin d → ℂ) (m : ℕ)
    (u : MultivariateEntire d)
    (h : ∀ n < m, ∀ word : Fin n → Fin d, orderedPartialJetEvalCLM (e x) word u = 0)
    (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    affineMultiIndexJetEvalCLM e x a u = 0 := by
  rw [affineMultiIndexJetEvalCLM_apply, multiIndexJetEvalCLM_apply,
    orderedPartialJetEvalCLM_apply, polarizedJetEvalCLM_affinePullback]
  refine polarizedJetEvalCLM_eq_zero_of_orderedPartialJetEvalCLM_eq_zero (e x) u ?_ _
  intro word
  exact h _ (by rw [card_multiIndexSlot]; exact ha) word

/-- **Affine observations depend only on the coordinate jets at the image point.**  Two sources
agreeing to order `m` at `e x` have the same mixed pullback jets of total degree below `m`. -/
theorem affineMultiIndexJetEvalCLM_congr_of_orderedPartialJetEvalCLM_eq
    {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) (x : Fin d → ℂ) (m : ℕ)
    (f g : MultivariateEntire d)
    (h : ∀ n < m, ∀ word : Fin n → Fin d,
      orderedPartialJetEvalCLM (e x) word f = orderedPartialJetEvalCLM (e x) word g)
    (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    affineMultiIndexJetEvalCLM e x a f = affineMultiIndexJetEvalCLM e x a g := by
  have hzero : affineMultiIndexJetEvalCLM e x a (f - g) = 0 := by
    refine affineMultiIndexJetEvalCLM_eq_zero_of_flat e x m (f - g) ?_ a ha
    intro n hn word
    rw [map_sub, h n hn word, sub_self]
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end

end GaloisForLFunctions.HTGeometry
