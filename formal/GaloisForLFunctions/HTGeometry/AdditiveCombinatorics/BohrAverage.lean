import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# The Bohr-average identity

For a unimodular multiplicative function `ψ` on a finite commutative group `Γ` and a subset
`B ⊆ Γ`, averaging a function `F` over the double translate `a ↦ a·b₁·b₂⁻¹`, `b₁, b₂ ∈ B`,
multiplies each `ψ`-Fourier coefficient of `F` by `(∑_{b ∈ B} ψ b) · conj (∑_{b ∈ B} ψ b)`.

This is the identity underlying the multiplicative dense model theorem of Matomäki--Teräväinen
(*Products of primes in arithmetic progressions*, Proposition 4.1; quoted as Proposition 3.3 of
*Linnik's problem for multiplicative functions*), where `Γ = ℤ_q^×`, `ψ` is a Dirichlet character,
and `B` is a multiplicative Bohr set.  Because the model is built as exactly such a double
average, all five conclusions of that proposition reduce to this one identity.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {Γ : Type*} [CommGroup Γ] [Fintype Γ]

/-- **The Bohr-average identity.**  Averaging a function over the double translate by a set `B`
multiplies its `ψ`-Fourier coefficient by `(∑_{b ∈ B} ψ b) · conj (∑_{b ∈ B} ψ b)`. -/
theorem bohr_convolution_identity
    (ψ : Γ → ℂ) (hmul : ∀ x y, ψ (x * y) = ψ x * ψ y)
    (hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ x⁻¹)
    (F : Γ → ℂ) (B : Finset Γ) :
    ∑ a : Γ, (∑ b₁ ∈ B, ∑ b₂ ∈ B, F (a * b₁ * b₂⁻¹)) * (starRingEnd ℂ) (ψ a)
      = (∑ b₁ ∈ B, ψ b₁) * (starRingEnd ℂ) (∑ b₂ ∈ B, ψ b₂)
        * ∑ c : Γ, F c * (starRingEnd ℂ) (ψ c) := by
  classical
  have hinner : ∀ b₁ b₂ : Γ,
      ∑ a : Γ, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a)
        = ψ b₁ * (starRingEnd ℂ) (ψ b₂) * ∑ c : Γ, F c * (starRingEnd ℂ) (ψ c) := by
    intro b₁ b₂
    have hre : ∑ c : Γ, F (c * (b₁⁻¹ * b₂) * b₁ * b₂⁻¹)
        * (starRingEnd ℂ) (ψ (c * (b₁⁻¹ * b₂)))
        = ∑ a : Γ, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a) :=
      Fintype.sum_equiv (Equiv.mulRight (b₁⁻¹ * b₂)) _ _ (fun c => rfl)
    rw [← hre, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have h1 : (b₁⁻¹ * b₂) * b₁ = b₂ := by
      rw [mul_comm b₁⁻¹ b₂, mul_assoc, inv_mul_cancel, mul_one]
    have hc : c * (b₁⁻¹ * b₂) * b₁ * b₂⁻¹ = c := by
      rw [mul_assoc c, h1, mul_inv_cancel_right]
    have hinv : (c * (b₁⁻¹ * b₂))⁻¹ = c⁻¹ * (b₁ * b₂⁻¹) := by
      rw [mul_inv, mul_inv, inv_inv]
    have hψ : (starRingEnd ℂ) (ψ (c * (b₁⁻¹ * b₂)))
        = ψ b₁ * (starRingEnd ℂ) (ψ b₂) * (starRingEnd ℂ) (ψ c) := by
      rw [hconj, hinv, hmul, hmul, ← hconj c, ← hconj b₂]
      ring
    rw [hc, hψ]
    ring
  have hdist : ∀ a : Γ, (∑ b₁ ∈ B, ∑ b₂ ∈ B, F (a * b₁ * b₂⁻¹)) * (starRingEnd ℂ) (ψ a)
      = ∑ b₁ ∈ B, ∑ b₂ ∈ B, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a) := by
    intro a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun b₁ _ => Finset.sum_mul _ _ _)
  rw [Finset.sum_congr rfl (fun a _ => hdist a), Finset.sum_comm]
  have hswap : ∀ b₁ : Γ, ∑ a : Γ, ∑ b₂ ∈ B, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a)
      = ∑ b₂ ∈ B, ∑ a : Γ, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a) := by
    intro b₁
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl (fun b₁ _ => hswap b₁)]
  have hval : ∀ b₁ ∈ B, ∑ b₂ ∈ B, ∑ a : Γ, F (a * b₁ * b₂⁻¹) * (starRingEnd ℂ) (ψ a)
      = ψ b₁ * ((starRingEnd ℂ) (∑ b₂ ∈ B, ψ b₂) * ∑ c : Γ, F c * (starRingEnd ℂ) (ψ c)) := by
    intro b₁ _
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b₂ _ => by rw [hinner b₁ b₂]; ring)
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, mul_assoc]

end GaloisForLFunctions.HTGeometry.AddComb
