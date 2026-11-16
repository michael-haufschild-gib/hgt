import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainIdealSums
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation

/-! # Primitive coefficients in angular plain sums

The finite conductor character identifies the plain-slot coefficients with the
Dirichlet coefficients of the actual primitive Grössencharacter L-function.
The angular smooth-sum bound therefore applies at its primitive conductor.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap nonZeroDivisors
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open HeckeFamily HeckeRowClosure HeckeInverseAmplification SchwartzPlanePoisson
local notation "O" => Eisenstein.O

/-- The primitive finite part of a ray class character, in the plain-slot family. -/
def grossenFiniteCharacter (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) : Character :=
  Character.ofResidue (heckeFiniteConductor 𝔪 ψ) (heckeFiniteConductor_ne_bot 𝔪 ψ)
    (heckePrimitiveFiniteCharacter 𝔪 ψ) (heckePrimitiveFiniteCharacter_globalUnit 𝔪 ψ)

@[simp] theorem grossenFiniteCharacter_modulus (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) :
    (grossenFiniteCharacter 𝔪 ψ).modulus = heckeFiniteConductor 𝔪 ψ := rfl

/-- Equality holds on every ideal, including the zero ideal and conductor divisors. -/
theorem idealCoeff_grossenFiniteCharacter (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (I : Ideal O) :
    idealCoeff (grossenFiniteCharacter 𝔪 ψ) I = primitiveIdealValue 𝔪 ψ I := by
  by_cases hI : I = ⊥
  · subst I
    exact (map_zero _).trans (map_zero _).symm
  · rw [← span_cubicIdealGenerator I]
    rw [idealCoeff_span _ (cubicIdealGenerator_ne_zero I hI),
      primitiveIdealValue_span_singleton _ _ (cubicIdealGenerator_ne_zero I hI)]
    rfl

/-- The actual primitive Dirichlet series uses exactly the angular plain-slot coefficients. -/
theorem grossenLFunction_eq_plain_coefficients (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w = ∑' I : (Ideal O)⁰,
      idealCoeff (grossenFiniteCharacter 𝔪 ψ) I.val * idealPsiSix I.val ^ k *
        (Ideal.absNorm I.val : ℂ) ^ (-w) := by
  rw [grossenLFunction_eq_tsum_ideals 𝔪 ψ hk hw]
  apply tsum_congr
  intro I
  rw [idealCoeff_grossenFiniteCharacter]
  simp only [grossenIdealTerm, MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- Smooth angular sums for the primitive L-function decay uniformly in the ray class
character, with its finite conductor norm as the only arithmetic scale. -/
theorem primitiveGrossenPlain_height_bound (k A : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ∃ (J : ℕ) (C : ℝ), 0 < C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
      (X : ℝ), 0 < X → ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖∑' I : NonzeroIdeal, primitiveIdealValue 𝔪 ψ I.val * idealPsiSix I.val ^ (k + 1) *
        twistProfile W σ t ((Ideal.absNorm I.val : ℝ) / X)‖ ≤
        (C * (1 + ‖t‖) ^ J) * (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) /
          (1 + X / (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ)) ^ A := by
  obtain ⟨J, C, hC, hb⟩ := grossenPlainIdealSum_height_bound k A W hW
  refine ⟨J, C, hC, ?_⟩
  intro 𝔪 ψ X hX σ hσ t
  have h := hb (grossenFiniteCharacter 𝔪 ψ) X hX σ hσ t
  simpa only [grossenPlainIdealSum, idealCoeff_grossenFiniteCharacter,
    grossenFiniteCharacter_modulus] using h

end GaloisForLFunctions.FamilyContinuationTheory
