import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.FamilyContinuationTheory.TheContinuationFrameAdmitsAHolomorphicCorrection

/-!
# The two estimates bound the zero abscissa

The half-plane route in one implication. Let `K` be the third cyclotomic field and `σ₀ < 1`.
Suppose that, whenever the pole-cleared Hecke `L`-functions of `K` are zero-free in `Re s > β`,
every ray class character `η` of `K` has a sum `J_η` with

* a direct bound `‖J_η(Z)‖ ≤ C Z^{a₁}`, and
* a comparison `‖J_η(Z) − f_η(Z)‖ ≤ C Z^{a₂}` with the signal `f_η` of
  `exp((s − c)²) H_η(s)/((s − 1) L(s, η))`,

where `a₁, a₂ < β` are common to all characters and `H_η` is holomorphic and nonvanishing on
`Re s > σ₀` and bounded on `Re s ≥ 2`. Then the zero abscissa of `ζ` is at most `σ₀`
(`zetaZeroAbscissa_le_of_two_estimates`). The premise is the pair of estimates and nothing else:
continuation of the Hecke `L`-functions, the factorization of the zeta function of `K`, and the
supremum step are theorems.
-/

noncomputable section

open Complex NumberField

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions _root_.RHTower

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- **The two estimates give the half-plane for `ζ`.** -/
theorem zetaZeroAbscissa_le_of_two_estimates {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (H : (Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) → ℂ → ℂ)
    (hH : ∀ η, DifferentiableOn ℂ (H η) {s : ℂ | σ₀ < s.re})
    (hH0 : ∀ η (s : ℂ), σ₀ < s.re → H η s ≠ 0)
    (hHb : ∀ η, ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H η s‖ ≤ C)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H η s /
                heckePoleCleared η.1 η.2 s) 2 Z‖ ≤ C * Z ^ a₂)) :
    zetaZeroAbscissa ≤ σ₀ :=
  zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic
    (heckeHalfPlane_of_family_corrected_signal K hσ₀ c H hH hH0 hHb hstep)

end GaloisForLFunctions.FamilyContinuationTheory
