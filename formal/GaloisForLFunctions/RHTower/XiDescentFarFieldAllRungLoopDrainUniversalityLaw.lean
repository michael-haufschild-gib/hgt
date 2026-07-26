import GaloisForLFunctions.RHTower.XiDescentAllRungLocalLoopDeckChargeUniversalityLaw
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# Xi-descent far-field all-rung loop-drain universality

The Euler-product zero-free half-plane is not only a pointwise charge anchor in the original
Xi coordinate.  After quadratic descent, every sufficiently small loop about the descended image
has zero additive loop charge at every dyadic rung.  Its deck character, descended local carrier
charge, and original Xi carrier charge all equal one.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Xi-descent far-field all-rung loop-drain universality law.**  Every point with
`1 < Re ρ` has a descended neighborhood on which every dyadic small-loop charge is exactly zero;
the corresponding multiplicative loop character and both local carrier charges are trivial. -/
theorem xiDescent_farField_allRungLocalLoopDrain
    {ρ : ℂ} (hfar : 1 < ρ.re) (k : ℕ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      loopCharge k
          (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
            (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) = 0 ∧
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) = 1 ∧
      carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ 2) = 1 ∧
      carrierCharge xi k ρ = 1 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hright : ρ ∈ rightHalf := by
    rw [mem_rightHalf]
    linarith
  have hxi : xi ρ ≠ 0 := xi_ne_zero_of_one_lt_re hfar
  have hxiCharge : carrierCharge xi k ρ = 1 :=
    carrierCharge_eq_one_of_ne_zero xi k hxi
  have hdescentCharge :
      carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ 2) = 1 :=
    (RHTower.xiDescent_carrierCharge_center_sq hright k).trans hxiCharge
  obtain ⟨R₀, hR₀, hloop⟩ :=
    deckChar_loopCharge_xiDescent_center_sq hright k
  refine ⟨R₀, hR₀, fun r hr hrR ↦ ?_⟩
  have hcharacter :
      deckChar (2 ^ k)
          (loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) = 1 :=
    (hloop r hr hrR).2.trans hxiCharge
  have hadditive :
      loopCharge k
          (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
            (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) = 0 := by
    apply deckChar_injective
    simpa using hcharacter
  exact ⟨hadditive, hcharacter, hdescentCharge, hxiCharge⟩

end

end RHTower
