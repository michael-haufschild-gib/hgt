import GaloisForLFunctions.RHTower.TwistedOrderLawTheta
import GaloisForLFunctions.RHTower.TwistedMobiusPerronShift
import GaloisForLFunctions.RHTower.SmoothPerronLittlewood

/-!
# Littlewood bound for twisted Mertens sums

The zero-abscissa theory supplies the analytic source data for the universal smooth-Perron
Littlewood law: holomorphy and freely small power growth of `1 / L(s, χ)` on every shifted line,
together with the shifted Perron identity.  Instantiating that law proves

`M_χ(X) = O(X^(Θ_χ + ε))`

for every nontrivial primitive Dirichlet character.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {Q : ℕ} [NeZero Q]

/-- **Unconditional twisted Littlewood estimate at the zero abscissa.** -/
theorem twistedMertensSubpowerBound_zeroAbscissa {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) : TwistedMertensSubpowerBound χ (zeroAbscissa χ) := by
  apply partialSumSeq_subpower_of_smoothPerron
    (b := ↗χ * ↗μ) (Θ := zeroAbscissa χ)
    (norm_twistedMobiusCoeff_le_one χ) (zeroAbscissa_pos hχ hprim)
  intro dl a hdl hdl1 ha
  have hc : 0 < zeroAbscissa χ + dl := by
    linarith [zeroAbscissa_pos hχ hprim]
  have hc2 : zeroAbscissa χ + dl ≤ 2 := by
    linarith [zeroAbscissa_le_one hχ hprim]
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
    exists_shift_data hχ hprim hdl hdl1 ha (2 : ℝ)
  let F : ℂ → ℂ := fun s => (DirichletCharacter.LFunction χ s)⁻¹
  refine ⟨F, Kb, hKb, ?_, ?_⟩
  · intro y
    have hline : ((zeroAbscissa χ + dl : ℝ) : ℂ) + (y : ℝ) * I ∈
        verticalStrip (zeroAbscissa χ + dl) 2 :=
      line_mem_verticalStrip le_rfl hc2 y
    simpa [F] using hFbd _ hline
  · intro N H hN hH
    have hprod : Integrable fun y : ℝ => F (((zeroAbscissa χ + dl : ℝ) : ℂ) +
        (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          (((zeroAbscissa χ + dl : ℝ) : ℂ) + (y : ℝ) * I) := by
      dsimp only [F]
      exact integrable_mul_mellin_smoothWeight_line hN hH hc hFdiff.continuousOn
        hKb ha.le hFbd le_rfl hc2
    have hperron := twistedMobius_perron_shift hχ hprim hdl hdl1 ha hN hH
      (σ := 2) (by norm_num) hc2
    exact ⟨hprod, by simpa only [F] using hperron⟩

/-- **Unconditional companion order law `(R15)`.** -/
theorem limsup_mertens_eq_zeroAbscissa {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {j : ℕ} :
    Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) Filter.atTop
      = 2 * ((j : ℝ) + 1) * (1 + zeroAbscissa χ) - 1 :=
  limsup_mertens_eq_of_subpowerBound hχ hprim
    (twistedMertensSubpowerBound_zeroAbscissa hχ hprim)

end RHTower
