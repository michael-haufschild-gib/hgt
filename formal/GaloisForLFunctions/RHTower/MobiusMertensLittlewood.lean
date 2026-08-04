import GaloisForLFunctions.RHTower.InvZetaRHSubpolynomial
import GaloisForLFunctions.RHTower.SmoothPerronLittlewood
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly
import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion

/-!
# Littlewood's Mertens criterion from RH

Existing RH source data makes the regular reciprocal zeta function holomorphic and
subpolynomially bounded on every strip strictly right of the critical line.  Shifting the exact
smoothed Perron formula into those strips and applying the universal Littlewood law gives the
classical bound

`M(N) = O(N^(1/2+ε))`

for every positive `ε`.  Combined with the corpus's converse, this closes the Mertens Prop
interface as an unconditional equivalence with RH.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

open Sieve

/-- Under RH, the exact smoothed Möbius Perron formula may be shifted to every line strictly
right of the critical line. -/
theorem mobius_perron_shift_of_riemannHypothesis (hRH : RiemannHypothesis)
    {dl a N H : ℝ} (hdl : 0 < dl) (hdl1 : dl < 1) (ha : 0 < a)
    (hN : 0 < N) (hH : 0 < H) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) *
          ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ, invZeta ((((1 / 2 : ℝ) + dl : ℝ) : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((((1 / 2 : ℝ) + dl : ℝ) : ℂ) + (y : ℝ) * I) := by
  have hc : 0 < (1 / 2 : ℝ) + dl := by linarith
  have hc2 : (1 / 2 : ℝ) + dl ≤ 2 := by linarith
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
    exists_invZeta_shift_data_of_rh hRH hdl hdl1 ha (2 : ℝ)
  calc
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) *
          ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
        ∫ y : ℝ, invZeta ((2 : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((2 : ℂ) + (y : ℝ) * I) :=
      tsum_moebius_smoothWeight_eq_invZeta_integral hN hH (by norm_num)
    _ = ∫ y : ℝ, invZeta ((((1 / 2 : ℝ) + dl : ℝ) : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((((1 / 2 : ℝ) + dl : ℝ) : ℂ) + (y : ℝ) * I) :=
      integral_mul_mellin_smoothWeight_shift hN hH hc hc2 hFdiff hKb ha.le hFbd

/-- **Littlewood's criterion, forward direction.**  RH implies every strict half-power Mertens
bound, with no additional analytic premise. -/
theorem riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound :
    RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound := by
  intro hRH
  have hsubpower := partialSumSeq_subpower_of_smoothPerron
    (b := fun n => (ArithmeticFunction.moebius n : ℂ)) (Θ := (1 / 2 : ℝ))
    (fun n => by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
    (by norm_num)
    (fun dl a hdl hdl1 ha => by
      obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
        exists_invZeta_shift_data_of_rh hRH hdl hdl1 ha (2 : ℝ)
      refine ⟨invZeta, Kb, hKb, ?_, ?_⟩
      · intro y
        have hline : (((1 / 2 : ℝ) + dl : ℝ) : ℂ) + (y : ℝ) * I ∈
            verticalStrip ((1 / 2 : ℝ) + dl) 2 :=
          line_mem_verticalStrip le_rfl (by linarith) y
        simpa using hFbd _ hline
      · intro N H hN hH
        have hc : 0 < (1 / 2 : ℝ) + dl := by linarith
        have hc2 : (1 / 2 : ℝ) + dl ≤ 2 := by linarith
        refine ⟨integrable_mul_mellin_smoothWeight_line hN hH hc hFdiff.continuousOn
          hKb ha.le hFbd le_rfl hc2, ?_⟩
        exact mobius_perron_shift_of_riemannHypothesis hRH hdl hdl1 ha hN hH)
  intro dl hdl
  obtain ⟨C, hC, hbound⟩ := hsubpower dl hdl
  refine ⟨C, hC.le, fun N => ?_⟩
  simpa [partialSumSeq, mobiusMertensPartialSum, mobiusComplexCoefficient] using hbound N

/-- **Closed Littlewood criterion.**  The all-strict-half-power Mertens bound is exactly RH. -/
theorem mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis :
    MobiusMertensAllStrictHalfPowerBound ↔ RiemannHypothesis :=
  ⟨mobiusMertensAllStrictHalfPowerBound_implies_riemannHypothesis,
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound⟩

end RHTower
