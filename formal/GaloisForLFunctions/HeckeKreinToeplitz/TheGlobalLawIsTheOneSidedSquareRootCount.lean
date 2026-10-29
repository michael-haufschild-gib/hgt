import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# The global law is the one-sided square-root count

Index zero of the Weil kernel has the same global law over `𝔽_q` and over `ℤ`: a one-sided count at
square-root precision.

* Over `𝔽_q` (`negIndex_traceKernel_eq_zero_iff_count`): the trace kernel of a curve datum has no
  negative square iff `N_k ≥ q^k + 1 − C q^{k/2}` for some `C`.
* Over `ℤ` (`negIndex_zetaKernel_eq_zero_iff_count`): the Weil kernel of `ζ` on `ℚ_{>0}` has no
  negative square iff `ψ(x) − x ≤ C √x log² x` eventually, for some `C ≥ 0` (von Koch and its
  converse).

Only one side of the count enters in both cases. This fixes the shape of the arithmetic
Krein–Langer theorem: the index is computed from local constituents and this one global law; over
`𝔽_q` the count comes from Stepanov or Riemann–Roch, over `ℤ` it is the open input.
-/

open Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **Over `ℤ`, index zero is the one-sided square-root prime count.** -/
theorem negIndex_zetaKernel_eq_zero_iff_count :
    negIndex zetaKernel = 0 ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
        Chebyshev.psi x - x ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  rw [← riemannHypothesis_iff_negIndex_zetaKernel_eq_zero]
  constructor
  · intro hRH
    refine ⟨max (200 * (xiLineTwoLogDerivConstant + 2)) 0, le_max_right _ _, ?_⟩
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx
    refine (chebyshevPsi_sub_le_of_riemannHypothesis hRH hx).trans ?_
    have : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
    nlinarith [le_max_left (200 * (xiLineTwoLogDerivConstant + 2)) 0]
  · rintro ⟨C, hC, h⟩
    exact riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq hC h

/-- **The same global law over `𝔽_q` and over `ℤ`.** -/
theorem global_law_count {ι : Type*} [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι) :
    (negIndex (traceKernel D) = 0 ↔
        ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k) ∧
      (negIndex zetaKernel = 0 ↔
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
          Chebyshev.psi x - x ≤ C * Real.sqrt x * Real.log x ^ 2) :=
  ⟨negIndex_traceKernel_eq_zero_iff_count D, negIndex_zetaKernel_eq_zero_iff_count⟩

end GaloisForLFunctions.HeckeKreinToeplitz
