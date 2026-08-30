import GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedContinuousLowerJetSystem
import GaloisForLFunctions.RHTower.BurnolSoninReflectedEvaluation
import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet
import GaloisForLFunctions.HTGeometry.AffineReflectionJet

/-!
# Reflected continuous lower zero-jet system on Burnol's co-Poisson source

The closed co-Poisson source is stable under the literal cosine involution.
Together with the completed Mellin functional equation, this transports the
already-closed right-half lower-jet system to the reflected Xi fibre.

The left-side expression below is intentionally the convergent right-half
Mellin germ of the cosine-reflected vector evaluated at `1 - w`; it is not an
assertion about a divergent raw left Mellin integral.  Its analyticity is
derived from the source-selected completed continuation and its local equality
with the literal Mellin evaluation in the right half-strip.

This discharges the complete lower-jet relation in both functional-equation
orientations (`COMP + ORIENT`).  It does not identify the resulting common
annihilator with Burnol's `P_aᗮ`, so it does not prove RH.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **Reflected closed cosine co-Poisson lower-jet descent.** At a left-half
Xi divisor, every lower completed Mellin jet of the cosine-reflected source
germ vanishes on the entire literal cosine-closed co-Poisson source space.
The exact conormal multiplicity and derivative parity are preserved by the
functional-equation involution. -/
theorem reflected_iteratedDeriv_soninMellinEvaluation_eq_zero_of_mem_burnolCoPoissonSourceSpace_of_lt
    {b : ℝ} (hb : 0 < b) (rho : XiDivisorSupport)
    (hleft : (rho : ℂ).re < 1 / 2) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    iteratedDeriv j (fun w : ℂ =>
      soninMellinEvaluation (1 - w)
        ((soninCosineUnitary f : evenSubspace) : SoninL2))
      (rho : ℂ) = 0 := by
  let eta : XiDivisorSupport := xiZeroReflectEquiv rho
  have heta : (eta : ℂ) = 1 - (rho : ℂ) := xiZeroReflectEquiv_apply rho
  have hright : 1 / 2 < (eta : ℂ).re := by
    rw [heta, Complex.sub_re, Complex.one_re]
    linarith
  have heta1 : (eta : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit eta).2
  have hjeta : j < burnolCoPoissonXiConormalOrder eta := by
    calc
      j < burnolCoPoissonXiConormalOrder rho := hj
      _ = xiSupportMultiplicity rho :=
        (xiSupportMultiplicity_eq_burnolCoPoissonXiConormalOrder rho).symm
      _ = xiSupportMultiplicity eta := (xiSupportMultiplicity_reflect rho).symm
      _ = burnolCoPoissonXiConormalOrder eta :=
        xiSupportMultiplicity_eq_burnolCoPoissonXiConormalOrder eta
  have hfcos : soninCosineUnitary f ∈ burnolCoPoissonSourceSpace b :=
    soninCosineUnitary_mem_coPoissonSourceSpace hf
  have hzero :=
    iteratedDeriv_soninMellinEvaluation_eq_zero_of_mem_burnolCoPoissonSourceSpace_of_lt
      hb eta hright hjeta hfcos
  let F : soninExtendedSpace b :=
    ⟨soninCosineUnitary f,
      burnolCoPoissonSourceSpace_le_soninExtendedSpace hb hfcos⟩
  have hcont : AnalyticAt ℂ
      (fun s : ℂ => soninExtendedCompletedMellinContinuation b hb F s) (eta : ℂ) := by
    unfold soninExtendedCompletedMellinContinuation
    exact (soninEval_analyticAt hb
      (soninExtendedToSoninEvenExtended b hb F).property.1
      (soninExtendedToSoninEvenExtended b hb F).property.2
      (by linarith) heta1).mul
        (analyticAt_mellinCompletionFactor_of_re_pos (by linarith))
  have hraw : AnalyticAt ℂ
      (fun s : ℂ => soninMellinEvaluation s
        ((soninCosineUnitary f : evenSubspace) : SoninL2)) (eta : ℂ) := by
    refine hcont.congr ?_
    simpa [F] using
      (eventuallyEq_soninEval_mul_completion_soninMellinEvaluation hb hright heta1 F)
  have hchain := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_one_sub_of_analyticAt
    j hraw
  rw [show 1 - (rho : ℂ) = (eta : ℂ) from heta.symm, hzero, mul_zero] at hchain
  exact hchain

end RHTower
