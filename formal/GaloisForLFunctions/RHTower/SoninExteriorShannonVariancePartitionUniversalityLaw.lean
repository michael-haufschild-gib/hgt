import GaloisForLFunctions.RHTower.SoninFullCountingReflection
import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy

/-!
# Sonin exterior Shannon-variance partition universality

Supersymmetric factor equality, impurity reflection, and the interior occupation budget transfer
the full Shannon-number partition to the zero-mode-subtracted exterior compressed Hamiltonian.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- The zero-mode-subtracted exterior compressed Hamiltonian has the exact central Shannon trace
`4a²`. -/
theorem re_opTrace_centralSoninExteriorCompression_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    Complex.re (opTrace (centralSoninExteriorCompression a)) = 4 * a ^ (2 : ℕ) := by
  have hreflection :=
    congrArg Complex.re
      (opTrace_centralSoninAlternatingBlock_eq_exteriorCompression a ha)
  calc
    Complex.re (opTrace (centralSoninExteriorCompression a)) =
        Complex.re
          (opTrace
            (soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a))) := hreflection.symm
    _ = 4 * a ^ (2 : ℕ) := re_opTrace_centralProlateBlock_eq_four_mul_sq a ha

/-- **Sonin exterior Shannon-variance partition law.**  Exterior retained energy plus exterior
free-fermion number variance is its full Shannon trace and equals the finite time--frequency area
`4a²`. -/
theorem hsNormSq_centralSoninExteriorCompression_add_impurity_eq_trace_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    hsNormSq (centralSoninExteriorCompression a) +
        Complex.re
          (opTrace
            (centralSoninExteriorCompression a -
              centralSoninExteriorCompression a *
                centralSoninExteriorCompression a)) =
      Complex.re (opTrace (centralSoninExteriorCompression a)) ∧
    Complex.re (opTrace (centralSoninExteriorCompression a)) = 4 * a ^ (2 : ℕ) := by
  have hbudget :
      hsNormSq (centralSoninExteriorCompression a) +
          Complex.re
            (opTrace
              (centralSoninExteriorCompression a -
                centralSoninExteriorCompression a *
                  centralSoninExteriorCompression a)) =
        4 * a ^ (2 : ℕ) := by
    rw [hsNormSq_centralSoninExteriorCompression_eq_prolateBlock a ha,
      re_opTrace_centralExteriorCompressionImpurity_eq_transition_hsNormSq a ha]
    exact hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq a ha
  have htrace := re_opTrace_centralSoninExteriorCompression_eq_four_mul_sq a ha
  exact ⟨hbudget.trans htrace.symm, htrace⟩

end

end RHTower
