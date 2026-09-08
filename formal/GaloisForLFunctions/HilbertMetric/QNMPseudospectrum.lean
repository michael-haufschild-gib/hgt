import GaloisForLFunctions.HilbertMetric.QNMBackwardError
import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Complete finite-dimensional pseudospectrum dictionary

The normalized quasimode, exact perturbation, and norm-resolvent descriptions
in Al Sheikh--Jaramillo, arXiv:2607.25133, equation (31), agree in finite dimension.
The proof closes the converse missing from the existing pseudospectrum module.
Positive tolerances are parametrized by exp(r), so there is no positivity premise.
The quasimode definition retains the nonzero-vector condition absent from the
paper's displayed formula.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem qnmQuasimodeSet_eq_normResolventPseudospectrum (A : E →L[ℂ] E) (r : ℝ) :
    qnmQuasimodeSet A 1 (Real.exp r) =
      normResolventPseudospectrum ℂ ⟨Real.exp r, Real.exp_pos r⟩ A := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  ext z
  constructor
  · intro hz
    rw [qnmQuasimodeSet_eq_unitResidual] at hz
    obtain ⟨v, hv, hr⟩ := hz
    exact mem_normResolventPseudospectrum_of_pseudomode
      ⟨Real.exp r, Real.exp_pos r⟩ A z hv (by simpa using hr)
  · intro hz
    rcases hz with hs | hr
    · have he : Module.End.HasEigenvalue (A : Module.End ℂ E) z :=
        Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
          rwa [ContinuousLinearMap.spectrum_eq] at hs)
      obtain ⟨v, hv⟩ := he.exists_hasEigenvector
      refine ⟨v, hv.2, ?_⟩
      have heq : A v = z • v := hv.apply_eq_smul
      simp [heq, Real.exp_pos]
    · by_cases hs : z ∈ spectrum ℂ A
      · have he : Module.End.HasEigenvalue (A : Module.End ℂ E) z :=
          Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
            rwa [ContinuousLinearMap.spectrum_eq] at hs)
        obtain ⟨v, hv⟩ := he.exists_hasEigenvector
        refine ⟨v, hv.2, ?_⟩
        have heq : A v = z • v := hv.apply_eq_smul
        simp [heq, Real.exp_pos]
      have hu : IsUnit (algebraMap ℂ (E →L[ℂ] E) z - A) := spectrum.notMem_iff.mp hs
      have hex : ∃ v : E, (Real.exp r)⁻¹ * ‖v‖ < ‖resolvent A z v‖ := by
        by_contra! h
        exact (not_lt_of_ge ((resolvent A z).opNorm_le_bound (by positivity) h)) hr
      obtain ⟨v, hv⟩ := hex
      have hn : 0 < ‖resolvent A z v‖ :=
        lt_of_le_of_lt (mul_nonneg (by positivity) (norm_nonneg v)) hv
      refine ⟨resolvent A z v, norm_ne_zero_iff.mp hn.ne', ?_⟩
      have hc := congrArg (fun T : E →L[ℂ] E => T v)
        (Ring.mul_inverse_cancel (algebraMap ℂ (E →L[ℂ] E) z - A) hu)
      have heq : A (resolvent A z v) - z • resolvent A z v = -v := by
        have hh : z • resolvent A z v - A (resolvent A z v) = v := by
          simpa [resolvent, sub_apply, smul_apply] using hc
        calc
          _ = -(z • resolvent A z v - A (resolvent A z v)) := by abel
          _ = -v := congrArg Neg.neg hh
      simp only [one_apply_eq_self, heq, norm_neg]
      rw [div_lt_iff₀ hn]
      have hscaled := mul_lt_mul_of_pos_left hv (Real.exp_pos r)
      simpa only [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero r), one_mul] using hscaled

end GaloisForLFunctions.HilbertMetric
