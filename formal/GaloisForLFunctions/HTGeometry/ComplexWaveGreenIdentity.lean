import GaloisForLFunctions.HTGeometry.WaveEnergyGreenIdentity
import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus

/-!
# Complex compact Green transposition

The literal Hawking--Peierls source is complex valued.  This file supplies the
coordinatewise compact Green identity in that codomain: one derivative is
skew under the bilinear integral pairing and two equal coordinate derivatives
are self-transpose.  The compact support is required only of the test factor,
so an interior smooth causal field may be paired without any global L2 claim.
-/

open MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

private theorem contDiff_coordDeriv {d : ℕ} {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (ScalarTwoJet.coordDeriv i f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A compact complex test transfers one coordinate derivative to the other
factor with the exact minus sign. -/
theorem complex_integral_mul_coordDeriv {d : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (i : Fin d) :
    (∫ x : Fin d → ℝ, f x * ScalarTwoJet.coordDeriv i g x) =
      -∫ x : Fin d → ℝ, ScalarTwoJet.coordDeriv i f x * g x := by
  let v : Fin d → ℝ := Pi.single i 1
  have hdf := contDiff_coordDeriv hf i
  have hdg := contDiff_coordDeriv hg i
  have hsdf : HasCompactSupport (ScalarTwoJet.coordDeriv i f) := by
    exact hfs.fderiv_apply ℝ v
  have h1 : Integrable (fun x : Fin d → ℝ => ScalarTwoJet.coordDeriv i f x * g x) :=
    (hdf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hsdf.mul_right
  have h2 : Integrable (fun x : Fin d → ℝ => f x * ScalarTwoJet.coordDeriv i g x) :=
    (hf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  have h3 : Integrable (fun x : Fin d → ℝ => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

/-- Two equal coordinate derivatives are self-transpose against a compact
complex test.  This is the temporal and horizontal part of the literal
compact-test wave transposition. -/
theorem complex_integral_mul_coordDeriv_two {d : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (i : Fin d) :
    (∫ x : Fin d → ℝ,
      f x * ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv i g) x) =
      ∫ x : Fin d → ℝ, ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv i f) x * g x := by
  have hdf := contDiff_coordDeriv hf i
  rw [complex_integral_mul_coordDeriv hf (contDiff_coordDeriv hg i) hfs i,
    complex_integral_mul_coordDeriv hdf hg (hfs.fderiv_apply ℝ (Pi.single i 1)) i]
  ring

end GaloisForLFunctions.HTGeometry
