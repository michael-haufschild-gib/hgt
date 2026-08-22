import GaloisForLFunctions.HTGeometry.OperatorNormLoewner
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bochner integrals and the Loewner order

The Bochner integral of a bounded family of positive elements of a C*-algebra is positive, and
therefore the integral is monotone for the Loewner order.  The proof avoids any theory of closed
convex cones: if `0 ≤ f ω ≤ R·1` pointwise then `‖R·1 - f ω‖ ≤ R`, so
`‖R·1 - ∫ f‖ ≤ ∫ ‖R·1 - f‖ ≤ R`, and a self-adjoint element within distance `R` of `R·1`
dominates `(R - R)·1 = 0`.
-/

open scoped Ring
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry.BuresWasserstein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The star operation as a real-linear continuous map. -/
def starCLM : A →L[ℝ] A where
  toFun := star
  map_add' := star_add
  map_smul' := fun r x => by
    simp [star_smul]
  cont := continuous_star

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma starCLM_apply (x : A) : (starCLM : A →L[ℝ] A) x = star x := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Bochner integral of a self-adjoint family is self-adjoint. -/
theorem isSelfAdjoint_integral {f : Ω → A} (hf : Integrable f μ)
    (hsa : ∀ w, IsSelfAdjoint (f w)) : IsSelfAdjoint (∫ w, f w ∂μ) := by
  show star (∫ w, f w ∂μ) = ∫ w, f w ∂μ
  have h := ContinuousLinearMap.integral_comp_comm (starCLM (A := A)) hf
  simp only [starCLM_apply] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact (hsa w).star_eq

/-- **The Bochner integral of a bounded positive family is positive.** -/
theorem integral_nonneg_of_le_smul_one [IsProbabilityMeasure μ] {f : Ω → A}
    (hf : Integrable f μ) {R : ℝ} (hR : 0 ≤ R)
    (hnn : ∀ w, 0 ≤ f w) (hb : ∀ w, f w ≤ R • (1 : A)) :
    0 ≤ ∫ w, f w ∂μ := by
  have hsa : ∀ w, IsSelfAdjoint (f w) := fun w => (hnn w).isSelfAdjoint
  have hIsa : IsSelfAdjoint (∫ w, f w ∂μ) := isSelfAdjoint_integral hf hsa
  have hdiff : IsSelfAdjoint ((∫ w, f w ∂μ) - R • (1 : A)) :=
    hIsa.sub (IsSelfAdjoint.smul (star_trivial R) (IsSelfAdjoint.one A))
  have hid : (∫ w, f w ∂μ) - R • (1 : A) = ∫ w, (f w - R • (1 : A)) ∂μ := by
    rw [integral_sub hf (integrable_const _), integral_const]
    simp
  have hptw : ∀ w, ‖f w - R • (1 : A)‖ ≤ R := by
    intro w
    have h1 : (0 : A) ≤ R • (1 : A) - f w := sub_nonneg.mpr (hb w)
    have h2 : R • (1 : A) - f w ≤ R • (1 : A) := sub_le_self _ (hnn w)
    have h3 : ‖R • (1 : A) - f w‖ ≤ R := norm_le_of_le_smul_one h1 hR h2
    rw [← norm_neg, neg_sub]
    exact h3
  have hnorm : ‖(∫ w, f w ∂μ) - R • (1 : A)‖ ≤ R := by
    rw [hid]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hle : ∫ w, ‖f w - R • (1 : A)‖ ∂μ ≤ ∫ _w : Ω, R ∂μ := by
      refine integral_mono ?_ (integrable_const _) hptw
      exact (hf.sub (integrable_const _)).norm
    rw [integral_const] at hle
    simpa using hle
  have hkey := smul_one_le_of_norm_sub_le hdiff hnorm (le_refl (R • (1 : A)))
  have hzero : (R - R) • (1 : A) = 0 := by simp
  rwa [hzero] at hkey

/-- **The Bochner integral is monotone for the Loewner order.** -/
theorem integral_mono_of_le [IsProbabilityMeasure μ] {f g : Ω → A}
    (hf : Integrable f μ) (hg : Integrable g μ) {R : ℝ} (hR : 0 ≤ R)
    (hle : ∀ w, f w ≤ g w) (hb : ∀ w, g w - f w ≤ R • (1 : A)) :
    (∫ w, f w ∂μ) ≤ ∫ w, g w ∂μ := by
  have hd : Integrable (fun w => g w - f w) μ := hg.sub hf
  have h := integral_nonneg_of_le_smul_one hd hR (fun w => sub_nonneg.mpr (hle w)) hb
  rw [integral_sub hg hf] at h
  exact sub_nonneg.mp h

end

end GaloisForLFunctions.HTGeometry
