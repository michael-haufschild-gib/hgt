import GaloisForLFunctions.BiScaleUncertainty.CoprimeTentHilbertFrame

/-!
# Actual Hilbert sequence shifts and coordinate masks

Orthonormal synthesis constructs the unilateral right shift on real or complex
ℓ². Its adjoint is the successor shift. Coordinate masks are contractions, with
closed fixed spaces; these objects need no summability admission hypotheses.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

abbrev SequenceData (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 2

private theorem orthonormal_successor_single (𝕜 : Type*) [RCLike 𝕜] :
    Orthonormal 𝕜 (fun j : ℕ => (lp.single 2 (j + 1) (1 : 𝕜) : SequenceData 𝕜)) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · simp [lp.inner_single_left, lp.single_apply, Pi.single_eq_of_ne, h]

def sequenceRightShift (𝕜 : Type*) [RCLike 𝕜] :
    SequenceData 𝕜 →ₗᵢ[𝕜] SequenceData 𝕜 :=
  (orthonormal_successor_single 𝕜).orthogonalFamily.linearIsometry

theorem sequenceRightShift_single (𝕜 : Type*) [RCLike 𝕜] (j : ℕ) (a : 𝕜) :
    sequenceRightShift 𝕜 (lp.single 2 j a) = lp.single 2 (j + 1) a := by
  rw [sequenceRightShift,
    (orthonormal_successor_single 𝕜).orthogonalFamily.linearIsometry_apply_single]
  ext k
  by_cases h : k = j + 1
  · subst k
    simp [lp.single_apply]
  · simp [lp.single_apply, Pi.single_eq_of_ne h]

def sequenceLeftShift (𝕜 : Type*) [RCLike 𝕜] :
    SequenceData 𝕜 →L[𝕜] SequenceData 𝕜 :=
  (sequenceRightShift 𝕜).toContinuousLinearMap.adjoint

theorem sequenceLeftShift_apply (𝕜 : Type*) [RCLike 𝕜] (v : SequenceData 𝕜) (k : ℕ) :
    sequenceLeftShift 𝕜 v k = v (k + 1) := by
  have h := (sequenceRightShift 𝕜).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 k (1 : 𝕜)) v
  change inner 𝕜 (lp.single 2 k (1 : 𝕜)) (sequenceLeftShift 𝕜 v) =
    inner 𝕜 (sequenceRightShift 𝕜 (lp.single 2 k (1 : 𝕜))) v at h
  simpa [sequenceRightShift_single, lp.inner_single_left] using h

theorem norm_sequenceLeftShift_le (𝕜 : Type*) [RCLike 𝕜] :
    ‖sequenceLeftShift 𝕜‖ ≤ 1 := by
  rw [sequenceLeftShift, ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem sequenceRightShift_zero (𝕜 : Type*) [RCLike 𝕜] (v : SequenceData 𝕜) :
    sequenceRightShift 𝕜 v 0 = 0 := by
  have hs : HasSum (fun j => v j • (lp.single 2 (j+1) (1 : 𝕜) : SequenceData 𝕜))
      (sequenceRightShift 𝕜 v) :=
    (orthonormal_successor_single 𝕜).orthogonalFamily.hasSum_linearIsometry v
  have h := (innerSL 𝕜 (lp.single 2 0 (1 : 𝕜))).hasSum hs
  have hz (j : ℕ) : inner 𝕜 (lp.single 2 0 (1 : 𝕜))
      (v j • (lp.single 2 (j+1) (1 : 𝕜) : SequenceData 𝕜)) = 0 := by
    rw [inner_smul_right, lp.inner_single_left]
    simp [lp.single_apply]
  simp only [innerSL_apply_apply, hz, lp.inner_single_left] at h
  simpa using h.tsum_eq.symm

theorem sequenceRightShift_succ (𝕜 : Type*) [RCLike 𝕜] (v : SequenceData 𝕜) (k : ℕ) :
    sequenceRightShift 𝕜 v (k + 1) = v k := by
  have h := congrArg (fun A : SequenceData 𝕜 →L[𝕜] SequenceData 𝕜 => A v)
    (sequenceRightShift 𝕜).adjoint_comp_self
  have hv : sequenceLeftShift 𝕜 (sequenceRightShift 𝕜 v) = v := h
  simpa [sequenceLeftShift_apply] using congrArg (fun w : SequenceData 𝕜 => w k) hv

def sequenceMask (𝕜 : Type*) [RCLike 𝕜] (P : ℕ → Prop) :
    SequenceData 𝕜 →L[𝕜] SequenceData 𝕜 := by
  classical
  let f (v : SequenceData 𝕜) : SequenceData 𝕜 :=
    ⟨fun k => if P k then v k else 0,
      (lp.memℓp v).mono' (fun k => by split_ifs <;> simp)⟩
  let A : SequenceData 𝕜 →ₗ[𝕜] SequenceData 𝕜 :=
    { toFun := f
      map_add' := by
        intro v w
        apply lp.ext
        funext k
        simp only [f, lp.coeFn_add, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro c v
        apply lp.ext
        funext k
        simp only [f, lp.coeFn_smul, Pi.smul_apply]
        split_ifs <;> simp }
  exact A.mkContinuous 1 (fun v => by
    have hn : ‖f v‖ ≤ ‖v‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      (fun k => by
        change ‖ite (P k) (v k) 0‖ ≤ ‖v k‖
        split_ifs <;> simp)
    change ‖f v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using hn)

theorem sequenceMask_apply (𝕜 : Type*) [RCLike 𝕜] (P : ℕ → Prop)
    (v : SequenceData 𝕜) (k : ℕ) :
    sequenceMask 𝕜 P v k = if P k then v k else 0 := by
  classical
  rfl

theorem norm_sequenceMask_le (𝕜 : Type*) [RCLike 𝕜] (P : ℕ → Prop) :
    ‖sequenceMask 𝕜 P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    (fun k => by rw [sequenceMask_apply]; split_ifs <;> simp)

theorem sequenceMask_idempotent (𝕜 : Type*) [RCLike 𝕜] (P : ℕ → Prop)
    (v : SequenceData 𝕜) : sequenceMask 𝕜 P (sequenceMask 𝕜 P v) = sequenceMask 𝕜 P v := by
  classical
  apply lp.ext
  funext k
  by_cases hk : P k <;> simp [sequenceMask_apply, hk]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
