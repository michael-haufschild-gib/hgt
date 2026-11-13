import GaloisForLFunctions.HTGeometry.HardyBoundary.HalfLineIntegratedShift
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient

/-!
# Outer Laplace multipliers generate the causal half-line

An exponential average of causal translations is the Cayley resolvent.
Consequently every closed translation-invariant subspace becomes shift-invariant
in disk coordinates. The shift difference of a datum is its bounded Laplace
multiplier, up to the nonzero normalization `sqrt(2)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Cayley transport with the literal half-line measure used by causal translations. -/
def halfLineCayleyUnitary : HardyDisk ≃ₗᵢ[ℂ] BurnolHalfLineL2 :=
  hardyDiskHalfLineCayleyUnitary

/-- Exact disk evaluation in the causal translation space. -/
theorem hardyFun_causalCayley_inverse_disk (f : BurnolHalfLineL2)
    {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (halfLineCayleyUnitary.symm f) z =
      (diskToRight z + 1) / (Real.sqrt 2 : ℂ) * laplaceRay f (diskToRight z) :=
  hardyFun_halfLineCayley_inverse_disk f hz

private theorem cayley_shift_weight {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * (diskToRight z + 1) = 2 := by
  have hden := one_sub_ne_zero_of_mem_unitBall (mem_ball_zero_iff.mpr hz)
  unfold diskToRight
  field_simp [hden]
  ring

/-- The Cayley shift difference is twice the exponential average of translations. -/
theorem halfLineCayley_shift_difference (f : BurnolHalfLineL2) :
    halfLineCayleyUnitary.symm f -
      hardyMul diskShift (halfLineCayleyUnitary.symm f) =
        (2 : ℂ) • halfLineCayleyUnitary.symm (halfLineShiftAverage f) := by
  apply hardyDisk_ext
  intro z hz
  rw [sub_eq_add_neg, ← neg_one_smul ℂ _, hardyFun_add _ _ hz,
    hardyFun_smul _ _ hz, hardyFun_hardyMul _ _ hz,
    hardyFun_smul _ _ hz, hardyFun_causalCayley_inverse_disk _ hz,
    hardyFun_causalCayley_inverse_disk _ hz,
    laplaceRay_halfLineShiftAverage f (diskToRight_re_pos (mem_ball_zero_iff.mpr hz))]
  change ((diskToRight z + 1) / (Real.sqrt 2 : ℂ) * laplaceRay f (diskToRight z)) +
    (-1) * (z * ((diskToRight z + 1) / (Real.sqrt 2 : ℂ) *
      laplaceRay f (diskToRight z))) = _
  have hplus : 1 + diskToRight z ≠ 0 := by
    rw [add_comm]
    exact add_one_ne_zero_of_re_nonneg (diskToRight_re_pos (mem_ball_zero_iff.mpr hz)).le
  have hc : (diskToRight z + 1) * (1 + diskToRight z)⁻¹ = 1 := by
    rw [add_comm (diskToRight z) 1, mul_inv_cancel₀ hplus]
  calc
    _ = ((1 - z) * (diskToRight z + 1)) / (Real.sqrt 2 : ℂ) *
        laplaceRay f (diskToRight z) := by ring
    _ = 2 / (Real.sqrt 2 : ℂ) * laplaceRay f (diskToRight z) := by
      rw [cayley_shift_weight hz]
    _ = 2 / (Real.sqrt 2 : ℂ) *
        ((diskToRight z + 1) * (1 + diskToRight z)⁻¹) * laplaceRay f (diskToRight z) := by
      rw [hc, mul_one]
    _ = _ := by ring

/-- The disk shift difference removes the Cayley weight from the literal Laplace transform. -/
theorem halfLineCayley_shift_difference_eq_laplace (f : BurnolHalfLineL2)
    (φ : DiskMultiplier)
    (hφ : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z = laplaceRay f (diskToRight z)) :
    halfLineCayleyUnitary.symm f -
      hardyMul diskShift (halfLineCayleyUnitary.symm f) =
        (Real.sqrt 2 : ℂ) • hardyOf φ := by
  apply hardyDisk_ext
  intro z hz
  rw [sub_eq_add_neg, ← neg_one_smul ℂ _, hardyFun_add _ _ hz,
    hardyFun_smul _ _ hz, hardyFun_hardyMul _ _ hz,
    hardyFun_smul _ _ hz, hardyFun_hardyOf _ hz,
    hardyFun_causalCayley_inverse_disk _ hz, hφ z (mem_ball_zero_iff.mpr hz)]
  change ((diskToRight z + 1) / (Real.sqrt 2 : ℂ) * laplaceRay f (diskToRight z)) +
    (-1) * (z * ((diskToRight z + 1) / (Real.sqrt 2 : ℂ) *
      laplaceRay f (diskToRight z))) = _
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hsq : (Real.sqrt 2 : ℂ) ^ (2 : ℕ) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hquot : 2 / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) :=
    (div_eq_iff hs).mpr (by simpa only [sq] using hsq.symm)
  calc
    _ = ((1 - z) * (diskToRight z + 1)) / (Real.sqrt 2 : ℂ) *
        laplaceRay f (diskToRight z) := by ring
    _ = _ := by rw [cayley_shift_weight hz, hquot]

/-- A closed causal invariant subspace containing an outer Laplace datum is the whole space. -/
theorem eq_top_of_causal_invariant_outerLaplace
    (M : Submodule ℂ BurnolHalfLineL2) (hc : IsClosed (M : Set BurnolHalfLineL2))
    (hshift : ∀ h : ℝ≥0, ∀ f ∈ M, burnolRightShift h f ∈ M)
    {f : BurnolHalfLineL2} (hf : f ∈ M) (φ : DiskMultiplier)
    (hφ : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z = laplaceRay f (diskToRight z))
    (houter : IsOuterDiskMultiplier φ) : M = ⊤ := by
  let U := halfLineCayleyUnitary
  let N : Submodule ℂ HardyDisk := M.comap U.toLinearEquiv.toLinearMap
  have hNclosed : IsClosed (N : Set HardyDisk) := hc.preimage U.continuous
  have hNshift : ∀ x ∈ N, hardyMul diskShift x ∈ N := by
    intro x hx
    have hUx : U x ∈ M := hx
    have havg := halfLineShiftAverage_mem M hc hshift hUx
    have he := congrArg U (halfLineCayley_shift_difference (U x))
    change U (U.symm (U x) - hardyMul diskShift (U.symm (U x))) =
      U ((2 : ℂ) • U.symm (halfLineShiftAverage (U x))) at he
    simp only [map_sub, map_smul,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] at he
    have hd : U x - U (hardyMul diskShift x) ∈ M := by
      rw [he]
      exact M.smul_mem _ havg
    have hh := M.sub_mem hUx hd
    change U (hardyMul diskShift x) ∈ M
    convert hh using 1 <;> abel
  have hy : U.symm f ∈ N := by
    change U (U.symm f) ∈ M
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hf
  have hphiN : hardyOf φ ∈ N := by
    have hd := N.sub_mem hy (hNshift _ hy)
    rw [halfLineCayley_shift_difference_eq_laplace f φ hφ] at hd
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hh := N.smul_mem (Real.sqrt 2 : ℂ)⁻¹ hd
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh
  have hcyc : cyclicSubspace (hardyOf φ) ≤ N := by
    apply Submodule.topologicalClosure_minimal _ _ hNclosed
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero => simpa using hphiN
    | succ n ih =>
      change ((hardyMul diskShift) ^ (n + 1)) (hardyOf φ) ∈ N
      rw [pow_succ']
      exact hNshift _ ih
  change cyclicSubspace (hardyOf φ) = ⊤ at houter
  rw [houter] at hcyc
  apply Submodule.eq_top_iff'.mpr
  intro g
  have hg : U.symm g ∈ N := hcyc (by simp)
  change U (U.symm g) ∈ M at hg
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hg

/-- The closed span of all causal translates of a half-line datum. -/
def causalCyclicSubspace (f : BurnolHalfLineL2) : Submodule ℂ BurnolHalfLineL2 :=
  (Submodule.span ℂ (range fun h : ℝ≥0 => burnolRightShift h f)).topologicalClosure

theorem self_mem_causalCyclicSubspace (f : BurnolHalfLineL2) : f ∈ causalCyclicSubspace f := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨0, burnolRightShift_zero f⟩

/-- Causal translation preserves the closed span of causal translates. -/
theorem burnolRightShift_mem_causalCyclicSubspace (f : BurnolHalfLineL2) (h : ℝ≥0) :
    ∀ g ∈ causalCyclicSubspace f, burnolRightShift h g ∈ causalCyclicSubspace f := by
  let A := Submodule.span ℂ (range fun k : ℝ≥0 => burnolRightShift k f)
  have hbase : ∀ g ∈ A, burnolRightShift h g ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      exact Submodule.subset_span ⟨h + k, burnolRightShift_add h k f⟩
    | zero => rw [map_zero]; exact A.zero_mem
    | add a b ha hb ia ib => rw [map_add]; exact A.add_mem ia ib
    | smul c a ha ia => rw [map_smul]; exact A.smul_mem c ia
  have hc : IsClosed {g : BurnolHalfLineL2 | burnolRightShift h g ∈ A.topologicalClosure} :=
    A.isClosed_topologicalClosure.preimage (burnolRightShift h).continuous
  exact hc.closure_subset_iff.mpr fun g hg => A.le_topologicalClosure (hbase g hg)

/-- Outerness of the literal Cayley Laplace multiplier implies density of causal translates. -/
theorem causalCyclicSubspace_eq_top_of_outerLaplace (f : BurnolHalfLineL2)
    (φ : DiskMultiplier)
    (hφ : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z = laplaceRay f (diskToRight z))
    (houter : IsOuterDiskMultiplier φ) : causalCyclicSubspace f = ⊤ :=
  eq_top_of_causal_invariant_outerLaplace (causalCyclicSubspace f)
    (Submodule.isClosed_topologicalClosure _)
    (burnolRightShift_mem_causalCyclicSubspace f)
    (self_mem_causalCyclicSubspace f) φ hφ houter

#print axioms causalCyclicSubspace_eq_top_of_outerLaplace

end GaloisForLFunctions.HTGeometry
