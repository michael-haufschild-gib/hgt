import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteCancelledInertia
import GaloisForLFunctions.RHTower.XiShiftEulerDenseFiniteSection

/-!
# Cancellation-aware finite shifted-Xi inertia on Euler nodes

When the strict-right shifted divisor is finite, the Euler-region Pick kernel has exact negative
index equal to the intrinsic restricted-adjoint rank after every numerator/denominator common
direction is removed.  Dense nested sections stabilize at this rank, and arbitrary finite samples
recover its sharp upper-bound and positivity laws.  No nonexceptionality assumption is required.
-/

open Complex Set
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Exact cancellation-aware inertia of the shifted-Xi Pick kernel on its Euler region. -/
theorem eulerXiShiftPick_exactNegativeSquares_finite_cancelled
    {omega : ℝ} (homega : 0 < omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1)
        (xiShiftFiniteCancelledNegativeIndex omega homega.le) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (fun z w : xiShiftEulerUpperSet omega =>
            eulerXiShiftPick omega z.1 w.1) r →
        r ≤ xiShiftFiniteCancelledNegativeIndex omega homega.le := by
  have hlocal := xiShiftRegularUpperKernel_openRegion_negativeDimension_iff
    omega (xiShiftEulerUpperSet omega)
    (isOpen_xiShiftEulerUpperSet omega)
    (xiShiftEulerUpperSet_subset_upperHalfPlane homega)
    (suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega)
    (xiShiftEulerUpperSet_nonempty omega)
  have hglobal :=
    xiShiftRegularUpperKernel_exactNegativeSquares_finite_cancelled homega.le
  constructor
  · have h := (hlocal (xiShiftFiniteCancelledNegativeIndex omega homega.le)).mpr
      hglobal.1
    simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h
  · intro r hr
    have hr' : HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r := by
      simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using hr
    exact hglobal.2 r ((hlocal r).mp hr')

/-- Dense nested Euler-region matrices stabilize at the exact cancellation-aware index. -/
theorem eulerXiShiftPick_denseFiniteSection_limit_finite_cancelled
    {omega : ℝ} (homega : 0 < omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (z : ℕ → xiShiftEulerUpperSet omega) (hz : DenseRange z) :
    Filter.Tendsto (eulerXiShiftPickFiniteSectionNegIndex omega z)
        Filter.atTop
        (nhds (xiShiftFiniteCancelledNegativeIndex omega homega.le)) ∧
      (∀ᶠ N in Filter.atTop,
        eulerXiShiftPickFiniteSectionNegIndex omega z N =
          xiShiftFiniteCancelledNegativeIndex omega homega.le) ∧
      eulerXiShiftPickFiniteSectionNegIndexSup omega z =
        (xiShiftFiniteCancelledNegativeIndex omega homega.le : WithTop ℕ) ∧
      ∀ N, eulerXiShiftPickFiniteSectionNegIndex omega z N ≤
        xiShiftFiniteCancelledNegativeIndex omega homega.le := by
  let D : Set ℂ := Set.range fun n => (z n).1
  let zd : ℕ → D := fun n => ⟨(z n).1, ⟨n, rfl⟩⟩
  have hzd : Function.Surjective zd := by
    intro w
    obtain ⟨n, hn⟩ := w.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  obtain ⟨p, hpU, hfreq⟩ := denseRange_subtype_range_accumulates
    (isOpen_xiShiftEulerUpperSet omega) (xiShiftEulerUpperSet_nonempty omega) z hz
  have hsub : D ⊆ upperHalfPlaneSet := by
    rintro w ⟨n, rfl⟩
    exact xiShiftEulerUpperSet_subset_upperHalfPlane homega (z n).2
  have hregular : ∀ w ∈ D, suzukiCanonicalE omega w ≠ 0 := by
    rintro w ⟨n, rfl⟩
    exact suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega (z n).1 (z n).2
  have hpUpper : p ∈ upperHalfPlaneSet :=
    xiShiftEulerUpperSet_subset_upperHalfPlane homega hpU
  let K := fun u v : D => eulerXiShiftPick omega u.1 v.1
  have hlocal := xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
    omega D hsub hregular p hpUpper hfreq
  have hglobal :=
    xiShiftRegularUpperKernel_exactNegativeSquares_finite_cancelled homega.le
  have hk : HasFiniteKernelNegativeDimension K
      (xiShiftFiniteCancelledNegativeIndex omega homega.le) := by
    have h := (hlocal (xiShiftFiniteCancelledNegativeIndex omega homega.le)).mpr
      hglobal.1
    simpa only [K, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h
  have hbound : ∀ r, HasFiniteKernelNegativeDimension K r →
      r ≤ xiShiftFiniteCancelledNegativeIndex omega homega.le := by
    intro r hr
    apply hglobal.2 r
    apply (hlocal r).mp
    simpa only [K, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using hr
  have hsection (N : ℕ) :
      kernelFiniteSectionNegIndex K zd N =
        eulerXiShiftPickFiniteSectionNegIndex omega z N := by
    rfl
  have hsectionFun : kernelFiniteSectionNegIndex K zd =
      eulerXiShiftPickFiniteSectionNegIndex omega z := funext hsection
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := tendsto_kernelFiniteSectionNegIndex_of_surjective
      K zd hzd hk hbound
    rw [hsectionFun] at h
    exact h
  · have h := eventually_kernelFiniteSectionNegIndex_eq_of_surjective
      K zd hzd hk hbound
    filter_upwards [h] with N hN
    simpa only [hsection] using hN
  · have h := kernelFiniteSectionNegIndexSup_eq_of_surjective
      K zd hzd hk hbound
    simpa [kernelFiniteSectionNegIndexSup,
      eulerXiShiftPickFiniteSectionNegIndexSup,
      eulerXiShiftPickFiniteSectionNegIndex, hsectionFun] using h
  · intro N
    rw [← hsection]
    exact kernelFiniteSectionNegIndex_le_of_global_bound hbound zd N

/-- Every finite Euler sample has inertia at most `m` exactly when the cancellation-aware index
does. -/
theorem eulerXiShiftPick_arbitrarySample_inertia_le_iff_finite_cancelled
    {omega : ℝ} (homega : 0 < omega)
    [Fintype (XiShiftRightZeroCopy omega)] (m : ℕ) :
    xiShiftFiniteCancelledNegativeIndex omega homega.le ≤ m ↔
      ∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
        hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m := by
  let K := fun z w : xiShiftEulerUpperSet omega =>
    eulerXiShiftPick omega z.1 w.1
  rw [show (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m) ↔
      ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ m by
    simpa only [K, eulerXiShiftPickSampleMatrix] using
      (finite_sample_negIndex_le_iff_global_bound K m)]
  have hexact := eulerXiShiftPick_exactNegativeSquares_finite_cancelled homega
  constructor
  · intro hindex r hr
    exact (hexact.2 r hr).trans hindex
  · intro hbound
    exact hbound _ hexact.1

/-- All finite Euler-region Pick matrices are positive semidefinite exactly when the intrinsic
cancellation-aware index vanishes. -/
theorem eulerXiShiftPick_everySample_posSemidef_iff_cancelledIndex_eq_zero
    {omega : ℝ} (homega : 0 < omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      (eulerXiShiftPickSampleMatrix omega w).PosSemidef) ↔
      xiShiftFiniteCancelledNegativeIndex omega homega.le = 0 := by
  have hpsd :
      (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
          (eulerXiShiftPickSampleMatrix omega w).PosSemidef) ↔
        ∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
          hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ 0 := by
    constructor
    · intro h N w
      rw [Nat.le_zero]
      exact (hermNegIndex_eq_zero_iff_posSemidef
        (eulerXiShiftPickSampleMatrix_isHermitian omega w)).mpr (h N w)
    · intro h N w
      apply (hermNegIndex_eq_zero_iff_posSemidef
        (eulerXiShiftPickSampleMatrix_isHermitian omega w)).mp
      exact Nat.eq_zero_of_le_zero (h N w)
  rw [hpsd,
    ← eulerXiShiftPick_arbitrarySample_inertia_le_iff_finite_cancelled
      homega 0,
    Nat.le_zero]

end

end RHTower
