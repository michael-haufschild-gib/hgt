import GaloisForLFunctions.RHTower.SuzukiShiftedXiCommonDivisorCancellation
import GaloisForLFunctions.RHTower.XiShiftEulerExceptionalIndex
import GaloisForLFunctions.RHTower.XiShiftEulerDenseFiniteSection

/-!
# Exact Euler Pick index after common-divisor cancellation

This leaf gives the literal Euler-region Pick system an intrinsic index at every positive shift,
including exceptional shifts and infinite strict-right divisors.  The index is the complete finite
dimension profile of the pole model space modulo the exact numerator-adjoint cancellation space.
Every such rank occurs in a prefix of every dense Euler-region sequence, and every prefix rank
comes from this quotient.  Thus its `WithTop` dimension is exactly the supremum of the nested
finite-matrix inertias without any finiteness or nonexceptionality premise.
-/

open Complex Set Topology Filter Matrix
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Full pole-model dimension after exact common-divisor cancellation, with `⊤` for unbounded
finite rank. -/
def xiShiftUncancelledDivisorIndex {omega : ℝ} (homega : 0 ≤ omega) : WithTop ℕ :=
  ⨆ q : {r : ℕ // HasIndependentDimensionAtLeast
      (XiShiftUncancelledDivisorQuotient homega) r}, (q.1 : WithTop ℕ)

/-- Every finite negative dimension of the literal Euler Pick kernel is exactly one finite
dimension of the complete pole divisor modulo all common-factor directions. -/
theorem eulerXiShiftPick_negativeDimension_iff_uncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 < omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega z.1 w.1) r ↔
      HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) r := by
  rw [eulerXiShiftPick_negativeDimension_iff_rankAtLeast homega r]
  exact restrictedAdjointRankAtLeast_iff_uncancelledQuotient
    (hardyMultiplierModelSpace
      (xiShiftPoleBlaschkeMultiplier homega.le))
    (hardyMul (xiShiftInfiniteSchurNumerator homega.le)) r

/-- Every finite quotient rank occurs in one prefix of every dense Euler-region sequence, and
every prefix rank is a quotient rank.  This is the exact cancellation-aware finite-section law,
uniformly covering finite, infinite, exceptional, and nonexceptional shifts. -/
theorem eulerXiShiftPick_denseFiniteSection_rankProfile
    {omega : ℝ} (homega : 0 < omega)
    (z : ℕ → xiShiftEulerUpperSet omega) (hz : DenseRange z) (r : ℕ) :
    HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) r ↔
      ∃ N : ℕ, r ≤ eulerXiShiftPickFiniteSectionNegIndex omega z N := by
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
  have hsection (N : ℕ) :
      kernelFiniteSectionNegIndex K zd N =
        eulerXiShiftPickFiniteSectionNegIndex omega z N := by
    rfl
  constructor
  · intro hq
    have hglobal : HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega) r :=
      (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
        homega.le r).mpr hq
    have hk : HasFiniteKernelNegativeDimension K r := by
      have h := (hlocal r).mpr hglobal
      simpa only [K, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h
    obtain ⟨N, hN⟩ :=
      exists_le_kernelFiniteSectionNegIndex_of_surjective K zd hzd hk
    exact ⟨N, by simpa only [hsection] using hN⟩
  · rintro ⟨N, hN⟩
    let KE := fun u v : xiShiftEulerUpperSet omega =>
      eulerXiShiftPick omega u.1 v.1
    have hk : HasFiniteKernelNegativeDimension KE
        (eulerXiShiftPickFiniteSectionNegIndex omega z N) := by
      simpa only [KE, eulerXiShiftPickFiniteSectionNegIndex] using
        (hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex KE z N)
    have hq :=
      (eulerXiShiftPick_negativeDimension_iff_uncancelledDivisorQuotient
        homega (eulerXiShiftPickFiniteSectionNegIndex omega z N)).mp hk
    exact hasIndependentDimensionAtLeast_of_le hN hq

/-- The supremum of every dense nested Euler Pick system is exactly the full uncancelled-divisor
index.  The equality includes the value `⊤`. -/
theorem eulerXiShiftPickFiniteSectionNegIndexSup_eq_uncancelledDivisorIndex
    {omega : ℝ} (homega : 0 < omega)
    (z : ℕ → xiShiftEulerUpperSet omega) (hz : DenseRange z) :
    eulerXiShiftPickFiniteSectionNegIndexSup omega z =
      xiShiftUncancelledDivisorIndex homega.le := by
  apply le_antisymm
  · apply iSup_le
    intro N
    have hk : HasFiniteKernelNegativeDimension
        (fun u v : xiShiftEulerUpperSet omega =>
          eulerXiShiftPick omega u.1 v.1)
        (eulerXiShiftPickFiniteSectionNegIndex omega z N) := by
      simpa only [eulerXiShiftPickFiniteSectionNegIndex] using
        (hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex
          (fun u v : xiShiftEulerUpperSet omega =>
            eulerXiShiftPick omega u.1 v.1) z N)
    have hq :=
      (eulerXiShiftPick_negativeDimension_iff_uncancelledDivisorQuotient
        homega (eulerXiShiftPickFiniteSectionNegIndex omega z N)).mp hk
    exact le_iSup_of_le
      (⟨eulerXiShiftPickFiniteSectionNegIndex omega z N, hq⟩ :
        {r : ℕ // HasIndependentDimensionAtLeast
          (XiShiftUncancelledDivisorQuotient homega.le) r}) le_rfl
  · apply iSup_le
    rintro ⟨r, hr⟩
    obtain ⟨N, hN⟩ :=
      (eulerXiShiftPick_denseFiniteSection_rankProfile homega z hz r).mp hr
    exact (WithTop.coe_le_coe.mpr hN).trans
      (le_iSup (fun N : ℕ =>
        (eulerXiShiftPickFiniteSectionNegIndex omega z N : WithTop ℕ)) N)

/-- All arbitrary finite Euler Pick matrices have inertia at most `m` exactly when the
uncancelled-divisor quotient has no independent family of size `m+1`. -/
theorem eulerXiShiftPick_arbitrarySample_inertia_le_iff_uncancelledDivisor
    {omega : ℝ} (homega : 0 < omega) (m : ℕ) :
    (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
        hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m) ↔
      ¬ HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) (m + 1) := by
  let K := fun z w : xiShiftEulerUpperSet omega =>
    eulerXiShiftPick omega z.1 w.1
  rw [show (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m) ↔
      ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ m by
    simpa only [K, eulerXiShiftPickSampleMatrix] using
      (finite_sample_negIndex_le_iff_global_bound K m)]
  constructor
  · intro hbound hbad
    have hneg :=
      (eulerXiShiftPick_negativeDimension_iff_uncancelledDivisorQuotient
        homega (m + 1)).mpr hbad
    exact (Nat.not_succ_le_self m) (hbound (m + 1) hneg)
  · intro hnot r hr
    have hq :=
      (eulerXiShiftPick_negativeDimension_iff_uncancelledDivisorQuotient
        homega r).mp hr
    by_contra hle
    have hmr : m + 1 ≤ r := by omega
    exact hnot (hasIndependentDimensionAtLeast_of_le hmr hq)

/-- Every finite Euler-region Pick matrix is positive semidefinite exactly when the intrinsic
uncancelled-divisor quotient has no nonzero direction. -/
theorem eulerXiShiftPick_everySample_posSemidef_iff_no_uncancelledDivisor
    {omega : ℝ} (homega : 0 < omega) :
    (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      (eulerXiShiftPickSampleMatrix omega w).PosSemidef) ↔
      ¬ HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) 1 := by
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
    eulerXiShiftPick_arbitrarySample_inertia_le_iff_uncancelledDivisor
      homega 0]

/-- At a nonexceptional shift, the intrinsic cancellation quotient recovers the raw strict-right
Xi divisor count exactly, including the value `⊤`. -/
theorem xiShiftUncancelledDivisorIndex_nonexceptional_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      xiShiftUncancelledDivisorIndex homega.le =
        (Nat.card (XiShiftRightZeroCopy omega) : WithTop ℕ)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      xiShiftUncancelledDivisorIndex homega.le = ⊤) := by
  rcases xiShiftRegularUpperKernel_negativeIndex_classification homega hnon with
    hfinite | hinfinite
  · left
    refine ⟨hfinite.1, le_antisymm ?_ ?_⟩
    · apply iSup_le
      rintro ⟨r, hr⟩
      exact WithTop.coe_le_coe.mpr (hfinite.2.2 r
        ((xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
          homega.le r).mpr hr))
    · have hq :=
        (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
          homega.le (Nat.card (XiShiftRightZeroCopy omega))).mp hfinite.2.1
      exact le_iSup_of_le
        (⟨Nat.card (XiShiftRightZeroCopy omega), hq⟩ :
          {r : ℕ // HasIndependentDimensionAtLeast
            (XiShiftUncancelledDivisorQuotient homega.le) r}) le_rfl
  · right
    refine ⟨hinfinite.1, WithTop.eq_top_iff_forall_ge.mpr ?_⟩
    intro r
    have hq :=
      (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
        homega.le r).mp (hinfinite.2 r)
    exact le_iSup_of_le
      (⟨r, hq⟩ : {s : ℕ // HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) s}) le_rfl

end
end RHTower
