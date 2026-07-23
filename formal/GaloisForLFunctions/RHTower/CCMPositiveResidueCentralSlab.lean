import GaloisForLFunctions.HTGeometry.PositiveResiduePoleForcing
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# CCM positive-residue central-slab law

The centered Xi function is unconditionally nonzero on the real interval `[-4,4]`.  Local-uniform
convergence to Xi therefore makes every approximant zero-free on that whole interval eventually.
Combining this compact-open fact with the universal positive-residue descent--pole law gives a
cofinal source theorem: any passive finite spectral realization whose pole polynomial converges to
Xi must eventually preserve the order of every pair of moving source samples in `[-4,4]`.

For the active-even CCM branch, the poles are the radical-quotient eigenvalues and the response
samples are the singular boundary-Pick data.  Thus one persistent descent of the actual CCM source
inside this unconditional central slab falsifies divisor-faithful determinant convergence.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- Local-uniform convergence to centered Xi makes the entire closed radius-four disk zero-free
eventually.  No differentiability of the approximants is needed. -/
theorem eventually_forall_ne_zero_closedBall_four_of_tendstoLocallyUniformly_XiC
    {F : ℕ → ℂ → ℂ} (hconv : TendstoLocallyUniformly F XiC atTop) :
    ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ℂ) 4, F k z ≠ 0 := by
  have hnonempty : (closedBall (0 : ℂ) 4).Nonempty :=
    ⟨0, mem_closedBall_self (by norm_num)⟩
  have hcontinuous : ContinuousOn (fun z => ‖XiC z‖) (closedBall (0 : ℂ) 4) :=
    XiC_analytic.continuous.continuousOn.norm
  obtain ⟨z₀, hz₀, hmin⟩ :=
    (isCompact_closedBall (0 : ℂ) 4).exists_isMinOn hnonempty hcontinuous
  have hXiNonzero : XiC z₀ ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_four
    have hre : |z₀.re| ≤ ‖z₀‖ := abs_re_le_norm z₀
    exact hre.trans (by simpa [dist_eq_norm] using (mem_closedBall.mp hz₀))
  have hminPos : 0 < ‖XiC z₀‖ := norm_pos_iff.mpr hXiNonzero
  have huniform : TendstoUniformlyOn F XiC atTop (closedBall (0 : ℂ) 4) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall (0 : ℂ) 4)).mp hconv.tendstoLocallyUniformlyOn
  have hclose : ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ℂ) 4,
      dist (F k z) (XiC z) < ‖XiC z₀‖ / 2 :=
    by
      simpa only [dist_comm] using
        (Metric.tendstoUniformlyOn_iff.mp huniform) (‖XiC z₀‖ / 2)
          (half_pos hminPos)
  filter_upwards [hclose] with k hk
  intro z hz hzero
  have hminZ : ‖XiC z₀‖ ≤ ‖XiC z‖ := hmin hz
  have hdist : dist (F k z) (XiC z) = ‖XiC z‖ := by simp [hzero]
  have hkz := hk z hz
  rw [hdist] at hkz
  linarith

/-- **Cofinal positive-residue order law.**  Let every declared pole be a zero of an approximant
converging locally uniformly to Xi.  For arbitrary moving nodes contained in `[-4,4]`, the
associated finite positive-residue response is eventually nondecreasing.  Dimensions, poles,
residues, and scalar offsets may all vary with the stage. -/
theorem eventually_positiveResidueResponse_mono_on_centralSlab_of_XiC_convergence
    {d : ℕ → ℕ} {F : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly F XiC atTop)
    (pole ell : ∀ k, Fin (d k) → ℝ) (offset left right : ℕ → ℝ)
    (hpoleZero : ∀ k j, F k (pole k j) = 0)
    (hnodes : ∀ᶠ k in atTop,
      -4 ≤ left k ∧ left k < right k ∧ right k ≤ 4) :
    ∀ᶠ k in atTop,
      HTGeometry.positiveResidueResponse Finset.univ (pole k) (ell k) (offset k) (left k) ≤
        HTGeometry.positiveResidueResponse Finset.univ (pole k) (ell k) (offset k) (right k) := by
  have hzeroFree :=
    eventually_forall_ne_zero_closedBall_four_of_tendstoLocallyUniformly_XiC hconv
  filter_upwards [hzeroFree, hnodes] with k hfree hnode
  obtain ⟨hleftBound, hleftRight, hrightBound⟩ := hnode
  have hleftMem : (left k : ℂ) ∈ closedBall (0 : ℂ) 4 := by
    rw [mem_closedBall, dist_zero_right]
    simpa only [norm_real, Real.norm_eq_abs] using
      (abs_le.mpr ⟨hleftBound, hleftRight.le.trans hrightBound⟩)
  have hrightMem : (right k : ℂ) ∈ closedBall (0 : ℂ) 4 := by
    rw [mem_closedBall, dist_zero_right]
    simpa only [norm_real, Real.norm_eq_abs] using
      (abs_le.mpr ⟨by linarith, hrightBound⟩)
  have hleftAvoid : ∀ j ∈ (Finset.univ : Finset (Fin (d k))), pole k j ≠ left k := by
    intro j _ hj
    apply hfree (left k) hleftMem
    simpa only [hj] using hpoleZero k j
  have hrightAvoid : ∀ j ∈ (Finset.univ : Finset (Fin (d k))), pole k j ≠ right k := by
    intro j _ hj
    apply hfree (right k) hrightMem
    simpa only [hj] using hpoleZero k j
  by_contra hmono
  push Not at hmono
  obtain ⟨j, _, hjpole⟩ :=
    HTGeometry.exists_pole_between_of_positiveResidueResponse_descent
      Finset.univ (pole k) (ell k) (offset k) hleftRight hleftAvoid hrightAvoid hmono
  have hpoleMem : (pole k j : ℂ) ∈ closedBall (0 : ℂ) 4 := by
    rw [mem_closedBall, dist_zero_right]
    have hpoleBounds : -4 ≤ pole k j ∧ pole k j ≤ 4 :=
      ⟨by linarith [hjpole.1], by linarith [hjpole.2]⟩
    simpa only [norm_real, Real.norm_eq_abs] using abs_le.mpr hpoleBounds
  exact hfree (pole k j) hpoleMem (hpoleZero k j)

end

end RHTower
