import GaloisForLFunctions.RHTower.RenormalizedFormationWorkDivisor
import GaloisForLFunctions.HTGeometry.GibbsDirichletCumulants

/-!
# The spectral cumulant shadow of renormalized formation work

On the convergence ray the shell source is the Dirichlet series of the shell indicator, so its
logarithmic derivative is minus the Gibbs expectation of `log n`.  The branch-free work form of the
survival transfer therefore reads as a difference of inherited and target Gibbs first moments plus
the universal normalization term.
-/

open Complex LSeries GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

namespace RHTower

noncomputable section

theorem lSeriesSummable_shellIndicator (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(shellIndicator k) s := by
  have hfun : ↗(shellIndicator k) = ↗(mFreeIndicator (k + 1)) - ↗(mFreeIndicator k) := by
    funext n
    simp
  rw [hfun]
  exact (LSeriesSummable_mFreeIndicator (k + 1) hs).sub (LSeriesSummable_mFreeIndicator k hs)

theorem abscissaOfAbsConv_shellIndicator_le (k : ℕ) :
    abscissaOfAbsConv ↗(shellIndicator k) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  refine lSeriesSummable_shellIndicator k ?_
  simpa using hy

theorem abscissaOfAbsConv_shellIndicator_lt {k : ℕ} {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv ↗(shellIndicator k) < (s.re : EReal) :=
  lt_of_le_of_lt (abscissaOfAbsConv_shellIndicator_le k) (by exact_mod_cast hs)

theorem shellSource_eventuallyEq_lSeries {k : ℕ} (hk : k ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    shellSource k =ᶠ[nhds s] LSeries ↗(shellIndicator k) := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact (LSeries_shellIndicator hk hz).symm

/-- **The shell logarithmic derivative is minus the Gibbs first moment.** -/
theorem logDeriv_shellSource {k : ℕ} (hk : k ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (shellSource k) s = -gibbsLogMean ↗(shellIndicator k) s := by
  have heq := shellSource_eventuallyEq_lSeries hk hs
  have h1 : logDeriv (shellSource k) s = logDeriv (LSeries ↗(shellIndicator k)) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [h1, logDeriv_LSeries (abscissaOfAbsConv_shellIndicator_lt hs)]

theorem shellSource_ne_zero {k : ℕ} (hk : 12 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    shellSource k s ≠ 0 := by
  rw [shellSource]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re (le_of_lt hs))
    (shellMultiplier_ne_zero hk (by linarith))

theorem shellResidueUnit_eventuallyEq {k : ℕ} {s : ℂ} (hs1 : s ≠ 1) :
    shellResidueUnit k =ᶠ[nhds s] fun z => (z - 1) * shellSource k z := by
  filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hs1)] with z hz
  have hz1 : z ≠ 1 := by simpa using hz
  rw [shellResidueUnit, zetaResidueUnit, Function.update_of_ne hz1, shellSource]
  ring

theorem logDeriv_shellResidueUnit {k : ℕ} (hk : 12 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (shellResidueUnit k) s = (s - 1)⁻¹ - gibbsLogMean ↗(shellIndicator k) s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hSne : shellSource k s ≠ 0 := shellSource_ne_zero hk hs
  have hSdiff : DifferentiableAt ℂ (shellSource k) s := by
    have h1 : AnalyticAt ℂ (shellSource k) s :=
      (analyticOn_riemannZeta s hs1).mul (analyticAt_shellMultiplier hk (by linarith))
    exact h1.differentiableAt
  have heq := shellResidueUnit_eventuallyEq (k := k) hs1
  have h1 : logDeriv (shellResidueUnit k) s
      = logDeriv (fun z => (z - 1) * shellSource k z) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [h1, logDeriv_mul (f := fun z : ℂ => z - 1) (g := shellSource k) s hs1' hSne
    ((differentiableAt_id).sub_const 1) hSdiff, logDeriv_shellSource (by omega) hs]
  have h2 : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    rw [deriv_sub_const, deriv_id'']
    simp
  rw [h2]
  ring

/-- **Spectral cumulant shadow** (DWP.13).  On the convergence ray the branch-free formation work
form is the inherited Gibbs first moment, minus the target Gibbs first moment, plus the universal
normalization term. -/
theorem neg_logDeriv_survivalTransfer_eq_gibbs {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (survivalTransfer m r) s
      = (r : ℂ) * gibbsLogMean ↗(shellIndicator m) ((r : ℂ) * s)
        - gibbsLogMean ↗(shellIndicator (r * m)) s + (s - 1)⁻¹ := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hhalf : (1 : ℝ) / 2 < s.re := by linarith
  have hrs : 1 < ((r : ℂ) * s).re := by
    have h : ((r : ℂ) * s).re = (r : ℝ) * s.re := by simp [Complex.mul_re]
    rw [h]
    have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hnumne : shellSource m ((r : ℂ) * s) ≠ 0 := shellSource_ne_zero hm hrs
  have hdenne : shellResidueUnit (r * m) s ≠ 0 := by
    rw [shellResidueUnit]
    refine mul_ne_zero ?_ (shellMultiplier_ne_zero hkm (by linarith))
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re (le_of_lt hs))
  have hnumdiff : DifferentiableAt ℂ (fun z => shellSource m ((r : ℂ) * z)) s :=
    (analyticAt_shellSource_natCast_mul hm hr hhalf).differentiableAt
  have hdendiff : DifferentiableAt ℂ (shellResidueUnit (r * m)) s :=
    (analyticAt_shellResidueUnit hkm hhalf).differentiableAt
  have hdiv : logDeriv (survivalTransfer m r) s
      = logDeriv (fun z => shellSource m ((r : ℂ) * z)) s
        - logDeriv (shellResidueUnit (r * m)) s :=
    logDeriv_div s hnumne hdenne hnumdiff hdendiff
  have hlin : DifferentiableAt ℂ (fun z : ℂ => (r : ℂ) * z) s :=
    (differentiableAt_id).const_mul _
  have hSdiff : DifferentiableAt ℂ (shellSource m) ((r : ℂ) * s) := by
    have hne1 : ((r : ℂ) * s) ≠ 1 := by
      intro h
      rw [h] at hrs
      norm_num at hrs
    exact ((analyticOn_riemannZeta _ hne1).mul
      (analyticAt_shellMultiplier hm (by linarith))).differentiableAt
  have hcomp : logDeriv (fun z => shellSource m ((r : ℂ) * z)) s
      = logDeriv (shellSource m) ((r : ℂ) * s) * (r : ℂ) := by
    have h := logDeriv_comp (f := shellSource m) (g := fun z : ℂ => (r : ℂ) * z) (x := s)
      hSdiff hlin
    rw [show deriv (fun z : ℂ => (r : ℂ) * z) s = (r : ℂ) from by simp] at h
    exact h
  rw [hdiv, hcomp, logDeriv_shellSource (by omega) hrs,
    logDeriv_shellResidueUnit hkm hs]
  ring

theorem lSeries_shellIndicator_ne_zero {k : ℕ} (hk : 12 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(shellIndicator k) s ≠ 0 := by
  rw [LSeries_shellIndicator (by omega) hs]
  exact shellSource_ne_zero hk hs

/-- **Spectral cumulant shadow, second order** (DWP.14).  The second derivative of the renormalized
formation work is the target Gibbs variance minus the inherited Gibbs variance minus the universal
normalization curvature. -/
theorem hasDerivAt_neg_logDeriv_survivalTransfer {m r : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt (fun z => -logDeriv (survivalTransfer m r) z)
      (gibbsLogVar ↗(shellIndicator (r * m)) s
        - (r : ℂ) ^ 2 * gibbsLogVar ↗(shellIndicator m) ((r : ℂ) * s)
        - ((s - 1) ^ 2)⁻¹) s := by
  have hkm : 12 ≤ r * m := le_trans hm (Nat.le_mul_of_pos_left m (by omega))
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hrs : 1 < ((r : ℂ) * s).re := by
    have h : ((r : ℂ) * s).re = (r : ℝ) * s.re := by simp [Complex.mul_re]
    rw [h]
    have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  -- derivative of the inherited term
  have hlin : HasDerivAt (fun z : ℂ => (r : ℂ) * z) (r : ℂ) s := by
    simpa using (hasDerivAt_id s).const_mul ((r : ℂ))
  have hmean1 : HasDerivAt (gibbsLogMean ↗(shellIndicator m))
      (-gibbsLogVar ↗(shellIndicator m) ((r : ℂ) * s)) ((r : ℂ) * s) :=
    GaloisForLFunctions.HTGeometry.hasDerivAt_gibbsLogMean
      (abscissaOfAbsConv_shellIndicator_lt hrs) (lSeries_shellIndicator_ne_zero hm hrs)
  have hterm1 : HasDerivAt (fun z : ℂ => (r : ℂ) * gibbsLogMean ↗(shellIndicator m) ((r : ℂ) * z))
      ((r : ℂ) * ((-gibbsLogVar ↗(shellIndicator m) ((r : ℂ) * s)) * (r : ℂ))) s :=
    ((hmean1.comp s hlin).const_mul ((r : ℂ)))
  have hterm2 : HasDerivAt (gibbsLogMean ↗(shellIndicator (r * m)))
      (-gibbsLogVar ↗(shellIndicator (r * m)) s) s :=
    GaloisForLFunctions.HTGeometry.hasDerivAt_gibbsLogMean
      (abscissaOfAbsConv_shellIndicator_lt hs) (lSeries_shellIndicator_ne_zero hkm hs)
  have hterm3 : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-((s - 1) ^ 2)⁻¹) s := by
    have hd : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
      simpa using (hasDerivAt_id s).sub_const 1
    have h := hd.inv hs1'
    have hval : -(1 : ℂ) / (s - 1) ^ 2 = -((s - 1) ^ 2)⁻¹ := by
      rw [neg_div, one_div]
    rw [hval] at h
    exact h
  have hsum := ((hterm1.sub hterm2).add hterm3)
  refine hsum.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · ring
  · filter_upwards [hopen.mem_nhds hs] with z hz
    exact neg_logDeriv_survivalTransfer_eq_gibbs hm hr hz

end

end RHTower
