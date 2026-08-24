import GaloisForLFunctions.HTGeometry.WaveGreenIdentityIntegrable
import GaloisForLFunctions.Bottcher.Brolin.RieszPerLevel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
import GaloisForLFunctions.HTGeometry.DiscRootMultiset

/-!
# Green identities and finite divisor potentials on the complex plane

This file supplies the compactly supported Green self-adjointness needed to pass from local
holomorphic factorizations to distributional divisor identities.  It also records the exact
conversion between a finite multiset of zeros and its logarithmic linear-factor potential.
-/

open MeasureTheory Complex Metric Filter Set Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Twice integrating by parts moves a pure real directional second derivative between two
`C²` compactly supported functions on the complex plane. -/
theorem integral_mul_dderiv_eq_integral_dderiv_mul
    (f g : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (v : ℂ) :
    (∫ x, f x * Bottcher.dderiv g v x) =
      ∫ x, Bottcher.dderiv f v x * g x := by
  let Df : ℂ → ℝ := fun x => fderiv ℝ f x v
  let Dg : ℂ → ℝ := fun x => fderiv ℝ g x v
  have hDf : ContDiff ℝ 1 Df := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
      (hf.fderiv_right (m := 1) (by norm_num))
  have hDg : ContDiff ℝ 1 Dg := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
      (hg.fderiv_right (m := 1) (by norm_num))
  have hDfc : HasCompactSupport Df := Bottcher.hasCompactSupport_fderiv_apply hfc v
  have hDgc : HasCompactSupport Dg := Bottcher.hasCompactSupport_fderiv_apply hgc v
  have hDDfc : HasCompactSupport (fun x => fderiv ℝ Df x v) :=
    Bottcher.hasCompactSupport_fderiv_apply hDfc v
  have hDDgc : HasCompactSupport (fun x => fderiv ℝ Dg x v) :=
    Bottcher.hasCompactSupport_fderiv_apply hDgc v
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := f) (g := Dg) (v := v)
    (hDf.continuous.mul hDg.continuous
      |>.integrable_of_hasCompactSupport hDfc.mul_right)
    (hf.continuous.mul
      ((hDg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport hDDgc.mul_left)
    (hf.continuous.mul hDg.continuous
      |>.integrable_of_hasCompactSupport hDgc.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hDg.differentiable (by norm_num) x)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := Df) (g := g) (v := v)
    (((hDf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous
      |>.integrable_of_hasCompactSupport hDDfc.mul_right)
    (hDf.continuous.mul hDg.continuous
      |>.integrable_of_hasCompactSupport hDfc.mul_right)
    (hDf.continuous.mul hg.continuous
      |>.integrable_of_hasCompactSupport hDfc.mul_right)
    (fun x _ => hDf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)
  change (∫ x, f x * fderiv ℝ Dg x v) = ∫ x, fderiv ℝ Df x v * g x
  rw [hfirst, hsecond]
  simp

/-- Green self-adjointness for `C²` compactly supported real functions on `ℂ`. -/
theorem integral_mul_laplacian_eq_integral_laplacian_mul
    (f g : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x, f x * Δ g x) = ∫ x, Δ f x * g x := by
  have hD2cont : ∀ (q : ℂ → ℝ), ContDiff ℝ 2 q → ∀ v : ℂ,
      Continuous (fun x => Bottcher.dderiv q v x) := by
    intro q hq v
    have hD : ContDiff ℝ 1 (fun x => fderiv ℝ q x v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
        (hq.fderiv_right (m := 1) (by norm_num))
    exact (hD.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hD2cs : ∀ (q : ℂ → ℝ), HasCompactSupport q → ∀ v : ℂ,
      HasCompactSupport (fun x => Bottcher.dderiv q v x) := by
    intro q hq v
    exact Bottcher.hasCompactSupport_fderiv_apply
      (Bottcher.hasCompactSupport_fderiv_apply hq v) v
  have hfg1 : Integrable (fun x => f x * Bottcher.dderiv g 1 x) :=
    hf.continuous.mul (hD2cont g hg 1) |>.integrable_of_hasCompactSupport
      (hD2cs g hgc 1).mul_left
  have hfgI : Integrable (fun x => f x * Bottcher.dderiv g I x) :=
    hf.continuous.mul (hD2cont g hg I) |>.integrable_of_hasCompactSupport
      (hD2cs g hgc I).mul_left
  have hgf1 : Integrable (fun x => Bottcher.dderiv f 1 x * g x) :=
    (hD2cont f hf 1).mul hg.continuous |>.integrable_of_hasCompactSupport
      (hD2cs f hfc 1).mul_right
  have hgfI : Integrable (fun x => Bottcher.dderiv f I x * g x) :=
    (hD2cont f hf I).mul hg.continuous |>.integrable_of_hasCompactSupport
      (hD2cs f hfc I).mul_right
  simp_rw [Bottcher.laplacian_eq_dderiv _ hf,
    Bottcher.laplacian_eq_dderiv _ hg, mul_add, add_mul]
  rw [integral_add hfg1 hfgI, integral_add hgf1 hgfI,
    integral_mul_dderiv_eq_integral_dderiv_mul f g hf hg hfc hgc 1,
    integral_mul_dderiv_eq_integral_dderiv_mul f g hf hg hfc hgc I]

/-- A harmonic function on a neighborhood of the test support contributes zero to the
distributional Laplacian pairing. -/
theorem integral_harmonic_mul_laplacian_eq_zero
    (u phi : ℂ → ℝ) {rin rout R : ℝ}
    (hrin : 0 < rin) (hrout : rin < rout) (hR : rout < R)
    (hu : HarmonicOnNhd u (ball 0 R))
    (hphi : ContDiff ℝ 2 phi) (hphic : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ ball 0 rin) :
    (∫ x, u x * Δ phi x) = 0 := by
  let bump : ContDiffBump (0 : ℂ) := ContDiffBump.mk rin rout hrin hrout
  let H : ℂ → ℝ := fun x => bump x * u x
  have hbump_smooth : ContDiff ℝ 2 (bump : ℂ → ℝ) := bump.contDiff
  have hH : ContDiff ℝ 2 H := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : ℂ) R
    · exact hbump_smooth.contDiffAt.mul (hu x hx).1
    · have hdist : R ≤ dist x 0 := by
        simpa [mem_ball, not_lt] using hx
      have hxout : x ∉ tsupport (bump : ℂ → ℝ) := by
        rw [bump.tsupport_eq, mem_closedBall]
        linarith
      have hnh : (tsupport (bump : ℂ → ℝ))ᶜ ∈ nhds x :=
        (isClosed_tsupport (bump : ℂ → ℝ)).isOpen_compl.mem_nhds hxout
      have heq : H =ᶠ[nhds x] (0 : ℂ → ℝ) := by
        filter_upwards [hnh] with y hy
        have hby : bump y = 0 := by
          by_contra hne
          exact hy (subset_tsupport (bump : ℂ → ℝ) hne)
        simp [H, hby]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hHc : HasCompactSupport H := bump.hasCompactSupport.mul_right
  have hsame : (∫ x, u x * Δ phi x) = ∫ x, H x * Δ phi x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport phi
    · have hxin : x ∈ ball (0 : ℂ) bump.rIn := by
        simpa [bump] using hsupp hx
      have hb1 : bump x = 1 :=
        (bump.eventuallyEq_one_of_mem_ball hxin).self_of_nhds
      simp [H, hb1]
    · have hnh : (tsupport phi)ᶜ ∈ nhds x :=
        (isClosed_tsupport phi).isOpen_compl.mem_nhds hx
      have heq : phi =ᶠ[nhds x] (0 : ℂ → ℝ) := by
        filter_upwards [hnh] with y hy
        by_contra hne
        exact hy (subset_tsupport phi hne)
      have hlap : Δ phi x = 0 := by
        rw [(laplacian_congr_nhds heq).eq_of_nhds,
          laplacian_eq_iteratedFDeriv_complexPlane]
        simp
      simp [hlap]
  rw [hsame, integral_mul_laplacian_eq_integral_laplacian_mul H phi hH hphi hHc hphic]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change Δ H x * phi x = (0 : ℝ)
  by_cases hxzero : phi x = 0
  · simp [hxzero]
  · have hxt : x ∈ tsupport phi := subset_tsupport phi hxzero
    have hxin : x ∈ ball (0 : ℂ) bump.rIn := by
      simpa [bump] using hsupp hxt
    have hxinR : x ∈ ball (0 : ℂ) R := by
      rw [mem_ball] at hxin ⊢
      have hrinR : bump.rIn < R := by simp [bump]; linarith
      linarith
    have hbeq : H =ᶠ[nhds x] u := by
      filter_upwards [bump.eventuallyEq_one_of_mem_ball hxin] with y hy
      change bump y * u y = u y
      rw [hy]
      simp
    have hlapH : Δ H x = Δ u x := (laplacian_congr_nhds hbeq).eq_of_nhds
    have hlapu : Δ u x = (0 : ℝ) := by
      simpa using (hu x hxinR).2.self_of_nhds
    rw [hlapH, hlapu, zero_mul]

/-- Away from its atoms, the root-log sum is exactly the logarithm of the norm of the
corresponding monic linear-factor product. -/
theorem rootLogSum_eq_log_norm_multisetLinearProd
    (M : Multiset ℂ) {z : ℂ} (hz : z ∉ M) :
    (M.map (fun r => Real.log ‖z - r‖)).sum =
      Real.log ‖_root_.HTGeometry.multisetLinearProd M z‖ := by
  induction M using Multiset.induction_on with
  | empty => simp [_root_.HTGeometry.multisetLinearProd]
  | cons a M ih =>
      have hza : z - a ≠ 0 := sub_ne_zero.mpr (by
        intro h
        subst a
        exact hz (by simp))
      have hzM : z ∉ M := by
        intro h
        exact hz (by simp [h])
      have hprod : ‖(M.map fun r => z - r).prod‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        refine Multiset.prod_ne_zero ?_
        intro hw
        obtain ⟨r, hr, hzr⟩ := Multiset.mem_map.mp hw
        exact hzM (by
          rw [sub_eq_zero.mp hzr]
          exact hr)
      rw [Multiset.map_cons, Multiset.sum_cons, ih hzM]
      unfold _root_.HTGeometry.multisetLinearProd
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hza) hprod]

/-- Summing a function over the multiset assembled from finite multiplicities is the weighted
finite-set sum. -/
theorem sum_map_multisetOfFinsetMultiplicities
    (s : Finset ℂ) (m : ℂ → ℕ) (phi : ℂ → ℝ) :
    ((_root_.HTGeometry.multisetOfFinsetMultiplicities s m).map phi).sum =
      ∑ u ∈ s, (m u : ℝ) * phi u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [_root_.HTGeometry.multisetOfFinsetMultiplicities]
  | insert a s ha ih =>
      rw [_root_.HTGeometry.multisetOfFinsetMultiplicities, Finset.sum_insert ha,
        Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, Finset.sum_insert ha,
        ← _root_.HTGeometry.multisetOfFinsetMultiplicities, ih, nsmul_eq_mul]

end

end GaloisForLFunctions.HTGeometry
