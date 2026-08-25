import GaloisForLFunctions.HTGeometry.ShiftedCircleLogKernel
import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen

/-!
# Boundary estimates for Nevanlinna translation

This module controls a Poisson-weighted meromorphic boundary logarithm by its ordinary absolute
circle mean.  Unlike the continuous harmonic version, it allows zeros and poles on the boundary
through mathlib's circle-integrability theorem for meromorphic logarithms.
-/

open Complex Metric Real Set Topology

namespace GaloisForLFunctions.HTGeometry

open PoissonJensen MeromorphicOn

noncomputable section

/-- Poisson-weighted meromorphic boundary logarithms are controlled by the unweighted absolute
logarithmic mean. -/
theorem circleAverage_poissonKernel_smul_log_norm_le_abs
    {f : ℂ → ℂ} {c w : ℂ} {R r : ℝ}
    (hfm : MeromorphicOn f (sphere c |R|))
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    Real.circleAverage
        (poissonKernel c w • fun z => Real.log ‖f z‖) c R ≤
      (R + r) / (R - r) *
        Real.circleAverage (fun z => |Real.log ‖f z‖|) c R := by
  have hR0 : 0 < R := pos_of_mem_ball hw
  have habs : |R| = R := abs_of_pos hR0
  have hlog : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    hfm.circleIntegrable_log_norm
  have hPcont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [habs]
    exact continuousOn_poissonKernel hw
  have hleft : CircleIntegrable
      (poissonKernel c w • fun z => Real.log ‖f z‖) c R :=
    hlog.smul_of_continuousOn hPcont
  have habslog : CircleIntegrable (fun z => |Real.log ‖f z‖|) c R := hlog.abs
  have hright : CircleIntegrable
      (fun z => (R + r) / (R - r) * |Real.log ‖f z‖|) c R :=
    habslog.const_mul _
  have hK0 : 0 ≤ (R + r) / (R - r) := by
    have hr0 : 0 ≤ r := (norm_nonneg _).trans hwr
    have hden : 0 < R - r := by linarith
    positivity
  have hmono := Real.circleAverage_mono hleft hright (fun z hz => ?_)
  · have hscale := Real.circleAverage_fun_smul
      (f := fun z => |Real.log ‖f z‖|) (c := c) (R := R)
      (a := (R + r) / (R - r))
    simpa [smul_eq_mul] using hmono.trans_eq hscale
  · rw [habs] at hz
    change poissonKernel c w z * Real.log ‖f z‖ ≤
      (R + r) / (R - r) * |Real.log ‖f z‖|
    have hP0 := poissonKernel_nonneg hz hw
    have hPK := poissonKernel_le hz hw hwr hrR
    calc
      poissonKernel c w z * Real.log ‖f z‖ ≤
          poissonKernel c w z * |Real.log ‖f z‖| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hP0
      _ ≤ (R + r) / (R - r) * |Real.log ‖f z‖| :=
        mul_le_mul_of_nonneg_right hPK (abs_nonneg _)

/-- Total pole multiplicity in a closed Nevanlinna disc. -/
noncomputable def poleMultiplicityMass (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, (divisor f (closedBall 0 |R|) u : ℝ)⁻

/-- Pointwise translation estimate: a regular nonzero interior value is controlled by the
Poisson-weighted outer boundary logarithm and the Green contributions of the enclosed poles. -/
theorem posLog_norm_le_poissonBoundary_add_poleGreen
    {f : ℂ → ℂ} {R r : ℝ} (hR : 0 < R)
    (hfm : Meromorphic f) (horder : ∀ u, meromorphicOrderAt f u ≠ ⊤)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R)
    (hwf : AnalyticAt ℂ f w) (hfw : f w ≠ 0)
    (hwr : ‖w‖ ≤ r) (hrR : r < R) :
    Real.posLog ‖f w‖ ≤
      (R + r) / (R - r) *
          Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R +
        ∑ᶠ u : ℂ, (divisor f (closedBall 0 |R|) u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ -
            Real.log ‖w - u‖) := by
  classical
  have hRabs : |R| = R := abs_of_pos hR
  have hmeroBall : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ => hfm z
  have hfiniteOrder : ∀ u : (closedBall (0 : ℂ) |R| : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤ := fun u => horder u
  obtain ⟨g, hg, hgfree, hlogeq, hPJ⟩ :=
    PoissonJensen.poissonJensen hR hmeroBall hfiniteOrder hw
  let D := divisor f (closedBall (0 : ℂ) |R|)
  change (fun x => Real.log ‖f x‖) =ᶠ[Filter.codiscreteWithin (closedBall 0 |R|)]
      (∑ᶠ u : ℂ, fun x => (D u : ℝ) * Real.log ‖x - u‖) +
        fun x => Real.log ‖g x‖ at hlogeq
  change Real.circleAverage
      ((Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖f ·‖)) 0 R =
    (∑ᶠ u : ℂ, (D u : ℝ) *
      Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) + Real.log ‖g w‖ at hPJ
  have hDfin : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hwclosed : w ∈ closedBall (0 : ℂ) |R| := by
    rw [hRabs]
    exact Metric.ball_subset_closedBall hw
  have hwclosedR : w ∈ closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
  let S := hDfin.toFinset
  have hsumD :
      (∑ᶠ u : ℂ, ((D u : ℝ) * Real.log ‖w - u‖)) =
        ∑ u ∈ S, ((D u : ℝ) * Real.log ‖w - u‖) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu
    apply hu
    simp [hDu]
  have hsumI :
      (∑ᶠ u : ℂ, ((D u : ℝ) *
          Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖)) =
        ∑ u ∈ S, ((D u : ℝ) *
          Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu
    apply hu
    simp [hDu]
  have hwD : D w = 0 := by
    dsimp [D]
    rw [divisor_apply hmeroBall hwclosed]
    rw [hwf.meromorphicOrderAt_eq, hwf.analyticOrderAt_eq_zero.mpr hfw]
    simp
  have hlogval : Real.log ‖f w‖ =
      (∑ᶠ u : ℂ, ((D u : ℝ) * Real.log ‖w - u‖)) + Real.log ‖g w‖ := by
    have hU : closedBall (0 : ℂ) |R| ∈ 𝓝 w := by
      have hmargin : 0 < R - ‖w‖ := by
        simpa [mem_ball_iff_norm] using hw
      apply Filter.mem_of_superset (Metric.ball_mem_nhds w hmargin)
      intro z hz
      have hz' : ‖z - w‖ < R - ‖w‖ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hzbound : ‖z‖ ≤ R := by
        calc
          ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
            have := norm_add_le (z - w) w
            simpa using this
          _ ≤ R := by linarith
      rw [mem_closedBall_iff_norm, hRabs]
      simpa using hzbound
    have hfunSum : (∑ᶠ u, ((D u : ℝ) * Real.log ‖· - u‖)) =
        ∑ u ∈ S, ((D u : ℝ) • fun z => Real.log ‖z - u‖) := by
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simp only [Function.mem_support] at hu
      simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
      intro hDu
      apply hu
      funext z
      simp [hDu]
    have hsumCont : ContinuousAt
        (∑ u ∈ S, ((D u : ℝ) • fun z => Real.log ‖z - u‖)) w := by
      induction S using Finset.induction with
      | empty => simp; fun_prop
      | @insert u T huT ih =>
          rw [Finset.sum_insert huT]
          apply ContinuousAt.add
          · by_cases hDu : D u = 0
            · rw [hDu, Int.cast_zero, zero_smul]
              fun_prop
            · have hwu : w ≠ u := by
                intro h
                subst u
                exact hDu hwD
              have hsub : ContinuousAt (fun z : ℂ => z - u) w :=
                continuousAt_id.sub continuousAt_const
              have hnorm : ContinuousAt (fun z : ℂ => ‖z - u‖) w := hsub.norm
              have hnz : ‖w - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwu)
              exact ContinuousAt.const_smul (hnorm.log hnz) _
          · exact ih
    have hrightCont : ContinuousAt
        ((∑ᶠ u, ((D u : ℝ) * Real.log ‖· - u‖)) + (Real.log ‖g ·‖)) w := by
      rw [hfunSum]
      apply ContinuousAt.add
      · exact hsumCont
      · have hwclosed : w ∈ closedBall (0 : ℂ) |R| := by
          exact hwclosed
        have hgw : g w ≠ 0 := hgfree ⟨w, hwclosed⟩
        exact (hg w hwclosed).continuousAt.norm.log (norm_ne_zero_iff.mpr hgw)
    have hleftCont : ContinuousAt (fun z => Real.log ‖f z‖) w := by
      exact hwf.continuousAt.norm.log (norm_ne_zero_iff.mpr hfw)
    have hlocal : (fun x => Real.log ‖f x‖) =ᶠ[nhdsWithin w {w}ᶜ]
        ((∑ᶠ u : ℂ, fun x => (D u : ℝ) * Real.log ‖x - u‖) +
          fun x => Real.log ‖g x‖) := by
      have hwU : w ∈ closedBall (0 : ℂ) |R| := mem_of_mem_nhds hU
      have hmem :=
        (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hlogeq) w hwU
      have hUne : closedBall (0 : ℂ) |R| ∈ nhdsWithin w {w}ᶜ :=
        nhdsWithin_le_nhds hU
      have hinter := Filter.inter_mem hmem hUne
      refine Filter.mem_of_superset hinter ?_
      rintro z ⟨hz1, hz2⟩
      rcases hz1 with hz1 | hz1
      · exact hz1
      · exact absurd hz2 hz1
    have hne : (nhdsWithin w ({w}ᶜ : Set ℂ)).NeBot :=
      Module.punctured_nhds_neBot ℂ ℂ w
    have hleftTendsto : Filter.Tendsto (fun z => Real.log ‖f z‖)
        (nhdsWithin w {w}ᶜ) (nhds (Real.log ‖f w‖)) :=
      hleftCont.continuousWithinAt
    have hrightTendsto : Filter.Tendsto
        ((∑ᶠ u : ℂ, fun x => (D u : ℝ) * Real.log ‖x - u‖) +
          fun x => Real.log ‖g x‖)
        (nhdsWithin w {w}ᶜ)
        (nhds (((∑ᶠ u : ℂ, fun x => (D u : ℝ) * Real.log ‖x - u‖) +
          fun x => Real.log ‖g x‖) w)) := by
      have hcwa : ContinuousWithinAt
          ((∑ᶠ u : ℂ, fun x => (D u : ℝ) * Real.log ‖x - u‖) +
            fun x => Real.log ‖g x‖) {w}ᶜ w :=
        hrightCont.continuousWithinAt
      exact hcwa
    have hval := tendsto_nhds_unique (hleftTendsto.congr' hlocal) hrightTendsto
    rw [hfunSum] at hval
    have hfin : Real.log ‖f w‖ =
        (∑ u ∈ S, (D u : ℝ) * Real.log ‖w - u‖) + Real.log ‖g w‖ := by
      simpa using hval
    rw [← hsumD] at hfin
    exact hfin
  rw [hsumD] at hlogval
  rw [hsumI] at hPJ
  have hidentity : Real.log ‖f w‖ =
      Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖f ·‖)) 0 R +
        ∑ u ∈ S, (D u : ℝ) *
          (Real.log ‖w - u‖ -
            Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) := by
    rw [hlogval, hPJ]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  have hboundary :
      Real.circleAverage
          ((Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖f ·‖)) 0 R ≤
        (R + r) / (R - r) *
          Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R := by
    have hp : (Complex.re ∘ herglotzRieszKernel 0 w) = poissonKernel 0 w := by
      funext z
      rw [poissonKernel_eq_re_herglotzRieszKernel]
    rw [hp]
    exact circleAverage_poissonKernel_smul_log_norm_le_abs
      (fun z _ => hfm z) hw (by simpa using hwr) hrR
  have hgreen : ∀ u ∈ S,
      0 ≤ Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖ := by
    intro u huS
    have huSupp : u ∈ D.support := by simpa [S] using huS
    have huBall : u ∈ closedBall (0 : ℂ) |R| := D.supportWithinDomain huSupp
    have hwu : w ≠ u := by
      intro h
      subst u
      exact (Function.mem_support.mp huSupp) hwD
    exact sub_nonneg.mpr
      (log_norm_sub_le_log_norm_innerLogKernel hR (by simpa [hRabs] using huBall)
        hwclosedR hwu)
  have hterm : ∀ u ∈ S,
      (D u : ℝ) *
          (Real.log ‖w - u‖ -
            Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖) ≤
        (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ -
            Real.log ‖w - u‖) := by
    intro u huS
    have hneg : -(D u : ℝ) ≤ (D u : ℝ)⁻ := neg_le_negPart _
    have hg := hgreen u huS
    nlinarith
  have hsumTerm := Finset.sum_le_sum hterm
  have hbound : Real.log ‖f w‖ ≤
      (R + r) / (R - r) *
          Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R +
        ∑ u ∈ S, (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ -
            Real.log ‖w - u‖) := by
    linarith [hidentity, hboundary, hsumTerm]
  have hRhs0 : 0 ≤
      (R + r) / (R - r) *
          Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R +
        ∑ u ∈ S, (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ -
            Real.log ‖w - u‖) := by
    have hK0 : 0 ≤ (R + r) / (R - r) := by
      have hr0 : 0 ≤ r := (norm_nonneg w).trans hwr
      have : 0 < R - r := by linarith
      positivity
    have havg0 : 0 ≤ Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R := by
      have hmeroSphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := fun z _ => hfm z
      have habsInt : CircleIntegrable (fun z => |Real.log ‖f z‖|) 0 R :=
        hmeroSphere.circleIntegrable_log_norm.abs
      have hmono := Real.circleAverage_mono
        (circleIntegrable_const (0 : ℝ) 0 R)
        habsInt (fun _ _ => abs_nonneg _)
      simpa [Real.circleAverage_const] using hmono
    have hsum0 : 0 ≤ ∑ u ∈ S, (D u : ℝ)⁻ *
        (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖) := by
      apply Finset.sum_nonneg
      intro u hu
      exact mul_nonneg (negPart_nonneg _) (hgreen u hu)
    positivity
  have hsumGreen :
      (∑ᶠ u : ℂ, (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖)) =
        ∑ u ∈ S, (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu
    apply hu
    simp [hDu]
  change Real.posLog ‖f w‖ ≤
      (R + r) / (R - r) *
          Real.circleAverage (fun z => |Real.log ‖f z‖|) 0 R +
        ∑ᶠ u : ℂ, (D u : ℝ)⁻ *
          (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖)
  rw [hsumGreen]
  rw [Real.posLog]
  exact max_le hRhs0 hbound

end

end GaloisForLFunctions.HTGeometry
