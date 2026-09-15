import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalBoundaryCollarBounds
import Mathlib.Topology.UniformSpace.UniformApproximation

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalBoundaryRestoration
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalCompleteTransfer
open D4BMOriginalBoundaryCollarBounds D4BMOriginalCompactBoundary D4BMOriginalCuspFlux
noncomputable section
set_option autoImplicit false

private def positiveTime : Set (ℝ×ℝ) := {z | 0<z.1}

/-- The leading trace is the uniform limit of the actual physical transfers,
including every time value and horizontal position at fixed cusp height. -/
theorem physical_transfer_horizon_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ (j : Fin 4) (k : ℝ),0≤k →
      TendstoUniformlyOn (fun L (z : ℝ×ℝ) => radialTransfer q br amp w j z.1 L z.2 k)
        (fun z : ℝ×ℝ => horizonTransfer q br amp w j z.1 z.2 k) atTop {z : ℝ×ℝ | 0<z.1} := by
  obtain ⟨G,hG,hg⟩ := radial_transfer_error q br amp 0
  refine ⟨G,hG,?_⟩
  intro w hwi hw j k hk
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  apply Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity.mpr
  intro epsilon hepsilon
  have ht : Tendsto (fun L : ℝ => C*Real.exp (-L)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  filter_upwards [hc,ht.eventually (gt_mem_nhds hepsilon)] with L hL hsmall z hz
  rw [dist_comm,dist_eq_norm]
  have h := hL z.1 z.2 k hz hk j
  simp only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at h
  exact (h.trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (by linarith : -z.1≤0)) (by positivity)).trans_eq (mul_one _))).trans_lt hsmall

/-- The actual leading trace has compact time/horizontal integral admission,
derived from uniform convergence of the original smooth physical fields. -/
theorem horizon_transfer_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ (j : Fin 4) (k : ℝ),0≤k →
      ContinuousOn (fun z : ℝ×ℝ => horizonTransfer q br amp w j z.1 z.2 k) {z : ℝ×ℝ | 0<z.1} := by
  obtain ⟨G,hG,hg⟩ := physical_transfer_horizon_uniform q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw j k hk
  apply (hg w hwi hw j k hk).continuousOn
  apply Filter.Eventually.frequently
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL z hz
  exact (radial_transfer_continuousAt q br amp w hwi L k hL j z hz).continuousWithinAt

private theorem horizontal_integrable (F : ℝ×ℝ→ℂ) (hF : ContinuousOn F positiveTime)
    (p : ℝ) (hp : 0<p) : IntervalIntegrable (fun x => F (p,x)) volume (-1/2:ℝ) (1/2:ℝ) := by
  have ho : IsOpen positiveTime := isOpen_lt continuous_const continuous_fst
  have hc : Continuous (fun x : ℝ => F (p,x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hF.continuousAt (ho.mem_nhds hp)).comp (f:=fun x : ℝ => (p,x))
      (show ContinuousAt (fun x : ℝ => (p,x)) x by fun_prop)
  exact hc.intervalIntegrable _ _

private theorem period_time_integrable (F : ℝ×ℝ→ℂ) (hF : ContinuousOn F positiveTime)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun p => ∫ x in (-1/2:ℝ)..1/2,F (p,x)) volume a b := by
  have hc : ContinuousOn F (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) :=
    hF.mono (fun z hz => ha.trans_le hz.1.1)
  have hi : Integrable F ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

/-- The leading horizon counterterm retains the complete physical endpoint/bulk functional. -/
def horizonBoundary (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b k : ℝ) : ℂ :=
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  let F := fun j p => ∫ x in (-1/2:ℝ)..1/2,horizonTransfer q br amp w j p x k
  (-(mu-2)*(F 0 b-F 0 a)+w*(mu*(∫ p in a..b,F 1 p)-(∫ p in a..b,F 2 p)-
    2*(mu-2)*(∫ p in a..b,F 0 p)-(∫ p in a..b,F 3 p)))

private theorem boundary_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b L k : ℝ) (ha : 0<a) (hab : a≤b) (hL : 0<L)
    (hH : ∀ j : Fin 4,ContinuousOn (fun z : ℝ×ℝ => horizonTransfer q br amp w j z.1 z.2 k) positiveTime) :
    radialBoundary q br amp w a b L k-horizonBoundary q br amp w a b k=
      boundaryError q br amp w a b L k := by
  let U := fun j (z : ℝ×ℝ) => radialTransfer q br amp w j z.1 L z.2 k
  let V := fun j (z : ℝ×ℝ) => horizonTransfer q br amp w j z.1 z.2 k
  have hU (j : Fin 4) : ContinuousOn (U j) positiveTime :=
    fun z hz => (radial_transfer_continuousAt q br amp w hw L k hL j z hz).continuousWithinAt
  have hp (j : Fin 4) (p : ℝ) (hp : 0<p) :
      (∫ x in (-1/2:ℝ)..1/2,U j (p,x)-V j (p,x))=
        (∫ x in (-1/2:ℝ)..1/2,U j (p,x))-(∫ x in (-1/2:ℝ)..1/2,V j (p,x)) :=
    intervalIntegral.integral_sub (horizontal_integrable (U j) (hU j) p hp)
      (horizontal_integrable (V j) (hH j) p hp)
  have ht (j : Fin 4) :
      (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,U j (p,x)-V j (p,x))=
        (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,U j (p,x))-
          (∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,V j (p,x)) := by
    calc
      _ = ∫ p in a..b,(∫ x in (-1/2:ℝ)..1/2,U j (p,x))-(∫ x in (-1/2:ℝ)..1/2,V j (p,x)) := by
        apply intervalIntegral.integral_congr
        intro p hpp
        have hpp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hpp
        exact hp j p (ha.trans_le hpp'.1)
      _ = _ := intervalIntegral.integral_sub (period_time_integrable (U j) (hU j) a b ha hab)
        (period_time_integrable (V j) (hH j) a b ha hab)
  unfold radialBoundary horizonBoundary boundaryError
  dsimp only
  change _ = -(D4BMLeftModeRadialEquation.eigenvalue q-2)*
    ((∫ x in (-1/2:ℝ)..1/2,U 0 (b,x)-V 0 (b,x))-(∫ x in (-1/2:ℝ)..1/2,U 0 (a,x)-V 0 (a,x)))+_
  rw [hp 0 b (ha.trans_le hab),hp 0 a ha,ht 0,ht 1,ht 2,ht 3]
  dsimp only [U,V]
  ring

/-- Literal complete metric boundary with its three prescribed cusp powers
and its actual leading horizon trace, in the original radial measure. -/
def physicalRestoredBoundary (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  let R := tortoiseRadius (-L/2)
  (((R:ℂ)^2-1)*((∫ p in a..b,
      (D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 0 p R (Real.exp k)-
        D4BMOriginalModularOrbit.modeCompleteTopFlux q q br true amp w 1 p R (Real.exp k)/((R:ℂ)^2-1))/(R:ℂ)^2)-
      ∑ i : Fin 3,compactBoundaryCoefficient q q br true amp w a b R i*
        Complex.exp (fluxExponent q q i*(k:ℂ)))-horizonBoundary q br amp w a b k)

/-- Exact identification of the restored physical boundary with the proved
integrable-error expression. All separate compact integral admission is derived. -/
theorem physical_boundary_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b L k : ℝ,0<a → a≤b → 0<L → 0≤k →
      physicalRestoredBoundary q br amp w a b L k=boundaryError q br amp w a b L k := by
  obtain ⟨G,hG,hg⟩ := horizon_transfer_continuous q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a b L k ha hab hL hk
  unfold physicalRestoredBoundary
  dsimp only
  rw [complete_metric_boundary_products q br amp w hwi a b L k ha hab hL,
    complete_boundary_radial_density q br amp w a b L k hL]
  exact boundary_difference q br amp w hwi a b L k ha hab hL (fun j => hg w hwi hw j k hk)

/-- The literal four-transfer physical boundary, with its actual cusp powers
and leading horizon trace, has an independent-cutoff collar limit. The factor
one-half is the original tortoise collar Jacobian. -/
theorem physical_boundary_collar_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ L0 : ℝ,0<L0 ∧
      ∀ (T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2}) (M : ℝ×ℝ→Ici L0),
        Tendsto (fun z : ℝ×ℝ => (∫ L in L0..(M z:ℝ),
          physicalRestoredBoundary q br amp w (T z).val.1 (T z).val.2 L z.2)/2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := physical_boundary_restoration q br amp
  obtain ⟨G2,_,h2⟩ := complete_boundary_collar_joint_limit q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨L0,hL0,hl⟩ := h2 w hwi hw2
  refine ⟨L0,hL0,?_⟩
  intro T M
  have he : (fun z : ℝ×ℝ => ∫ L in L0..(M z:ℝ),
      boundaryError q br amp w (T z).val.1 (T z).val.2 L z.2) =ᶠ[
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ))]
      (fun z : ℝ×ℝ => ∫ L in L0..(M z:ℝ),
        physicalRestoredBoundary q br amp w (T z).val.1 (T z).val.2 L z.2) := by
    filter_upwards [(eventually_ge_atTop (0:ℝ)).prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
    apply intervalIntegral.integral_congr
    intro L hL
    have hM : L0≤(M z:ℝ) := (M z).property
    have hL' : L∈Icc L0 (M z:ℝ) := by simpa only [uIcc_of_le hM] using hL
    exact (h1 w hwi hw1 (T z).val.1 (T z).val.2 L z.2
      (T z).property.1 (T z).property.2 (hL0.trans_le hL'.1) hz.2).symm
  simpa only [zero_div] using ((hl T M).congr' he).div_const (2:ℂ)

end
end RHTower.D4BMOriginalBoundaryRestoration
