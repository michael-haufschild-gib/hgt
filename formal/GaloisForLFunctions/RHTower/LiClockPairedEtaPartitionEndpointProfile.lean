import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionDensityTail
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

open MeasureTheory Set Filter RiemannGaussian
open scoped Topology Interval BigOperators
noncomputable section
namespace RHTower

def liClockPairedEtaPartitionSourceEta (b : ℝ) : ℝ :=
  b*(∫ v : ℝ, Real.exp (-b*v) ∂ RiemannGaussian.pairedEtaLogMeasure)

-- P2: all finite coordinates and both half-tilts remain in g_A,N.

def liClockPairedEtaPartitionEndpointProfile (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp ((Real.log (2*(N:ℝ))-y)/2)*
    liClockPairedEtaPartitionRawDifferenceDensity N (Real.log (2*(N:ℝ))-y)

-- P3: exactly one upper-factor half-average.

def liClockPairedEtaPartitionEndpointProfileLimit (y : ℝ) : ℝ :=
  (1/2)*(∫ v in Icc 0 y, Real.exp (-v) ∂ RiemannGaussian.pairedEtaLogMeasure)

private theorem ep_segment {b l u : ℝ} (hb : 0<b) (hlu : l≤u) :
    (∫ v in Ioc l u, Real.exp (-b*v)) =
      (Real.exp (-b*l)-Real.exp (-b*u))/b := by
  rw [← intervalIntegral.integral_of_le hlu,
    intervalIntegral.integral_comp_mul_left (f:=Real.exp) (c:= -b) (neg_ne_zero.mpr hb.ne'),
    integral_exp]
  simp only [smul_eq_mul,inv_neg]
  ring

private theorem ep_exp_log {b x : ℝ} (hx : 0<x) :
    Real.exp (-b*Real.log x)=x^(-b) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem liClockPairedEtaPartitionSourceEta_bounds
    {b : ℝ} (hb : 0<b) :
  1-(2:ℝ)^(-b)≤liClockPairedEtaPartitionSourceEta b ∧
    liClockPairedEtaPartitionSourceEta b≤1 := by
  have hi:=integrable_rexp_neg_mul_pairedEtaLogMeasure hb
  have hlo:=integral_mono_measure
    (Measure.restrict_mono_set volume Ioc_zero_log_two_subset_pairedEtaLogSupport)
    (Eventually.of_forall (fun v : ℝ=>(Real.exp_pos (-b*v)).le)) hi
  have hip : IntegrableOn (fun v : ℝ=>Real.exp (-b*v)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a:= -b) (by linarith) 0
  have hup:=integral_mono_measure pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
    (Eventually.of_forall (fun v : ℝ=>(Real.exp_pos (-b*v)).le)) hip
  change (∫v in Ioc 0 (Real.log 2),Real.exp (-b*v))≤
    (∫v,Real.exp (-b*v) ∂pairedEtaLogMeasure) at hlo
  rw [ep_segment hb (Real.log_nonneg (by norm_num)),mul_zero,Real.exp_zero,ep_exp_log (by norm_num : 0<(2:ℝ))] at hlo
  change (∫v,Real.exp (-b*v) ∂pairedEtaLogMeasure)≤
    (∫v in Ioi 0,Real.exp (-b*v)) at hup
  rw [integral_exp_mul_Ioi (a:= -b) (by linarith) 0] at hup
  simp only [mul_zero,Real.exp_zero,neg_div_neg_eq,one_div] at hup
  constructor
  · unfold liClockPairedEtaPartitionSourceEta
    simpa only [mul_comm] using (div_le_iff₀ hb).mp hlo
  · unfold liClockPairedEtaPartitionSourceEta
    have h:=mul_le_mul_of_nonneg_left hup hb.le
    simpa only [mul_inv_cancel₀ hb.ne'] using h

theorem liClockPairedEtaPartitionSourceEta_pos
    {b : ℝ} (hb : 0<b) :
  0<liClockPairedEtaPartitionSourceEta b := by
  have he : (2:ℝ)^(-b)<1 := by
    rw [Real.rpow_def_of_pos (by norm_num),Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (Real.log_pos (by norm_num)) (neg_neg_of_pos hb)
  exact (sub_pos.mpr he).trans_le (liClockPairedEtaPartitionSourceEta_bounds hb).1

private theorem ep_paired_source {b : ℝ} (hb : 0<b) :
    liClockPairedEtaPartitionSourceEta b =
      ∑' n : ℕ, ((2*(n:ℝ)+1)^(-b)-(2*(n:ℝ)+2)^(-b)) := by
  have hi := integrable_rexp_neg_mul_pairedEtaLogMeasure hb
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hi
  unfold liClockPairedEtaPartitionSourceEta
  rw [pairedEtaLogMeasure_eq_sum_restrict, integral_sum_measure hi, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change b*(∫v in Ioc (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+2)),
    Real.exp (-b*v)) = _
  rw [ep_segment hb (Real.log_le_log (by positivity) (by linarith)),
    ep_exp_log (by positivity : 0<2*(n:ℝ)+1),
    ep_exp_log (by positivity : 0<2*(n:ℝ)+2)]
  field_simp

theorem summable_norm_liClockPairedEtaPartitionSourceEtaDirichlet
    {b : ℝ} (hb : 1<b) :
  Summable (fun n : ℕ => ‖(-1:ℝ)^n*((n:ℝ)+1)^(-b)‖) := by
  have h := (Real.summable_nat_rpow.mpr (by linarith : -b < -1)).comp_injective
    Nat.succ_injective
  have hn := h.norm
  simpa only [Function.comp_def, Nat.cast_succ, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul] using hn

theorem liClockPairedEtaPartitionSourceEta_eq_paired_tsum
    {b : ℝ} (hb : 1<b) :
  liClockPairedEtaPartitionSourceEta b =
    ∑' n : ℕ, ((2*(n:ℝ)+1)^(-b)-(2*(n:ℝ)+2)^(-b)) :=
  ep_paired_source (by linarith)

theorem liClockPairedEtaPartitionSourceEta_eq_alternating_tsum
    {b : ℝ} (hb : 1<b) :
  liClockPairedEtaPartitionSourceEta b =
    ∑' n : ℕ, (-1:ℝ)^n*((n:ℝ)+1)^(-b) := by
  let f : ℕ → ℝ := fun n => (-1:ℝ)^n*((n:ℝ)+1)^(-b)
  have hs : Summable f := (summable_norm_liClockPairedEtaPartitionSourceEtaDirichlet hb).of_norm
  have he : Summable (fun n => f (2*n)) := hs.comp_injective (by intro n m h; change 2*n=2*m at h; omega)
  have ho : Summable (fun n => f (2*n+1)) := hs.comp_injective (by intro n m h; change 2*n+1=2*m+1 at h; omega)
  have hsplit := tsum_even_add_odd he ho
  rw [← hsplit, ← he.tsum_add ho, liClockPairedEtaPartitionSourceEta_eq_paired_tsum hb]
  apply tsum_congr
  intro n
  simp only [f, pow_mul, pow_add, show (-1:ℝ)^2=1 by norm_num, one_pow,
    pow_one, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [show 2*(n:ℝ)+1+1=2*(n:ℝ)+2 by ring]
  ring

theorem liClockPairedEtaPartitionSourceEta_one :
  liClockPairedEtaPartitionSourceEta 1=Real.log 2 := by
  rw [ep_paired_source (by norm_num)]
  convert GaloisForLFunctions.HTGeometry.tsum_alternatingHarmonicPair using 1
  apply tsum_congr
  intro n
  simp only [GaloisForLFunctions.HTGeometry.alternatingHarmonicPair,
    Real.rpow_neg_one, one_div]

private theorem ep_source_positive : ∀ᵐ v ∂pairedEtaLogMeasure, 0<v := by
  change ∀ᵐ v ∂volume.restrict pairedEtaLogSupport, 0<v
  filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogSupport] with v hv
  exact pairedEtaLogSupport_subset_Ioi_zero hv

theorem tendsto_liClockPairedEtaPartitionSourceEta_one_right :
  Tendsto liClockPairedEtaPartitionSourceEta
    (nhdsWithin (1:ℝ) (Ioi 1)) (nhds (Real.log 2)) := by
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ:=pairedEtaLogMeasure) (F:=fun b v : ℝ => Real.exp (-b*v))
    (f:=fun v : ℝ => Real.exp (-v)) (l:=nhdsWithin (1:ℝ) (Ioi 1))
    (fun v : ℝ => Real.exp (-v))
    (Eventually.of_forall (fun b => (show Continuous (fun v : ℝ => Real.exp (-b*v))
      by fun_prop).aestronglyMeasurable))
    (by
      filter_upwards [self_mem_nhdsWithin] with b hb
      filter_upwards [ep_source_positive] with v hv
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hb' : 1<b := hb
      nlinarith)
    (by simpa using integrable_rexp_neg_mul_pairedEtaLogMeasure (a:=1) (by norm_num))
    (Eventually.of_forall (fun v => by
      simpa using (show Continuous (fun b : ℝ => Real.exp (-b*v)) by fun_prop).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (1:ℝ) (Ioi 1) ≤ nhds 1)))
  have hid : Tendsto (fun b : ℝ => b) (nhdsWithin (1:ℝ) (Ioi 1)) (nhds 1) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have h:=hid.mul hi
  have he : (∫v:ℝ,Real.exp (-v) ∂pairedEtaLogMeasure)=Real.log 2 := by
    simpa [liClockPairedEtaPartitionSourceEta] using liClockPairedEtaPartitionSourceEta_one
  change Tendsto (fun b : ℝ => b*(∫v:ℝ,Real.exp (-b*v) ∂pairedEtaLogMeasure)) _ _
  simpa only [he, one_mul] using h

theorem tendsto_liClockPairedEtaPartitionSourceEta_atTop :
  Tendsto liClockPairedEtaPartitionSourceEta atTop (nhds (1:ℝ)) := by
  have hp := (tendsto_rpow_atBot_of_base_gt_one (2:ℝ) (by norm_num)).comp
    (tendsto_neg_atTop_atBot : Tendsto (fun b : ℝ => -b) atTop atBot)
  have hlo : Tendsto (fun b : ℝ => 1-(2:ℝ)^(-b)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
    exact (liClockPairedEtaPartitionSourceEta_bounds hb).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
    exact (liClockPairedEtaPartitionSourceEta_bounds hb).2

private theorem ep_cumulative_laplace {η : Measure ℝ} [SFinite η]
    (hsupport : ∀ᵐ v ∂η, 0 < v)
    (hbase : Integrable (fun v : ℝ => Real.exp (-v)) η)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.exp (-a*y) *
      (∫ v in Icc 0 y, Real.exp (-v) ∂η)) (Ioi 0) ∧
    (∫ y in Ioi 0, Real.exp (-a*y) * (∫ v in Icc 0 y, Real.exp (-v) ∂η)) =
      (1/a) * (∫ v : ℝ, Real.exp (-(a+1)*v) ∂η) := by
  let ρ : Measure ℝ := volume.restrict (Ioi 0)
  let C : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  let k : ℝ × ℝ → ℝ := C.indicator
    (fun p => Real.exp (-p.1) * Real.exp (-a*p.2))
  have hC : MeasurableSet C :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hdecay : Integrable (fun y : ℝ => Real.exp (-a*y)) ρ :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0
  have hk : Integrable k (η.prod ρ) := (hbase.mul_prod hdecay).indicator hC
  have hright (y : ℝ) : (∫ v : ℝ, k (v,y) ∂η) =
      Real.exp (-a*y) * (∫ v in Icc 0 y, Real.exp (-v) ∂η) := by
    have heq : (fun v : ℝ => k (v,y)) = fun v : ℝ =>
        Real.exp (-a*y) * (Icc 0 y).indicator (fun v => Real.exp (-v)) v := by
      funext v
      simp only [k, C, Set.indicator_apply, mem_setOf_eq, mem_Icc]
      split_ifs <;> ring
    rw [heq, integral_const_mul, integral_indicator measurableSet_Icc]
  have houter : Integrable (fun y : ℝ => Real.exp (-a*y) *
      (∫ v in Icc 0 y, Real.exp (-v) ∂η)) ρ := by
    simpa only [hright] using hk.integral_prod_right
  have hleft (v : ℝ) (hv : 0 < v) :
      (∫ y : ℝ, k (v,y) ∂ρ) = (1/a)*Real.exp (-(a+1)*v) := by
    have heq : (fun y : ℝ => k (v,y)) = fun y : ℝ =>
        Real.exp (-v) * (Ici v).indicator (fun y => Real.exp (-a*y)) y := by
      funext y
      simp only [k, C, Set.indicator_apply, mem_setOf_eq, mem_Ici,
        hv.le, true_and]
      split_ifs <;> ring
    have hinter : Ioi (0 : ℝ) ∩ Ici v = Ici v :=
      Set.inter_eq_right.mpr (fun y hy => lt_of_lt_of_le hv hy)
    rw [heq, integral_const_mul]
    change Real.exp (-v) * (∫ y in Ioi 0,
      (Ici v).indicator (fun y => Real.exp (-a*y)) y) = _
    rw [setIntegral_indicator measurableSet_Ici, hinter, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_neg_of_pos ha) v]
    rw [show -(a+1)*v = -v + (-a*v) by ring, Real.exp_add]
    ring
  refine ⟨houter, ?_⟩
  change (∫ y : ℝ, Real.exp (-a*y) * (∫ v in Icc 0 y, Real.exp (-v) ∂η) ∂ρ) = _
  calc
    _ = ∫ y : ℝ, ∫ v : ℝ, k (v,y) ∂η ∂ρ := by simp_rw [hright]
    _ = ∫ v : ℝ, ∫ y : ℝ, k (v,y) ∂ρ ∂η :=
      (integral_integral_swap (f := fun v y => k (v,y)) hk).symm
    _ = ∫ v : ℝ, (1/a)*Real.exp (-(a+1)*v) ∂η := by
      apply integral_congr_ae
      filter_upwards [hsupport] with v hv
      exact hleft v hv
    _ = _ := integral_const_mul _ _

theorem liClockPairedEtaPartitionEndpointProfileLimit_laplace
    {a : ℝ} (ha : 0<a) :
  IntegrableOn (fun y : ℝ => Real.exp (-a*y)*
    liClockPairedEtaPartitionEndpointProfileLimit y) (Ioi 0) ∧
  (∫ y in Ioi 0, Real.exp (-a*y)*liClockPairedEtaPartitionEndpointProfileLimit y) =
    liClockPairedEtaPartitionSourceEta (a+1)/(2*a*(a+1)) := by
  have hb : Integrable (fun v : ℝ => Real.exp (-v)) pairedEtaLogMeasure := by
    simpa using integrable_rexp_neg_mul_pairedEtaLogMeasure (a:=1) (by norm_num)
  have h:=ep_cumulative_laplace ep_source_positive hb ha
  constructor
  · have heq : (fun y : ℝ => Real.exp (-a*y)*liClockPairedEtaPartitionEndpointProfileLimit y)=
        (fun y : ℝ => (1/2)*(Real.exp (-a*y)*(∫v in Icc 0 y,Real.exp (-v) ∂pairedEtaLogMeasure))) := by
      funext y
      unfold liClockPairedEtaPartitionEndpointProfileLimit
      ring
    rw [heq]
    exact h.1.const_mul (1/2:ℝ)
  · unfold liClockPairedEtaPartitionEndpointProfileLimit
    simp_rw [show ∀y:ℝ, Real.exp (-a*y)*((1/2)*(∫v in Icc 0 y,Real.exp (-v) ∂pairedEtaLogMeasure))=
      (1/2)*(Real.exp (-a*y)*(∫v in Icc 0 y,Real.exp (-v) ∂pairedEtaLogMeasure)) by intro y; ring]
    rw [integral_const_mul,h.2]
    unfold liClockPairedEtaPartitionSourceEta
    field_simp

private def ep_indicator (v : ℝ) : ℝ :=
  pairedEtaLogSupport.indicator (fun _ => (1:ℝ)) v

private theorem ep_indicator_bounds (v : ℝ) : 0≤ep_indicator v ∧ ep_indicator v≤1 := by
  by_cases hv : v∈pairedEtaLogSupport <;> simp [ep_indicator,hv]

private theorem ep_retained_integrable (y r : ℝ) :
    IntegrableOn (fun v : ℝ => Real.exp (-v)*ep_indicator v*ep_indicator (v+r)) (Icc 0 y) := by
  have hA : Measurable ep_indicator := measurable_const.indicator measurableSet_pairedEtaLogSupport
  have hs : Measurable (fun v : ℝ => v+r) := by fun_prop
  have hm : Measurable (fun v : ℝ => Real.exp (-v)*ep_indicator v*ep_indicator (v+r)) :=
    ((show Measurable (fun v : ℝ => Real.exp (-v)) by fun_prop).mul hA).mul (hA.comp hs)
  have hi : Integrable (fun v : ℝ => Real.exp (-v)) (volume.restrict (Icc 0 y)) :=
    (show Continuous (fun v : ℝ => Real.exp (-v)) by fun_prop).continuousOn.integrableOn_Icc
  change Integrable _ (volume.restrict (Icc 0 y))
  apply hi.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  have hA0 := (ep_indicator_bounds v).1
  have hA1 := (ep_indicator_bounds v).2
  have hB0 := (ep_indicator_bounds (v+r)).1
  have hB1 := (ep_indicator_bounds (v+r)).2
  have h0 : 0≤Real.exp (-v)*ep_indicator v := mul_nonneg (Real.exp_pos _).le hA0
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 hB0)]
  exact (mul_le_of_le_one_right h0 hB1).trans
    (mul_le_of_le_one_right (Real.exp_pos _).le hA1)

private theorem ep_scaled_product {N : ℕ} (hN : 0<N) {y : ℝ}
    (_hy : 0≤y) (hyL : y≤Real.log (2*(N:ℝ))) (v : ℝ) :
    Real.exp ((Real.log (2*(N:ℝ))-y)/2)*
      (liClockPairedEtaPartitionHalfTiltWeight N (v+Real.log (2*(N:ℝ))-y)*
        liClockPairedEtaPartitionHalfTiltWeight N v)=
      (Icc 0 y).indicator (fun v => Real.exp (-v)*ep_indicator v*
        ep_indicator (v+Real.log (2*(N:ℝ))-y)) v := by
  let L : ℝ := Real.log (2*(N:ℝ))
  have hf := liClockPairedEtaPartitionLogSupport_eq_infinite_inter hN
  have heq : (v∈liClockPairedEtaPartitionLogSupport N ∧
      v+L-y∈liClockPairedEtaPartitionLogSupport N) ↔
      (v∈Icc 0 y ∧ v∈pairedEtaLogSupport ∧ v+L-y∈pairedEtaLogSupport) := by
    rw [hf]
    simp only [mem_inter_iff,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨⟨hv,hv0,hvL⟩,hvr,hvr0,hvrL⟩
      exact ⟨⟨hv0.le,by linarith⟩,hv,hvr⟩
    · rintro ⟨⟨hv0,hvy⟩,hv,hvr⟩
      have hvp := pairedEtaLogSupport_subset_Ioi_zero hv
      have hvrp := pairedEtaLogSupport_subset_Ioi_zero hvr
      exact ⟨⟨hv,hvp,by linarith⟩,hvr,hvrp,by linarith⟩
  change Real.exp ((L-y)/2)*(liClockPairedEtaPartitionHalfTiltWeight N (v+L-y)*
    liClockPairedEtaPartitionHalfTiltWeight N v)=
    (Icc 0 y).indicator (fun v => Real.exp (-v)*ep_indicator v*ep_indicator (v+L-y)) v
  by_cases hp : v∈liClockPairedEtaPartitionLogSupport N ∧
      v+L-y∈liClockPairedEtaPartitionLogSupport N
  · obtain ⟨hyv,hva,hvra⟩ := heq.mp hp
    simp only [liClockPairedEtaPartitionHalfTiltWeight,indicator_of_mem hp.1,
      indicator_of_mem hp.2,indicator_of_mem hyv,ep_indicator,
      indicator_of_mem hva,indicator_of_mem hvra,mul_one]
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    dsimp [L]
    ring
  · have hl : Real.exp ((L-y)/2)*(liClockPairedEtaPartitionHalfTiltWeight N (v+L-y)*
      liClockPairedEtaPartitionHalfTiltWeight N v)=0 := by
      unfold liClockPairedEtaPartitionHalfTiltWeight
      by_cases hv : v∈liClockPairedEtaPartitionLogSupport N
      · have hvr : v+L-y∉liClockPairedEtaPartitionLogSupport N := fun h => hp ⟨hv,h⟩
        simp [hv,hvr]
      · simp [hv]
    rw [hl]
    by_cases hyv : v∈Icc 0 y
    · rw [indicator_of_mem hyv]
      by_cases hva : v∈pairedEtaLogSupport
      · by_cases hvra : v+L-y∈pairedEtaLogSupport
        · exact (hp (heq.mpr ⟨hyv,hva,hvra⟩)).elim
        · simp [ep_indicator,hvra,L]
      · simp [ep_indicator,hva]
    · simp only [indicator_of_notMem hyv]

theorem liClockPairedEtaPartitionEndpointProfile_eq_source
    {N : ℕ} (hN : 0<N) {y : ℝ} (hy : 0≤y)
    (hyL : y≤Real.log (2*(N:ℝ))) :
  liClockPairedEtaPartitionEndpointProfile N y =
    ∫ v in Icc 0 y, Real.exp (-v)*
      (RiemannGaussian.pairedEtaLogSupport.indicator (fun _ : ℝ => (1:ℝ)) v)*
      (RiemannGaussian.pairedEtaLogSupport.indicator (fun _ : ℝ => (1:ℝ))
        (v+Real.log (2*(N:ℝ))-y)) := by
  let r : ℝ := Real.log (2*(N:ℝ))-y
  have hi := (ep_retained_integrable y r).integrable_indicator measurableSet_Icc
  have heq (v : ℝ) := ep_scaled_product hN hy hyL v
  have hscaled : Integrable (fun v : ℝ => Real.exp (r/2)*
      (liClockPairedEtaPartitionHalfTiltWeight N (v+r)*liClockPairedEtaPartitionHalfTiltWeight N v)) := by
    apply hi.congr
    apply Eventually.of_forall
    intro v
    simpa [r,sub_eq_add_neg,add_assoc] using (heq v).symm
  have hc : Real.exp (-r/2)*Real.exp (r/2)=1 := by
    rw [←Real.exp_add,show -r/2+r/2=0 by ring,Real.exp_zero]
  have hprod : Integrable (fun v : ℝ => liClockPairedEtaPartitionHalfTiltWeight N (v+r)*
      liClockPairedEtaPartitionHalfTiltWeight N v) := by
    simpa only [←mul_assoc,hc,one_mul] using hscaled.const_mul (Real.exp (-r/2))
  unfold liClockPairedEtaPartitionEndpointProfile liClockPairedEtaPartitionRawDifferenceDensity
  rw [←integral_const_mul]
  calc
    _ = ∫v:ℝ,(Icc 0 y).indicator (fun v => Real.exp (-v)*ep_indicator v*
          ep_indicator (v+Real.log (2*(N:ℝ))-y)) v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => by simpa [sub_eq_add_neg,add_assoc] using heq v)
    _ = _ := by rw [integral_indicator measurableSet_Icc]; rfl

theorem liClockPairedEtaContiguousEndpointProfile_eq
    {N : ℕ} (hN : 0<N) {y : ℝ} (hy : 0≤y)
    (hyL : y≤Real.log (2*(N:ℝ))) :
  Real.exp ((Real.log (2*(N:ℝ))-y)/2)*
    liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ)))
      (Real.log (2*(N:ℝ))-y) = 1-Real.exp (-y) := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    have hcast : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  rcases hy.eq_or_lt with hy | hy
  · subst y
    rw [sub_zero,liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs
      (by rw [abs_of_pos hL]),mul_zero,neg_zero,Real.exp_zero,sub_self]
  · rw [liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg (by linarith) (by linarith)]
    have he : Real.exp ((Real.log (2*(N:ℝ))-y)/2)*
        Real.exp (-(Real.log (2*(N:ℝ))-y)/2)=1 := by
      rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [show Real.log (2*(N:ℝ))-y-Real.log (2*(N:ℝ)) = -y by ring,
      ←mul_assoc,he,one_mul]

theorem liClockPairedEtaPartitionEndpointProfile_bounds
    {N : ℕ} (hN : 0<N) {y : ℝ} (hy : 0≤y)
    (hyL : y≤Real.log (2*(N:ℝ))) :
  0≤liClockPairedEtaPartitionEndpointProfile N y ∧
    liClockPairedEtaPartitionEndpointProfile N y≤1-Real.exp (-y) ∧
    1-Real.exp (-y)≤1 := by
  refine ⟨mul_nonneg (Real.exp_pos _).le (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N _),?_,by linarith [(Real.exp_pos (-y)).le]⟩
  rw [←liClockPairedEtaContiguousEndpointProfile_eq hN hy hyL]
  exact mul_le_mul_of_nonneg_left (liClockPairedEtaPartitionRawDifferenceDensity_le_contiguous N _)
    (Real.exp_pos _).le

private theorem ep_indicator_exp {v : ℝ} (hv : 0≤v) :
    liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp v)=ep_indicator v := by
  rw [liClockPairedEtaInfinitePartitionArithmeticIndicator_eq_log_support
    (Real.one_le_exp_iff.mpr hv),Real.log_exp]
  rfl

private theorem ep_exp_jacobian {v : ℝ} (hv : 0≤v) :
    Real.exp v*(liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp v)/(Real.exp v)^2)=
      Real.exp (-v)*ep_indicator v := by
  rw [ep_indicator_exp hv,Real.exp_neg]
  field_simp

private theorem ep_exp_jacobian_pair {v r : ℝ} (hv : 0≤v) (hr : 0≤r) :
    Real.exp v*(liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp v)*
      liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*Real.exp v)/(Real.exp v)^2)=
      Real.exp (-v)*ep_indicator v*ep_indicator (v+r) := by
  rw [show Real.exp v*(liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp v)*
    liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*Real.exp v)/(Real.exp v)^2)=
    (Real.exp v*(liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp v)/(Real.exp v)^2))*
      liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*Real.exp v) by ring,
    ep_exp_jacobian hv,←Real.exp_add,ep_indicator_exp (add_nonneg hr hv),add_comm r v]

private theorem ep_mass_indicator (s : Set ℝ) (hs : MeasurableSet s) :
    (∫v in s,Real.exp (-v)*ep_indicator v)=
      ∫v in s,Real.exp (-v) ∂pairedEtaLogMeasure := by
  have heq : (fun v : ℝ => Real.exp (-v)*ep_indicator v)=
      pairedEtaLogSupport.indicator (fun v => Real.exp (-v)) := by
    funext v
    by_cases hv : v∈pairedEtaLogSupport <;> simp [ep_indicator,hv]
  rw [heq,setIntegral_indicator measurableSet_pairedEtaLogSupport]
  change _=∫v:ℝ,Real.exp (-v) ∂(volume.restrict pairedEtaLogSupport).restrict s
  rw [Measure.restrict_restrict hs]

private theorem ep_source_reciprocal :
    IntegrableOn (fun w : ℝ => liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2) (Ioi 1) ∧
      (∫w in Ioi (1:ℝ),liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2)=
        liClockPairedEtaPartitionSourceEta 1 := by
  let g : ℝ → ℝ := fun w => liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2
  have hj (v : ℝ) (hv : v∈Ioi (0:ℝ)) : |Real.exp v|•g (Real.exp v)=
      Real.exp (-v)*ep_indicator v := by
    rw [abs_of_pos (Real.exp_pos _),smul_eq_mul]
    exact ep_exp_jacobian hv.le
  have hJ : IntegrableOn (fun v : ℝ => |Real.exp v|•g (Real.exp v)) (Ioi 0) := by
    have href := (integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) (0:ℝ)).indicator
      measurableSet_pairedEtaLogSupport
    apply href.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hj v hv]
    by_cases hA : v∈pairedEtaLogSupport <;> simp [ep_indicator,hA]
  have hderiv (v : ℝ) (_hv : v∈Ioi (0:ℝ)) :
      HasDerivWithinAt Real.exp (Real.exp v) (Ioi 0) v := (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hinj : InjOn Real.exp (Ioi (0:ℝ)) := Real.exp_injective.injOn
  have hadmit := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj g).mpr hJ
  rw [Real.image_exp_Ioi,Real.exp_zero] at hadmit
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  rw [Real.image_exp_Ioi,Real.exp_zero] at hsub
  refine ⟨hadmit,?_⟩
  calc
    _ = ∫v in Ioi (0:ℝ),Real.exp (-v)*ep_indicator v := by
      rw [hsub]
      exact setIntegral_congr_fun measurableSet_Ioi hj
    _ = ∫v in Ioi (0:ℝ),Real.exp (-v) ∂pairedEtaLogMeasure :=
      ep_mass_indicator (Ioi 0) measurableSet_Ioi
    _ = ∫v:ℝ,Real.exp (-v) ∂pairedEtaLogMeasure := by
      change (∫v:ℝ,Real.exp (-v) ∂(volume.restrict pairedEtaLogSupport).restrict (Ioi 0))=_
      rw [Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_right.mpr pairedEtaLogSupport_subset_Ioi_zero]
      rfl
    _ = _ := by simp [liClockPairedEtaPartitionSourceEta]

private theorem ep_source_one_by_substitution :
    liClockPairedEtaPartitionSourceEta 1 = Real.log 2 := by
  rw [←ep_source_reciprocal.2,liClockPairedEtaInfinitePartition_retained_inverse_mass]

private theorem ep_cutoff_pair {y r : ℝ} (_hy : 0≤y) (hr : 0≤r) :
    IntegrableOn (fun w : ℝ => liClockPairedEtaInfinitePartitionArithmeticIndicator w*
      liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*w)/w^2) (Icc 1 (Real.exp y)) ∧
      (∫v in Icc 0 y,Real.exp (-v)*ep_indicator v*ep_indicator (v+r))=
        ∫w in Ioc 1 (Real.exp y),liClockPairedEtaInfinitePartitionArithmeticIndicator w*
          liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*w)/w^2 := by
  let g : ℝ → ℝ := fun w => liClockPairedEtaInfinitePartitionArithmeticIndicator w*
    liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp r*w)/w^2
  have hj (v : ℝ) (hv : v∈Icc (0:ℝ) y) : |Real.exp v|•g (Real.exp v)=
      Real.exp (-v)*ep_indicator v*ep_indicator (v+r) := by
    rw [abs_of_pos (Real.exp_pos _),smul_eq_mul]
    exact ep_exp_jacobian_pair hv.1 hr
  have hJ : IntegrableOn (fun v : ℝ => |Real.exp v|•g (Real.exp v)) (Icc 0 y) := by
    apply (ep_retained_integrable y r).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hj v hv).symm
  have hderiv (v : ℝ) (_hv : v∈Icc (0:ℝ) y) :
      HasDerivWithinAt Real.exp (Real.exp v) (Icc 0 y) v := (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (0:ℝ) y) := Real.exp_injective.injOn
  have hadmit := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj g).mpr hJ
  rw [Real.image_exp_Icc,Real.exp_zero] at hadmit
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj g
  rw [Real.image_exp_Icc,Real.exp_zero] at hsub
  refine ⟨hadmit,?_⟩
  calc
    _ = ∫v in Icc (0:ℝ) y,|Real.exp v|•g (Real.exp v) := by
      exact setIntegral_congr_fun measurableSet_Icc (fun v hv => (hj v hv).symm)
    _ = ∫w in Icc (1:ℝ) (Real.exp y),g w := hsub.symm
    _ = _ := integral_Icc_eq_integral_Ioc

private theorem ep_cutoff_single {y : ℝ} (_hy : 0≤y) :
    IntegrableOn (fun w : ℝ => liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2) (Icc 1 (Real.exp y)) ∧
      (∫v in Icc 0 y,Real.exp (-v)*ep_indicator v)=
        ∫w in Ioc 1 (Real.exp y),liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2 := by
  let g : ℝ → ℝ := fun w => liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2
  have hj (v : ℝ) (hv : v∈Icc (0:ℝ) y) : |Real.exp v|•g (Real.exp v)=
      Real.exp (-v)*ep_indicator v := by
    rw [abs_of_pos (Real.exp_pos _),smul_eq_mul]
    exact ep_exp_jacobian hv.1
  have hJ : IntegrableOn (fun v : ℝ => |Real.exp v|•g (Real.exp v)) (Icc 0 y) := by
    have href := ((show Continuous (fun v : ℝ => Real.exp (-v)) by fun_prop).integrableOn_Icc
      (a:=(0:ℝ)) (b:=y) (μ:=volume)).indicator measurableSet_pairedEtaLogSupport
    apply href.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    rw [hj v hv]
    by_cases hA : v∈pairedEtaLogSupport <;> simp [ep_indicator,hA]
  have hderiv (v : ℝ) (_hv : v∈Icc (0:ℝ) y) :
      HasDerivWithinAt Real.exp (Real.exp v) (Icc 0 y) v := (Real.hasDerivAt_exp v).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (0:ℝ) y) := Real.exp_injective.injOn
  have hadmit := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj g).mpr hJ
  rw [Real.image_exp_Icc,Real.exp_zero] at hadmit
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj g
  rw [Real.image_exp_Icc,Real.exp_zero] at hsub
  refine ⟨hadmit,?_⟩
  calc
    _ = ∫v in Icc (0:ℝ) y,|Real.exp v|•g (Real.exp v) := by
      exact setIntegral_congr_fun measurableSet_Icc (fun v hv => (hj v hv).symm)
    _ = ∫w in Icc (1:ℝ) (Real.exp y),g w := hsub.symm
    _ = _ := integral_Icc_eq_integral_Ioc

private theorem ep_profile_continuous (N : ℕ) :
    Continuous (liClockPairedEtaPartitionEndpointProfile N) := by
  have hf : Continuous (fun y : ℝ => Real.log (2*(N:ℝ))-y) := by fun_prop
  have hg : Continuous (fun y : ℝ => (Real.log (2*(N:ℝ))-y)/2) := by fun_prop
  exact (Real.continuous_exp.comp hg).mul
    ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).comp hf)

private theorem ep_limit_bounds (y : ℝ) :
    0≤liClockPairedEtaPartitionEndpointProfileLimit y ∧
      liClockPairedEtaPartitionEndpointProfileLimit y≤1/2 := by
  have hi : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) 0
  have hle : pairedEtaLogMeasure.restrict (Icc 0 y)≤volume.restrict (Ioi 0) :=
    Measure.restrict_le_self.trans pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
  have h:=integral_mono_measure hle (Eventually.of_forall (fun v:ℝ => (Real.exp_pos (-v)).le)) hi
  have he : (∫v in Ioi (0:ℝ),Real.exp (-v))=1 := by
    simpa using integral_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) 0
  rw [he] at h
  constructor
  · exact mul_nonneg (by norm_num) (integral_nonneg (fun v => (Real.exp_pos (-v)).le))
  · change (1/2)*(∫v in Icc 0 y,Real.exp (-v) ∂pairedEtaLogMeasure)≤1/2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤1/2)

private theorem ep_limit_measurable : Measurable liClockPairedEtaPartitionEndpointProfileLimit := by
  let C : Set (ℝ×ℝ) := {p | 0≤p.2 ∧ p.2≤p.1}
  let k : ℝ×ℝ → ℝ := C.indicator (fun p => Real.exp (-p.2))
  have hC : MeasurableSet C :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hk : Measurable k := (show Measurable (fun p : ℝ×ℝ => Real.exp (-p.2))
    by fun_prop).indicator hC
  have hmeas : Measurable (fun y : ℝ => ∫v in Icc 0 y,Real.exp (-v) ∂pairedEtaLogMeasure) := by
    have heq (y : ℝ) : (fun v : ℝ => k (y,v))=(Icc 0 y).indicator (fun v => Real.exp (-v)) := by
      funext v
      simp only [k,C,Set.indicator_apply,mem_setOf_eq,mem_Icc]
    have h:=hk.stronglyMeasurable.integral_prod_right' (ν:=pairedEtaLogMeasure)
    simpa only [heq,integral_indicator measurableSet_Icc] using h.measurable
  exact measurable_const.mul hmeas


private abbrev ep_cutoffavg_ea := liClockPairedEtaInfinitePartitionArithmeticIndicator

private def ep_cutoffavg_endpointCell (B : ℝ) (n : ℕ) : Set ℝ :=
  Ioc (2*(n:ℝ)+1) (min (2*(n:ℝ)+2) B)

private theorem ep_cutoffavg_endpointCell_subset (B : ℝ) (n : ℕ) :
    ep_cutoffavg_endpointCell B n ⊆ Ioc (1:ℝ) B := by
  intro x hx
  exact ⟨by dsimp [ep_cutoffavg_endpointCell] at hx; linarith [hx.1, Nat.cast_nonneg (α := ℝ) n],
    hx.2.trans (min_le_right _ _)⟩

private theorem ep_cutoffavg_endpointCell_mem_odd {B x : ℝ} {n : ℕ}
    (hx : x ∈ ep_cutoffavg_endpointCell B n) :
    x ∈ ⋃ k : ℤ, Ioc (2*(k:ℝ)+1) (2*(k:ℝ)+2) := by
  apply mem_iUnion.mpr
  refine ⟨(n:ℤ), ?_⟩
  have he : (((n:ℤ):ℝ)) = (n:ℝ) := by norm_cast
  rw [he]
  exact ⟨hx.1, hx.2.trans (min_le_left _ _)⟩

private theorem ep_cutoffavg_endpointCells_unique {B x : ℝ} {m n : ℕ}
    (hm : x ∈ ep_cutoffavg_endpointCell B m) (hn : x ∈ ep_cutoffavg_endpointCell B n) : m=n := by
  have hmhi := hm.2.trans (min_le_left (2*(m:ℝ)+2) B)
  have hnhi := hn.2.trans (min_le_left (2*(n:ℝ)+2) B)
  rcases lt_trichotomy m n with h | h | h
  · have hc : (m:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    have hnlo := hn.1
    linarith
  · exact h
  · have hc : (n:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    have hmlo := hm.1
    linarith

private theorem ep_cutoffavg_endpointOdd_mem_cell {B x : ℝ} {K : ℕ}
    (hK : B ≤ 2*(K:ℝ)) (hx : x ∈ Ioc (1:ℝ) B)
    (ho : x ∈ ⋃ k : ℤ, Ioc (2*(k:ℝ)+1) (2*(k:ℝ)+2)) :
    ∃ n ∈ Finset.range K, x ∈ ep_cutoffavg_endpointCell B n := by
  obtain ⟨k,hlo,hhi⟩ := mem_iUnion.mp ho
  have hk : 0 ≤ k := by
    by_contra h
    have hk1 : k ≤ -1 := by omega
    have hkr : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    linarith [hx.1]
  let n := k.toNat
  have he : (n:ℝ) = (k:ℝ) := by exact_mod_cast (Int.toNat_of_nonneg hk)
  have hnlt : n<K := by
    have hnr : (n:ℝ)<(K:ℝ) := by linarith [hx.2]
    exact_mod_cast hnr
  refine ⟨n, Finset.mem_range.mpr hnlt, ?_⟩
  change (2*(n:ℝ)+1 < x) ∧ (x ≤ min (2*(n:ℝ)+2) B)
  rw [he]
  exact ⟨hlo, le_min hhi hx.2⟩

private theorem ep_cutoffavg_endpoint_indicator_partition {B : ℝ} {K : ℕ}
    (hK : B ≤ 2*(K:ℝ)) (g : ℝ → ℝ) (x : ℝ) :
    (Ioc (1:ℝ) B).indicator (fun x => ep_cutoffavg_ea x*g x) x =
      ∑ n ∈ Finset.range K, (ep_cutoffavg_endpointCell B n).indicator g x := by
  classical
  by_cases hx : x ∈ Ioc (1:ℝ) B
  · rw [indicator_of_mem hx]
    dsimp only [ep_cutoffavg_ea]
    rw [liClockPairedEtaInfinitePartitionArithmeticIndicator_eq_indicator]
    by_cases ho : x ∈ ⋃ k : ℤ, Ioc (2*(k:ℝ)+1) (2*(k:ℝ)+2)
    · rw [indicator_of_mem ho, one_mul]
      obtain ⟨n,hn,hxn⟩ := ep_cutoffavg_endpointOdd_mem_cell hK hx ho
      symm
      rw [Finset.sum_eq_single n]
      · exact indicator_of_mem hxn _
      · intro m hm hmn
        apply indicator_of_notMem
        intro hxm
        exact hmn (ep_cutoffavg_endpointCells_unique hxm hxn)
      · intro hnot
        exact (hnot hn).elim
    · rw [indicator_of_notMem ho, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro n hn
      apply indicator_of_notMem
      intro hxn
      exact ho (ep_cutoffavg_endpointCell_mem_odd hxn)
  · rw [indicator_of_notMem hx]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    apply indicator_of_notMem
    intro hxn
    exact hx (ep_cutoffavg_endpointCell_subset B n hxn)

private theorem ep_cutoffavg_endpoint_weight_integrable {B : ℝ}
    {σ : ℝ → ℝ} (hm : Measurable σ) (hσ : ∀ x : ℝ, |σ x|≤1) :
    IntegrableOn (fun x : ℝ => σ x/x^2) (Ioc (1:ℝ) B) := by
  have hc : ContinuousOn (fun x : ℝ => 1/x^2) (Icc (1:ℝ) B) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero _ (by linarith [hx.1]))
  have hi : IntegrableOn (fun x : ℝ => 1/x^2) (Ioc (1:ℝ) B) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.mono' ((hm.div (measurable_id.pow_const 2)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun x => by
    change |σ x/x^2| ≤ 1/x^2
    rw [abs_div, abs_of_nonneg (sq_nonneg x)]
    exact div_le_div_of_nonneg_right (hσ x) (sq_nonneg x))

private theorem ep_cutoffavg_endpoint_integral_partition {B : ℝ} {K : ℕ}
    (hK : B ≤ 2*(K:ℝ)) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc (1:ℝ) B)) :
    (∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x*g x) =
      ∑ n ∈ Finset.range K, ∫ x in ep_cutoffavg_endpointCell B n, g x := by
  have hi (n : ℕ) : Integrable ((ep_cutoffavg_endpointCell B n).indicator g) :=
    (hg.mono_set (ep_cutoffavg_endpointCell_subset B n)).integrable_indicator measurableSet_Ioc
  calc
    _ = ∫ x : ℝ, (Ioc (1:ℝ) B).indicator (fun x => ep_cutoffavg_ea x*g x) x :=
      (integral_indicator measurableSet_Ioc).symm
    _ = ∫ x : ℝ, ∑ n ∈ Finset.range K, (ep_cutoffavg_endpointCell B n).indicator g x := by
      congr 1
      funext x
      exact ep_cutoffavg_endpoint_indicator_partition hK g x
    _ = ∑ n ∈ Finset.range K, ∫ x : ℝ, (ep_cutoffavg_endpointCell B n).indicator g x :=
      integral_finsetSum _ (fun n _ => hi n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_indicator measurableSet_Ioc

private theorem ep_cutoffavg_endpoint_cell_centered_bound {B r : ℝ} (hr : 0<r) (n : ℕ) :
    |∫ x in ep_cutoffavg_endpointCell B n, (ep_cutoffavg_ea (r*x)-1/2)/x^2| ≤ 1/(2*r) := by
  let b : ℝ := 2*(n:ℝ)+1
  let d : ℝ := min (2*(n:ℝ)+2) B
  have hb : 1≤b := by
    dsimp [b]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  by_cases hB : B≤b
  · have hd : d≤b := (min_le_right _ _).trans hB
    have he : ep_cutoffavg_endpointCell B n = ∅ := Ioc_eq_empty_of_le hd
    rw [he]
    simp
    positivity
  · have hbd : b≤d := le_min (by dsimp [b]; linarith) (le_of_lt (lt_of_not_ge hB))
    change |∫ x in Ioc b d, (liClockPairedEtaInfinitePartitionArithmeticIndicator (r*x)-1/2)/x^2| ≤ _
    rw [← intervalIntegral.integral_of_le hbd]
    have he := liClockPairedEtaInfinitePartitionPrimitiveB_interval_error_le hr
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hb) hbd
    calc
      _ ≤ 1/(2*r*b^2) := he
      _ ≤ 1/(2*r) := by
        have hsq : 1 ≤ b^2 := by nlinarith [hb]
        have hden : 2*r ≤ 2*r*b^2 := by nlinarith
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

private theorem ep_cutoffavg_endpoint_averaging_admissions {B r : ℝ} :
    IntegrableOn (fun x : ℝ => ep_cutoffavg_ea x*ep_cutoffavg_ea (r*x)/x^2) (Ioc (1:ℝ) B) ∧
    IntegrableOn (fun x : ℝ => ep_cutoffavg_ea x/x^2) (Ioc (1:ℝ) B) ∧
    IntegrableOn (fun x : ℝ => (ep_cutoffavg_ea (r*x)-1/2)/x^2) (Ioc (1:ℝ) B) := by
  have ha := measurable_liClockPairedEtaInfinitePartitionArithmeticIndicator
  have har : Measurable (fun x : ℝ => ep_cutoffavg_ea (r*x)) := ha.comp (measurable_const.mul measurable_id)
  refine ⟨ep_cutoffavg_endpoint_weight_integrable (ha.mul har) ?_,
    ep_cutoffavg_endpoint_weight_integrable ha ?_, ep_cutoffavg_endpoint_weight_integrable (har.sub measurable_const) ?_⟩
  · intro x
    have hx := liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg x
    have hy := liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg (r*x)
    have hxp := liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one x
    have hyp := liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (r*x)
    rw [abs_of_nonneg (mul_nonneg hx hy)]
    nlinarith
  · intro x
    rw [abs_of_nonneg (liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg x)]
    exact liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one x
  · intro x
    apply abs_le.mpr
    have hx := liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg (r*x)
    have hp := liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (r*x)
    constructor <;> linarith

private theorem ep_cutoffavg_endpoint_averaging_error {B r : ℝ} (hr : 0<r)
    (K : ℕ) (hK : B ≤ 2*(K:ℝ)) :
    |(∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x*ep_cutoffavg_ea (r*x)/x^2) -
      (1/2)*(∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x/x^2)| ≤ (K:ℝ)/(2*r) := by
  obtain ⟨hprod,hplain,hg⟩ := ep_cutoffavg_endpoint_averaging_admissions (B := B) (r := r)
  have he : (∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x*ep_cutoffavg_ea (r*x)/x^2) -
      (1/2)*(∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x/x^2) =
      ∫ x in Ioc (1:ℝ) B, ep_cutoffavg_ea x*((ep_cutoffavg_ea (r*x)-1/2)/x^2) := by
    rw [← integral_const_mul, ← integral_sub hprod (hplain.const_mul (1/2))]
    congr 1
    funext x
    ring
  rw [he, ep_cutoffavg_endpoint_integral_partition hK hg]
  calc
    _ ≤ ∑ n ∈ Finset.range K,
        |∫ x in ep_cutoffavg_endpointCell B n, (ep_cutoffavg_ea (r*x)-1/2)/x^2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range K, 1/(2*r) :=
      Finset.sum_le_sum (fun n _ => ep_cutoffavg_endpoint_cell_centered_bound hr n)
    _ = _ := by simp; ring

private theorem ep_cutoffavg_li_producer_endpoint_fixed_cutoff_averaging
    {B r : ℝ} (hB : 1≤B) (hr : 0<r) (K : ℕ) (hK : B≤2*(K:ℝ)) :
    IntegrableOn (fun x : ℝ =>
      liClockPairedEtaInfinitePartitionArithmeticIndicator x *
        liClockPairedEtaInfinitePartitionArithmeticIndicator (r*x)/x^2) (Ioc (1:ℝ) B) ∧
    IntegrableOn (fun x : ℝ =>
      liClockPairedEtaInfinitePartitionArithmeticIndicator x/x^2) (Ioc (1:ℝ) B) ∧
    |(∫ x in Ioc (1:ℝ) B,
      liClockPairedEtaInfinitePartitionArithmeticIndicator x *
        liClockPairedEtaInfinitePartitionArithmeticIndicator (r*x)/x^2) -
      (1/2)*(∫ x in Ioc (1:ℝ) B,
        liClockPairedEtaInfinitePartitionArithmeticIndicator x/x^2)| ≤ (K:ℝ)/(2*r) := by
  rcases hB.eq_or_lt with hB | hB
  · subst B
    constructor
    · simp
    constructor
    · simp
    · simp
      positivity
  · obtain ⟨hprod,hplain,hg⟩ := ep_cutoffavg_endpoint_averaging_admissions (B := B) (r := r)
    exact ⟨hprod,hplain,ep_cutoffavg_endpoint_averaging_error hr K hK⟩


private theorem ep_profile_as_cutoff {N : ℕ} (hN : 0<N) {y : ℝ}
    (hy : 0≤y) (hyL : y≤Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionEndpointProfile N y =
      ∫w in Ioc 1 (Real.exp y),liClockPairedEtaInfinitePartitionArithmeticIndicator w*
        liClockPairedEtaInfinitePartitionArithmeticIndicator (Real.exp (Real.log (2*(N:ℝ))-y)*w)/w^2 := by
  rw [liClockPairedEtaPartitionEndpointProfile_eq_source hN hy hyL]
  simpa only [ep_indicator,sub_eq_add_neg,add_assoc] using
    (ep_cutoff_pair hy (sub_nonneg.mpr hyL)).2

private theorem ep_limit_as_cutoff {y : ℝ} (hy : 0≤y) :
    liClockPairedEtaPartitionEndpointProfileLimit y =
      (1/2)*(∫w in Ioc 1 (Real.exp y),liClockPairedEtaInfinitePartitionArithmeticIndicator w/w^2) := by
  unfold liClockPairedEtaPartitionEndpointProfileLimit
  rw [←ep_mass_indicator (Icc 0 y) measurableSet_Icc,(ep_cutoff_single hy).2]

private theorem ep_profile_zero (N : ℕ) : liClockPairedEtaPartitionEndpointProfile N 0=0 := by
  unfold liClockPairedEtaPartitionEndpointProfile
  rw [sub_zero,liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs
    (le_abs_self _),mul_zero]

private theorem ep_limit_zero : liClockPairedEtaPartitionEndpointProfileLimit 0=0 := by
  rw [ep_limit_as_cutoff (by norm_num),Real.exp_zero]
  simp

private theorem ep_scale_tendsto (y : ℝ) :
    Tendsto (fun N : ℕ => Real.exp (Real.log (2*(N:ℝ))-y)) atTop atTop := by
  have h : Tendsto (fun N : ℕ => (2*Real.exp (-y))*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos (by norm_num) (Real.exp_pos _))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  rw [Real.exp_sub,Real.exp_log (by exact_mod_cast (show 0<2*N by omega)),Real.exp_neg]
  ring

theorem tendsto_liClockPairedEtaPartitionEndpointProfile
    {y : ℝ} (hy : 0≤y) :
  Tendsto (fun N : ℕ => liClockPairedEtaPartitionEndpointProfile N y)
    atTop (nhds (liClockPairedEtaPartitionEndpointProfileLimit y)) := by
  rcases hy.eq_or_lt with hy | hy
  · subst y
    simpa only [ep_profile_zero,ep_limit_zero] using
      (tendsto_const_nhds : Tendsto (fun N : ℕ => (0:ℝ)) atTop (nhds 0))
  · obtain ⟨K,hK⟩ := exists_nat_gt (Real.exp y)
    have hK' : Real.exp y≤2*(K:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) K]
    have hlog : Tendsto (fun N : ℕ => Real.log (2*(N:ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have hsmall : Tendsto (fun N : ℕ => (K:ℝ)/(2*Real.exp (Real.log (2*(N:ℝ))-y)))
        atTop (nhds 0) := by
      have h:=(ep_scale_tendsto y).inv_tendsto_atTop.const_mul ((K:ℝ)/2)
      simp only [mul_zero] at h
      apply h.congr'
      apply Eventually.of_forall
      intro N
      simp only [Pi.inv_apply,div_eq_mul_inv,mul_inv_rev]
      ring
    have hz : Tendsto (fun N : ℕ => liClockPairedEtaPartitionEndpointProfile N y-
        liClockPairedEtaPartitionEndpointProfileLimit y) atTop (nhds 0) := by
      apply squeeze_zero_norm' ?_ hsmall
      filter_upwards [eventually_gt_atTop (0:ℕ),hlog.eventually (eventually_ge_atTop y)] with N hN hyL
      rw [Real.norm_eq_abs,ep_profile_as_cutoff hN hy.le hyL,ep_limit_as_cutoff hy.le]
      exact (ep_cutoffavg_li_producer_endpoint_fixed_cutoff_averaging
        (Real.one_le_exp_iff.mpr hy.le) (Real.exp_pos _) K hK').2.2
    simpa only [sub_add_cancel,zero_add] using hz.add_const (liClockPairedEtaPartitionEndpointProfileLimit y)

end RHTower
