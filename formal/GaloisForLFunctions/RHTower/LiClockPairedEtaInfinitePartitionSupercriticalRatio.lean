import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBoundary
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionEndpointProfile
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.LiClockCriticalAngularAsymptotic
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionDensityRatio
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem sc_root_gt_half {c : ℝ} (hc : 1/4<c) : 1/2<Real.sqrt c := by
  have hc0 : 0≤c := by linarith
  nlinarith [Real.sq_sqrt hc0,Real.sqrt_nonneg c]

private theorem sc_root_quarter : Real.sqrt (1/4:ℝ)=(1/2:ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : 0≤(1/4:ℝ)),Real.sqrt_nonneg (1/4:ℝ)]

def liClockPairedEtaSupercriticalScale (L t : ℝ) : ℝ :=
  Real.sqrt L*Real.exp (L/2-2*Real.sqrt (t*L))

def liClockPairedEtaSupercriticalReferencePrefactor (c : ℝ) : ℝ :=
  1/(8*Real.sqrt Real.pi*c^(1/4:ℝ)*
    (Real.sqrt c-1/2)*(Real.sqrt c+1/2))

def liClockPairedEtaSupercriticalActualPrefactor (c : ℝ) : ℝ :=
  liClockPairedEtaPartitionSourceEta (Real.sqrt c+1/2)/
    (4*liClockPairedEtaInfinitePartitionNormalizer^2*Real.sqrt Real.pi*c^(1/4:ℝ)*
      (Real.sqrt c-1/2)*(Real.sqrt c+1/2))

def liClockPairedEtaSupercriticalRatioLimit (c : ℝ) : ℝ :=
  2*liClockPairedEtaPartitionSourceEta (Real.sqrt c+1/2)/
    liClockPairedEtaInfinitePartitionNormalizer^2

def liClockPairedEtaSupercriticalRate (c : ℝ) : ℝ :=
  2*(Real.sqrt c-1/2)^2

theorem liClockPairedEtaSupercriticalConstants_pos
    {c : ℝ} (hc : 1/4<c) :
  0<liClockPairedEtaSupercriticalReferencePrefactor c ∧
  0<liClockPairedEtaSupercriticalActualPrefactor c ∧
  0<liClockPairedEtaSupercriticalRatioLimit c ∧
  0<liClockPairedEtaSupercriticalRate c := by
  have hc0 : 0<c := by linarith
  have hs := sc_root_gt_half hc
  have hd : 0<Real.sqrt c-1/2 := by linarith
  have hb : 0<Real.sqrt c+1/2 := by linarith [Real.sqrt_nonneg c]
  have hpi : 0<Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hr : 0<c^(1/4:ℝ) := Real.rpow_pos_of_pos hc0 _
  have hZ := liClockPairedEtaInfinitePartitionNormalizer_pos
  have hE := liClockPairedEtaPartitionSourceEta_pos hb
  unfold liClockPairedEtaSupercriticalReferencePrefactor
    liClockPairedEtaSupercriticalActualPrefactor liClockPairedEtaSupercriticalRatioLimit
    liClockPairedEtaSupercriticalRate
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

theorem tendsto_liClockPairedEtaSupercriticalRatioLimit_quarter_right :
  Tendsto liClockPairedEtaSupercriticalRatioLimit
    (nhdsWithin (1/4:ℝ) (Ioi (1/4)))
    (nhds liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have hmap : Tendsto (fun c : ℝ => Real.sqrt c+1/2)
      (nhdsWithin (1/4:ℝ) (Ioi (1/4))) (nhdsWithin (1:ℝ) (Ioi 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hs : Tendsto Real.sqrt (nhdsWithin (1/4:ℝ) (Ioi (1/4)))
          (nhds (Real.sqrt (1/4:ℝ))) :=
        (Real.continuous_sqrt.tendsto (1/4:ℝ)).mono_left nhdsWithin_le_nhds
      have h := hs.add_const (1/2:ℝ)
      simpa only [sc_root_quarter,show (1/2:ℝ)+1/2=1 by norm_num] using h
    · filter_upwards [eventually_mem_nhdsWithin] with c hc
      change 1<Real.sqrt c+1/2
      have hs := sc_root_gt_half hc
      linarith
  have h := ((tendsto_liClockPairedEtaPartitionSourceEta_one_right.comp hmap).const_mul
    (2:ℝ)).div_const (liClockPairedEtaInfinitePartitionNormalizer^2)
  change Tendsto (fun c : ℝ =>
    2*liClockPairedEtaPartitionSourceEta (Real.sqrt c+1/2)/
      liClockPairedEtaInfinitePartitionNormalizer^2)
    (nhdsWithin (1/4:ℝ) (Ioi (1/4)))
    (nhds (2*Real.log 2/liClockPairedEtaInfinitePartitionNormalizer^2))
  simpa only [Function.comp_def] using h

theorem tendsto_liClockPairedEtaSupercriticalRatioLimit_atTop :
  Tendsto liClockPairedEtaSupercriticalRatioLimit atTop
    (nhds (2/liClockPairedEtaInfinitePartitionNormalizer^2)) := by
  have hmap : Tendsto (fun c : ℝ => Real.sqrt c+1/2) atTop atTop :=
    tendsto_atTop_mono (fun c : ℝ => show Real.sqrt c≤Real.sqrt c+1/2 by linarith)
      Real.tendsto_sqrt_atTop
  have h := ((tendsto_liClockPairedEtaPartitionSourceEta_atTop.comp hmap).const_mul
    (2:ℝ)).div_const (liClockPairedEtaInfinitePartitionNormalizer^2)
  change Tendsto (fun c : ℝ =>
    2*liClockPairedEtaPartitionSourceEta (Real.sqrt c+1/2)/
      liClockPairedEtaInfinitePartitionNormalizer^2) atTop
    (nhds (2/liClockPairedEtaInfinitePartitionNormalizer^2))
  simpa only [Function.comp_def,mul_one] using h

theorem liClockPairedEtaSupercriticalRatio_order_boundary :
  Tendsto liClockPairedEtaSupercriticalRatioLimit atTop
    (nhds (2/liClockPairedEtaInfinitePartitionNormalizer^2)) ∧
  (∀ N : ℕ, 0<N → Tendsto (fun t : ℝ => liClockPairedEtaPartitionBorelKernel N t/
    liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
      (nhds (liClockPairedEtaPartitionComparisonScale N))) ∧
  Tendsto liClockPairedEtaPartitionComparisonScale atTop
    (nhds (4/liClockPairedEtaInfinitePartitionNormalizer^2)) ∧
  2/liClockPairedEtaInfinitePartitionNormalizer^2 =
    (1/2)*(4/liClockPairedEtaInfinitePartitionNormalizer^2) ∧
  2/liClockPairedEtaInfinitePartitionNormalizer^2 ≠
    4/liClockPairedEtaInfinitePartitionNormalizer^2 := by
  have hbank := liClockPairedEtaInfinitePartition_Borel_ratio_order_boundary
  refine ⟨tendsto_liClockPairedEtaSupercriticalRatioLimit_atTop,hbank.1,hbank.2.1,?_,?_⟩
  · ring
  · exact (div_lt_div_of_pos_right (by norm_num : (2:ℝ)<4)
      (sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos)).ne

private theorem sr_compact_even_integral {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (he : ∀ x : ℝ, f (-x) = f x)
    (hz : ∀ x : ℝ, L ≤ |x| → f x = 0) :
    (∫ x : ℝ, f x) = 2 * ∫ x in Icc 0 L, f x := by
  have hcut : (∫ x in Icc (-L) L, f x) = ∫ x : ℝ, f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply hz x
    by_contra h
    have ha : |x| < L := lt_of_not_ge h
    exact hx ⟨(abs_lt.mp ha).1.le, (abs_lt.mp ha).2.le⟩
  have hneg : (∫ x in (-L)..0, f x) = ∫ x in (0 : ℝ)..L, f x := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := L)
    simpa only [he, neg_zero] using h.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (μ := (volume : Measure ℝ))
    (hf.intervalIntegrable (-L) 0) (hf.intervalIntegrable 0 L)
  rw [← hcut, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -L ≤ L by linarith), ← hadd, hneg,
    intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  ring


/- Prepared source bridge; requires certified AngularKernel and existing finite sources.
   No unfinished dependency import or compiler claim is attached to this fragment. -/

private theorem sr_summable_even (w : ℝ) :
    Summable (fun j : ℕ => w^(2*j) / (((2*j).factorial : ℝ)^2)) := by
  have hr : Summable (fun n : ℕ => w^n / ((n.factorial : ℝ)^2)) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
      (summable_norm_liClockCriticalScalarTermComplex (w : ℂ)).of_norm
  exact hr.comp_injective (fun x y h => by omega)

private theorem sr_even_kernel_neg (w : ℝ) :
    liClockCriticalEvenKernel (-w) = liClockCriticalEvenKernel w := by
  unfold liClockCriticalEvenKernel
  apply tsum_congr
  intro j
  simp only [pow_mul, neg_sq]

private theorem sr_compact_mul_integrable {g : ℝ → ℝ} {L : ℝ}
    (hg : Continuous g) (hz : ∀ x : ℝ, L ≤ |x| → g x = 0)
    (φ : ℝ → ℝ) (hφ : Continuous φ) : Integrable (fun x => g x * φ x) := by
  have hs : Function.support (fun x => g x * φ x) ⊆ Icc (-L) L := by
    intro x hx
    have hxg : g x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hxL : |x| < L := lt_of_not_ge (fun h => hxg (hz x h))
    exact ⟨(abs_lt.mp hxL).1.le, (abs_lt.mp hxL).2.le⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    ((hg.mul hφ).continuousOn.integrableOn_Icc)

private theorem sr_borel_raw_integral
    {g : ℝ → ℝ} {M : ℕ → ℝ} {L Z B t : ℝ}
    (hL : 0 ≤ L) (hZ : Z ≠ 0) (ht : 0 ≤ t)
    (hg : Continuous g) (hp : ∀ x : ℝ, 0 ≤ g x)
    (he : ∀ x : ℝ, g (-x) = g x) (hz : ∀ x : ℝ, L ≤ |x| → g x = 0)
    (hm : ∀ j : ℕ, (∫ x : ℝ, x^(2*j)*g x) = Z^2*M j)
    (hb : HasSum (fun j : ℕ => M j*t^(2*j)/((2*j).factorial : ℝ)^2) B) :
    B = (2/Z^2) * ∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x) := by
  let f : ℕ → ℝ → ℝ := fun j x =>
    g x * (t*x)^(2*j) / ((2*j).factorial : ℝ)^2
  have hfpos : ∀ j x, 0 ≤ f j x := by
    intro j x
    dsimp [f]
    rw [mul_pow]
    apply div_nonneg
    · exact mul_nonneg (hp x) (mul_nonneg (pow_nonneg ht _) (by
        rw [pow_mul]
        positivity))
    · positivity
  have hfsum : ∀ x, HasSum (fun j => f j x)
      (g x * liClockCriticalEvenKernel (t*x)) := by
    intro x
    apply ((sr_summable_even (t*x)).hasSum.mul_left (g x)).congr_fun
    intro j
    dsimp [f]
    ring
  have hfc : Continuous (fun x => g x * liClockCriticalEvenKernel (t*x)) :=
    hg.mul (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hfi : Integrable (fun x => g x * liClockCriticalEvenKernel (t*x)) :=
    sr_compact_mul_integrable hg hz _
      (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hfb : Integrable (fun x => ∑' j, f j x) :=
    hfi.congr (Filter.Eventually.of_forall (fun x => (hfsum x).tsum_eq.symm))
  have hsum : HasSum (fun j => ∫ x : ℝ, f j x)
      (∫ x : ℝ, g x * liClockCriticalEvenKernel (t*x)) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence f
    · intro j
      have hc : Continuous (f j) := by
        dsimp [f]
        exact (hg.mul ((continuous_const.mul continuous_id).pow _)).div_const _
      exact hc.aestronglyMeasurable
    · intro j
      exact Filter.Eventually.of_forall (fun x => le_of_eq (Real.norm_of_nonneg (hfpos j x)))
    · exact Filter.Eventually.of_forall (fun x => (hfsum x).summable)
    · exact hfb
    · exact Filter.Eventually.of_forall hfsum
  have hterm (j : ℕ) : (∫ x : ℝ, f j x) =
      Z^2 * (M j*t^(2*j)/((2*j).factorial : ℝ)^2) := by
    have heq : f j = fun x : ℝ =>
        (t^(2*j)/((2*j).factorial : ℝ)^2) * (x^(2*j)*g x) := by
      funext x
      dsimp [f]
      rw [mul_pow]
      ring
    rw [heq, integral_const_mul, hm j]
    ring
  have hsumB : HasSum (fun j => ∫ x : ℝ, f j x) (Z^2*B) := by
    apply (hb.mul_left (Z^2)).congr_fun
    exact hterm
  have hfold : (∫ x : ℝ, g x * liClockCriticalEvenKernel (t*x)) =
      2 * ∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x) := by
    apply sr_compact_even_integral hL hfc
    · intro x
      rw [he x, show t*(-x) = -(t*x) by ring, sr_even_kernel_neg]
    · intro x hx
      rw [hz x hx, zero_mul]
  have hZ2 : Z^2 ≠ 0 := pow_ne_zero _ hZ
  calc
    B = (Z^2*B)/Z^2 := by field_simp
    _ = (2*(∫ x in Icc 0 L, g x * liClockCriticalEvenKernel (t*x)))/Z^2 := by
      rw [← hsum.unique hsumB, hfold]
    _ = _ := by ring

private theorem sr_actual_raw_eq
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
  liClockPairedEtaPartitionBorelKernel N t =
    (2/liClockPairedEtaPartitionNormalizer N^2) *
      ∫ r in Set.Icc 0 (Real.log (2*(N : ℝ))),
        liClockPairedEtaPartitionRawDifferenceDensity N r *
          liClockCriticalEvenKernel (t*r) := by
  have hL : 0 ≤ Real.log (2*(N : ℝ)) := by
    apply Real.log_nonneg
    have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
    linarith
  apply sr_borel_raw_integral hL (liClockPairedEtaPartitionNormalizer_pos hN).ne' ht
    (continuous_liClockPairedEtaPartitionRawDifferenceDensity N)
    (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N)
    (liClockPairedEtaPartitionRawDifferenceDensity_even N)
    (fun _ hx => liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs hx)
    (liClockPairedEtaPartitionRawDifferenceDensity_moment hN)
  simpa only [liClockPairedEtaPartitionBorelKernel_eq_tsum] using
    (summable_liClockPairedEtaPartitionBorelTerm hN t).hasSum

private theorem sr_reference_raw_eq
    {L t : ℝ} (hL : 0<L) (ht : 0≤t) :
  liClockPairedEtaContiguousBorelKernel L t =
    (2/liClockPairedEtaContiguousPartitionNormalizer L^2) *
      ∫ r in Set.Icc 0 L,
        liClockPairedEtaContiguousRawDifferenceDensity L r *
          liClockCriticalEvenKernel (t*r) := by
  apply sr_borel_raw_integral hL.le (liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne' ht
    (continuous_liClockPairedEtaContiguousRawDifferenceDensity L)
    (liClockPairedEtaContiguousRawDifferenceDensity_nonneg L)
    (liClockPairedEtaContiguousRawDifferenceDensity_even L)
    (fun _ hx => liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs hx)
    (liClockPairedEtaContiguousRawDifferenceDensity_moment hL)
  have hs := (summable_liClockPairedEtaContiguousBorelTerm hL t).hasSum
  change HasSum _ (liClockPairedEtaContiguousBorelKernel L t) at hs
  apply hs.congr_fun
  intro j
  unfold liClockPairedEtaContiguousBorelCoefficient
  ring



private theorem sr_actual_raw_integral
    {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
  IntegrableOn (fun r : ℝ => liClockPairedEtaPartitionRawDifferenceDensity N r*
    liClockCriticalEvenKernel (t*r)) (Icc 0 (Real.log (2*(N:ℝ)))) ∧
  liClockPairedEtaPartitionBorelKernel N t =
    (2/liClockPairedEtaPartitionNormalizer N^2)*
      (∫ r in Icc 0 (Real.log (2*(N:ℝ))),
        liClockPairedEtaPartitionRawDifferenceDensity N r*liClockCriticalEvenKernel (t*r)) := by
  refine ⟨?_,sr_actual_raw_eq hN ht⟩
  exact ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).mul
    (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))).integrableOn_Icc

private theorem sr_reference_raw_integral
    {L : ℝ} (hL : 0<L) {t : ℝ} (ht : 0≤t) :
  IntegrableOn (fun r : ℝ => liClockPairedEtaContiguousRawDifferenceDensity L r*
    liClockCriticalEvenKernel (t*r)) (Icc 0 L) ∧
  liClockPairedEtaContiguousBorelKernel L t =
    (2/liClockPairedEtaContiguousPartitionNormalizer L^2)*
      (∫ r in Icc 0 L,
        liClockPairedEtaContiguousRawDifferenceDensity L r*liClockCriticalEvenKernel (t*r)) := by
  refine ⟨?_,sr_reference_raw_eq hL ht⟩
  exact ((continuous_liClockPairedEtaContiguousRawDifferenceDensity L).mul
    (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))).integrableOn_Icc

private theorem sr_split_reflected {f : ℝ→ℝ} {L : ℝ} (hL : 0≤L) (hf : Continuous f) :
    (∫ r in Icc 0 L, f r) =
      (∫ r in Icc 0 (L/2), f r)+(∫ y in Icc 0 (L/2), f (L-y)) := by
  have he := intervalIntegral.integral_comp_sub_left (f:=f) (a:=(0:ℝ)) (b:=L/2) L
  have hm : L-L/2=L/2 := by ring
  rw [hm,sub_zero] at he
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (μ:=(volume:Measure ℝ)) (hf.intervalIntegrable 0 (L/2)) (hf.intervalIntegrable (L/2) L)
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hL,
    ←ha,←he,intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤L/2),
    intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤L/2),
    ←integral_Icc_eq_integral_Ioc,←integral_Icc_eq_integral_Ioc]

private theorem sr_reference_laplace {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun y : ℝ => Real.exp (-a*y)*(1-Real.exp (-y))) (Ioi 0) ∧
    (∫y in Ioi (0:ℝ),Real.exp (-a*y)*(1-Real.exp (-y)))=1/(a*(a+1)) := by
  have hb : 0<a+1 := by linarith
  have hi := integrableOn_exp_mul_Ioi (a:= -a) (by linarith) (0:ℝ)
  have hj := integrableOn_exp_mul_Ioi (a:= -(a+1)) (by linarith) (0:ℝ)
  have he (y:ℝ) : Real.exp (-a*y)*(1-Real.exp (-y))=
      Real.exp (-a*y)-Real.exp (-(a+1)*y) := by
    rw [mul_sub,mul_one,←Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  refine ⟨hi.sub hj,?_⟩
  rw [integral_sub hi hj,integral_exp_mul_Ioi (by linarith : -a<0),
    integral_exp_mul_Ioi (by linarith : -(a+1)<0)]
  simp only [mul_zero,Real.exp_zero]
  field_simp
  ring

private def sr_weight (L t : ℝ) : ℝ :=
  Real.sqrt L*Real.exp (L/2-2*Real.sqrt (t*L))

private def sr_scalar (L t y : ℝ) : ℝ :=
  Real.sqrt L*Real.exp (y/2-2*Real.sqrt (t*L))*liClockCriticalEvenKernel (t*(L-y))

private theorem sr_profile_continuous (N : ℕ) :
    Continuous (liClockPairedEtaPartitionEndpointProfile N) := by
  have hf : Continuous (fun y : ℝ => Real.log (2*(N:ℝ))-y) := by fun_prop
  have hg : Continuous (fun y : ℝ => (Real.log (2*(N:ℝ))-y)/2) := by fun_prop
  exact (Real.continuous_exp.comp hg).mul
    ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).comp hf)

private theorem sr_scalar_continuous (L t : ℝ) : Continuous (sr_scalar L t) := by
  have h1 : Continuous (fun y : ℝ => y/2-2*Real.sqrt (t*L)) := by fun_prop
  have h2 : Continuous (fun y : ℝ => t*(L-y)) := by fun_prop
  exact (continuous_const.mul (Real.continuous_exp.comp h1)).mul
    (continuous_liClockCriticalEvenKernel.comp h2)

private theorem sr_scalar_nonneg {L t y : ℝ} : 0 ≤ sr_scalar L t y :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    (liClockCriticalEvenKernel_nonneg _)

private theorem sr_scaled_integral_split {f : ℝ→ℝ} {L D : ℝ}
    (hL : 0≤L) (hf : Continuous f) :
    D*(∫r in Icc 0 L,f r) =
      D*(∫r in Icc 0 (L/2),f r)+(∫y in Icc 0 (L/2),D*f (L-y)) := by
  rw [sr_split_reflected hL hf,mul_add,integral_const_mul]

private theorem sr_actual_scalar_identity (N : ℕ) (t y : ℝ) :
    sr_weight (Real.log (2*(N:ℝ))) t*
      (liClockPairedEtaPartitionRawDifferenceDensity N (Real.log (2*(N:ℝ))-y)*
        liClockCriticalEvenKernel (t*(Real.log (2*(N:ℝ))-y))) =
      sr_scalar (Real.log (2*(N:ℝ))) t y*liClockPairedEtaPartitionEndpointProfile N y := by
  unfold sr_weight sr_scalar liClockPairedEtaPartitionEndpointProfile
  have he : Real.exp (y/2-2*Real.sqrt (t*Real.log (2*(N:ℝ))))*
      Real.exp ((Real.log (2*(N:ℝ))-y)/2)=
        Real.exp (Real.log (2*(N:ℝ))/2-2*Real.sqrt (t*Real.log (2*(N:ℝ)))) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _=Real.sqrt (Real.log (2*(N:ℝ)))*
      (Real.exp (y/2-2*Real.sqrt (t*Real.log (2*(N:ℝ))))*
        Real.exp ((Real.log (2*(N:ℝ))-y)/2))*
      liClockPairedEtaPartitionRawDifferenceDensity N (Real.log (2*(N:ℝ))-y)*
        liClockCriticalEvenKernel (t*(Real.log (2*(N:ℝ))-y)) := by rw [he];ring
    _=_ := by ring

private theorem sr_reference_scalar_identity {N : ℕ} (hN : 0<N) {t y : ℝ}
    (hy : 0≤y) (hyL : y≤Real.log (2*(N:ℝ))) :
    sr_weight (Real.log (2*(N:ℝ))) t*
      (liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ)))
        (Real.log (2*(N:ℝ))-y)*liClockCriticalEvenKernel (t*(Real.log (2*(N:ℝ))-y))) =
      sr_scalar (Real.log (2*(N:ℝ))) t y*(1-Real.exp (-y)) := by
  rw [←liClockPairedEtaContiguousEndpointProfile_eq hN hy hyL]
  unfold sr_weight sr_scalar
  have he : Real.exp (y/2-2*Real.sqrt (t*Real.log (2*(N:ℝ))))*
      Real.exp ((Real.log (2*(N:ℝ))-y)/2)=
        Real.exp (Real.log (2*(N:ℝ))/2-2*Real.sqrt (t*Real.log (2*(N:ℝ)))) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _=Real.sqrt (Real.log (2*(N:ℝ)))*
      (Real.exp (y/2-2*Real.sqrt (t*Real.log (2*(N:ℝ))))*
        Real.exp ((Real.log (2*(N:ℝ))-y)/2))*
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ)))
        (Real.log (2*(N:ℝ))-y)*liClockCriticalEvenKernel (t*(Real.log (2*(N:ℝ))-y)) := by rw [he];ring
    _=_ := by ring

private theorem sr_actual_scaled_split {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
    sr_weight (Real.log (2*(N:ℝ))) t*liClockPairedEtaPartitionBorelKernel N t =
      (2/liClockPairedEtaPartitionNormalizer N^2)*
        (sr_weight (Real.log (2*(N:ℝ))) t*
          (∫r in Icc 0 (Real.log (2*(N:ℝ))/2),
            liClockPairedEtaPartitionRawDifferenceDensity N r*liClockCriticalEvenKernel (t*r))+
          ∫y in Icc 0 (Real.log (2*(N:ℝ))/2),
            sr_scalar (Real.log (2*(N:ℝ))) t y*liClockPairedEtaPartitionEndpointProfile N y) := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    have h : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  have hf : Continuous (fun r : ℝ => liClockPairedEtaPartitionRawDifferenceDensity N r*
      liClockCriticalEvenKernel (t*r)) :=
    (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).mul
    (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hs := sr_scaled_integral_split (D:=sr_weight (Real.log (2*(N:ℝ))) t) hL.le hf
  simp only [sr_actual_scalar_identity] at hs
  rw [(sr_actual_raw_integral hN ht).2]
  calc
    _=(2/liClockPairedEtaPartitionNormalizer N^2)*
      (sr_weight (Real.log (2*(N:ℝ))) t*(∫r in Icc 0 (Real.log (2*(N:ℝ))),
        liClockPairedEtaPartitionRawDifferenceDensity N r*liClockCriticalEvenKernel (t*r))) := by ring
    _=_ := by rw [hs]

private theorem sr_reference_scaled_split {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
    sr_weight (Real.log (2*(N:ℝ))) t*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t =
      (2/liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2)*
        (sr_weight (Real.log (2*(N:ℝ))) t*
          (∫r in Icc 0 (Real.log (2*(N:ℝ))/2),
            liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r*
              liClockCriticalEvenKernel (t*r))+
          ∫y in Icc 0 (Real.log (2*(N:ℝ))/2),
            sr_scalar (Real.log (2*(N:ℝ))) t y*(1-Real.exp (-y))) := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    have h : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  have hf : Continuous (fun r : ℝ =>
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r*
        liClockCriticalEvenKernel (t*r)) :=
    (continuous_liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ)))).mul
    (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))
  have hs := sr_scaled_integral_split (D:=sr_weight (Real.log (2*(N:ℝ))) t) hL.le hf
  have he : (∫y in Icc 0 (Real.log (2*(N:ℝ))/2),
      sr_weight (Real.log (2*(N:ℝ))) t*
        (liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ)))
          (Real.log (2*(N:ℝ))-y)*liClockCriticalEvenKernel (t*(Real.log (2*(N:ℝ))-y))))=
      ∫y in Icc 0 (Real.log (2*(N:ℝ))/2),
        sr_scalar (Real.log (2*(N:ℝ))) t y*(1-Real.exp (-y)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact sr_reference_scalar_identity hN hy.1 (by linarith [hy.2])
  rw [he] at hs
  rw [(sr_reference_raw_integral hL ht).2]
  calc
    _=(2/liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2)*
      (sr_weight (Real.log (2*(N:ℝ))) t*(∫r in Icc 0 (Real.log (2*(N:ℝ))),
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r*
          liClockCriticalEvenKernel (t*r))) := by ring
    _=_ := by rw [hs]

private theorem sr_nearzero_source_bounds {N : ℕ} (hN : 0<N) {r : ℝ}
    (hr : r∈Icc 0 (Real.log (2*(N:ℝ))/2)) :
    (0≤liClockPairedEtaPartitionRawDifferenceDensity N r ∧
      liClockPairedEtaPartitionRawDifferenceDensity N r≤Real.exp (-r/2)) ∧
    (0≤liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r ∧
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r≤Real.exp (-r/2)) := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    have h : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  have hu : liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) r≤Real.exp (-r/2) := by
    rw [liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg hr.1 (by linarith [hr.2])]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (by linarith [Real.exp_pos (r-Real.log (2*(N:ℝ)))])
  exact ⟨⟨liClockPairedEtaPartitionRawDifferenceDensity_nonneg N r,
    (liClockPairedEtaPartitionRawDifferenceDensity_le_contiguous N r).trans hu⟩,
    liClockPairedEtaContiguousRawDifferenceDensity_nonneg _ _,hu⟩

private theorem sr_endpoint_dct {L : ℕ→ℝ} {f : ℕ→ℝ→ℝ} {g bound : ℝ→ℝ}
    (hL : Tendsto L atTop atTop)
    (hf : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)))
    (hb0 : ∀ y : ℝ, 0<y → 0≤bound y)
    (hb : ∀ᶠ n in atTop, ∀ y : ℝ, 0<y → y≤L n/2 → ‖f n y‖≤bound y)
    (hbi : IntegrableOn bound (Ioi 0))
    (hlim : ∀ y : ℝ, 0<y → Tendsto (fun n => f n y) atTop (nhds (g y))) :
    (∀ᶠ n in atTop, IntegrableOn (f n) (Icc 0 (L n/2))) ∧
    Tendsto (fun n => ∫y in Icc 0 (L n/2),f n y)
      atTop (nhds (∫y in Ioi (0:ℝ),g y)) := by
  let F : ℕ→ℝ→ℝ := fun n => (Iic (L n/2)).indicator (f n)
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) (volume.restrict (Ioi 0)) := by
    filter_upwards [hf] with n hn
    exact hn.indicator measurableSet_Iic
  have hbound : ∀ᶠ n in atTop, ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ‖F n y‖≤bound y := by
    filter_upwards [hb] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    by_cases hs : y≤L n/2
    · dsimp only [F]
      rw [indicator_of_mem (show y∈Iic (L n/2) from hs)]
      exact hn y hy hs
    · dsimp only [F]
      rw [indicator_of_notMem (show y∉Iic (L n/2) from hs),norm_zero]
      exact hb0 y hy
  have hint : ∀ᶠ n in atTop, Integrable (F n) (volume.restrict (Ioi 0)) := by
    filter_upwards [hmeas,hbound] with n hm hb
    exact hbi.mono' hm hb
  have hadmit : ∀ᶠ n in atTop, IntegrableOn (f n) (Icc 0 (L n/2)) := by
    filter_upwards [hint] with n hn
    have hi : IntegrableOn (f n) (Iic (L n/2) ∩ Ioi 0) :=
      (integrableOn_indicator_iff measurableSet_Iic).mp hn
    have he : Iic (L n/2) ∩ Ioi (0:ℝ) = Ioc 0 (L n/2) := by
      ext y
      simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc,and_comm]
    rw [he] at hi
    exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hi
  have hpoint : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun n => F n y) atTop (nhds (g y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply (hlim y hy).congr'
    filter_upwards [hL.eventually (eventually_ge_atTop (2*y))] with n hn
    exact (indicator_of_mem (show y∈Iic (L n/2) by change y≤L n/2; linarith) (f n)).symm
  have h := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound hbi hpoint
  refine ⟨hadmit,h.congr ?_⟩
  intro n
  change (∫y in Ioi (0:ℝ),(Iic (L n/2)).indicator (f n) y)=_
  rw [setIntegral_indicator measurableSet_Iic]
  have he : Ioi (0:ℝ) ∩ Iic (L n/2) = Ioc 0 (L n/2) := by
    ext y
    simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]
  rw [he,integral_Icc_eq_integral_Ioc]

private theorem sr_nearzero_bound {g : ℝ→ℝ} {L t a : ℝ}
    (hL : 0<L) (ht : 0≤t) (hg : Continuous g)
    (hb : ∀r∈Icc 0 (L/2), 0≤g r ∧ g r≤Real.exp (-r/2))
    (he : ∀r∈Icc 0 (L/2),
      L/2-r/2+2*Real.sqrt (t*r)-2*Real.sqrt (t*L)≤-a*L/2) :
    IntegrableOn (fun r => g r*liClockCriticalEvenKernel (t*r)) (Icc 0 (L/2)) ∧
    |Real.sqrt L*Real.exp (L/2-2*Real.sqrt (t*L))*
      (∫r in Icc 0 (L/2),g r*liClockCriticalEvenKernel (t*r))|≤
      Real.sqrt L*(L/2)*Real.exp (-a*L/2) := by
  have hi : IntegrableOn (fun r => g r*liClockCriticalEvenKernel (t*r)) (Icc 0 (L/2)) :=
    (hg.mul (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id))).integrableOn_Icc
  let D : ℝ := Real.sqrt L*Real.exp (L/2-2*Real.sqrt (t*L))
  have hD : 0≤D := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hbound : ∀r∈Icc 0 (L/2),
      ‖D*(g r*liClockCriticalEvenKernel (t*r))‖≤Real.sqrt L*Real.exp (-a*L/2) := by
    intro r hr
    have hg0 := (hb r hr).1
    have hF0 := liClockCriticalEvenKernel_nonneg (t*r)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD (mul_nonneg hg0 hF0))]
    have hprod : g r*liClockCriticalEvenKernel (t*r)≤
        Real.exp (-r/2)*Real.exp (2*Real.sqrt (t*r)) :=
      mul_le_mul (hb r hr).2 (liClockCriticalEvenKernel_le_exp (mul_nonneg ht hr.1))
        hF0 (Real.exp_pos _).le
    calc
      _≤D*(Real.exp (-r/2)*Real.exp (2*Real.sqrt (t*r))) :=
        mul_le_mul_of_nonneg_left hprod hD
      _=Real.sqrt L*Real.exp (L/2-r/2+2*Real.sqrt (t*r)-2*Real.sqrt (t*L)) := by
        dsimp [D]
        rw [mul_assoc,←Real.exp_add,←Real.exp_add]
        congr 2
        ring
      _≤Real.sqrt L*Real.exp (-a*L/2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (he r hr)) (Real.sqrt_nonneg _)
  have hv : (volume : Measure ℝ) (Icc 0 (L/2))<⊤ := by simp
  have h := norm_setIntegral_le_of_norm_le_const_ae hv
    (show ∀ᵐ r ∂volume.restrict (Icc 0 (L/2)),
      ‖D*(g r*liClockCriticalEvenKernel (t*r))‖≤Real.sqrt L*Real.exp (-a*L/2) by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hbound r hr)
  rw [integral_const_mul,Real.norm_eq_abs,
    Real.volume_real_Icc_of_le (by linarith : (0:ℝ)≤L/2),sub_zero] at h
  refine ⟨hi,?_⟩
  calc
    _≤(Real.sqrt L*Real.exp (-a*L/2))*(L/2) := h
    _=_ := by ring

private theorem sr_nearzero_envelope_tendsto {L : ℕ→ℝ} (hL : Tendsto L atTop atTop)
    {a : ℝ} (ha : 0<a) :
    Tendsto (fun n => Real.sqrt (L n)*(L n/2)*Real.exp (-a*L n/2))
      atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3/2:ℝ) (a/2) (by linarith)).comp hL
  have hh := h.div_const 2
  simp only [zero_div,Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with n hn
  rw [Real.sqrt_eq_rpow,show (3/2:ℝ)=1/2+1 by norm_num,Real.rpow_add hn,
    Real.rpow_one]
  have he : -(a/2)*L n = -a*L n/2 := by ring
  rw [he]
  ring

private def sr_lower_ratio (c : ℝ) : ℝ := (c+1/4)/2

private theorem sr_lower_ratio_bounds {c : ℝ} (hc : 1/4<c) :
    1/4<sr_lower_ratio c ∧ sr_lower_ratio c<c ∧
      0<Real.sqrt (sr_lower_ratio c)-1/2 := by
  have h0 : 0<sr_lower_ratio c := by unfold sr_lower_ratio;linarith
  have hs := Real.sq_sqrt h0.le
  have hn := Real.sqrt_nonneg (sr_lower_ratio c)
  constructor
  · unfold sr_lower_ratio
    linarith
  constructor
  · unfold sr_lower_ratio
    linarith
  · have hq : (1/4:ℝ)<sr_lower_ratio c := by unfold sr_lower_ratio;linarith
    nlinarith

private theorem sr_regime {L t : ℕ→ℝ} {c : ℝ}
    (hL : Tendsto L atTop atTop) (hc : 1/4<c)
    (ht : Tendsto (fun k => t k/L k) atTop (nhds c)) :
    ∀ᶠ k in atTop, 0<L k ∧ 0<t k ∧ sr_lower_ratio c≤t k/L k := by
  have hb := sr_lower_ratio_bounds hc
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),
    ht.eventually (eventually_gt_nhds hb.2.1)] with k hLk hr
  have hr0 : 0<t k/L k := by linarith [hb.1]
  have htk : 0<t k := by
    have h:=(lt_div_iff₀ hLk).mp hr0
    simpa only [zero_mul] using h
  exact ⟨hLk,htk,hr.le⟩

private theorem sr_div_integrand (f g : ℝ→ℝ) (D : ℝ) :
    (fun y => (f y/D)*g y)=(fun y => (1/D)*(f y*g y)) := by
  funext y
  ring

private theorem sr_scaled_profile_integrals {c : ℝ} (hc : 1/4<c) :
    (IntegrableOn (fun y : ℝ =>
      (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
        liClockPairedEtaPartitionEndpointProfileLimit y) (Ioi 0) ∧
    (∫y in Ioi (0:ℝ),
      (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
        liClockPairedEtaPartitionEndpointProfileLimit y) =
      liClockPairedEtaPartitionSourceEta (Real.sqrt c+1/2)/
        ((4*Real.sqrt Real.pi*c^(1/4:ℝ))*(2*(Real.sqrt c-1/2)*(Real.sqrt c+1/2)))) ∧
    (IntegrableOn (fun y : ℝ =>
      (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
        (1-Real.exp (-y))) (Ioi 0) ∧
    (∫y in Ioi (0:ℝ),
      (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
        (1-Real.exp (-y))) =
      1/((4*Real.sqrt Real.pi*c^(1/4:ℝ))*((Real.sqrt c-1/2)*(Real.sqrt c+1/2)))) := by
  have hc0 : 0<c := by linarith
  have hs := Real.sq_sqrt hc0.le
  have hn := Real.sqrt_nonneg c
  have ha : 0<Real.sqrt c-1/2 := by nlinarith
  have hab : Real.sqrt c-1/2+1=Real.sqrt c+1/2 := by ring
  have hp := liClockPairedEtaPartitionEndpointProfileLimit_laplace ha
  have hu := sr_reference_laplace ha
  constructor
  · rw [sr_div_integrand]
    refine ⟨hp.1.const_mul _,?_⟩
    rw [integral_const_mul,hp.2,hab]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [sr_div_integrand]
    refine ⟨hu.1.const_mul _,?_⟩
    rw [integral_const_mul,hu.2,hab]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

private theorem ss_sqrt_concavity {L y : ℝ}
    (hL : 0<L) (_hy : 0≤y) (hyL : y≤L) :
    Real.sqrt (L-y) ≤ Real.sqrt L-y/(2*Real.sqrt L) := by
  have hb : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have ha2 := Real.sq_sqrt (sub_nonneg.mpr hyL)
  have hb2 := Real.sq_sqrt hL.le
  have h : y/(2*Real.sqrt L) ≤ Real.sqrt L-Real.sqrt (L-y) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hb)).mpr
    nlinarith [sq_nonneg (Real.sqrt (L-y)-Real.sqrt L)]
  linarith

private theorem ss_endpoint_exponent_le {L t y : ℝ}
    (hL : 0<L) (ht : 0≤t) (hy : 0≤y) (hyL : y≤L) :
    y/2+2*Real.sqrt (t*(L-y))-2*Real.sqrt (t*L) ≤
      -(Real.sqrt (t/L)-1/2)*y := by
  have hb : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have h := mul_le_mul_of_nonneg_left (ss_sqrt_concavity hL hy hyL)
    (show 0≤2*Real.sqrt t by positivity)
  rw [Real.sqrt_mul ht, Real.sqrt_mul ht, Real.sqrt_div ht]
  have he : -(Real.sqrt t/Real.sqrt L-1/2)*y =
      y/2-2*Real.sqrt t*(y/(2*Real.sqrt L)) := by field_simp; ring
  rw [he]
  nlinarith

private theorem ss_rate_pos {c : ℝ} (hc : 1/4<c) :
    0<Real.sqrt c-1/2 := by
  have hc0 : 0<c := by linarith
  have h := Real.sq_sqrt hc0.le
  have hs := Real.sqrt_nonneg c
  nlinarith

private theorem ss_endpoint_exponent_le_lower {L t c0 y : ℝ}
    (hL : 0<L) (ht : 0≤t) (hr : c0≤t/L) (hy : 0≤y) (hyL : y≤L) :
    y/2+2*Real.sqrt (t*(L-y))-2*Real.sqrt (t*L) ≤
      -(Real.sqrt c0-1/2)*y := by
  refine (ss_endpoint_exponent_le hL ht hy hyL).trans ?_
  have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) hy
  linarith

private theorem ss_endpoint_majorant {L t c0 y : ℝ}
    (hL : 0<L) (ht : 0<t) (hc0 : 1/4<c0) (hr : c0≤t/L)
    (hy : 0≤y) (hyL : y≤L/2) :
    Real.sqrt L*Real.exp (y/2-2*Real.sqrt (t*L))*
      liClockCriticalEvenKernel (t*(L-y)) ≤
    (Real.sqrt Real.pi/(2*Real.sqrt 2*Real.sqrt (Real.sqrt c0)))*
      Real.exp (-(Real.sqrt c0-1/2)*y) := by
  have hc : 0<c0 := by linarith
  have hyL' : y<L := by linarith
  have hw : 0<t*(L-y) := mul_pos ht (sub_pos.mpr hyL')
  let q : ℝ := 2*Real.sqrt (t*(L-y))
  have hq : 0<q := mul_pos (by norm_num) (Real.sqrt_pos.mpr hw)
  have he : q^2/4=t*(L-y) := by
    dsimp [q]; nlinarith [Real.sq_sqrt hw.le]
  have htr : c0*L≤t := (le_div_iff₀ hL).mp hr
  have hsq : (Real.sqrt c0*L)^2 ≤ q^2 := by
    have h1 := mul_le_mul_of_nonneg_right htr (sub_nonneg.mpr hyL'.le)
    have h2 := mul_le_mul_of_nonneg_left (show L/2≤L-y by linarith) (mul_pos hc hL).le
    have h3 := Real.sq_sqrt hc.le
    have h4 : q^2=4*(t*(L-y)) := by linarith [he]
    nlinarith [sq_nonneg L]
  have hlq : Real.sqrt c0*L≤q := by
    have h0 : 0≤Real.sqrt c0*L := by positivity
    nlinarith
  have hd : Real.sqrt (Real.sqrt c0)*Real.sqrt L ≤ Real.sqrt q := by
    simpa only [Real.sqrt_mul (Real.sqrt_nonneg c0)] using Real.sqrt_le_sqrt hlq
  have hdc : 0<Real.sqrt (Real.sqrt c0) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hc)
  have hdq : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have ham : Real.sqrt L/Real.sqrt q ≤ 1/Real.sqrt (Real.sqrt c0) := by
    apply (div_le_div_iff₀ hdq hdc).mpr
    simpa only [one_mul,mul_comm] using hd
  have hF := (liClockCriticalEvenKernel_le_positive hw.le).trans
    (by simpa only [he] using liClockCriticalPositiveKernel_le_exp_div_sqrt hq)
  have h1 := mul_le_mul_of_nonneg_left hF
    (show 0≤Real.sqrt L*Real.exp (y/2-2*Real.sqrt (t*L)) by positivity)
  have hex := Real.exp_le_exp.mpr
    (ss_endpoint_exponent_le_lower hL ht.le hr hy hyL'.le)
  have hprod := mul_le_mul_of_nonneg_left ham
    (show 0≤(Real.sqrt Real.pi/(2*Real.sqrt 2))*
      Real.exp (y/2+q-2*Real.sqrt (t*L)) by positivity)
  have hprod2 := mul_le_mul_of_nonneg_left hex
    (show 0≤Real.sqrt Real.pi/(2*Real.sqrt 2*Real.sqrt (Real.sqrt c0)) by positivity)
  refine h1.trans ((le_of_eq ?_).trans (hprod.trans ?_))
  · have heq : Real.exp (y/2-2*Real.sqrt (t*L))*Real.exp q =
        Real.exp (y/2+q-2*Real.sqrt (t*L)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.sqrt Real.pi/(2*Real.sqrt 2))*
          (Real.exp (y/2-2*Real.sqrt (t*L))*Real.exp q)*(Real.sqrt L/Real.sqrt q) := by ring
      _ = _ := by rw [heq]
  · convert hprod2 using 1
    dsimp [q]
    ring

private theorem ss_endpoint_majorant_integrable {c0 : ℝ} (hc0 : 1/4<c0) :
    0<Real.sqrt Real.pi/(2*Real.sqrt 2*Real.sqrt (Real.sqrt c0)) ∧
    IntegrableOn (fun y : ℝ =>
      (Real.sqrt Real.pi/(2*Real.sqrt 2*Real.sqrt (Real.sqrt c0)))*
        Real.exp (-(Real.sqrt c0-1/2)*y)) (Ioi 0) := by
  constructor
  · have hc : 0<c0 := by linarith
    have hπ := Real.pi_pos
    positivity
  · exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (ss_rate_pos hc0)) 0).const_mul _

private theorem ss_quarter_power {w : ℝ} (hw : 0≤w) :
    Real.sqrt (Real.sqrt w)=w^(1/4:ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ←Real.rpow_mul hw]
  norm_num

private theorem ss_amplitude_eq {L w : ℝ} (hL : 0<L) (hw : 0<w) :
    Real.sqrt L/w^(1/4:ℝ) =
      1/Real.sqrt (Real.sqrt (w/L^2)) := by
  have hL0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hw0 := ne_of_gt (Real.rpow_pos_of_pos hw (1/4:ℝ))
  rw [Real.sqrt_div hw.le, Real.sqrt_sq hL.le,
    Real.sqrt_div (Real.sqrt_nonneg w), ss_quarter_power hw.le]
  field_simp

private theorem ss_exponent_eq {L t y : ℝ}
    (hL : 0<L) (ht : 0≤t) (hyL : y<L) :
    y/2+2*Real.sqrt (t*(L-y))-2*Real.sqrt (t*L) =
      y/2-2*y*Real.sqrt (t/L)/(Real.sqrt (1-y/L)+1) := by
  have hL0 : L≠0 := ne_of_gt hL
  have hb : Real.sqrt L≠0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hd : Real.sqrt (L-y)+Real.sqrt L≠0 := by
    have h1 := Real.sqrt_nonneg (L-y)
    have h2 := Real.sqrt_pos.mpr hL
    positivity
  have hi : 1-y/L=(L-y)/L := by field_simp
  rw [hi,Real.sqrt_div (sub_pos.mpr hyL).le,Real.sqrt_div ht,
    Real.sqrt_mul ht,Real.sqrt_mul ht]
  have ha2 := Real.sq_sqrt (sub_pos.mpr hyL).le
  have hb2 := Real.sq_sqrt hL.le
  have hr : (Real.sqrt (L-y)-Real.sqrt L)*
      (Real.sqrt (L-y)+Real.sqrt L)=-y := by nlinarith
  field_simp
  nlinarith [congrArg (fun x:ℝ=>Real.sqrt t*x) hr]

private theorem ss_endpoint_tendsto {L t : ℕ→ℝ} {c y : ℝ}
    (hL : Tendsto L atTop atTop)
    (hr : Tendsto (fun k=>t k/L k) atTop (nhds c))
    (hc : 1/4<c) (_hy : 0≤y) :
    Tendsto (fun k=>Real.sqrt (L k)*
      Real.exp (y/2-2*Real.sqrt (t k*L k))*
        liClockCriticalEvenKernel (t k*(L k-y))) atTop
      (nhds (Real.exp (-(Real.sqrt c-1/2)*y)/
        (4*Real.sqrt Real.pi*c^(1/4:ℝ)))) := by
  have hc0 : 0<c := by linarith
  have ht : Tendsto t atTop atTop := by
    have h := hr.pos_mul_atTop hc0 hL
    apply h.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with k hk
    exact div_mul_cancel₀ _ (ne_of_gt hk)
  let w : ℕ→ℝ := fun k=>t k*(L k-y)
  have hw : Tendsto w atTop atTop := by
    have hLy : Tendsto (fun k=>L k-y) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [hL.eventually_ge_atTop (b+y)] with k hk
      linarith
    exact ht.atTop_mul_atTop₀ hLy
  have hn : Tendsto (fun k=>1-y/L k) atTop (nhds (1:ℝ)) := by
    simpa only [sub_zero] using
      (show Tendsto (fun _ :ℕ=>(1:ℝ)) atTop (nhds 1) from tendsto_const_nhds).sub
        (hL.const_div_atTop y)
  have hd : Tendsto (fun k=>w k/(L k)^2) atTop (nhds c) := by
    have h := hr.mul hn
    simp only [mul_one] at h
    apply h.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with k hk
    dsimp [w]
    field_simp
  have ham : Tendsto (fun k=>Real.sqrt (L k)/(w k)^(1/4:ℝ))
      atTop (nhds (1/c^(1/4:ℝ))) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp hd)
    have hsc : Real.sqrt (Real.sqrt c)≠0 := by positivity
    have h := (show Tendsto (fun _ :ℕ=>(1:ℝ)) atTop (nhds 1) from tendsto_const_nhds).div hs hsc
    rw [ss_quarter_power hc0.le] at h
    apply h.congr'
    filter_upwards [hL.eventually_gt_atTop 0,hw.eventually_gt_atTop 0] with k hk hwk
    exact (ss_amplitude_eq hk hwk).symm
  have hrat : Tendsto (fun k=>Real.sqrt (t k/L k)/
      (Real.sqrt (1-y/L k)+1)) atTop (nhds (Real.sqrt c/2)) := by
    have hden := (Real.continuous_sqrt.continuousAt.tendsto.comp hn).add_const 1
    norm_num at hden
    exact (Real.continuous_sqrt.continuousAt.tendsto.comp hr).div hden (by norm_num)
  have hex : Tendsto (fun k=>y/2+2*Real.sqrt (w k)-2*Real.sqrt (t k*L k))
      atTop (nhds (-(Real.sqrt c-1/2)*y)) := by
    have h := (show Tendsto (fun _ :ℕ=>y/2) atTop (nhds (y/2)) from tendsto_const_nhds).sub (hrat.const_mul (2*y))
    have he : y/2-(2*y)*(Real.sqrt c/2)=-(Real.sqrt c-1/2)*y := by ring
    rw [he] at h
    apply h.congr'
    filter_upwards [hL.eventually_gt_atTop (max 0 y),ht.eventually_gt_atTop 0] with k hk htk
    dsimp [w]
    have hk0 : 0<L k := (le_max_left 0 y).trans_lt hk
    have hky : y<L k := (le_max_right 0 y).trans_lt hk
    convert (ss_exponent_eq hk0 htk.le hky).symm using 1
    ring
  have hF := tendsto_liClockCriticalEvenKernel_scaled.comp hw
  have h := (ham.mul (Real.continuous_exp.continuousAt.tendsto.comp hex)).mul hF
  have hcne := ne_of_gt (Real.rpow_pos_of_pos hc0 (1/4:ℝ))
  have hπne := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hlim : (1/c^(1/4:ℝ)*Real.exp (-(Real.sqrt c-1/2)*y))*
      (1/(4*Real.sqrt Real.pi)) =
      Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)) := by
    field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [hL.eventually_gt_atTop 0,hw.eventually_gt_atTop 0] with k hk hwk
  simp only [Function.comp_def]
  have hwn := ne_of_gt (Real.rpow_pos_of_pos hwk (1/4:ℝ))
  have he : Real.exp (y/2+2*Real.sqrt (w k)-2*Real.sqrt (t k*L k))*
      Real.exp (-2*Real.sqrt (w k)) =
      Real.exp (y/2-2*Real.sqrt (t k*L k)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.sqrt (L k)*
        (Real.exp (y/2+2*Real.sqrt (w k)-2*Real.sqrt (t k*L k))*
          Real.exp (-2*Real.sqrt (w k)))*liClockCriticalEvenKernel (w k) := by field_simp
    _ = _ := by rw [he]

private theorem sr_endpoint_with_profile {L t : ℕ→ℝ} {c : ℝ}
    {P : ℕ→ℝ→ℝ} {p : ℝ→ℝ}
    (hL : Tendsto L atTop atTop) (hc : 1/4<c)
    (ht : Tendsto (fun k => t k/L k) atTop (nhds c))
    (hP : ∀k,Continuous (P k))
    (hbP : ∀ᶠ k in atTop,∀y:ℝ,0<y → y≤L k/2 → 0≤P k y ∧ P k y≤1)
    (hlimP : ∀y:ℝ,0<y → Tendsto (fun k => P k y) atTop (nhds (p y))) :
    Tendsto (fun k => ∫y in Icc 0 (L k/2),sr_scalar (L k) (t k) y*P k y)
      atTop (nhds (∫y in Ioi (0:ℝ),
        (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*p y)) := by
  let c0 := sr_lower_ratio c
  let C : ℝ := Real.sqrt Real.pi/(2*Real.sqrt 2*Real.sqrt (Real.sqrt c0))
  have hc0 : 1/4<c0 := (sr_lower_ratio_bounds hc).1
  have hC := ss_endpoint_majorant_integrable hc0
  have hreg := sr_regime hL hc ht
  apply (sr_endpoint_dct hL (bound:=fun y => C*Real.exp (-(Real.sqrt c0-1/2)*y)) ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun k =>
      ((sr_scalar_continuous (L k) (t k)).mul (hP k)).aestronglyMeasurable)
  · intro y _
    exact mul_nonneg hC.1.le (Real.exp_pos _).le
  · filter_upwards [hreg,hbP] with k hk hpk
    intro y hy hyL
    have hp := hpk y hy hyL
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg sr_scalar_nonneg hp.1)]
    calc
      _ ≤ sr_scalar (L k) (t k) y := mul_le_of_le_one_right sr_scalar_nonneg hp.2
      _≤C*Real.exp (-(Real.sqrt c0-1/2)*y) :=
        ss_endpoint_majorant hk.1 hk.2.1 hc0 hk.2.2 hy.le hyL
  · exact hC.2
  · intro y hy
    have hs : Tendsto (fun k => sr_scalar (L k) (t k) y) atTop
        (nhds (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))) := by
      simpa only [sr_scalar] using ss_endpoint_tendsto hL ht hc hy.le
    exact hs.mul (hlimP y hy)

private theorem sr_literal_endpoint_limits {ν : ℕ→ℕ} {t : ℕ→ℝ} {c : ℝ}
    (hν : Tendsto ν atTop atTop) (hc : 1/4<c)
    (ht : Tendsto (fun k => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
    Tendsto (fun k => ∫y in Icc 0 (Real.log (2*(ν k:ℝ))/2),
      sr_scalar (Real.log (2*(ν k:ℝ))) (t k) y*liClockPairedEtaPartitionEndpointProfile (ν k) y)
      atTop (nhds (∫y in Ioi (0:ℝ),
        (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
          liClockPairedEtaPartitionEndpointProfileLimit y)) ∧
    Tendsto (fun k => ∫y in Icc 0 (Real.log (2*(ν k:ℝ))/2),
      sr_scalar (Real.log (2*(ν k:ℝ))) (t k) y*(1-Real.exp (-y)))
      atTop (nhds (∫y in Ioi (0:ℝ),
        (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
          (1-Real.exp (-y)))) := by
  have hL : Tendsto (fun k => Real.log (2*(ν k:ℝ))) atTop atTop :=
    tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  constructor
  · apply sr_endpoint_with_profile hL hc ht (fun k => sr_profile_continuous (ν k))
    · filter_upwards [hν.eventually (eventually_gt_atTop (0:ℕ)),
        hL.eventually (eventually_gt_atTop (0:ℝ))] with k hk hLk
      intro y hy hyL
      have hp := liClockPairedEtaPartitionEndpointProfile_bounds hk hy.le (by linarith)
      exact ⟨hp.1,hp.2.1.trans hp.2.2⟩
    · intro y hy
      exact (tendsto_liClockPairedEtaPartitionEndpointProfile hy.le).comp hν
  · apply sr_endpoint_with_profile (P:=fun _ y => 1-Real.exp (-y)) hL hc ht
      (fun _ => continuous_const.sub (Real.continuous_exp.comp continuous_neg))
    · apply Eventually.of_forall
      intro k y hy _
      exact ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)),by linarith [Real.exp_pos (-y)]⟩
    · intro y _
      exact tendsto_const_nhds

private theorem sr_nearzero_exponent_from_lower {L t c0 r : ℝ}
    (hL : 0<L) (ht : 0≤t) (hc0 : 1/4<c0) (hratio : c0≤t/L)
    (hr : r∈Icc 0 (L/2)) :
    L/2-r/2+2*Real.sqrt (t*r)-2*Real.sqrt (t*L)≤
      -(Real.sqrt c0-1/2)*L/2 := by
  have hs := ss_endpoint_exponent_le hL ht
    (show 0≤L-r by linarith [hr.2]) (show L-r≤L by linarith [hr.1])
  rw [show L-(L-r)=r by ring] at hs
  have hroot : Real.sqrt c0≤Real.sqrt (t/L) := Real.sqrt_le_sqrt hratio
  have hc0p : 0<c0 := by linarith
  have hs0 := Real.sq_sqrt hc0p.le
  have hnn := Real.sqrt_nonneg c0
  have ha : 0<Real.sqrt c0-1/2 := by nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hroot) (show 0≤L-r by linarith [hr.2])
  have hlast := mul_nonneg ha.le (show 0≤L/2-r by linarith [hr.2])
  nlinarith

private theorem sr_literal_nearzero_limits {ν : ℕ→ℕ} {t : ℕ→ℝ} {c : ℝ}
    (hν : Tendsto ν atTop atTop) (hc : 1/4<c)
    (ht : Tendsto (fun k => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
    Tendsto (fun k => sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
      (∫r in Icc 0 (Real.log (2*(ν k:ℝ))/2),
        liClockPairedEtaPartitionRawDifferenceDensity (ν k) r*liClockCriticalEvenKernel (t k*r)))
      atTop (nhds 0) ∧
    Tendsto (fun k => sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
      (∫r in Icc 0 (Real.log (2*(ν k:ℝ))/2),
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(ν k:ℝ))) r*
          liClockCriticalEvenKernel (t k*r)))
      atTop (nhds 0) := by
  have hL : Tendsto (fun k => Real.log (2*(ν k:ℝ))) atTop atTop :=
    tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have hc0 := sr_lower_ratio_bounds hc
  have hreg := sr_regime hL hc ht
  have hz := sr_nearzero_envelope_tendsto hL hc0.2.2
  have hb : ∀ᶠ k in atTop,
      |sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
        (∫r in Icc 0 (Real.log (2*(ν k:ℝ))/2),
          liClockPairedEtaPartitionRawDifferenceDensity (ν k) r*liClockCriticalEvenKernel (t k*r))|≤
        Real.sqrt (Real.log (2*(ν k:ℝ)))*(Real.log (2*(ν k:ℝ))/2)*
          Real.exp (-(Real.sqrt (sr_lower_ratio c)-1/2)*Real.log (2*(ν k:ℝ))/2) ∧
      |sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
        (∫r in Icc 0 (Real.log (2*(ν k:ℝ))/2),
          liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(ν k:ℝ))) r*
            liClockCriticalEvenKernel (t k*r))|≤
        Real.sqrt (Real.log (2*(ν k:ℝ)))*(Real.log (2*(ν k:ℝ))/2)*
          Real.exp (-(Real.sqrt (sr_lower_ratio c)-1/2)*Real.log (2*(ν k:ℝ))/2) := by
    filter_upwards [hν.eventually (eventually_gt_atTop (0:ℕ)),hreg] with k hNk hk
    have he (r : ℝ) (hr : r∈Icc 0 (Real.log (2*(ν k:ℝ))/2)) :=
      sr_nearzero_exponent_from_lower hk.1 hk.2.1.le hc0.1 hk.2.2 hr
    constructor
    · exact (sr_nearzero_bound hk.1 hk.2.1.le
        (continuous_liClockPairedEtaPartitionRawDifferenceDensity (ν k))
        (fun r hr => (sr_nearzero_source_bounds hNk hr).1) he).2
    · exact (sr_nearzero_bound hk.1 hk.2.1.le
        (continuous_liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(ν k:ℝ))))
        (fun r hr => (sr_nearzero_source_bounds hNk hr).2) he).2
  constructor
  · apply squeeze_zero_norm' ?_ hz
    filter_upwards [hb] with k hk
    simpa only [Real.norm_eq_abs] using hk.1
  · apply squeeze_zero_norm' ?_ hz
    filter_upwards [hb] with k hk
    simpa only [Real.norm_eq_abs] using hk.2

theorem tendsto_liClockPairedEtaSupercriticalActual_prefactor
    {c : ℝ} (hc : 1/4<c) {ν : ℕ→ℕ} {t : ℕ→ℝ}
    (hν : Tendsto ν atTop atTop)
    (ht : Tendsto (fun k : ℕ => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
  Tendsto (fun k : ℕ =>
    liClockPairedEtaSupercriticalScale (Real.log (2*(ν k:ℝ))) (t k)*
      liClockPairedEtaPartitionBorelKernel (ν k) (t k))
    atTop (nhds (liClockPairedEtaSupercriticalActualPrefactor c)) := by
  have hc0 : 0<c := by linarith
  have hL : Tendsto (fun k => Real.log (2*(ν k:ℝ))) atTop atTop :=
    tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have hi := (sr_literal_endpoint_limits hν hc ht).1
  have hz := (sr_literal_nearzero_limits hν hc ht).1
  have hZ : liClockPairedEtaInfinitePartitionNormalizer^2≠0 :=
    pow_ne_zero _ liClockPairedEtaInfinitePartitionNormalizer_pos.ne'
  have hq : Tendsto (fun k => 2/liClockPairedEtaPartitionNormalizer (ν k)^2)
      atTop (nhds (2/liClockPairedEtaInfinitePartitionNormalizer^2)) :=
    tendsto_const_nhds.div ((tendsto_liClockPairedEtaInfinitePartitionNormalizer.comp hν).pow 2) hZ
  have h := hq.mul (hz.add hi)
  have hint := (sr_scaled_profile_integrals hc).1.2
  have hconst : (2/liClockPairedEtaInfinitePartitionNormalizer^2)*
      (0+(∫y in Ioi (0:ℝ),
        (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
          liClockPairedEtaPartitionEndpointProfileLimit y)) =
      liClockPairedEtaSupercriticalActualPrefactor c := by
    rw [zero_add,hint]
    unfold liClockPairedEtaSupercriticalActualPrefactor
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hconst] at h
  change Tendsto (fun k => sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
    liClockPairedEtaPartitionBorelKernel (ν k) (t k)) atTop _
  apply h.congr'
  filter_upwards [hν.eventually (eventually_gt_atTop (0:ℕ)),sr_regime hL hc ht] with k hNk hk
  exact (sr_actual_scaled_split hNk hk.2.1.le).symm

theorem tendsto_liClockPairedEtaSupercriticalReference_prefactor
    {c : ℝ} (hc : 1/4<c) {ν : ℕ→ℕ} {t : ℕ→ℝ}
    (hν : Tendsto ν atTop atTop)
    (ht : Tendsto (fun k : ℕ => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
  Tendsto (fun k : ℕ =>
    liClockPairedEtaSupercriticalScale (Real.log (2*(ν k:ℝ))) (t k)*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k:ℝ))) (t k))
    atTop (nhds (liClockPairedEtaSupercriticalReferencePrefactor c)) := by
  have hc0 : 0<c := by linarith
  have hL : Tendsto (fun k => Real.log (2*(ν k:ℝ))) atTop atTop :=
    tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have hi := (sr_literal_endpoint_limits hν hc ht).2
  have hz := (sr_literal_nearzero_limits hν hc ht).2
  have hq : Tendsto (fun k =>
      2/liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(ν k:ℝ)))^2)
      atTop (nhds (2/(2:ℝ)^2)) :=
    tendsto_const_nhds.div ((tendsto_liClockPairedEtaHalfLinePartitionNormalizer.comp hν).pow 2)
      (by norm_num)
  have h := hq.mul (hz.add hi)
  have hint := (sr_scaled_profile_integrals hc).2.2
  have hconst : (2/(2:ℝ)^2)*
      (0+(∫y in Ioi (0:ℝ),
        (Real.exp (-(Real.sqrt c-1/2)*y)/(4*Real.sqrt Real.pi*c^(1/4:ℝ)))*
          (1-Real.exp (-y)))) = liClockPairedEtaSupercriticalReferencePrefactor c := by
    rw [zero_add,hint]
    unfold liClockPairedEtaSupercriticalReferencePrefactor
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hconst] at h
  change Tendsto (fun k => sr_weight (Real.log (2*(ν k:ℝ))) (t k)*
    liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k:ℝ))) (t k)) atTop _
  apply h.congr'
  filter_upwards [hν.eventually (eventually_gt_atTop (0:ℕ)),sr_regime hL hc ht] with k hNk hk
  exact (sr_reference_scaled_split hNk hk.2.1.le).symm

theorem tendsto_liClockPairedEtaSupercriticalRatio
    {c : ℝ} (hc : 1/4<c) {ν : ℕ→ℕ} {t : ℕ→ℝ}
    (hν : Tendsto ν atTop atTop)
    (ht : Tendsto (fun k : ℕ => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
  Tendsto (fun k : ℕ => liClockPairedEtaPartitionBorelKernel (ν k) (t k)/
    liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k:ℝ))) (t k))
    atTop (nhds (liClockPairedEtaSupercriticalRatioLimit c)) := by
  have hc0 : 0<c := by linarith
  have ha : 0<Real.sqrt c-1/2 := by
    nlinarith [Real.sq_sqrt hc0.le,Real.sqrt_nonneg c]
  have hb : 0<Real.sqrt c+1/2 := by positivity
  have hcp : 0<c^(1/4:ℝ) := Real.rpow_pos_of_pos hc0 _
  have hπ : 0<Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hZ := liClockPairedEtaInfinitePartitionNormalizer_pos
  have hpos := liClockPairedEtaSupercriticalConstants_pos hc
  have h := (tendsto_liClockPairedEtaSupercriticalActual_prefactor hc hν ht).div
    (tendsto_liClockPairedEtaSupercriticalReference_prefactor hc hν ht) hpos.1.ne'
  have he : liClockPairedEtaSupercriticalActualPrefactor c/
      liClockPairedEtaSupercriticalReferencePrefactor c=liClockPairedEtaSupercriticalRatioLimit c := by
    have hdiv (E Z p q a b : ℝ) (hZ : Z≠0) (hp : p≠0) (hq : q≠0)
        (ha : a≠0) (hb : b≠0) :
        (E/(4*Z^2*p*q*a*b))/(1/(8*p*q*a*b))=2*E/Z^2 := by
      field_simp
      ring
    unfold liClockPairedEtaSupercriticalActualPrefactor liClockPairedEtaSupercriticalReferencePrefactor
      liClockPairedEtaSupercriticalRatioLimit
    exact hdiv _ _ _ _ _ _ hZ.ne' hπ.ne' hcp.ne' ha.ne' hb.ne'
  rw [he] at h
  apply h.congr'
  filter_upwards [(tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν).eventually
    (eventually_gt_atTop (0:ℝ))] with k hk
  have hw : liClockPairedEtaSupercriticalScale (Real.log (2*(ν k:ℝ))) (t k)≠0 := by
    unfold liClockPairedEtaSupercriticalScale
    exact mul_ne_zero (Real.sqrt_pos.mpr hk).ne' (Real.exp_ne_zero _)
  exact mul_div_mul_left _ _ hw

private theorem transfer_eventually_positive
    {L t B : ℕ → ℝ} {K : ℝ}
    (hL : Tendsto L atTop atTop) (hK : 0<K)
    (hB : Tendsto (fun n : ℕ =>
      (Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt (t n*L n)))*B n)
      atTop (nhds K)) :
    ∀ᶠ n : ℕ in atTop,
      0<L n ∧ 0<Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt (t n*L n)) ∧ 0<B n := by
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),
    hB.eventually (eventually_gt_nhds hK)] with n hLn hBn
  have hscale : 0<Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt (t n*L n)) :=
    mul_pos (Real.sqrt_pos.mpr hLn) (Real.exp_pos _)
  exact ⟨hLn,hscale,(mul_pos_iff_of_pos_left hscale).mp hBn⟩

private theorem transfer_root_ratio {l : ℝ} (hl : 0<l) (t : ℝ) :
    Real.sqrt (t*l)=Real.sqrt (t/l)*l := by
  calc
    _ = Real.sqrt ((t/l)*l^2) := by
      congr 1
      field_simp [hl.ne']
    _ = Real.sqrt (t/l)*Real.sqrt (l^2) := Real.sqrt_mul' _ (sq_nonneg l)
    _ = _ := by rw [Real.sqrt_sq hl.le]

private theorem transfer_weight_factor {l c : ℝ} (hl : 0<l) (hc : 0≤c) :
    (Real.sqrt l*Real.exp (l/2-2*Real.sqrt ((c*l)*l)))*
      (l^(-(1/2:ℝ))*Real.exp (-2*(Real.sqrt c-1/2)^2*l)) =
      Real.exp (-2*c*l) := by
  have hhalf : l^(-(1/2:ℝ))=(Real.sqrt l)⁻¹ := by
    rw [Real.rpow_neg hl.le,←Real.sqrt_eq_rpow]
  have hs : Real.sqrt ((c*l)*l)=Real.sqrt c*l := by
    rw [show (c*l)*l=c*l^2 by ring,Real.sqrt_mul hc,Real.sqrt_sq hl.le]
  have hb : -2*(Real.sqrt c-1/2)^2 = -2*c+2*Real.sqrt c-1/2 := by
    nlinarith [Real.sq_sqrt hc]
  have he : (l/2-2*Real.sqrt c*l)+(-2*(Real.sqrt c-1/2)^2*l) = -2*c*l := by
    rw [hb]
    ring
  rw [hhalf,hs]
  calc
    _ = (Real.sqrt l*(Real.sqrt l)⁻¹)*
      (Real.exp (l/2-2*(Real.sqrt c*l))*Real.exp (-2*(Real.sqrt c-1/2)^2*l)) := by ring
    _ = Real.exp (l/2-2*(Real.sqrt c*l))*Real.exp (-2*(Real.sqrt c-1/2)^2*l) := by
      rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hl).ne',one_mul]
    _ = Real.exp ((l/2-2*Real.sqrt c*l)+(-2*(Real.sqrt c-1/2)^2*l)) := by
      rw [Real.exp_add]
      congr 2
      ring
    _ = _ := by rw [he]

private theorem transfer_log_identity {l b : ℝ} (hl : 0<l) (hb : 0<b) (t : ℝ) :
    Real.log (Real.exp (-2*t)*b)/l =
      Real.log ((Real.sqrt l*Real.exp (l/2-2*Real.sqrt (t*l)))*b)/l -
      (Real.log l/l)/2 -2*(t/l) -(1/2:ℝ) +2*Real.sqrt (t/l) := by
  have hs : 0<Real.sqrt l := Real.sqrt_pos.mpr hl
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne',Real.log_exp,
    Real.log_mul (mul_ne_zero hs.ne' (Real.exp_ne_zero _)) hb.ne',
    Real.log_mul hs.ne' (Real.exp_ne_zero _),Real.log_sqrt hl.le,Real.log_exp,
    transfer_root_ratio hl]
  field_simp [hl.ne']
  ring

private theorem li_producer_supercritical_weighted_equivalent
    {L B : ℕ → ℝ} {c K : ℝ}
    (hL : Tendsto L atTop atTop) (hc : 1/4<c) (hK : 0<K)
    (hB : Tendsto (fun n : ℕ =>
      (Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt ((c*L n)*L n)))*B n)
      atTop (nhds K)) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => Real.exp (-2*c*L n)*B n)
      (fun n : ℕ => K*(L n)^(-(1/2:ℝ))*
        Real.exp (-2*(Real.sqrt c-1/2)^2*L n)) := by
  have hc0 : 0≤c := by linarith
  have hpos := transfer_eventually_positive hL hK hB
  have hq : Tendsto (fun n : ℕ =>
      ((Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt ((c*L n)*L n)))*B n)/K)
      atTop (nhds 1) := by
    simpa only [div_self hK.ne'] using hB.div_const K
  apply Asymptotics.isEquivalent_of_tendsto_one
  change Tendsto (fun n : ℕ => (Real.exp (-2*c*L n)*B n)/
    (K*(L n)^(-(1/2:ℝ))*Real.exp (-2*(Real.sqrt c-1/2)^2*L n))) atTop (nhds 1)
  apply hq.congr'
  filter_upwards [hpos] with n hn
  obtain ⟨hLn,_hscale,_hBn⟩ := hn
  have hp : (L n)^(-(1/2:ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hLn _).ne'
  rw [←transfer_weight_factor hLn hc0]
  field_simp [hK.ne',hp,Real.exp_ne_zero]

private theorem li_producer_supercritical_weighted_log_rate
    {L t B : ℕ → ℝ} {c K : ℝ}
    (hL : Tendsto L atTop atTop) (hc : 1/4<c) (hK : 0<K)
    (ht : Tendsto (fun n : ℕ => t n/L n) atTop (nhds c))
    (hB : Tendsto (fun n : ℕ =>
      (Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt (t n*L n)))*B n)
      atTop (nhds K)) :
    Tendsto (fun n : ℕ => Real.log (Real.exp (-2*t n)*B n)/L n)
      atTop (nhds (-2*(Real.sqrt c-1/2)^2)) := by
  have hc0 : 0≤c := by linarith
  have hpos := transfer_eventually_positive hL hK hB
  have hA : Tendsto (fun n : ℕ =>
      Real.log ((Real.sqrt (L n)*Real.exp (L n/2-2*Real.sqrt (t n*L n)))*B n)/L n)
      atTop (nhds 0) := by
    have h := (hB.log hK.ne').mul hL.inv_tendsto_atTop
    simpa only [Pi.inv_apply,←div_eq_mul_inv,mul_zero] using h
  have hlog : Tendsto (fun n : ℕ => Real.log (L n)/L n) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hL
  have hcalc := (((hA.sub (hlog.div_const 2)).sub (ht.const_mul 2)).sub_const (1/2:ℝ)).add
    (ht.sqrt.const_mul 2)
  have he : 0-0/2-2*c-(1/2:ℝ)+2*Real.sqrt c = -2*(Real.sqrt c-1/2)^2 := by
    nlinarith [Real.sq_sqrt hc0]
  rw [he] at hcalc
  apply hcalc.congr'
  filter_upwards [hpos] with n hn
  obtain ⟨hLn,_hscale,hBn⟩ := hn
  exact (transfer_log_identity hLn hBn (t n)).symm

theorem liClockPairedEtaSupercritical_weighted_equivalents
    {c : ℝ} (hc : 1/4<c) :
  Asymptotics.IsEquivalent atTop
    (fun N : ℕ => Real.exp (-2*c*Real.log (2*(N:ℝ)))*
      liClockPairedEtaPartitionBorelKernel N (c*Real.log (2*(N:ℝ))))
    (fun N : ℕ => liClockPairedEtaSupercriticalActualPrefactor c*
      (Real.log (2*(N:ℝ)))^(-(1/2:ℝ))*
      Real.exp (-liClockPairedEtaSupercriticalRate c*Real.log (2*(N:ℝ)))) ∧
  Asymptotics.IsEquivalent atTop
    (fun N : ℕ => Real.exp (-2*c*Real.log (2*(N:ℝ)))*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ)))
        (c*Real.log (2*(N:ℝ))))
    (fun N : ℕ => liClockPairedEtaSupercriticalReferencePrefactor c*
      (Real.log (2*(N:ℝ)))^(-(1/2:ℝ))*
      Real.exp (-liClockPairedEtaSupercriticalRate c*Real.log (2*(N:ℝ)))) := by
  have hL := tendsto_liClockPairedEtaPartitionLogEndpoint
  have ht : Tendsto (fun N : ℕ => (c*Real.log (2*(N:ℝ)))/Real.log (2*(N:ℝ)))
      atTop (nhds c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with N hN
    field_simp
  have hA := tendsto_liClockPairedEtaSupercriticalActual_prefactor hc (ν:=id)
    (t:=fun N => c*Real.log (2*(N:ℝ))) tendsto_id ht
  have hU := tendsto_liClockPairedEtaSupercriticalReference_prefactor hc (ν:=id)
    (t:=fun N => c*Real.log (2*(N:ℝ))) tendsto_id ht
  simp only [id_eq] at hA hU
  have hp := liClockPairedEtaSupercriticalConstants_pos hc
  constructor
  · simpa only [liClockPairedEtaSupercriticalScale,liClockPairedEtaSupercriticalRate,neg_mul] using
      li_producer_supercritical_weighted_equivalent hL hc hp.2.1 hA
  · simpa only [liClockPairedEtaSupercriticalScale,liClockPairedEtaSupercriticalRate,neg_mul] using
      li_producer_supercritical_weighted_equivalent hL hc hp.1 hU

theorem liClockPairedEtaSupercritical_weighted_log_rates
    {c : ℝ} (hc : 1/4<c) {ν : ℕ→ℕ} {t : ℕ→ℝ}
    (hν : Tendsto ν atTop atTop)
    (ht : Tendsto (fun k : ℕ => t k/Real.log (2*(ν k:ℝ))) atTop (nhds c)) :
  Tendsto (fun k : ℕ =>
    Real.log (Real.exp (-2*t k)*liClockPairedEtaPartitionBorelKernel (ν k) (t k))/
      Real.log (2*(ν k:ℝ))) atTop (nhds (-liClockPairedEtaSupercriticalRate c)) ∧
  Tendsto (fun k : ℕ =>
    Real.log (Real.exp (-2*t k)*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(ν k:ℝ))) (t k))/
      Real.log (2*(ν k:ℝ))) atTop (nhds (-liClockPairedEtaSupercriticalRate c)) := by
  have hL : Tendsto (fun k => Real.log (2*(ν k:ℝ))) atTop atTop :=
    tendsto_liClockPairedEtaPartitionLogEndpoint.comp hν
  have hA := tendsto_liClockPairedEtaSupercriticalActual_prefactor hc hν ht
  have hU := tendsto_liClockPairedEtaSupercriticalReference_prefactor hc hν ht
  have hp := liClockPairedEtaSupercriticalConstants_pos hc
  constructor
  · simpa only [liClockPairedEtaSupercriticalScale,liClockPairedEtaSupercriticalRate,neg_mul] using
      li_producer_supercritical_weighted_log_rate hL hc hp.2.1 ht hA
  · simpa only [liClockPairedEtaSupercriticalScale,liClockPairedEtaSupercriticalRate,neg_mul] using
      li_producer_supercritical_weighted_log_rate hL hc hp.1 ht hU

end RHTower
