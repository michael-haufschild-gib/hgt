import GaloisForLFunctions.RHTower.MobiusCriticalFisherSteinContact
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PortAdmissionCapacity
import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic
import Mathlib.Analysis.InnerProductSpace.LinearPMap

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- Normalized critical prime-log Laplace feature. -/
def primeLogCriticalLaplaceFeature (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * t * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) *
    Real.exp (-(Real.log (p : ℝ) * t))

/-- Exact cubic Laplace Gram identity before any completion or divisor data. -/
theorem integral_primeLogCriticalLaplaceFeature_mul
    (p q : Nat.Primes) :
    (∫ t : ℝ in Ioi 0,
      primeLogCriticalLaplaceFeature p t *
        primeLogCriticalLaplaceFeature q t) =
      8 * Real.log (p : ℝ) ^ 2 * Real.log (q : ℝ) ^ 2 /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3) := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hqLog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  have hrate : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) :=
    add_pos hpLog hqLog
  rw [show (fun t : ℝ =>
      primeLogCriticalLaplaceFeature p t *
        primeLogCriticalLaplaceFeature q t) =
      fun t =>
        (4 * Real.log (p : ℝ) ^ 2 * Real.log (q : ℝ) ^ 2 /
          (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) *
          (t ^ 2 * Real.exp (-((Real.log (p : ℝ) +
            Real.log (q : ℝ)) * t))) by
    funext t
    simp only [primeLogCriticalLaplaceFeature]
    calc
      2 * t * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) *
            Real.exp (-(Real.log (p : ℝ) * t)) *
          (2 * t * Real.log (q : ℝ) ^ 2 / Real.sqrt (q : ℝ) *
            Real.exp (-(Real.log (q : ℝ) * t))) =
          (4 * Real.log (p : ℝ) ^ 2 * Real.log (q : ℝ) ^ 2 /
            (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) * t ^ 2 *
            (Real.exp (-(Real.log (p : ℝ) * t)) *
              Real.exp (-(Real.log (q : ℝ) * t))) := by ring
      _ = (4 * Real.log (p : ℝ) ^ 2 * Real.log (q : ℝ) ^ 2 /
            (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) *
          (t ^ 2 * Real.exp (-((Real.log (p : ℝ) +
            Real.log (q : ℝ)) * t))) := by
        have hexp :
            Real.exp (-(Real.log (p : ℝ) * t)) *
                Real.exp (-(Real.log (q : ℝ) * t)) =
              Real.exp (-((Real.log (p : ℝ) +
                Real.log (q : ℝ)) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring]
  rw [integral_const_mul, integral_Ioi_pow_mul_exp_neg_rate 2 hrate]
  norm_num
  field_simp
  ring

/-- Each feature has exactly the critical prime-log mass as squared `L²` norm. -/
theorem integral_primeLogCriticalLaplaceFeature_sq (p : Nat.Primes) :
    (∫ t : ℝ in Ioi 0, primeLogCriticalLaplaceFeature p t ^ 2) =
      Real.log (p : ℝ) / (p : ℝ) := by
  rw [show (fun t : ℝ => primeLogCriticalLaplaceFeature p t ^ 2) =
      fun t => primeLogCriticalLaplaceFeature p t *
        primeLogCriticalLaplaceFeature p t by
    funext t
    ring,
    integral_primeLogCriticalLaplaceFeature_mul]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  rw [Real.mul_self_sqrt hp.le]
  field_simp [hp.ne', hpLog.ne']
  ring

/-- Complex realization of the normalized critical feature. -/
def primeLogCriticalLaplaceFeatureC (p : Nat.Primes) (t : ℝ) : ℂ :=
  (primeLogCriticalLaplaceFeature p t : ℂ)

theorem continuous_primeLogCriticalLaplaceFeatureC (p : Nat.Primes) :
    Continuous (primeLogCriticalLaplaceFeatureC p) := by
  unfold primeLogCriticalLaplaceFeatureC primeLogCriticalLaplaceFeature
  fun_prop

theorem integrableOn_norm_sq_primeLogCriticalLaplaceFeatureC
    (p : Nat.Primes) :
    IntegrableOn (fun t : ℝ => ‖primeLogCriticalLaplaceFeatureC p t‖ ^ 2) (Ioi 0) := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (2 : ℝ))
    (b := 2 * Real.log (p : ℝ)) (by norm_num) (by norm_num)
    (mul_pos (by norm_num) hpLog)
  have hconst : IntegrableOn
      (fun t : ℝ =>
        (4 * Real.log (p : ℝ) ^ 4 / (p : ℝ)) *
          (t ^ 2 * Real.exp (-((2 * Real.log (p : ℝ)) * t))))
      (Ioi 0) := by
    apply (hbase.const_mul
      (4 * Real.log (p : ℝ) ^ 4 / (p : ℝ))).congr
    filter_upwards with t
    norm_num [Real.rpow_two, Real.rpow_one]
  apply hconst.congr
  filter_upwards with t
  rw [primeLogCriticalLaplaceFeatureC, norm_real, Real.norm_eq_abs, sq_abs]
  rw [primeLogCriticalLaplaceFeature]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  field_simp [hsqrt]
  rw [Real.sq_sqrt hp.le]
  have hexp : Real.exp (-(Real.log (p : ℝ) * t)) ^ 2 =
      Real.exp (-((2 * Real.log (p : ℝ)) * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

abbrev primeLogCriticalHalfLineL2 :=
  Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

abbrev primeLogCriticalSourceL2 :=
  HTGeometry.ConstraintMotiveRelativity.SourceL2 Nat.Primes

/-- Critical feature as an actual half-line `L²` vector. -/
def primeLogCriticalLaplaceFeatureL2 (p : Nat.Primes) :
    primeLogCriticalHalfLineL2 :=
  ((memLp_two_iff_integrable_sq_norm
    (continuous_primeLogCriticalLaplaceFeatureC p).aestronglyMeasurable.restrict).2
      (integrableOn_norm_sq_primeLogCriticalLaplaceFeatureC p)).toLp
        (primeLogCriticalLaplaceFeatureC p)

theorem primeLogCriticalLaplaceFeatureL2_ae (p : Nat.Primes) :
    (primeLogCriticalLaplaceFeatureL2 p : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))]
        primeLogCriticalLaplaceFeatureC p := by
  unfold primeLogCriticalLaplaceFeatureL2
  exact ((memLp_two_iff_integrable_sq_norm
    (continuous_primeLogCriticalLaplaceFeatureC p).aestronglyMeasurable.restrict).2
      (integrableOn_norm_sq_primeLogCriticalLaplaceFeatureC p)).coeFn_toLp

theorem primeLogCritical_srcEmb_injective :
    Function.Injective
      (HTGeometry.ConstraintMotiveRelativity.srcEmb
        (P := Nat.Primes)) := by
  intro l m hlm
  ext p
  rw [← HTGeometry.ConstraintMotiveRelativity.srcEmb_apply l p,
    ← HTGeometry.ConstraintMotiveRelativity.srcEmb_apply m p, hlm]

/-- Literal finite-prime synthesis into the half-line feature space. -/
def primeLogCriticalLaplaceMass :
    (Nat.Primes →₀ ℂ) →ₗ[ℂ] primeLogCriticalHalfLineL2 :=
  Finsupp.linearCombination ℂ primeLogCriticalLaplaceFeatureL2

theorem primeLogCriticalLaplaceMass_eq_sum (l : Nat.Primes →₀ ℂ) :
    primeLogCriticalLaplaceMass l =
      ∑ p ∈ l.support, l p • primeLogCriticalLaplaceFeatureL2 p := by
  rw [primeLogCriticalLaplaceMass, Finsupp.linearCombination_apply, Finsupp.sum]

/-- The Hilbert synthesis retains the literal finite-prime pointwise sum. -/
theorem primeLogCriticalLaplaceMass_ae (l : Nat.Primes →₀ ℂ) :
    (primeLogCriticalLaplaceMass l : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))]
        fun t => ∑ p ∈ l.support,
          l p * primeLogCriticalLaplaceFeatureC p t := by
  have hsum := Lp.coeFn_fun_finsetSum l.support (fun p =>
    l p • primeLogCriticalLaplaceFeatureL2 p)
  have hterms : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ p ∈ l.support,
        (l p • primeLogCriticalLaplaceFeatureL2 p) t =
          l p * primeLogCriticalLaplaceFeatureC p t := by
    apply (eventually_all_finset l.support).2
    intro p hp
    filter_upwards [Lp.coeFn_smul (l p)
      (primeLogCriticalLaplaceFeatureL2 p),
      primeLogCriticalLaplaceFeatureL2_ae p] with t hsmul hfeature
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfeature]
  filter_upwards [hsum, hterms] with t hsumt htermst
  calc
    primeLogCriticalLaplaceMass l t =
        ∑ p ∈ l.support,
          (l p • primeLogCriticalLaplaceFeatureL2 p) t := by
      simpa [primeLogCriticalLaplaceMass_eq_sum] using hsumt
    _ = ∑ p ∈ l.support,
          l p * primeLogCriticalLaplaceFeatureC p t := by
      exact Finset.sum_congr rfl fun p hp => htermst p hp

/-- At every positive time, literal prime evaluation is a bounded `ℓ²` reporter. -/
theorem memℓp_primeLogCriticalLaplaceFeatureC (t : ℝ) (ht : 0 < t) :
    Memℓp (fun p : Nat.Primes => primeLogCriticalLaplaceFeatureC p t) 2 := by
  have hnat := HTGeometry.summable_log_pow_div_nat_rpow 4
    (show (1 : ℝ) < 1 + 2 * t by linarith)
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) ^ 4 /
        (((p : ℕ) : ℝ) ^ (1 + 2 * t))) :=
    Summable.subtype hnat Nat.Prime
  apply memℓp_gen
  refine (hprime.mul_left (4 * t ^ 2)).congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hfeaturePos : 0 < primeLogCriticalLaplaceFeature p t := by
    unfold primeLogCriticalLaplaceFeature
    positivity
  have hexp : Real.exp (-(t * Real.log (p : ℝ))) ^ 2 =
      (p : ℝ) ^ (-(2 * t)) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [primeLogCriticalLaplaceFeatureC, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hfeaturePos,
    primeLogCriticalLaplaceFeature]
  norm_num
  field_simp [hsqrt]
  rw [Real.sq_sqrt hp.le, hexp, Real.rpow_add hp,
    Real.rpow_one, Real.rpow_neg hp.le]
  have hpow : (p : ℝ) ^ (t * 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hp _).ne'
  field_simp [hpow]
  norm_num

/-- Positive-time evaluation is represented by an actual source Hilbert vector. -/
def primeLogCriticalEvaluationVector (t : ℝ) (ht : 0 < t) :
    primeLogCriticalSourceL2 :=
  ⟨fun p => primeLogCriticalLaplaceFeatureC p t,
    memℓp_primeLogCriticalLaplaceFeatureC t ht⟩

/-- Literal finite synthesis is the source inner product against evaluation. -/
theorem primeLogCriticalLaplaceMass_pointwise_eq_inner
    (l : Nat.Primes →₀ ℂ) (t : ℝ) (ht : 0 < t) :
    ∑ p ∈ l.support, l p * primeLogCriticalLaplaceFeatureC p t =
      inner ℂ (primeLogCriticalEvaluationVector t ht)
        (HTGeometry.ConstraintMotiveRelativity.srcEmb l) := by
  rw [lp.inner_eq_tsum]
  have hsum : (∑' p : Nat.Primes,
      inner ℂ ((primeLogCriticalEvaluationVector t ht :
        primeLogCriticalSourceL2) p)
        ((HTGeometry.ConstraintMotiveRelativity.srcEmb l :
          primeLogCriticalSourceL2) p)) =
      ∑ p ∈ l.support,
        inner ℂ ((primeLogCriticalEvaluationVector t ht :
          primeLogCriticalSourceL2) p)
          ((HTGeometry.ConstraintMotiveRelativity.srcEmb l :
            primeLogCriticalSourceL2) p) := by
    apply tsum_eq_sum
    intro p hp
    rw [RCLike.inner_apply,
      HTGeometry.ConstraintMotiveRelativity.srcEmb_apply]
    simp only [Finsupp.not_mem_support_iff.mp hp, mul_zero]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RCLike.inner_apply,
    HTGeometry.ConstraintMotiveRelativity.srcEmb_apply]
  simp [primeLogCriticalEvaluationVector,
    primeLogCriticalLaplaceFeatureC]
  ring

/-- Finite-prime synthesis as a partial operator on the completed source `ℓ²`. -/
def primeLogCriticalLaplaceSynthesis :
    primeLogCriticalSourceL2 →ₗ.[ℂ] primeLogCriticalHalfLineL2 where
  domain := LinearMap.range
    (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes))
  toFun := primeLogCriticalLaplaceMass ∘ₗ
    (LinearEquiv.ofInjective _ primeLogCritical_srcEmb_injective).symm.toLinearMap

theorem primeLogCriticalLaplaceSynthesis_apply
    (l : Nat.Primes →₀ ℂ)
    (hmem : HTGeometry.ConstraintMotiveRelativity.srcEmb l ∈
      LinearMap.range
        (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes))) :
    primeLogCriticalLaplaceSynthesis
        ⟨HTGeometry.ConstraintMotiveRelativity.srcEmb l, hmem⟩ =
      primeLogCriticalLaplaceMass l := by
  have hval :
      (LinearEquiv.ofInjective _ primeLogCritical_srcEmb_injective) l =
        (⟨HTGeometry.ConstraintMotiveRelativity.srcEmb l, hmem⟩ :
          LinearMap.range
            (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes))) :=
    Subtype.ext rfl
  have hsymm :
      (LinearEquiv.ofInjective _ primeLogCritical_srcEmb_injective).symm
          (⟨HTGeometry.ConstraintMotiveRelativity.srcEmb l, hmem⟩ :
            LinearMap.range
              (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes))) = l := by
    rw [← hval, LinearEquiv.symm_apply_apply]
  exact congrArg primeLogCriticalLaplaceMass hsymm

/-- Literal finite-prime core is dense in the source Hilbert chart. -/
theorem dense_primeLogCriticalLaplaceSynthesis_domain :
    Dense (primeLogCriticalLaplaceSynthesis.domain :
      Set primeLogCriticalSourceL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [Submodule.eq_top_iff']
  intro f
  have hsum := lp.hasSum_single
    (E := fun _ : Nat.Primes => ℂ) (p := 2) (by norm_num) f
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto hsum
  apply Filter.Eventually.of_forall
  intro s
  let l : Nat.Primes →₀ ℂ :=
    ∑ p ∈ s, Finsupp.single p ((f : Nat.Primes → ℂ) p)
  refine ⟨l, ?_⟩
  simp only [l, map_sum,
    HTGeometry.ConstraintMotiveRelativity.srcEmb_single,
    HTGeometry.ConstraintMotiveRelativity.srcBasis]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← lp.single_smul]
  simp

/-- A sequential zero-fibre criterion constructs the closed graph rather than assuming it. -/
theorem LinearPMap.isClosable_of_tendsto_graph_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →ₗ.[ℂ] F)
    (hzero : ∀ (x : ℕ → T.domain) (y : F),
      Tendsto (fun n => (x n : E)) atTop (nhds 0) →
      Tendsto (fun n => T (x n)) atTop (nhds y) → y = 0) :
    T.IsClosable := by
  let G := T.graph.topologicalClosure
  have hvertical : ∀ (z : E × F), z ∈ G → z.fst = 0 → z.snd = 0 := by
    intro z hz hz0
    obtain ⟨w, hwG, hw⟩ := mem_closure_iff_seq_limit.mp hz
    have hwfst : Tendsto (fun n => (w n).fst) atTop (nhds z.fst) :=
      (continuous_fst.tendsto z).comp hw
    have hwsnd : Tendsto (fun n => (w n).snd) atTop (nhds z.snd) :=
      (continuous_snd.tendsto z).comp hw
    have hdom : ∀ n, (w n).fst ∈ T.domain := fun n =>
      LinearPMap.mem_domain_of_mem_graph (hwG n)
    let x : ℕ → T.domain := fun n => ⟨(w n).fst, hdom n⟩
    have happ : ∀ n, T (x n) = (w n).snd := by
      intro n
      obtain ⟨v, hv1, hv2⟩ := T.mem_graph_iff.mp (hwG n)
      have hxv : x n = v := Subtype.ext hv1.symm
      rw [hxv]
      exact hv2
    apply hzero x z.snd
    · simpa [x, hz0] using hwfst
    · simpa only [happ] using hwsnd
  refine ⟨G.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq G hvertical).symm

end

end RHTower
