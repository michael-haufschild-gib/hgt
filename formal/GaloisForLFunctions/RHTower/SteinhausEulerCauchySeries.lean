import GaloisForLFunctions.RHTower.SteinhausEulerCauchyKernel
import GaloisForLFunctions.RHTower.SteinhausEulerCauchyMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open MeasureTheory Complex
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

local notation "ν" => ProbabilityTheory.cauchyMeasure (0 : ℝ) (1 / 2)

private def criticalTerm (ω : Omega) (n : ℕ) (t : ℝ) : ℂ :=
  steinhausEulerPrimeTerm ((1 / 2 : ℂ) + (t : ℂ) * I) ω n

private def criticalProduct (N : ℕ) (ω : Omega) (t : ℝ) : ℂ :=
  steinhausFiniteEulerProduct (Nat.primesBelow N) ((1 / 2 : ℂ) + (t : ℂ) * I) ω

private theorem criticalTerm_norm {n : ℕ} (hn : 0 < n) (ω : Omega) (t : ℝ) :
    ‖criticalTerm ω n t‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold criticalTerm
  rw [norm_steinhausEulerPrimeTerm hn]
  norm_num

private theorem measurable_criticalTerm {n : ℕ} (hn : 0 < n) (ω : Omega) :
    Measurable (criticalTerm ω n) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold criticalTerm steinhausEulerPrimeTerm
  simp_rw [Complex.cpow_def_of_ne_zero hnc]
  fun_prop

private theorem measurable_criticalProduct (N : ℕ) (ω : Omega) :
    Measurable (criticalProduct N ω) := by
  unfold criticalProduct steinhausFiniteEulerProduct
  apply Finset.measurable_prod
  intro p hp
  exact (measurable_const.sub
    (measurable_criticalTerm (Nat.mem_primesBelow.mp hp).2.pos ω)).inv

private theorem criticalProduct_norm_le (N : ℕ) (ω : Omega) (t : ℝ) :
    ‖criticalProduct N ω t‖ ≤ ∑' n : Nat.smoothNumbers N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < ((1 / 2 : ℂ) + (t : ℂ) * I).re := by norm_num
  have heq := (hasSum_steinhausEulerSmoothSeries N hs ω).tsum_eq
  have hsum := summable_norm_steinhausEulerSmoothSeries N hs ω
  have hbound := norm_tsum_le_tsum_norm hsum
  rw [heq] at hbound
  have hn : (fun n : Nat.smoothNumbers N =>
      ‖steinhausEulerPrimeTerm ((1 / 2 : ℂ) + (t : ℂ) * I) ω n‖) =
      (fun n : Nat.smoothNumbers N => (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    funext n
    exact criticalTerm_norm (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)) ω t
  rw [hn] at hbound
  exact hbound

private theorem integrable_criticalNormSq (N : ℕ) (ω : Omega) :
    Integrable (fun t => ‖criticalProduct N ω t‖ ^ (2 : ℕ)) ν := by
  let C := ∑' n : Nat.smoothNumbers N, (n : ℝ) ^ (-(1 / 2 : ℝ))
  refine Integrable.mono' (integrable_const (C ^ (2 : ℕ)))
    ((measurable_criticalProduct N ω).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with t
  have h := criticalProduct_norm_le N ω t
  change ‖criticalProduct N ω t‖ ≤ C at h
  have hC : 0 ≤ C := (norm_nonneg _).trans h
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (criticalProduct N ω t)]

private theorem criticalPair_norm {a c : ℕ} (ha : 0 < a) (hc : 0 < c) (ω : Omega) (t : ℝ) :
    ‖criticalTerm ω a t * (starRingEnd ℂ) (criticalTerm ω c t)‖ =
      (a : ℝ) ^ (-(1 / 2 : ℝ)) * (c : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_mul, Complex.norm_conj, criticalTerm_norm ha, criticalTerm_norm hc]

private theorem integrable_criticalPair {a c : ℕ} (ha : 0 < a) (hc : 0 < c) (ω : Omega) :
    Integrable (fun t => criticalTerm ω a t * (starRingEnd ℂ) (criticalTerm ω c t)) ν := by
  have hm : Measurable (fun t => criticalTerm ω a t * (starRingEnd ℂ) (criticalTerm ω c t)) := by
    have h := (measurable_criticalTerm ha ω).mul
      (Complex.continuous_conj.measurable.comp (measurable_criticalTerm hc ω))
    convert h using 1
    ext t
    rfl
  refine Integrable.mono' (integrable_const
    ((a : ℝ) ^ (-(1 / 2 : ℝ)) * (c : ℝ) ^ (-(1 / 2 : ℝ)))) hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun t => (criticalPair_norm ha hc ω t).le)

private theorem integral_criticalPair {a c : ℕ} (ha : 0 < a) (hc : 0 < c) (ω : Omega) :
    (∫ t, criticalTerm ω a t * (starRingEnd ℂ) (criticalTerm ω c t) ∂ν) =
      X a ω * (starRingEnd ℂ) (X c ω) / (max a c : ℕ) := by
  have hpoint (t : ℝ) : criticalTerm ω a t * (starRingEnd ℂ) (criticalTerm ω c t) =
      (X a ω * (starRingEnd ℂ) (X c ω)) *
        ((a : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)) *
          (starRingEnd ℂ) ((c : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)))) := by
    simp only [criticalTerm, steinhausEulerPrimeTerm, map_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul]
  have hkernel := integral_halfCauchy_criticalPower_pair
    (by exact_mod_cast ha : (0 : ℝ) < a) (by exact_mod_cast hc : (0 : ℝ) < c)
  rw [← Nat.cast_max] at hkernel
  norm_cast at hkernel
  rw [hkernel]
  simp only [div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Exact smooth-pair expansion of the literal whole-line squared Euler integral. -/
theorem integral_steinhausEulerCauchy_normSq_eq_smoothPair (N : ℕ) (ω : Omega) :
    ((∫ t, ‖steinhausFiniteEulerProduct (Nat.primesBelow N)
      ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ (2 : ℕ) ∂ν : ℝ) : ℂ) =
      ∑' ac : Nat.smoothNumbers N × Nat.smoothNumbers N,
        X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ) := by
  have hpos (n : Nat.smoothNumbers N) : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  have hnormsum : Summable (fun ac : Nat.smoothNumbers N × Nat.smoothNumbers N =>
      ∫ t, ‖criticalTerm ω ac.1 t * (starRingEnd ℂ) (criticalTerm ω ac.2 t)‖ ∂ν) := by
    have h := summable_smoothNumbers_neg_rpow N (σ := 1 / 2) (by norm_num)
    have hp := h.mul_of_nonneg h (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have heq : (fun ac : Nat.smoothNumbers N × Nat.smoothNumbers N =>
        ∫ t, ‖criticalTerm ω ac.1 t * (starRingEnd ℂ) (criticalTerm ω ac.2 t)‖ ∂ν) =
        (fun ac : Nat.smoothNumbers N × Nat.smoothNumbers N =>
          (ac.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (ac.2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
      funext ac
      simp_rw [criticalPair_norm (hpos ac.1) (hpos ac.2)]
      simp
    rw [heq]
    exact hp
  have hswap := integral_tsum_of_summable_integral_norm
    (fun ac : Nat.smoothNumbers N × Nat.smoothNumbers N =>
      integrable_criticalPair (hpos ac.1) (hpos ac.2) ω) hnormsum
  have hpoint (t : ℝ) : ((‖criticalProduct N ω t‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑' ac : Nat.smoothNumbers N × Nat.smoothNumbers N,
        criticalTerm ω ac.1 t * (starRingEnd ℂ) (criticalTerm ω ac.2 t) := by
    have hs : 0 < ((1 / 2 : ℂ) + (t : ℂ) * I).re := by norm_num
    have hsum := summable_norm_steinhausEulerSmoothSeries N hs ω
    change Summable (fun n : Nat.smoothNumbers N => ‖criticalTerm ω n t‖) at hsum
    have heq := (hasSum_steinhausEulerSmoothSeries N hs ω).tsum_eq
    have hprod : criticalProduct N ω t * (starRingEnd ℂ) (criticalProduct N ω t) =
        ((‖criticalProduct N ω t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [← hprod]
    change _ * _ = _
    change (∑' n : Nat.smoothNumbers N, criticalTerm ω n t) = criticalProduct N ω t at heq
    rw [← heq, Complex.conj_tsum]
    exact tsum_mul_tsum_of_summable_norm hsum (by simpa only [Complex.norm_conj] using hsum)
  calc
    _ = ∫ t, ((‖criticalProduct N ω t‖ ^ (2 : ℕ) : ℝ) : ℂ) ∂ν := integral_complex_ofReal.symm
    _ = ∫ t, ∑' ac : Nat.smoothNumbers N × Nat.smoothNumbers N,
        criticalTerm ω ac.1 t * (starRingEnd ℂ) (criticalTerm ω ac.2 t) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := by
      rw [← hswap]
      apply tsum_congr
      intro ac
      exact integral_criticalPair (hpos ac.1) (hpos ac.2) ω

/-- The arithmetic maximum kernel is exactly the original normalized Cauchy mass. -/
theorem steinhausEulerCauchyMass_eq_smoothPair (N : ℕ) (ω : Omega) :
    steinhausEulerCauchyMass N ω = ENNReal.ofReal
      ((steinhausEulerPartition (Nat.primesBelow N) (1 / 2))⁻¹ *
        (∑' ac : Nat.smoothNumbers N × Nat.smoothNumbers N,
          X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) /
            (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)).re) := by
  let M := steinhausEulerPartition (Nat.primesBelow N) (1 / 2)
  have hM : 0 < M := steinhausEulerPartition_pos _
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (by norm_num)
  have hi : Integrable (fun t => ‖criticalProduct N ω t‖ ^ (2 : ℕ) / M) ν := by
    simpa only [div_eq_mul_inv] using (integrable_criticalNormSq N ω).mul_const M⁻¹
  have hnonneg : 0 ≤ᵐ[ν] (fun t => ‖criticalProduct N ω t‖ ^ (2 : ℕ) / M) :=
    Filter.Eventually.of_forall (fun t => div_nonneg (sq_nonneg _) hM.le)
  change (∫⁻ t, ENNReal.ofReal (‖criticalProduct N ω t‖ ^ (2 : ℕ) / M) ∂ν) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg, integral_div]
  have hre := congrArg Complex.re (integral_steinhausEulerCauchy_normSq_eq_smoothPair N ω)
  simp only [Complex.ofReal_re] at hre
  change (∫ t, ‖criticalProduct N ω t‖ ^ (2 : ℕ) ∂ν) = _ at hre
  rw [hre]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

end RHTower
