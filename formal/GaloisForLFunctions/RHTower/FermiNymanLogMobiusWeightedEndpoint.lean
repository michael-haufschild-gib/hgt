import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead
import GaloisForLFunctions.RHTower.ChebyshevDyadicWeightedEnergy
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovLinearL1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic Möbius Fermi approximation in the weighted endpoint norm

The literal approximation with coefficients `μ(d) log(N/d)/log N` converges to Haar
in `L²(t dt)`. The bound is `(N+1)⁻² + (C+9)/(log N)²`, where `C` is the finite,
nonnegative dyadic Chebyshev source energy. The exact head identity and a linear
Barban–Vehov coefficient-mass bound control the two pieces separately.

This theorem is unconditional. Its extra factor `t` remains part of the conclusion;
no convergence in the canonical PM norm `L²(dt)` follows from this bound alone.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
noncomputable section
namespace RHTower

theorem norm_logMobiusFermiApprox_le_linear (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖logMobiusFermiApprox N t‖ ≤ 3 * (N : ℝ) / Real.log N := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hs : (∑ d ∈ Finset.Icc 1 N,
      ‖((((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((N : ℝ) / d) /
        Real.log N : ℝ) : ℂ)‖ * 3) =
      (∑ d ∈ Finset.Icc 1 N, |Sieve.barbanVehovWeight N d|) * (3 / Real.log N) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Sieve.barbanVehovWeight, if_pos (Finset.mem_Icc.mp hd).2,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlog]
    ring
  calc
    _ ≤ _ := norm_logMobiusFermiApprox_le N t
    _ = _ := hs
    _ ≤ (N : ℝ) * (3 / Real.log N) := mul_le_mul_of_nonneg_right
      (Sieve.sum_abs_barbanVehovWeight_le_linear (by omega)) (by positivity)
    _ = _ := by ring

theorem norm_dyadicHaar_sub_logMobiusFermiApprox_le (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖dyadicHaar t - logMobiusFermiApprox N t‖ ≤ 1 + 3 * (N : ℝ) / Real.log N := by
  calc
    _ ≤ ‖dyadicHaar t‖ + ‖logMobiusFermiApprox N t‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_dyadicHaar]
      exact add_le_add le_rfl (norm_logMobiusFermiApprox_le_linear N hN t)

theorem integrableOn_weighted_logMobiusFermiError (N : ℕ) :
    IntegrableOn (fun t : ℝ => t * ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2)
      (Ioc 0 1) := by
  refine (integrableOn_normSq_dyadicHaar_sub_logMobiusFermiApprox N).mono'
    (measurable_id.mul ((measurable_dyadicHaar.sub
      (measurable_logMobiusFermiApprox N)).norm.pow_const 2)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1.le (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) ht.2

/-- The literal logarithmic Fermi error measured in `t dt`. -/
def weightedLogMobiusFermiErrorEnergy (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, t * ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2

theorem weightedLogMobiusFermiErrorEnergy_nonneg (N : ℕ) :
    0 ≤ weightedLogMobiusFermiErrorEnergy N :=
  setIntegral_nonneg measurableSet_Ioc (fun _ ht => mul_nonneg ht.1.le (sq_nonneg _))

/-- A finite arithmetic source constant, independent of the approximation cutoff. -/
def dyadicChebyshevWeightedEnergy : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1,
    t * (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2

theorem dyadicChebyshevWeightedEnergy_nonneg : 0 ≤ dyadicChebyshevWeightedEnergy :=
  setIntegral_nonneg measurableSet_Ioc (fun _ ht => mul_nonneg ht.1.le (sq_nonneg _))

theorem weightedLogMobiusFermiErrorEnergy_head_le (N : ℕ) (hN : 2 ≤ N) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
      t * ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) ≤
      dyadicChebyshevWeightedEnergy / Real.log N ^ 2 := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have heq : (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
      t * ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) =
      (1 / Real.log N ^ 2) * ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
        t * (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp
    rw [dyadicHaar_sub_logMobiusFermiApprox N hN ht.1 ht.2,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
    ring
  rw [heq, show dyadicChebyshevWeightedEnergy / Real.log (N : ℝ) ^ 2 =
    (1 / Real.log (N : ℝ) ^ 2) * dyadicChebyshevWeightedEnergy by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold dyadicChebyshevWeightedEnergy
  apply setIntegral_mono_set integrableOn_weighted_dyadicChebyshevError
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg ht.1.le (sq_nonneg _)
  · exact Filter.Eventually.of_forall (Ioc_subset_Ioc hc0 le_rfl)

theorem weightedLogMobiusFermiErrorEnergy_tail_le (N : ℕ) (hN : 2 ≤ N) :
    (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      t * ‖dyadicHaar t - logMobiusFermiApprox N t‖ ^ 2) ≤
      (1 / ((N : ℝ) + 1)) ^ 2 + 9 / Real.log N ^ 2 := by
  let c : ℝ := 1 / ((N : ℝ) + 1)
  let b : ℝ := 3 * (N : ℝ) / Real.log N
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one (by positivity)).mpr
    (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have ht : IntegrableOn (fun t : ℝ => t) (Ioc 0 c) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      measurable_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_pos ht.1]
    exact ht.2.trans hc1
  have hint : (∫ t in Ioc (0 : ℝ) c, t) = c ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hc0, integral_id]
    norm_num
  have hi := (integrableOn_weighted_logMobiusFermiError N).mono_set
    (Ioc_subset_Ioc le_rfl hc1)
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) c, t * (1 + b) ^ 2 := by
      apply setIntegral_mono_on hi (ht.mul_const _) measurableSet_Ioc
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicHaar_sub_logMobiusFermiApprox_le N hN t) 2)
        ht.1.le
    _ = c ^ 2 / 2 * (1 + b) ^ 2 := by rw [integral_mul_const, hint]
    _ ≤ c ^ 2 * (1 + b ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]
    _ = c ^ 2 + (9 / Real.log N ^ 2) * ((N : ℝ) / (N + 1)) ^ 2 := by
      dsimp [c, b]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      have hn : (N : ℝ) / (N + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have hn0 : 0 ≤ (N : ℝ) / (N + 1) := by positivity
      simpa using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hn 2)
        (by positivity : 0 ≤ 9 / Real.log (N : ℝ) ^ 2)

/-- Explicit unconditional convergence rate in the weighted norm `t dt`. -/
theorem weightedLogMobiusFermiErrorEnergy_le (N : ℕ) (hN : 2 ≤ N) :
    weightedLogMobiusFermiErrorEnergy N ≤ (1 / ((N : ℝ) + 1)) ^ 2 +
      (dyadicChebyshevWeightedEnergy + 9) / Real.log N ^ 2 := by
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hi := integrableOn_weighted_logMobiusFermiError N
  rw [weightedLogMobiusFermiErrorEnergy, ← Ioc_union_Ioc_eq_Ioc hc0 hc1,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hi.mono_set (Ioc_subset_Ioc le_rfl hc1)) (hi.mono_set (Ioc_subset_Ioc hc0 le_rfl))]
  calc
    _ ≤ _ := add_le_add (weightedLogMobiusFermiErrorEnergy_tail_le N hN)
      (weightedLogMobiusFermiErrorEnergy_head_le N hN)
    _ = _ := by ring

theorem tendsto_weightedLogMobiusFermiErrorEnergy_zero :
    Tendsto weightedLogMobiusFermiErrorEnergy atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcut : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 hcast)
  have hlog : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hcast)
  have hrate : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) ^ 2 +
      (dyadicChebyshevWeightedEnergy + 9) / Real.log N ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hcut.pow 2).add (hlog.pow 2 |>.const_mul
      (dyadicChebyshevWeightedEnergy + 9))
  apply squeeze_zero' (Filter.Eventually.of_forall weightedLogMobiusFermiErrorEnergy_nonneg)
    _ hrate
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact weightedLogMobiusFermiErrorEnergy_le N hN

end RHTower
