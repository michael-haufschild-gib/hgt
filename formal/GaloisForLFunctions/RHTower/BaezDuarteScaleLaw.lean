import GaloisForLFunctions.RHTower.BaezDuarteWaveletPairing
import GaloisForLFunctions.RHTower.MobiusWeightedMomentZeroFree

/-!
# Exact beta values and the Cauchy--Schwarz scale law

The beta shift `B(a+1,n+1) = B(a,n+1)(a+1)/(a+n+2)` turns the three-term expansion of the weighted
wavelet norm into a single rational multiple of `B(a,n+1)`, whose numerator has leading coefficient
`α²+α+1`.  At `α = 0` everything cancels to `1/(2(2k+1))`, and Cauchy--Schwarz against the
critical Möbius boundary vector gives the unconditional `k^{-1/2}` law.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

/-- The falling product in the beta evaluation. -/
def bdBetaProd (a : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range (n + 1), (a + 1 + (j : ℝ))

theorem bdBetaProd_pos {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 < bdBetaProd a n := by
  refine Finset.prod_pos fun j _ => ?_
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem bdBeta_eq_prod {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    bdBeta a n = (n.factorial : ℝ) / bdBetaProd a n := bdBeta_eq ha n

theorem bdBetaProd_shift (a : ℝ) (n : ℕ) :
    bdBetaProd (a + 1) n * (a + 1) = bdBetaProd a n * (a + (n : ℝ) + 2) := by
  have hkey : (∏ i ∈ Finset.range (n + 2), (a + 1 + (i : ℝ)))
      = (∏ i ∈ Finset.range (n + 1), (a + 1 + ((i : ℝ) + 1))) * (a + 1 + 0) := by
    have h := Finset.prod_range_succ' (fun i : ℕ => a + 1 + (i : ℝ)) (n + 1)
    simpa using h
  have hkey2 : (∏ i ∈ Finset.range (n + 2), (a + 1 + (i : ℝ)))
      = (∏ i ∈ Finset.range (n + 1), (a + 1 + (i : ℝ))) * (a + 1 + ((n : ℝ) + 1)) := by
    have h := Finset.prod_range_succ (fun i : ℕ => a + 1 + (i : ℝ)) (n + 1)
    rw [h]
    congr 1
    push_cast
    ring
  have hprod : (∏ i ∈ Finset.range (n + 1), (a + 1 + ((i : ℝ) + 1))) = bdBetaProd (a + 1) n := by
    rw [bdBetaProd]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hkey, hprod] at hkey2
  rw [bdBetaProd]
  have : bdBetaProd (a + 1) n * (a + 1 + 0)
      = (∏ i ∈ Finset.range (n + 1), (a + 1 + (i : ℝ))) * (a + 1 + ((n : ℝ) + 1)) := hkey2
  rw [bdBetaProd] at this ⊢
  linarith [this]

/-- **The beta shift.**  Raising the first parameter by one. -/
theorem bdBeta_succ {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    bdBeta (a + 1) n = bdBeta a n * (a + 1) / (a + (n : ℝ) + 2) := by
  have ha1 : (0 : ℝ) ≤ a + 1 := by linarith
  have hP := bdBetaProd_pos ha n
  have hP1 := bdBetaProd_pos ha1 n
  have hden : (0 : ℝ) < a + (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [bdBeta_eq_prod ha1, bdBeta_eq_prod ha]
  rw [div_mul_eq_mul_div, div_div, eq_div_iff (by positivity)]
  have hshift := bdBetaProd_shift a n
  field_simp
  nlinarith [hshift, hP, hP1]

theorem bdBetaProd_zero (n : ℕ) : bdBetaProd 0 n = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp [bdBetaProd]
  | succ n ih =>
    rw [bdBetaProd, Finset.prod_range_succ, ← bdBetaProd, ih]
    have h1 : ((n + 1 + 1).factorial : ℝ) = ((n + 2 : ℕ) : ℝ) * (((n + 1).factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [h1]
    push_cast
    ring

theorem bdBeta_zero (n : ℕ) : bdBeta 0 n = 1 / ((n : ℝ) + 1) := by
  rw [bdBeta_eq_prod le_rfl, bdBetaProd_zero, Nat.factorial_succ]
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  push_cast
  field_simp

theorem bdBeta_one (n : ℕ) : bdBeta 1 n = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have h := bdBeta_succ (a := 0) le_rfl n
  rw [zero_add] at h
  rw [h, bdBeta_zero]
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  field_simp
  ring

theorem bdBeta_two (n : ℕ) :
    bdBeta 2 n = 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have h := bdBeta_succ (a := 1) (by norm_num) n
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
  rw [h, bdBeta_one]
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  field_simp
  ring

/-- **Equation (10) at `α = 0`.**  The unweighted `L²` norm of the beta wavelet is exactly
`1/(2(2k+1))`. -/
theorem integral_bdKernel_sq (k : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), (bdKernel k t) ^ 2) = 1 / (2 * (2 * (k : ℝ) + 1)) := by
  have h := integral_bdKernel_weighted_sq_eq k (α := 0) le_rfl
  have hlhs : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-((0 : ℝ) * t)) * bdKernel k t) ^ 2)
      = ∫ t in Set.Ioi (0 : ℝ), (bdKernel k t) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    norm_num
  rw [hlhs] at h
  norm_num at h
  rw [h, bdBeta_zero, bdBeta_one, bdBeta_two]
  have hc : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [hc]
  have h1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
  have h3 : (0 : ℝ) < 2 * (k : ℝ) + 3 := by positivity
  field_simp
  ring

/-- **Equation (10).**  The closed form of the weighted `L²` norm: the leading numerator
coefficient is `α² + α + 1`. -/
theorem integral_bdKernel_weighted_sq_closed (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-(α * t)) * bdKernel k t) ^ 2)
      = (bdBeta α (2 * k) / 2)
        * (((α ^ 2 + α + 1) * (2 * (k : ℝ) + 3) ^ 2 - (2 * α ^ 2 + 1) * (2 * (k : ℝ) + 3)
              + (α ^ 2 - α))
           / ((α + 2 * (k : ℝ) + 2) * (α + 2 * (k : ℝ) + 3))) := by
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have hc : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  have hs1 := bdBeta_succ hα (2 * k)
  have hs2 := bdBeta_succ hα1 (2 * k)
  rw [hc] at hs1 hs2
  have hu : (0 : ℝ) < α + 2 * (k : ℝ) + 2 := by positivity
  have hv : (0 : ℝ) < α + 2 * (k : ℝ) + 3 := by positivity
  have hs2' : bdBeta (α + 2) (2 * k)
      = bdBeta α (2 * k) * (α + 1) * (α + 2)
        / ((α + 2 * (k : ℝ) + 2) * (α + 2 * (k : ℝ) + 3)) := by
    rw [show (α + 1 + 1 : ℝ) = α + 2 by ring] at hs2
    rw [hs2, hs1]
    field_simp
    ring
  rw [integral_bdKernel_weighted_sq_eq k hα, hs1, hs2']
  field_simp
  ring

/-! ## The Cauchy--Schwarz consequence -/

/-- The `e^{-αt}`-weighted beta wavelet vector. -/
def weightedBdKernelVector (α : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-(α * t)) : ℝ) : ℂ) * bdKernelVector k t

theorem weightedMertens_mul_weightedKernel (α : ℝ) (k : ℕ) (t : ℝ) :
    weightedMertensVector α t * weightedBdKernelVector α k t
      = criticalMertensVector t * bdKernelVector k t := by
  have hone : ((Real.exp (α * t) : ℂ)) * ((Real.exp (-(α * t)) : ℝ) : ℂ) = 1 := by
    rw [show ((Real.exp (α * t) : ℂ)) = ((Real.exp (α * t) : ℝ) : ℂ) from rfl,
      ← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [weightedMertensVector, weightedBdKernelVector]
  calc ((Real.exp (α * t) : ℂ)) * criticalMertensVector t
        * (((Real.exp (-(α * t)) : ℝ) : ℂ) * bdKernelVector k t)
      = (((Real.exp (α * t) : ℂ)) * ((Real.exp (-(α * t)) : ℝ) : ℂ))
          * (criticalMertensVector t * bdKernelVector k t) := by ring
    _ = criticalMertensVector t * bdKernelVector k t := by rw [hone, one_mul]

theorem memLp_weightedBdKernelVector {α : ℝ} (hα : 0 ≤ α) (k : ℕ) :
    MeasureTheory.MemLp (weightedBdKernelVector α k) 2 MeasureTheory.volume := by
  refine MeasureTheory.MemLp.of_le (memLp_bdKernelVector k) ?_ ?_
  · refine (Measurable.mul ?_ (measurable_bdKernelVector k)).aestronglyMeasurable
    exact Complex.continuous_ofReal.measurable.comp
      ((Real.continuous_exp.comp (by fun_prop)).measurable)
  · filter_upwards with t
    rw [weightedBdKernelVector, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · have hle : Real.exp (-(α * t)) ≤ 1 := by
        have h : Real.exp (-(α * t)) ≤ Real.exp 0 := by
          refine Real.exp_le_exp.mpr ?_
          have : (0 : ℝ) < t := ht
          nlinarith
        rwa [Real.exp_zero] at h
      nlinarith [norm_nonneg (bdKernelVector k t)]
    · rw [bdKernelVector, Set.indicator_of_notMem ht, norm_zero]
      simp

theorem integral_weighted_eq_bdCoeff (α : ℝ) (k : ℕ) :
    (∫ t : ℝ, weightedMertensVector α t * weightedBdKernelVector α k t) = bdCoeff (k + 1) := by
  have hfun : (fun t : ℝ => weightedMertensVector α t * weightedBdKernelVector α k t)
      = Set.indicator (Set.Ioi (0 : ℝ))
          (fun t : ℝ => mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ)) := by
    funext t
    rw [weightedMertens_mul_weightedKernel]
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, criticalMertensVector, Set.indicator_of_mem ht,
        bdKernelVector, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, criticalMertensVector, Set.indicator_of_notMem ht,
        zero_mul]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi,
    integral_criticalMertens_bdKernel]

/-- The weighted domain condition `(11)` gives global `L²` membership, because the weighted
vector vanishes off the positive ray. -/
theorem memLp_weightedMertensVector_of_moment {α : ℝ} (h : WeightedMertensMoment α) :
    MeasureTheory.MemLp (weightedMertensVector α) 2 MeasureTheory.volume := by
  have hind : Set.indicator (Set.Ioi (0 : ℝ)) (weightedMertensVector α)
      = weightedMertensVector α := by
    funext t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, weightedMertensVector, criticalMertensVector,
        Set.indicator_of_notMem ht, mul_zero]
  rw [← hind]
  exact (MeasureTheory.memLp_indicator_iff_restrict measurableSet_Ioi).mpr h

/-- **Equations (11)–(12).**  Cauchy--Schwarz between the weighted Möbius boundary vector and the
weighted beta wavelet. -/
theorem norm_bdCoeff_le_weighted (k : ℕ) {α : ℝ} (hα : 0 ≤ α)
    (hmom : WeightedMertensMoment α) :
    ‖bdCoeff (k + 1)‖
      ≤ (∫ t : ℝ, ‖weightedMertensVector α t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫ t : ℝ, ‖weightedBdKernelVector α k t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hm := memLp_weightedMertensVector_of_moment hmom
  have hk := memLp_weightedBdKernelVector hα k
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hm2 : MeasureTheory.MemLp (weightedMertensVector α) (ENNReal.ofReal 2)
      MeasureTheory.volume := by
    simpa using hm
  have hk2 : MeasureTheory.MemLp (weightedBdKernelVector α k) (ENNReal.ofReal 2)
      MeasureTheory.volume := by
    simpa using hk
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hconj hm2 hk2
  rw [← integral_weighted_eq_bdCoeff α k]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine le_trans (le_of_eq ?_) hholder
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [norm_mul]

theorem integral_norm_sq_weightedBdKernelVector_zero (k : ℕ) :
    (∫ t : ℝ, ‖weightedBdKernelVector 0 k t‖ ^ (2 : ℝ)) = 1 / (2 * (2 * (k : ℝ) + 1)) := by
  have hfun : (fun t : ℝ => ‖weightedBdKernelVector 0 k t‖ ^ (2 : ℝ))
      = Set.indicator (Set.Ioi (0 : ℝ)) (fun t : ℝ => (bdKernel k t) ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, weightedBdKernelVector, bdKernelVector,
        Set.indicator_of_mem ht]
      norm_num
    · rw [Set.indicator_of_notMem ht, weightedBdKernelVector, bdKernelVector,
        Set.indicator_of_notMem ht, mul_zero, norm_zero]
      rw [Real.zero_rpow (by norm_num)]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi, integral_bdKernel_sq]

/-- **Equation (13).**  The unconditional `k^{-1/2}` scale law for the Báez--Duarte coefficients. -/
theorem norm_bdCoeff_le_unconditional (k : ℕ) :
    ‖bdCoeff (k + 1)‖
      ≤ (∫ t : ℝ, ‖criticalMertensVector t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (1 / (2 * (2 * (k : ℝ) + 1))) ^ ((1 : ℝ) / 2) := by
  have h := norm_bdCoeff_le_weighted k (α := 0) le_rfl weightedMertensMoment_zero
  rwa [weightedMertensVector_zero, integral_norm_sq_weightedBdKernelVector_zero] at h

end

end RHTower
