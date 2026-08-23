import GaloisForLFunctions.RHTower.BaezDuarteWaveletNorm
import GaloisForLFunctions.RHTower.BaezDuarteMobiusSeries
import GaloisForLFunctions.RHTower.MobiusCenteredMertensLimit
import GaloisForLFunctions.RHTower.MobiusCausalSourceLimit
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# The Báez--Duarte coefficient as a critical Möbius wavelet pairing

Abel summation on `[0, T]` writes the pairing of the critical Möbius boundary vector
`m_0(t) = Σ_{n ≤ e^t} μ(n)/n` against the beta wavelet as a partial Möbius sum minus a boundary
term.  The boundary term is `O(e^{-T/2})` because `|m_0(T)| ≤ 2 e^{T/2}`, so letting `T → ∞` gives
the exact value relation `∫_0^∞ m_0 K_{k+1} = c_{k+1}`.
-/

namespace RHTower

open Real MeasureTheory ArithmeticFunction

noncomputable section

theorem continuous_bdKernel (k : ℕ) : Continuous (bdKernel k) := by
  unfold bdKernel
  fun_prop

theorem intervalIntegrable_bdKernel (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (bdKernel k) MeasureTheory.volume a b :=
  (continuous_bdKernel k).intervalIntegrable a b

/-- The fundamental theorem of calculus for the beta wavelet. -/
theorem integral_bdKernel (k : ℕ) (a b : ℝ) :
    ∫ t in a..b, bdKernel k t = bdWavelet (k + 1) a - bdWavelet (k + 1) b := by
  have hneg : ∫ t in a..b, -(bdKernel k t) = bdWavelet (k + 1) b - bdWavelet (k + 1) a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_bdWavelet k x) ?_
    exact (intervalIntegrable_bdKernel k a b).neg
  rw [intervalIntegral.integral_neg] at hneg
  linarith

/-- The wavelet primitive at a logarithmic jump. -/
theorem bdWavelet_log_natCast (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    bdWavelet (k + 1) (Real.log n) = (1 / (n : ℝ)) * (1 - 1 / (n : ℝ) ^ 2) ^ (k + 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.exp (-Real.log n) = 1 / (n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hn0, one_div]
  have h2 : Real.exp (-2 * Real.log n) = 1 / (n : ℝ) ^ 2 := by
    rw [show -2 * Real.log (n : ℝ) = -(2 * Real.log (n : ℝ)) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), one_div]
  rw [bdWavelet, h1, h2]

theorem measurable_jumpKernel (k : ℕ) (a : ℝ) :
    Measurable (fun t : ℝ => (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t) := by
  refine Measurable.mul ?_ (continuous_bdKernel k).measurable
  exact measurable_const.piecewise (measurableSet_le measurable_const measurable_id) measurable_const

theorem intervalIntegrable_jumpKernel (k : ℕ) (a b c : ℝ) :
    IntervalIntegrable (fun t : ℝ => (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t)
      MeasureTheory.volume b c := by
  refine (intervalIntegrable_bdKernel k b c).mono_fun
    (measurable_jumpKernel k a).aestronglyMeasurable ?_
  filter_upwards with t
  by_cases h : a ≤ t
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul, norm_zero]
    exact norm_nonneg _

/-- The jump indicator integrates the wavelet kernel from the jump to the endpoint. -/
theorem integral_jump_bdKernel (k : ℕ) {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (∫ t in (0 : ℝ)..T, (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t)
      = bdWavelet (k + 1) a - bdWavelet (k + 1) T := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_jumpKernel k a 0 a) (intervalIntegrable_jumpKernel k a a T)
  have hae : ∀ᵐ t : ℝ, t ≠ a := by
    have hm : MeasureTheory.volume ({a} : Set ℝ) = 0 := MeasureTheory.measure_singleton a
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hm] with t ht
    simpa using ht
  have hlow : (∫ t in (0 : ℝ)..a, (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t) = 0 := by
    have hcong : (∫ t in (0 : ℝ)..a, (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t)
        = ∫ _t in (0 : ℝ)..a, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with t hne ht
      rw [Set.uIoc_of_le ha] at ht
      have hlt : t < a := lt_of_le_of_ne ht.2 hne
      rw [if_neg (by linarith), zero_mul]
    rw [hcong, intervalIntegral.integral_zero]
  have hhigh : (∫ t in a..T, (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t)
      = ∫ t in a..T, bdKernel k t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le haT] at ht
    show (if a ≤ t then (1 : ℝ) else 0) * bdKernel k t = bdKernel k t
    rw [if_pos ht.1, one_mul]
  rw [hlow, hhigh, integral_bdKernel] at hsplit
  linarith [hsplit]

/-! ## The finite-aperture pairing -/

theorem log_le_iff_le_floor {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Real.log n ≤ t ↔ n ≤ ⌊Real.exp t⌋₊ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Nat.le_floor_iff (Real.exp_pos t).le]
  constructor
  · intro h
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr h
  · intro h
    have := Real.log_le_log hn0 h
    rwa [Real.log_exp] at this

theorem mobiusPartial_eq_jumpSum {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    mobiusWeightedPartial 1 t
      = ∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
          ((if Real.log n ≤ t then (1 : ℝ) else 0) : ℂ) * mobiusRealWeight 1 n := by
  have hfloor : ⌊Real.exp t⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr htT)
  have hfilter : (Finset.range (⌊Real.exp T⌋₊ + 1)).filter (fun n : ℕ => Real.log n ≤ t)
      = Finset.range (⌊Real.exp t⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Real.log_zero]
      constructor
      · intro _; omega
      · intro _; exact ⟨by omega, ht⟩
    · rw [log_le_iff_le_floor hn]
      constructor
      · rintro ⟨_, h2⟩; omega
      · intro h; exact ⟨by omega, by omega⟩
  have hsum : ∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
      ((if Real.log n ≤ t then (1 : ℝ) else 0) : ℂ) * mobiusRealWeight 1 n
      = ∑ n ∈ (Finset.range (⌊Real.exp T⌋₊ + 1)).filter (fun n : ℕ => Real.log n ≤ t),
          mobiusRealWeight 1 n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : Real.log n ≤ t
    · rw [if_pos h, if_pos h]; norm_num
    · rw [if_neg h, if_neg h]; norm_num
  rw [hsum, hfilter, mobiusWeightedPartial]

theorem mobiusRealWeight_mul_bdWavelet (k n : ℕ) :
    mobiusRealWeight 1 n * ((bdWavelet (k + 1) (Real.log n) : ℝ) : ℂ) = bdMobiusTerm (k + 1) n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [mobiusRealWeight, bdMobiusTerm]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnC : ((n : ℂ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    rw [bdWavelet_log_natCast k hn, mobiusRealWeight, if_neg (by omega),
      Real.rpow_neg_one, bdMobiusTerm]
    push_cast
    field_simp

theorem intervalIntegrable_jumpKernelComplex (k n : ℕ) (b c : ℝ) :
    IntervalIntegrable (fun t : ℝ => mobiusRealWeight 1 n *
      (((if Real.log n ≤ t then (1 : ℝ) else 0) * bdKernel k t : ℝ) : ℂ))
      MeasureTheory.volume b c := by
  have h := intervalIntegrable_jumpKernel k (Real.log n) b c
  exact IntervalIntegrable.const_mul ⟨h.1.ofReal, h.2.ofReal⟩ _

theorem log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem log_natCast_le {n : ℕ} {T : ℝ} (hT : 0 ≤ T) (hnT : n ≤ ⌊Real.exp T⌋₊) :
    Real.log n ≤ T := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simpa using hT
  · exact (log_le_iff_le_floor hn T).mpr hnT

/-- **Equation (5), finite aperture.**  Abel summation of the wavelet pairing up to `T`. -/
theorem integral_partial_bdKernel (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
      = (∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1), bdMobiusTerm (k + 1) n)
        - ((bdWavelet (k + 1) T : ℝ) : ℂ) * mobiusWeightedPartial 1 T := by
  have hcong : (∫ t in (0 : ℝ)..T, mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
      = ∫ t in (0 : ℝ)..T, ∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
          mobiusRealWeight 1 n
            * (((if Real.log n ≤ t then (1 : ℝ) else 0) * bdKernel k t : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    show mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ) = _
    rw [mobiusPartial_eq_jumpSum ht.1 ht.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [hcong, intervalIntegral.integral_finsetSum
    (fun n _ => intervalIntegrable_jumpKernelComplex k n 0 T)]
  have hterm : ∀ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1),
      (∫ t in (0 : ℝ)..T, mobiusRealWeight 1 n
          * (((if Real.log n ≤ t then (1 : ℝ) else 0) * bdKernel k t : ℝ) : ℂ))
        = bdMobiusTerm (k + 1) n
          - ((bdWavelet (k + 1) T : ℝ) : ℂ) * mobiusRealWeight 1 n := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnT : n ≤ ⌊Real.exp T⌋₊ := by omega
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_jump_bdKernel k (log_natCast_nonneg n) (log_natCast_le hT hnT)]
    rw [Complex.ofReal_sub, mul_sub, mobiusRealWeight_mul_bdWavelet]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl

/-! ## The infinite aperture -/

/-- The wavelet kernel as a causal `L²` vector. -/
def bdKernelVector (k : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ)) (fun s : ℝ => ((bdKernel k s : ℝ) : ℂ)) t

theorem norm_bdKernel_le (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖bdKernel k t‖ ≤ (2 * (k : ℝ) + 4) * Real.exp (-t) := by
  have h1 : 0 < 1 - Real.exp (-2 * t) := one_sub_exp_pos ht
  have h2 : Real.exp (-2 * t) < 1 := by linarith
  have h3 : (0 : ℝ) < Real.exp (-2 * t) := Real.exp_pos _
  have hpow : (1 - Real.exp (-2 * t)) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hpow0 : (0 : ℝ) ≤ (1 - Real.exp (-2 * t)) ^ k := pow_nonneg h1.le k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsign : |1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t)| ≤ 2 * (k : ℝ) + 4 := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [bdKernel, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hexp.le, abs_of_nonneg hpow0]
  calc Real.exp (-t) * (1 - Real.exp (-2 * t)) ^ k
        * |1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t)|
      ≤ Real.exp (-t) * 1 * (2 * (k : ℝ) + 4) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hexp.le) hsign (abs_nonneg _) ?_
        positivity
    _ = (2 * (k : ℝ) + 4) * Real.exp (-t) := by ring

theorem measurable_bdKernelVector (k : ℕ) : Measurable (bdKernelVector k) := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact (Complex.continuous_ofReal.comp (continuous_bdKernel k)).measurable

theorem memLp_bdKernelVector (k : ℕ) :
    MeasureTheory.MemLp (bdKernelVector k) 2 MeasureTheory.volume := by
  refine MeasureTheory.MemLp.of_le
    ((memLp_causalPoleVector).const_mul (((2 * (k : ℝ) + 4) : ℝ) : ℂ))
    (measurable_bdKernelVector k).aestronglyMeasurable ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [bdKernelVector, Set.indicator_of_mem ht, causalPoleVector, Set.indicator_of_mem ht]
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_exp]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ) + 4)]
    simpa using norm_bdKernel_le k ht
  · rw [bdKernelVector, Set.indicator_of_notMem ht, norm_zero]
    positivity

theorem integrableOn_criticalMertens_bdKernel (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ)) (Set.Ioi 0) := by
  have hprod : MeasureTheory.Integrable
      (criticalMertensVector * bdKernelVector k) MeasureTheory.volume :=
    memLp_criticalMertensVector.integrable_mul (memLp_bdKernelVector k)
  refine (hprod.integrableOn (s := Set.Ioi (0 : ℝ))).congr_fun ?_ measurableSet_Ioi
  intro t ht
  rw [Pi.mul_apply, criticalMertensVector, Set.indicator_of_mem ht, bdKernelVector,
    Set.indicator_of_mem ht]

theorem abs_bdWavelet_le {k : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    |bdWavelet (k + 1) T| ≤ Real.exp (-T) := by
  have h0 : Real.exp (-2 * T) ≤ 1 := by
    have h : Real.exp (-2 * T) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h
  have h1 : (0 : ℝ) < Real.exp (-2 * T) := Real.exp_pos _
  have hb0 : (0 : ℝ) ≤ 1 - Real.exp (-2 * T) := by linarith
  have hb1 : 1 - Real.exp (-2 * T) ≤ 1 := by linarith
  have hpow : (1 - Real.exp (-2 * T)) ^ (k + 1) ≤ 1 := pow_le_one₀ hb0 hb1
  have hpow0 : (0 : ℝ) ≤ (1 - Real.exp (-2 * T)) ^ (k + 1) := pow_nonneg hb0 _
  have hexp : (0 : ℝ) < Real.exp (-T) := Real.exp_pos _
  rw [bdWavelet, abs_mul, abs_of_nonneg hexp.le, abs_of_nonneg hpow0]
  nlinarith

theorem norm_mobiusWeightedPartial_le (T : ℝ) :
    ‖mobiusWeightedPartial 1 T‖ ≤ 2 * Real.exp (T / 2) := by
  set N := ⌊Real.exp T⌋₊ with hN
  have hstep : ‖mobiusWeightedPartial 1 T‖ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (n : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hzero : ∑ n ∈ Finset.range (N + 1), ‖mobiusRealWeight 1 n‖
        = ∑ n ∈ Finset.Icc 1 N, ‖mobiusRealWeight 1 n‖ := by
      rw [Finset.range_eq_Ico, show Finset.Ico 0 (N + 1) = insert 0 (Finset.Icc 1 N) by
        ext m; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega]
      rw [Finset.sum_insert (by simp)]
      simp [mobiusRealWeight]
    rw [hzero]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hb : |(moebius n : ℤ)| ≤ 1 := by
      by_cases h : Squarefree n
      · rw [moebius_apply_of_squarefree h]
        simp [abs_pow]
      · rw [moebius_eq_zero_of_not_squarefree h]; simp
    have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      have hcast : (((moebius n : ℤ) : ℂ)) = (((moebius n : ℤ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast hb
    rw [mobiusRealWeight, if_neg (by omega), norm_mul]
    have hw : ‖(((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ)‖ = 1 / (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg_one,
        abs_of_nonneg (by positivity), one_div]
    rw [hw]
    have hinv : 1 / (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by
      have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
        nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ),
          Real.one_le_sqrt.mpr (by exact_mod_cast hn1 : (1:ℝ) ≤ (n:ℝ))]
      have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      exact one_div_le_one_div_of_le hs0 hs
    nlinarith [hmu, hinv, one_div_nonneg.mpr hn0.le]
  refine le_trans hstep (le_trans (sum_inv_sqrt_le N) ?_)
  have hNe : (N : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos T).le
  have hsq : Real.sqrt (Real.exp T) = Real.exp (T / 2) := by
    rw [show Real.exp T = (Real.exp (T / 2)) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have : Real.sqrt (N : ℝ) ≤ Real.exp (T / 2) := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hNe
  linarith

theorem tendsto_floor_exp_atTop :
    Filter.Tendsto (fun T : ℝ => ⌊Real.exp T⌋₊ + 1) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun T : ℝ => ⌊Real.exp T⌋₊) Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  exact Filter.tendsto_atTop_mono (fun T => Nat.le_succ _) h1

theorem tendsto_bdWavelet_mul_partial (k : ℕ) :
    Filter.Tendsto (fun T : ℝ => ((bdWavelet (k + 1) T : ℝ) : ℂ) * mobiusWeightedPartial 1 T)
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => 2 * Real.exp (-(T / 2))) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hstep : |bdWavelet (k + 1) T| * ‖mobiusWeightedPartial 1 T‖
        ≤ Real.exp (-T) * (2 * Real.exp (T / 2)) :=
      mul_le_mul (abs_bdWavelet_le hT) (norm_mobiusWeightedPartial_le T) (norm_nonneg _)
        (Real.exp_pos _).le
    have heq : Real.exp (-T) * (2 * Real.exp (T / 2)) = 2 * Real.exp (-(T / 2)) := by
      rw [show (2 : ℝ) * Real.exp (-(T / 2)) = 2 * Real.exp (-T + T / 2) by
        congr 2; ring]
      rw [Real.exp_add]
      ring
    linarith [hstep, heq.le, heq.ge]
  · have h1 : Filter.Tendsto (fun T : ℝ => -(T / 2)) Filter.atTop Filter.atBot := by
      have : Filter.Tendsto (fun T : ℝ => T / 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_id.atTop_div_const (by norm_num)
      exact Filter.tendsto_neg_atTop_atBot.comp this
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (2 : ℝ)

/-- **Equation (5).**  The Báez--Duarte coefficient is the beta-wavelet pairing of the critical
Möbius boundary vector. -/
theorem integral_criticalMertens_bdKernel (k : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
      = bdCoeff (k + 1) := by
  have hint := integrableOn_criticalMertens_bdKernel k
  have hlhs := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint
    (Filter.tendsto_id : Filter.Tendsto (fun T : ℝ => T) Filter.atTop Filter.atTop)
  have hsum : Filter.Tendsto
      (fun T : ℝ => ∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1), bdMobiusTerm (k + 1) n)
      Filter.atTop (nhds (bdCoeff (k + 1))) :=
    (hasSum_bdMobiusTerm (k + 1)).tendsto_sum_nat.comp tendsto_floor_exp_atTop
  have hrhs : Filter.Tendsto
      (fun T : ℝ => (∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1), bdMobiusTerm (k + 1) n)
        - ((bdWavelet (k + 1) T : ℝ) : ℂ) * mobiusWeightedPartial 1 T)
      Filter.atTop (nhds (bdCoeff (k + 1))) := by
    simpa using hsum.sub (tendsto_bdWavelet_mul_partial k)
  have heq : (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      mobiusWeightedPartial 1 t * ((bdKernel k t : ℝ) : ℂ))
      =ᶠ[Filter.atTop] fun T : ℝ =>
        (∑ n ∈ Finset.range (⌊Real.exp T⌋₊ + 1), bdMobiusTerm (k + 1) n)
          - ((bdWavelet (k + 1) T : ℝ) : ℂ) * mobiusWeightedPartial 1 T := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    exact integral_partial_bdKernel k hT
  exact tendsto_nhds_unique (hlhs.congr' heq) hrhs

end

end RHTower
