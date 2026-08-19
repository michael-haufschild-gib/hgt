import GaloisForLFunctions.RHTower.MobiusPrimeApertureRetainedMass
import GaloisForLFunctions.RHTower.ExponentialIntegralE1
import GaloisForLFunctions.RHTower.MertensSecondRealVariable
import GaloisForLFunctions.RHTower.PrimeRecipBelowWindow

/-!
# The critical prime-aperture profile of the Möbius boundary layer

At the critical scaling `N = exp(c/(2ω))` the prime tail sum `∑_{p > N} p^{-1-2ω}` is exactly a
weighted integral of the prime reciprocal window, by interchanging the sum with the elementary
identity `p^{-2ω} = ∫_{2ω log p}^{∞} e^{-u} du`.  Mertens' second theorem evaluates the window,
and dominated convergence produces the exponential integral `E₁(c)`.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The prime reciprocal sum up to a real bound. -/
def primeRecipUpTo (x : ℝ) : ℝ := primeRecipSum ⌊x⌋₊

/-- The critical prime cutoff `N_ω = exp(c/(2ω))`. -/
def criticalCutoff (c ω : ℝ) : ℝ := Real.exp (c / (2 * ω))

/-- The prime reciprocal window between the critical cutoff and `exp(u/(2ω))`. -/
def apertureWindow (c ω u : ℝ) : ℝ :=
  primeRecipUpTo (Real.exp (u / (2 * ω))) - primeRecipUpTo (criticalCutoff c ω)

/-- The summand of the critical prime tail: `1/p · p^{-2ω}` above the cutoff. -/
def apertureTerm (c ω : ℝ) (n : ℕ) : ℝ :=
  if ⌊criticalCutoff c ω⌋₊ < n then primeRecipWeight n * (n : ℝ) ^ (-(2 * ω)) else 0

/-- The critical prime tail sum `∑_{p > N_ω} p^{-1-2ω}`. -/
def apertureTailSum (c ω : ℝ) : ℝ := ∑' n : ℕ, apertureTerm c ω n

/-! ## Elementary facts about the cutoff -/

theorem criticalCutoff_pos (c ω : ℝ) : 0 < criticalCutoff c ω := Real.exp_pos _

theorem primeRecipSum_mono {M N : ℕ} (h : M ≤ N) : primeRecipSum M ≤ primeRecipSum N := by
  rw [primeRecipSum, primeRecipSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h) ?_
  exact fun n _ _ => primeRecipWeight_nonneg n

theorem primeRecipSum_eq_sum_range (N : ℕ) :
    primeRecipSum N = ∑ n ∈ Finset.range (N + 1), primeRecipWeight n := by
  rw [primeRecipSum, show Finset.Icc 0 N = Finset.range (N + 1) by ext n; simp]

/-- The finite window sum in terms of the two prime reciprocal sums. -/
theorem sum_range_ite_eq_sub {K M : ℕ} (h : K ≤ M) :
    ∑ n ∈ Finset.range (M + 1), (if K < n then primeRecipWeight n else 0)
      = primeRecipSum M - primeRecipSum K := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => if K < n then primeRecipWeight n else 0) (Nat.succ_le_succ h)
  have hlow : ∑ n ∈ Finset.range (K + 1), (if K < n then primeRecipWeight n else 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [if_neg (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  have hhigh : ∑ n ∈ Finset.Ico (K + 1) (M + 1), (if K < n then primeRecipWeight n else 0)
      = ∑ n ∈ Finset.Ico (K + 1) (M + 1), primeRecipWeight n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : K + 1 ≤ n := (Finset.mem_Ico.mp hn).1
    rw [if_pos (by omega : K < n)]
  rw [hlow, hhigh, zero_add] at hsplit
  have hsplit2 := Finset.sum_range_add_sum_Ico primeRecipWeight (Nat.succ_le_succ h)
  rw [primeRecipSum_eq_sum_range, primeRecipSum_eq_sum_range, ← hsplit2, ← hsplit]
  ring

/-! ## The prime tail as a weighted window integral -/

/-- The integrand family: the elementary identity `p^{-2ω} = ∫_{2ω log p}^∞ e^{-u} du`. -/
def apertureIntegrand (c ω : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if ⌊criticalCutoff c ω⌋₊ < n then
    primeRecipWeight n * Set.indicator (Ici (2 * ω * Real.log n)) (fun v => Real.exp (-v)) u
  else 0

theorem apertureIntegrand_nonneg (c ω : ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ apertureIntegrand c ω n u := by
  simp only [apertureIntegrand]
  split_ifs with h
  · refine mul_nonneg (primeRecipWeight_nonneg n) ?_
    refine Set.indicator_nonneg (fun v _ => ?_) u
    exact (Real.exp_pos _).le
  · exact le_rfl

theorem measurable_apertureIntegrand (c ω : ℝ) (n : ℕ) :
    Measurable (apertureIntegrand c ω n) := by
  unfold apertureIntegrand
  split_ifs
  · exact (measurable_const.mul
      ((Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ici))
  · exact measurable_const

/-- The cutoff exponent: `2ω log N_ω = c`. -/
theorem two_mul_log_criticalCutoff {c ω : ℝ} (hω : 0 < ω) :
    2 * ω * Real.log (criticalCutoff c ω) = c := by
  rw [criticalCutoff, Real.log_exp]
  field_simp

theorem criticalCutoff_lt_of_floor_lt {c ω : ℝ} {n : ℕ} (h : ⌊criticalCutoff c ω⌋₊ < n) :
    criticalCutoff c ω < n :=
  (Nat.floor_lt (criticalCutoff_pos c ω).le).mp h

/-- Above the cutoff the exponent exceeds `c`. -/
theorem lt_two_mul_log_of_floor_lt {c ω : ℝ} (hω : 0 < ω) {n : ℕ}
    (h : ⌊criticalCutoff c ω⌋₊ < n) : c < 2 * ω * Real.log n := by
  have hlt := criticalCutoff_lt_of_floor_lt h
  have hlog : Real.log (criticalCutoff c ω) < Real.log n :=
    Real.log_lt_log (criticalCutoff_pos c ω) hlt
  have h2 : (0 : ℝ) < 2 * ω := by linarith
  calc c = 2 * ω * Real.log (criticalCutoff c ω) := (two_mul_log_criticalCutoff hω).symm
    _ < 2 * ω * Real.log n := by exact mul_lt_mul_of_pos_left hlog h2

/-- The integral of one term of the family is the corresponding prime tail term. -/
theorem integral_apertureIntegrand {c ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    ∫ u in Ioi c, apertureIntegrand c ω n u = apertureTerm c ω n := by
  simp only [apertureIntegrand, apertureTerm]
  by_cases h : ⌊criticalCutoff c ω⌋₊ < n
  · simp only [if_pos h]
    rw [integral_const_mul]
    have hlt := lt_two_mul_log_of_floor_lt hω h
    have hset : Ioi c ∩ Ici (2 * ω * Real.log n) = Ici (2 * ω * Real.log n) := by
      refine Set.inter_eq_right.mpr fun v hv => ?_
      exact lt_of_lt_of_le hlt hv
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici, hset]
    have hIci : ∫ v in Ici (2 * ω * Real.log n), Real.exp (-v)
        = ∫ v in Ioi (2 * ω * Real.log n), Real.exp (-v) := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [hIci, integral_exp_neg_Ioi]
    congr 1
    have hn : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_def_of_pos hnpos]
    ring_nf
  · simp only [if_neg h]
    exact integral_zero _ _

/-! ## Summability and the interchange -/

theorem apertureTerm_nonneg (c ω : ℝ) (n : ℕ) : 0 ≤ apertureTerm c ω n := by
  simp only [apertureTerm]
  split_ifs with h
  · exact mul_nonneg (primeRecipWeight_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

theorem apertureTerm_le {ω : ℝ} (_hω : 0 < ω) (c : ℝ) (n : ℕ) :
    apertureTerm c ω n ≤ ((n : ℝ) ^ (1 + 2 * ω))⁻¹ := by
  simp only [apertureTerm]
  split_ifs with h
  · have hn : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsplit : ((n : ℝ) ^ (1 + 2 * ω))⁻¹ = (n : ℝ)⁻¹ * (n : ℝ) ^ (-(2 * ω)) := by
      rw [Real.rpow_add hnpos, Real.rpow_one, Real.rpow_neg hnpos.le, mul_inv]
    rw [hsplit]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have := primeRecipWeight_le_one_div n
    rwa [one_div] at this
  · positivity

theorem summable_apertureTerm {ω : ℝ} (hω : 0 < ω) (c : ℝ) : Summable (apertureTerm c ω) := by
  refine Summable.of_nonneg_of_le (apertureTerm_nonneg c ω) (apertureTerm_le hω c) ?_
  exact Real.summable_nat_rpow_inv.mpr (by linarith)

/-- **The pointwise window sum.**  For `u > c` the family sums to the weighted prime window. -/
theorem tsum_apertureIntegrand {c ω u : ℝ} (hω : 0 < ω) (hc : 0 < c) (hcu : c < u) :
    ∑' n : ℕ, apertureIntegrand c ω n u = Real.exp (-u) * apertureWindow c ω u := by
  classical
  set y : ℝ := Real.exp (u / (2 * ω)) with hy
  set K : ℕ := ⌊criticalCutoff c ω⌋₊ with hK
  set M : ℕ := ⌊y⌋₊ with hM
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  have hdiv : c / (2 * ω) ≤ u / (2 * ω) := by
    have hinv : (0 : ℝ) < (2 * ω)⁻¹ := inv_pos.mpr hωpos
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcu.le hinv.le
  have hcy : criticalCutoff c ω ≤ y := by
    rw [criticalCutoff, hy]
    exact Real.exp_le_exp.mpr hdiv
  have hKM : K ≤ M := Nat.floor_mono hcy
  have hypos : (0 : ℝ) < y := Real.exp_pos _
  have hlogy : Real.log y = u / (2 * ω) := Real.log_exp _
  have hzero : ∀ n ∉ Finset.range (M + 1), apertureIntegrand c ω n u = 0 := by
    intro n hn
    have hMn : M < n := by
      simpa [Nat.lt_succ_iff] using hn
    have hyn : y < (n : ℝ) := (Nat.floor_lt hypos.le).mp hMn
    have hlog : Real.log y < Real.log n := Real.log_lt_log hypos hyn
    have hu : u < 2 * ω * Real.log n := by
      rw [hlogy] at hlog
      have := (div_lt_iff₀ hωpos).mp hlog
      linarith
    simp only [apertureIntegrand]
    split_ifs with hcase
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ici]; linarith), mul_zero]
    · rfl
  rw [tsum_eq_sum hzero]
  have hval : ∀ n ∈ Finset.range (M + 1),
      apertureIntegrand c ω n u = (if K < n then primeRecipWeight n else 0) * Real.exp (-u) := by
    intro n hn
    have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hlogn : 2 * ω * Real.log n ≤ u := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0
        simp only [Nat.cast_zero, Real.log_zero, mul_zero]
        linarith
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        have hny : (n : ℝ) ≤ y := by
          calc (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
            _ ≤ y := Nat.floor_le hypos.le
        have hlog : Real.log n ≤ Real.log y := Real.log_le_log hnpos hny
        rw [hlogy] at hlog
        have := (le_div_iff₀ hωpos).mp hlog
        linarith
    simp only [apertureIntegrand]
    split_ifs with hcase
    · rw [Set.indicator_of_mem (by simp only [Set.mem_Ici]; linarith), mul_comm]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, sum_range_ite_eq_sub hKM, mul_comm]
  rfl

/-- **The prime tail is the weighted window integral.** -/
theorem integral_apertureWindow_eq_tailSum {c ω : ℝ} (hω : 0 < ω) :
    ∑' n : ℕ, ∫ u in Ioi c, apertureIntegrand c ω n u = apertureTailSum c ω := by
  rw [apertureTailSum]
  exact tsum_congr (fun n => integral_apertureIntegrand hω n)

/-! ## The interchange -/

theorem integrableOn_apertureIntegrand (c ω : ℝ) (n : ℕ) :
    IntegrableOn (apertureIntegrand c ω n) (Ioi c) volume := by
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi c) volume := by
    have h := exp_neg_integrableOn_Ioi c (b := 1) one_pos
    refine h.congr_fun (fun v _ => by simp) measurableSet_Ioi
  unfold apertureIntegrand
  split_ifs
  · exact ((hexp.indicator measurableSet_Ici).const_mul _)
  · exact integrableOn_zero

theorem integral_tsum_apertureIntegrand {c ω : ℝ} (hω : 0 < ω) :
    ∫ u in Ioi c, (∑' n : ℕ, apertureIntegrand c ω n u) = apertureTailSum c ω := by
  have hfin : ∑' n : ℕ, ∫⁻ u in Ioi c, ‖apertureIntegrand c ω n u‖ₑ ≠ ⊤ := by
    have hterm : ∀ n : ℕ, ∫⁻ u in Ioi c, ‖apertureIntegrand c ω n u‖ₑ
        = ENNReal.ofReal (apertureTerm c ω n) := by
      intro n
      have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi c)] apertureIntegrand c ω n :=
        Filter.Eventually.of_forall (fun u => apertureIntegrand_nonneg c ω n u)
      have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrableOn_apertureIntegrand c ω n) hnn
      rw [integral_apertureIntegrand hω n] at h
      rw [h]
      refine lintegral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact Real.enorm_eq_ofReal (apertureIntegrand_nonneg c ω n u)
    rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (apertureTerm_nonneg c ω)
      (summable_apertureTerm hω c)]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.integral_tsum
    (fun n => (measurable_apertureIntegrand c ω n).aestronglyMeasurable) hfin]
  exact integral_apertureWindow_eq_tailSum hω

/-- **The critical prime tail is the weighted Mertens window integral.** -/
theorem apertureTailSum_eq_integral {c ω : ℝ} (hω : 0 < ω) (hc : 0 < c) :
    apertureTailSum c ω = ∫ u in Ioi c, Real.exp (-u) * apertureWindow c ω u := by
  rw [← integral_tsum_apertureIntegrand hω]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  exact tsum_apertureIntegrand hω hc hu

/-! ## The critical limit -/

/-- The Mertens remainder `∑_{p ≤ y} 1/p − log log y`. -/
def mertensRemainder (y : ℝ) : ℝ := primeRecipSum ⌊y⌋₊ - Real.log (Real.log y)

theorem tendsto_mertensRemainder :
    Tendsto mertensRemainder atTop (nhds mertensSecondConstant) :=
  tendsto_primeRecipSum_floor_sub_logLog

/-- The critical cutoff blows up as the shift descends to the boundary. -/
theorem tendsto_exp_div_nhdsGT {u : ℝ} (hu : 0 < u) :
    Tendsto (fun ω : ℝ => Real.exp (u / (2 * ω))) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun ω : ℝ => ω⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hmul : Tendsto (fun ω : ℝ => (u / 2) * ω⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith) hinv
  have hcongr : Tendsto (fun ω : ℝ => u / (2 * ω)) (𝓝[>] (0 : ℝ)) atTop := by
    refine hmul.congr fun ω => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]
  exact Real.tendsto_exp_atTop.comp hcongr

theorem tendsto_criticalCutoff {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => criticalCutoff c ω) (𝓝[>] (0 : ℝ)) atTop :=
  tendsto_exp_div_nhdsGT hc

/-- The window decomposes into two Mertens remainders and the logarithmic profile. -/
theorem apertureWindow_eq {c ω u : ℝ} (hω : 0 < ω) (hc : 0 < c) (hu : 0 < u) :
    apertureWindow c ω u
      = mertensRemainder (Real.exp (u / (2 * ω)))
        - mertensRemainder (criticalCutoff c ω) + Real.log (u / c) := by
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  have hlu : Real.log (Real.exp (u / (2 * ω))) = u / (2 * ω) := Real.log_exp _
  have hlc : Real.log (criticalCutoff c ω) = c / (2 * ω) := by
    rw [criticalCutoff, Real.log_exp]
  have hupos : (0 : ℝ) < u / (2 * ω) := div_pos hu hωpos
  have hcpos : (0 : ℝ) < c / (2 * ω) := div_pos hc hωpos
  have hsplit : Real.log (u / (2 * ω)) - Real.log (c / (2 * ω)) = Real.log (u / c) := by
    rw [Real.log_div hu.ne' hωpos.ne', Real.log_div hc.ne' hωpos.ne',
      Real.log_div hu.ne' hc.ne']
    ring
  simp only [apertureWindow, primeRecipUpTo, mertensRemainder, hlu, hlc]
  rw [← hsplit]
  ring

/-- **Pointwise critical profile.**  For each `u > c` the window tends to `log(u/c)`. -/
theorem tendsto_apertureWindow {c u : ℝ} (hc : 0 < c) (hcu : c < u) :
    Tendsto (fun ω : ℝ => apertureWindow c ω u) (𝓝[>] (0 : ℝ))
      (nhds (Real.log (u / c))) := by
  have hu : 0 < u := lt_trans hc hcu
  have h1 : Tendsto (fun ω : ℝ => mertensRemainder (Real.exp (u / (2 * ω))))
      (𝓝[>] (0 : ℝ)) (nhds mertensSecondConstant) :=
    tendsto_mertensRemainder.comp (tendsto_exp_div_nhdsGT hu)
  have h2 : Tendsto (fun ω : ℝ => mertensRemainder (criticalCutoff c ω))
      (𝓝[>] (0 : ℝ)) (nhds mertensSecondConstant) :=
    tendsto_mertensRemainder.comp (tendsto_criticalCutoff hc)
  have h3 := ((h1.sub h2).add_const (Real.log (u / c)))
  rw [sub_self, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (apertureWindow_eq (Set.mem_Ioi.mp hω) hc hu).symm

theorem apertureWindow_nonneg {c ω u : ℝ} (hω : 0 < ω) (hcu : c ≤ u) :
    0 ≤ apertureWindow c ω u := by
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  have hle : criticalCutoff c ω ≤ Real.exp (u / (2 * ω)) := by
    rw [criticalCutoff]
    refine Real.exp_le_exp.mpr ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcu (inv_pos.mpr hωpos).le
  simp only [apertureWindow, primeRecipUpTo, sub_nonneg]
  exact primeRecipSum_mono (Nat.floor_mono hle)

/-- **Uniform domination of the window.**  Eventually in the boundary limit the window is at most
`log(u/c) + 2`, uniformly in `u`. -/
theorem eventually_apertureWindow_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ω in 𝓝[>] (0 : ℝ), ∀ u : ℝ, c < u →
      apertureWindow c ω u ≤ Real.log (u / c) + 2 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, ∀ y ≥ y₀, |mertensRemainder y - mertensSecondConstant| ≤ 1 := by
    have h := tendsto_mertensRemainder (Metric.closedBall_mem_nhds mertensSecondConstant one_pos)
    rw [Filter.mem_map, mem_atTop_sets] at h
    obtain ⟨y₀, hy₀⟩ := h
    refine ⟨y₀, fun y hy => ?_⟩
    have := hy₀ y hy
    simpa [Real.dist_eq] using this
  filter_upwards [(tendsto_criticalCutoff hc).eventually_ge_atTop y₀, self_mem_nhdsWithin]
    with ω hcut hωmem u hu
  have hω : 0 < ω := Set.mem_Ioi.mp hωmem
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  have hupos : 0 < u := lt_trans hc hu
  have hle : criticalCutoff c ω ≤ Real.exp (u / (2 * ω)) := by
    rw [criticalCutoff]
    refine Real.exp_le_exp.mpr ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu.le (inv_pos.mpr hωpos).le
  have hb1 := hy₀ (Real.exp (u / (2 * ω))) (le_trans hcut hle)
  have hb2 := hy₀ (criticalCutoff c ω) hcut
  rw [apertureWindow_eq hω hc hupos]
  have h1 := abs_le.mp hb1
  have h2 := abs_le.mp hb2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## The exponential-integral profile -/

theorem measurable_apertureWindow {c ω : ℝ} (hω : 0 < ω) :
    Measurable (fun u : ℝ => apertureWindow c ω u) := by
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  have hmono : Monotone (fun u : ℝ => primeRecipUpTo (Real.exp (u / (2 * ω)))) := by
    intro a b hab
    simp only [primeRecipUpTo]
    refine primeRecipSum_mono (Nat.floor_mono (Real.exp_le_exp.mpr ?_))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hab (inv_pos.mpr hωpos).le
  exact hmono.measurable.sub measurable_const

theorem integrableOn_exp_neg_Ioi' (c : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi c) volume :=
  (exp_neg_integrableOn_Ioi c (b := 1) one_pos).congr_fun (fun v _ => by simp) measurableSet_Ioi

/-- **The critical prime-aperture profile.**  At the scaling `N = exp(c/(2ω))` the prime tail sum
converges to the exponential integral `E₁(c)` as the shift descends to the boundary. -/
theorem tendsto_apertureTailSum {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => apertureTailSum c ω) (𝓝[>] (0 : ℝ))
      (nhds (expIntegralOne c)) := by
  have hboundInt : IntegrableOn (fun u : ℝ => Real.exp (-u) * (Real.log (u / c) + 2))
      (Ioi c) volume := by
    have h1 := integrableOn_exp_neg_mul_log_div_Ioi hc
    have h2 := integrableOn_exp_neg_Ioi' c
    exact (h1.add (h2.const_mul 2)).congr_fun
      (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hmain : Tendsto (fun ω : ℝ => ∫ u in Ioi c, Real.exp (-u) * apertureWindow c ω u)
      (𝓝[>] (0 : ℝ)) (nhds (∫ u in Ioi c, Real.exp (-u) * Real.log (u / c))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u => Real.exp (-u) * (Real.log (u / c) + 2)) ?_ ?_ hboundInt ?_
    · filter_upwards [self_mem_nhdsWithin] with ω hωmem
      exact ((Real.measurable_exp.comp measurable_neg).mul
        (measurable_apertureWindow (Set.mem_Ioi.mp hωmem))).aestronglyMeasurable
    · filter_upwards [eventually_apertureWindow_le hc, self_mem_nhdsWithin] with ω hb hωmem
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun u hu => ?_))
      have hω : 0 < ω := Set.mem_Ioi.mp hωmem
      have hu' : c < u := Set.mem_Ioi.mp hu
      have hW0 := apertureWindow_nonneg hω hu'.le
      have hWb := hb u hu'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hW0)]
      exact mul_le_mul_of_nonneg_left hWb (Real.exp_pos _).le
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun u hu => ?_))
      exact (tendsto_apertureWindow hc (Set.mem_Ioi.mp hu)).const_mul (Real.exp (-u))
  rw [integral_exp_neg_mul_log_div_Ioi hc] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hωmem
  exact (apertureTailSum_eq_integral (Set.mem_Ioi.mp hωmem) hc).symm

/-! ## From the tail sum to the Euler logarithm -/

theorem sub_log_one_add_le_sq {t : ℝ} (ht : 0 ≤ t) : t - Real.log (1 + t) ≤ t ^ 2 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : Real.log ((1 + t)⁻¹) ≤ (1 + t)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h2
  have hkey : t - 1 + (1 + t)⁻¹ ≤ t ^ 2 := by
    rw [← sub_nonneg]
    have hid : t ^ 2 - (t - 1 + (1 + t)⁻¹) = t ^ 3 / (1 + t) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (pow_nonneg ht 3) h1.le
  linarith

theorem log_one_add_nonneg' {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.log (1 + t) :=
  Real.log_nonneg (by linarith)

theorem log_one_add_le_self {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)
  linarith

/-- The prime tail term in closed exponent form. -/
theorem apertureTerm_eq (c ω : ℝ) (n : ℕ) :
    apertureTerm c ω n
      = if ⌊criticalCutoff c ω⌋₊ < n ∧ n.Prime then (n : ℝ) ^ (-(1 + 2 * ω)) else 0 := by
  simp only [apertureTerm, primeRecipWeight]
  by_cases h : ⌊criticalCutoff c ω⌋₊ < n
  · by_cases hp : n.Prime
    · rw [if_pos h, if_pos hp, if_pos ⟨h, hp⟩]
      have hn : 0 < n := hp.pos
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : (n : ℝ) ^ (-(1 + 2 * ω)) = (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (-(2 * ω)) := by
        rw [← Real.rpow_add hnpos]
        ring_nf
      have h2 : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg hnpos.le, Real.rpow_one]
      rw [h1, h2]
    · rw [if_pos h, if_neg hp, if_neg (by tauto), zero_mul]
  · rw [if_neg h, if_neg (by tauto)]

/-- The Euler logarithm term above the critical cutoff. -/
def apertureLogTerm (c ω : ℝ) (n : ℕ) : ℝ :=
  if ⌊criticalCutoff c ω⌋₊ < n ∧ n.Prime then Real.log (1 + (n : ℝ) ^ (-(1 + 2 * ω))) else 0

/-- The Euler logarithm sum above the critical cutoff. -/
def apertureLogSum (c ω : ℝ) : ℝ := ∑' n : ℕ, apertureLogTerm c ω n

theorem apertureLogTerm_nonneg (c ω : ℝ) (n : ℕ) : 0 ≤ apertureLogTerm c ω n := by
  simp only [apertureLogTerm]
  split_ifs with h
  · exact log_one_add_nonneg' (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

theorem apertureLogTerm_le_apertureTerm (c ω : ℝ) (n : ℕ) :
    apertureLogTerm c ω n ≤ apertureTerm c ω n := by
  rw [apertureTerm_eq]
  simp only [apertureLogTerm]
  split_ifs with h
  · exact log_one_add_le_self (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

theorem summable_apertureLogTerm {ω : ℝ} (hω : 0 < ω) (c : ℝ) :
    Summable (apertureLogTerm c ω) :=
  Summable.of_nonneg_of_le (apertureLogTerm_nonneg c ω)
    (apertureLogTerm_le_apertureTerm c ω) (summable_apertureTerm hω c)

/-- The square tail of the harmonic-square series above an index. -/
def sqTail (K : ℕ) : ℝ := ∑' n : ℕ, (if K < n then ((n : ℝ) ^ 2)⁻¹ else 0)

theorem summable_invSq : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine h.congr fun n => ?_
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem summable_invSq_tail (K : ℕ) :
    Summable (fun n : ℕ => if K < n then ((n : ℝ) ^ 2)⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_invSq
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · positivity

theorem sqTail_eq_tsum_shift (K : ℕ) :
    sqTail K = ∑' i : ℕ, ((((i + (K + 1) : ℕ)) : ℝ) ^ 2)⁻¹ := by
  have hinj : Function.Injective (fun i : ℕ => i + (K + 1)) := add_left_injective (K + 1)
  have hsupp : Function.support (fun n : ℕ => if K < n then ((n : ℝ) ^ 2)⁻¹ else 0)
      ⊆ Set.range (fun i : ℕ => i + (K + 1)) := by
    intro n hn
    by_cases h : K < n
    · exact ⟨n - (K + 1), by show n - (K + 1) + (K + 1) = n; omega⟩
    · exact absurd (if_neg h) hn
  have h := hinj.tsum_eq hsupp
  rw [sqTail, ← h]
  refine tsum_congr fun i => ?_
  rw [if_pos (by omega)]

theorem tendsto_sqTail : Tendsto sqTail atTop (nhds 0) := by
  have h := tendsto_sum_nat_add (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
  have hshift : Tendsto (fun K : ℕ => K + 1) atTop atTop := Filter.tendsto_add_atTop_nat 1
  have h2 := h.comp hshift
  refine h2.congr fun K => ?_
  rw [sqTail_eq_tsum_shift]
  rfl

/-! ## The Euler logarithm has the same profile -/

theorem apertureTerm_sub_logTerm_le {ω : ℝ} (hω : 0 < ω) (c : ℝ) (n : ℕ) :
    apertureTerm c ω n - apertureLogTerm c ω n
      ≤ (if ⌊criticalCutoff c ω⌋₊ < n then ((n : ℝ) ^ 2)⁻¹ else 0) := by
  rw [apertureTerm_eq]
  simp only [apertureLogTerm]
  by_cases h : ⌊criticalCutoff c ω⌋₊ < n
  · by_cases hp : n.Prime
    · rw [if_pos ⟨h, hp⟩, if_pos ⟨h, hp⟩, if_pos h]
      have hn2 : 2 ≤ n := hp.two_le
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_lt.le
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      set t : ℝ := (n : ℝ) ^ (-(1 + 2 * ω)) with ht
      have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have htle : t ≤ ((n : ℝ))⁻¹ := by
        rw [ht, show (-(1 + 2 * ω) : ℝ) = -(1 : ℝ) + -(2 * ω) by ring,
          Real.rpow_add hnpos, Real.rpow_neg hnpos.le, Real.rpow_one]
        refine mul_le_of_le_one_right (by positivity) ?_
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      calc t - Real.log (1 + t) ≤ t ^ 2 := sub_log_one_add_le_sq ht0
        _ ≤ (((n : ℝ))⁻¹) ^ 2 := by
            exact pow_le_pow_left₀ ht0 htle 2
        _ = ((n : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
    · rw [if_neg (by tauto), if_neg (by tauto), if_pos h, sub_zero]
      positivity
  · rw [if_neg (by tauto), if_neg (by tauto), if_neg h, sub_zero]

theorem apertureTailSum_sub_logSum_le {ω : ℝ} (hω : 0 < ω) (c : ℝ) :
    apertureTailSum c ω - apertureLogSum c ω ≤ sqTail ⌊criticalCutoff c ω⌋₊ := by
  rw [apertureTailSum, apertureLogSum, sqTail,
    ← (summable_apertureTerm hω c).tsum_sub (summable_apertureLogTerm hω c)]
  exact ((summable_apertureTerm hω c).sub (summable_apertureLogTerm hω c)).tsum_le_tsum
    (fun n => apertureTerm_sub_logTerm_le hω c n) (summable_invSq_tail _)

theorem apertureLogSum_le_tailSum {ω : ℝ} (hω : 0 < ω) (c : ℝ) :
    apertureLogSum c ω ≤ apertureTailSum c ω := by
  rw [apertureLogSum, apertureTailSum]
  exact (summable_apertureLogTerm hω c).tsum_le_tsum
    (fun n => apertureLogTerm_le_apertureTerm c ω n) (summable_apertureTerm hω c)

/-- **The Euler logarithm sum has the exponential-integral profile.** -/
theorem tendsto_apertureLogSum {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => apertureLogSum c ω) (𝓝[>] (0 : ℝ))
      (nhds (expIntegralOne c)) := by
  have hfloor : Tendsto (fun ω : ℝ => ⌊criticalCutoff c ω⌋₊) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_criticalCutoff hc)
  have hsq : Tendsto (fun ω : ℝ => sqTail ⌊criticalCutoff c ω⌋₊) (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_sqTail.comp hfloor
  have hdiff : Tendsto (fun ω : ℝ => apertureTailSum c ω - apertureLogSum c ω)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      have := apertureLogSum_le_tailSum (Set.mem_Ioi.mp hω) c
      linarith
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      exact apertureTailSum_sub_logSum_le (Set.mem_Ioi.mp hω) c
  have h := (tendsto_apertureTailSum hc).sub hdiff
  rw [sub_zero] at h
  refine h.congr fun ω => ?_
  ring

/-- The retained mass fraction of the Möbius channel at the critical prime cutoff. -/
def criticalRetainedMass (c ω : ℝ) : ℝ := Real.exp (-apertureLogSum c ω)

/-- **Equation (8): the critical prime-aperture theorem.**  At the scaling `N = exp(c/(2ω))` the
retained norm fraction of the normalized Möbius channel tends to `exp(-E₁(c))`. -/
theorem tendsto_criticalRetainedMass {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => criticalRetainedMass c ω) (𝓝[>] (0 : ℝ))
      (nhds (Real.exp (-expIntegralOne c))) :=
  (Real.continuous_exp.tendsto _).comp ((tendsto_apertureLogSum hc).neg)

/-! ## Identification with the finite-prime Euler product -/

theorem tsum_primes_eq_tsum_nat (f : ℕ → ℝ) :
    ∑' p : Nat.Primes, f (p : ℕ) = ∑' n : ℕ, (if n.Prime then f n else 0) := by
  classical
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Nat.Primes.coe_nat_injective
  have hsupp : Function.support (fun n : ℕ => if n.Prime then f n else 0)
      ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact absurd (if_neg hp) hn
  have h := hinj.tsum_eq hsupp
  rw [← h]
  exact tsum_congr fun p => (if_pos p.2).symm

theorem tsum_shift_prime_ite (K : ℕ) (f : ℕ → ℝ) :
    ∑' i : ℕ, (if (i + (K + 1)).Prime then f (i + (K + 1)) else 0)
      = ∑' n : ℕ, (if K < n ∧ n.Prime then f n else 0) := by
  classical
  have hinj : Function.Injective (fun i : ℕ => i + (K + 1)) := add_left_injective (K + 1)
  have hsupp : Function.support (fun n : ℕ => if K < n ∧ n.Prime then f n else 0)
      ⊆ Set.range (fun i : ℕ => i + (K + 1)) := by
    intro n hn
    by_cases h : K < n
    · exact ⟨n - (K + 1), by show n - (K + 1) + (K + 1) = n; omega⟩
    · exact absurd (if_neg (by tauto)) hn
  have h := hinj.tsum_eq hsupp
  rw [← h]
  refine tsum_congr fun i => ?_
  by_cases hp : (i + (K + 1)).Prime
  · rw [if_pos hp, if_pos ⟨by omega, hp⟩]
  · rw [if_neg hp, if_neg (by tauto)]

theorem summable_log_one_add_nat_rpow {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => if n.Prime then Real.log (1 + (n : ℝ) ^ (-sigma)) else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1))
  · split_ifs
    · exact log_one_add_nonneg' (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact le_rfl
  · split_ifs
    · exact log_one_add_le_self (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- The Euler logarithm splits into the finite aperture and the tail above it. -/
theorem log_squarefreeMobiusTotal_split {sigma : ℝ} (hsigma : 1 < sigma) (K : ℕ) :
    Real.log (squarefreeMobiusTotal sigma)
      = (∑ p ∈ (K + 1).primesBelow, Real.log (1 + (p : ℝ) ^ (-sigma)))
        + ∑' n : ℕ, (if K < n ∧ n.Prime then Real.log (1 + (n : ℝ) ^ (-sigma)) else 0) := by
  classical
  set L : ℕ → ℝ := fun n => Real.log (1 + (n : ℝ) ^ (-sigma)) with hL
  set g : ℕ → ℝ := fun n => if n.Prime then L n else 0 with hg
  have hgs : Summable g := summable_log_one_add_nat_rpow hsigma
  have hsplit := hgs.sum_add_tsum_nat_add (K + 1)
  have htotal : ∑' n : ℕ, g n = Real.log (squarefreeMobiusTotal sigma) := by
    rw [← tsum_primes_eq_tsum_nat L]
    exact tsum_log_one_add_prime_rpow hsigma
  have hfin : ∑ i ∈ Finset.range (K + 1), g i
      = ∑ p ∈ (K + 1).primesBelow, L p := by
    rw [Nat.primesBelow, Finset.sum_filter]
  have htail : ∑' i : ℕ, g (i + (K + 1))
      = ∑' n : ℕ, (if K < n ∧ n.Prime then L n else 0) := tsum_shift_prime_ite K L
  rw [← htotal, ← hsplit, hfin, htail]

/-- **Equation (4).**  The critical retained mass is the finite Euler aperture divided by the
squarefree partition function. -/
theorem criticalRetainedMass_eq {c ω : ℝ} (hω : 0 < ω) :
    criticalRetainedMass c ω
      = (∏ p ∈ (⌊criticalCutoff c ω⌋₊ + 1).primesBelow, (1 + (p : ℝ) ^ (-(1 + 2 * ω))))
        / squarefreeMobiusTotal (1 + 2 * ω) := by
  have hsigma : (1 : ℝ) < 1 + 2 * ω := by linarith
  have hZ : 0 < squarefreeMobiusTotal (1 + 2 * ω) := squarefreeMobiusTotal_pos hsigma
  have hsplit := log_squarefreeMobiusTotal_split hsigma ⌊criticalCutoff c ω⌋₊
  have hlog : apertureLogSum c ω
      = Real.log (squarefreeMobiusTotal (1 + 2 * ω))
        - ∑ p ∈ (⌊criticalCutoff c ω⌋₊ + 1).primesBelow,
            Real.log (1 + (p : ℝ) ^ (-(1 + 2 * ω))) := by
    rw [apertureLogSum, hsplit]
    simp only [apertureLogTerm]
    ring
  rw [criticalRetainedMass, hlog, neg_sub, Real.exp_sub, Real.exp_sum, Real.exp_log hZ]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp2.pos
  refine Real.exp_log ?_
  have : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + 2 * ω)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  linarith

end

end RHTower
