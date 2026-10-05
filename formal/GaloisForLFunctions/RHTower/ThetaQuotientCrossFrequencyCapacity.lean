import GaloisForLFunctions.RHTower.ThetaQuotientPairedBlockMetric

/-!
# The cross-frequency capacity of the theta quotient

The full cross-frequency operator `R = D − D₀` carries the logarithm-squared spectral mass of the
Xi divisor.  By Weyl's inequality and the Ky Fan triangle inequality
`K_N(R) ≥ Σ_{j ≤ N} |λ_j(D)| − K_N(D₀)`; the eigenvalue sum is `(1/(2π) + o(1))(log N)²` while
`K_N(D₀) = o((log N)²)`.  Hence `liminf K_N(R)/(log N)² ≥ 1/(2π)`, `R` is neither trace class nor
weak Schatten-one, and `limsup N s_N(R)/log N ≥ 1/π`.  No hypothesis on the location of the Xi
zeros inside the critical strip is used.
-/

open MeasureTheory Set Filter Topology Module
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

theorem kyFanSum_thetaQuotientOperator_le (N : ℕ) :
    kyFanSum thetaQuotientOperator N ≤
      kyFanSum thetaCrossFrequencyOperator N + kyFanSum thetaBlockDiagonal N := by
  have h : thetaQuotientOperator = thetaCrossFrequencyOperator + thetaBlockDiagonal := by
    rw [thetaCrossFrequencyOperator, sub_add_cancel]
  calc kyFanSum thetaQuotientOperator N = kyFanSum (thetaCrossFrequencyOperator + thetaBlockDiagonal) N := by
        rw [← h]
    _ ≤ _ := kyFanSum_add_le isCompactOperator_thetaCrossFrequencyOperator
        isCompactOperator_thetaBlockDiagonal N

/-- **The capacity lower bound**: `K_N(R) ≥ Σ_{j ≤ N}|λ_j(D)| − K_N(D₀)`. -/
theorem thetaQuotientEigenSum_sub_le_kyFanSum (N : ℕ) :
    thetaQuotientEigenSum N - kyFanSum thetaBlockDiagonal N ≤ kyFanSum thetaCrossFrequencyOperator N := by
  have h1 := thetaQuotientEigenSum_le_kyFanSum N
  have h2 := kyFanSum_thetaQuotientOperator_le N
  linarith

/-- **Item 3**: `liminf_{N→∞} K_N(R)/(log N)² ≥ 1/(2π)`. -/
theorem eventually_kyFanSum_thetaCrossFrequency_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 / (2 * Real.pi) - ε) * Real.log N ^ 2 ≤ kyFanSum thetaCrossFrequencyOperator N := by
  have hΛ := tendsto_thetaQuotientEigenSum_div_log_sq
  have hD₀ := tendsto_kyFanSum_thetaBlockDiagonal_div_log_sq
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hΛ.eventually (Ioi_mem_nhds (show 1 / (2 * Real.pi) - ε / 2 < 1 / (2 * Real.pi) by linarith)),
    hD₀.eventually (Iio_mem_nhds (half_pos hε)), hℓ.eventually_gt_atTop 0] with N h1 h2 hN
  have hsq : 0 < Real.log N ^ 2 := by positivity
  rw [lt_div_iff₀ hsq] at h1
  rw [div_lt_iff₀ hsq] at h2
  have h3 := thetaQuotientEigenSum_sub_le_kyFanSum N
  nlinarith

theorem tendsto_kyFanSum_thetaCrossFrequency_atTop :
    Tendsto (fun N : ℕ => kyFanSum thetaCrossFrequencyOperator N) atTop atTop := by
  have hpi : 0 < 1 / (4 * Real.pi) := by positivity
  have hε : 0 < 1 / (4 * Real.pi) := hpi
  have hℓ : Tendsto (fun N : ℕ => Real.log N ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine tendsto_atTop_mono' atTop ?_ (hℓ.const_mul_atTop hpi)
  filter_upwards [eventually_kyFanSum_thetaCrossFrequency_ge hε] with N hN
  have : 1 / (2 * Real.pi) - 1 / (4 * Real.pi) = 1 / (4 * Real.pi) := by field_simp; ring
  rw [this] at hN
  exact hN

/-- **`R` is not trace class.** -/
theorem not_memSchattenClass_one_thetaCrossFrequency : ¬ MemSchattenClass 1 thetaCrossFrequencyOperator := by
  intro h
  have hs : Summable fun n => approxNumber thetaCrossFrequencyOperator n := by
    unfold MemSchattenClass at h
    simpa only [Real.rpow_one] using h
  have hbdd : ∀ N, kyFanSum thetaCrossFrequencyOperator N ≤ ∑' n, approxNumber thetaCrossFrequencyOperator n :=
    fun N => hs.sum_le_tsum _ fun n _ => approxNumber_nonneg _ n
  obtain ⟨N, hN⟩ := (tendsto_kyFanSum_thetaCrossFrequency_atTop.eventually_gt_atTop
    (∑' n, approxNumber thetaCrossFrequencyOperator n)).exists
  exact absurd (hbdd N) (not_le.2 hN)

/-- **`R` is not weak Schatten-one.** -/
theorem not_memWeakSchattenClass_one_thetaCrossFrequency :
    ¬ MemWeakSchattenClass 1 thetaCrossFrequencyOperator := by
  rintro ⟨C, hC, hCn⟩
  have hK : ∀ N : ℕ, kyFanSum thetaCrossFrequencyOperator N ≤ C * (1 + Real.log N) := by
    intro N
    calc kyFanSum thetaCrossFrequencyOperator N ≤ ∑ n ∈ Finset.range N, C * (1 / ((n : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have := hCn n
          rw [Real.rpow_one] at this
          rw [mul_one_div]; exact this
      _ = C * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by rw [Finset.mul_sum]
      _ ≤ C * (1 + Real.log N) := mul_le_mul_of_nonneg_left (sum_range_inv_succ_le_one_add_log N) hC
  have hε : 0 < 1 / (4 * Real.pi) := by positivity
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, h1, h2⟩ := ((eventually_kyFanSum_thetaCrossFrequency_ge hε).and
    (hℓ.eventually_ge_atTop (8 * Real.pi * (C + 1) + 1))).exists
  have : 1 / (2 * Real.pi) - 1 / (4 * Real.pi) = 1 / (4 * Real.pi) := by field_simp; ring
  rw [this] at h1
  have h3 := hK N
  set L := Real.log N
  have hpi := Real.pi_pos
  have hL : 0 < L := by nlinarith
  -- `L²/(4π) ≥ 2(C+1)L > C(1+L)`
  have h4 : 2 * (C + 1) * L ≤ 1 / (4 * Real.pi) * L ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hL1 : 1 ≤ L := by nlinarith
  nlinarith [mul_nonneg hC (sub_nonneg.2 hL1)]

theorem sum_range_log_div_le {N₀ a : ℕ} (hN₀ : 4 ≤ N₀) :
    ∑ i ∈ Finset.range a, Real.log ((N₀ + i : ℕ) : ℝ) / ((N₀ + i : ℕ) : ℝ) ≤
      Real.log ((N₀ + a : ℕ) : ℝ) ^ 2 / 2 := by
  set x₀ : ℝ := (N₀ : ℝ) - 1
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hx₀ : 3 ≤ x₀ := by
    have : (4 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    simp only [x₀]; linarith
  have he : Real.exp 1 ≤ x₀ := by have := Real.exp_one_lt_d9; linarith
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x) (Icc x₀ (x₀ + a)) :=
    Real.log_div_self_antitoneOn.mono fun x hx => le_trans he hx.1
  have hsum := hanti.sum_le_integral
  have hcongr : ∑ i ∈ Finset.range a, Real.log ((N₀ + i : ℕ) : ℝ) / ((N₀ + i : ℕ) : ℝ) =
      ∑ i ∈ Finset.range a, (fun x : ℝ => Real.log x / x) (x₀ + ((i + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [x₀]
    push_cast
    ring_nf
  rw [hcongr]
  refine hsum.trans ?_
  rw [integral_log_div (by linarith) (by linarith)]
  have hlx : 0 ≤ Real.log (x₀ + a) := Real.log_nonneg (by linarith)
  have hle : Real.log (x₀ + a) ≤ Real.log ((N₀ + a : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by simp only [x₀]; push_cast; linarith)
  have h1 : Real.log (x₀ + a) ^ 2 ≤ Real.log ((N₀ + a : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ hlx hle 2
  have h2 : 0 ≤ Real.log x₀ ^ 2 := sq_nonneg _
  linarith

/-- **Logarithmic enhancement of the singular values**: `limsup_{N→∞} N s_N(R)/log N ≥ 1/π`, in
the form: every `c < 1/π` satisfies `c log N ≤ N s_N(R)` for infinitely many `N`. -/
theorem frequently_le_mul_approxNumber_thetaCrossFrequency {c : ℝ} (hc : c < 1 / Real.pi) :
    ∃ᶠ N : ℕ in atTop, c * Real.log N ≤ N * approxNumber thetaCrossFrequencyOperator N := by
  by_cases hc0 : c ≤ 0
  · refine Frequently.of_forall fun N => ?_
    have h1 : c * Real.log N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 (Real.log_natCast_nonneg N)
    have h2 : 0 ≤ (N : ℝ) * approxNumber thetaCrossFrequencyOperator N :=
      mul_nonneg (by positivity) (approxNumber_nonneg _ _)
    linarith
  push Not at hc0
  intro hev
  set R := thetaCrossFrequencyOperator
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  set N₀ := N₁ + 4
  have ha : ∀ j : ℕ, N₀ ≤ j → approxNumber R j ≤ c * (Real.log j / j) := by
    intro j hj
    have h := hN₁ j (by omega)
    push Not at h
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    rw [mul_div_assoc', le_div_iff₀ hj0, mul_comm]
    exact h.le
  -- `K_N(R) ≤ K_{N₀}(R) + (c/2)(log N)²`
  have hK : ∀ a : ℕ, kyFanSum R (N₀ + a) ≤ kyFanSum R N₀ + c / 2 * Real.log ((N₀ + a : ℕ) : ℝ) ^ 2 := by
    intro a
    rw [kyFanSum, kyFanSum, Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range a, approxNumber R (N₀ + i) ≤
        ∑ i ∈ Finset.range a, c * (Real.log ((N₀ + i : ℕ) : ℝ) / ((N₀ + i : ℕ) : ℝ)) :=
      Finset.sum_le_sum fun i _ => ha _ (by omega)
    rw [← Finset.mul_sum] at h1
    have h2 := sum_range_log_div_le (N₀ := N₀) (a := a) (by omega)
    have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
    linarith
  set ε := (1 / (2 * Real.pi) - c / 2) / 2
  have hpi := Real.pi_pos
  have hε : 0 < ε := by
    have : c / 2 < 1 / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ hpi] at hc
      linarith
    simp only [ε]; linarith
  have hℓ : Tendsto (fun N : ℕ => Real.log N ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hlow, hbig, hNN⟩ := ((eventually_kyFanSum_thetaCrossFrequency_ge hε).and
    ((hℓ.eventually_gt_atTop (kyFanSum R N₀ / ε)).and (eventually_ge_atTop N₀))).exists
  have hup := hK (N - N₀)
  rw [Nat.add_sub_cancel' hNN] at hup
  rw [div_lt_iff₀ hε] at hbig
  have : 1 / (2 * Real.pi) - ε - c / 2 = ε := by simp only [ε]; ring
  nlinarith

end

end RHTower
