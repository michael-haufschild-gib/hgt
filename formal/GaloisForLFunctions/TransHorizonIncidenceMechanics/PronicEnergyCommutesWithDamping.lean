import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrefixEnergyLinearityAndBandNonCommutation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiCompleteTraceValuationStability
import GaloisForLFunctions.BezoutValuationIncidence.FermiCellJumpReciprocityAndPronicTailBridge

/-!
# The pronic observable commutes with the damping limit

The complete sieve pronic energy `P(N, c) = Σ_{n ≥ 1} s_N(n)²/(n(n+1))` weights the cells by their
length in the reciprocal picture, so it sees only bounded arguments: for any weight with `|c| ≤ 1`
the response is dominated by the divisor count, `|s_N(n)| ≤ τ(n)`, and `τ(n)²/(n(n+1))` is summable.
Hence the pronic energy follows the pointwise limit of the response:

* Möbius: `s_N(n; μ) = [n = 1]` once `N ≥ n`, so `P(N; μ) → 1/2`;
* damped: `s_N(n; c_ε) = τ_ε(n)` once `N ≥ n`, so `P(N; c_ε) → Σ_n τ_ε(n)²/(n(n+1))`;
* and `τ_ε(n) → [n = 1]` as `ε → 0⁺`, so the damped limit tends to `1/2`.

So `lim_{ε→0} lim_N P(N; c_ε) = 1/2 = lim_N P(N; μ)`: the pronic observable commutes with the damping
limit, unlike the period variance, the dissipation and the trans-horizon energy profile, whose limits
do not commute. The horizon effect lives in the trans-horizon bulk that the pronic weight suppresses.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Weights bounded by one give responses bounded by the divisor count. -/
theorem abs_sieveSeq_le_card_divisors {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (N : ℕ) {n : ℕ}
    (hn : 0 < n) : |sieveSeq N c n| ≤ (n.divisors.card : ℝ) := by
  unfold sieveSeq
  calc |∑ d ∈ (Icc 1 N).filter (· ∣ n), c d| ≤ ∑ d ∈ (Icc 1 N).filter (· ∣ n), |c d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Icc 1 N).filter (· ∣ n), (1 : ℝ) := sum_le_sum fun d _ => hc d
    _ = ((Icc 1 N).filter (· ∣ n)).card := by simp
    _ ≤ n.divisors.card := by
        exact_mod_cast card_le_card fun d hd => by
          simp only [mem_filter, mem_Icc] at hd
          exact Nat.mem_divisors.mpr ⟨hd.2, hn.ne'⟩

/-- The pronic cell weights of the divisor count are summable along the paired cells. -/
private theorem summable_pronic_divisor_bound :
    ∃ G : ℕ → ℝ, Summable G ∧ ∀ m,
      ((2 * m + 1).divisors.card : ℝ) ^ 2 / (pronicSeq (2 * m + 1) : ℝ) +
        ((2 * m + 2).divisors.card : ℝ) ^ 2 / (pronicSeq (2 * m + 2) : ℝ) ≤ G m := by
  obtain ⟨K, hK, hτ⟩ := RHTower.card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨fun m => 2 * K ^ 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)), ?_, fun m => ?_⟩
  · have := (Real.summable_nat_rpow.mpr (show -(3 / 2 : ℝ) < -1 by norm_num)).comp_injective
      (add_left_injective 1)
    simpa [Function.comp_def] using this.mul_left (2 * K ^ 2)
  · -- each cell `n ∈ {2m+1, 2m+2}` contributes at most `K² n^{-3/2} ≤ K² (m+1)^{-3/2}`
    have hcell : ∀ n : ℕ, m + 1 ≤ n → 0 < n →
        ((n.divisors.card : ℝ)) ^ 2 / (pronicSeq n : ℝ) ≤ K ^ 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      intro n hmn hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
      have hd := hτ n hn
      have hd2 : ((n.divisors.card : ℝ)) ^ 2 ≤ K ^ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        have h0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
        calc ((n.divisors.card : ℝ)) ^ 2 ≤ (K * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ h0 hd 2
          _ = K ^ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hnR.le]
              norm_num
      have hpr : (n : ℝ) ^ 2 ≤ (pronicSeq n : ℝ) := by
        unfold pronicSeq; push_cast; nlinarith
      calc ((n.divisors.card : ℝ)) ^ 2 / (pronicSeq n : ℝ) ≤ K ^ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
            div_le_div₀ (by positivity) hd2 (by positivity) hpr
        _ = K ^ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
            rw [mul_div_assoc, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnR]; norm_num
        _ ≤ K ^ 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hmR hmn' (by norm_num))
              (sq_nonneg K)
    have h1 := hcell (2 * m + 1) (by omega) (by omega)
    have h2 := hcell (2 * m + 2) (by omega) (by omega)
    linarith

/-- **Pronic energy follows the pointwise response.** If a family of weights bounded by one has
responses converging at every argument, its complete pronic energy converges to the pronic energy
of the limit profile. -/
theorem tendsto_sieveTotalPronicEnergy_of_pointwise {c : ℕ → ℕ → ℝ} (hc : ∀ N d, |c N d| ≤ 1)
    {σ : ℕ → ℝ} (hσ : ∀ n, 0 < n → Tendsto (fun N => sieveSeq N (c N) n) atTop (𝓝 (σ n))) :
    Tendsto (fun N => sieveTotalPronicEnergy N (c N)) atTop
      (𝓝 (∑' m : ℕ, (σ (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ) +
        σ (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ)))) := by
  obtain ⟨G, hG, hGb⟩ := summable_pronic_divisor_bound
  unfold sieveTotalPronicEnergy sievePairedPronicEnergy
  simp only [sum_singleton]
  refine tendsto_tsum_of_dominated_convergence (bound := G) hG (fun m => ?_) ?_
  · exact (((hσ _ (by omega)).pow 2).div_const _).add (((hσ _ (by omega)).pow 2).div_const _)
  · filter_upwards with N m
    have b1 := abs_sieveSeq_le_card_divisors (hc N) N (show 0 < 2 * m + 1 by omega)
    have b2 := abs_sieveSeq_le_card_divisors (hc N) N (show 0 < 2 * m + 2 by omega)
    have q1 : sieveSeq N (c N) (2 * m + 1) ^ 2 ≤ ((2 * m + 1).divisors.card : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b1 2
    have q2 : sieveSeq N (c N) (2 * m + 2) ^ 2 ≤ ((2 * m + 2).divisors.card : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b2 2
    have p1 : (0 : ℝ) < (pronicSeq (2 * m + 1) : ℝ) := by unfold pronicSeq; positivity
    have p2 : (0 : ℝ) < (pronicSeq (2 * m + 2) : ℝ) := by unfold pronicSeq; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    refine le_trans ?_ (hGb m)
    exact add_le_add (div_le_div_of_nonneg_right q1 p1.le) (div_le_div_of_nonneg_right q2 p2.le)

/-! ### Möbius and the damped rows -/

/-- **Möbius pronic energy.** `P(N; μ) → 1/2`: only the cell `n = 1` survives. -/
theorem tendsto_sieveTotalPronicEnergy_moebius :
    Tendsto (fun N => sieveTotalPronicEnergy N moebiusReal) atTop (𝓝 (1 / 2)) := by
  have hc : ∀ (N : ℕ) d, |(fun _ : ℕ => moebiusReal) N d| ≤ 1 := fun _ d => by
    show |moebiusReal d| ≤ 1
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h := tendsto_sieveTotalPronicEnergy_of_pointwise hc
    (σ := fun n => if n = 1 then 1 else 0) (fun n hn => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      exact (sieveSeq_moebiusReal_eq_ite_of_le hn hN).symm)
  have hval : (∑' m : ℕ, ((if 2 * m + 1 = 1 then (1 : ℝ) else 0) ^ 2 / (pronicSeq (2 * m + 1) : ℝ) +
      (if 2 * m + 2 = 1 then (1 : ℝ) else 0) ^ 2 / (pronicSeq (2 * m + 2) : ℝ))) = 1 / 2 := by
    rw [tsum_eq_single 0 (fun m hm => by
      rw [if_neg (show 2 * m + 1 ≠ 1 by omega), if_neg (show 2 * m + 2 ≠ 1 by omega)]; simp)]
    simp [pronicSeq]
  rw [hval] at h
  exact h

/-- **Damped pronic energy.** `P(N; c_ε) → Σ_n τ_ε(n)²/(n(n+1))` for `ε ≥ 0`. -/
theorem tendsto_sieveTotalPronicEnergy_pmPowerDamped {ε : ℝ} (hε : 0 ≤ ε) :
    Tendsto (fun N => sieveTotalPronicEnergy N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (∑' m : ℕ, (RHTower.pmPowerDampedDivisorCoeff ε (2 * m + 1) ^ 2 /
          (pronicSeq (2 * m + 1) : ℝ) +
        RHTower.pmPowerDampedDivisorCoeff ε (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ)))) := by
  have hc : ∀ (N : ℕ) d, |(fun _ : ℕ => pmPowerDampedRealWeight ε) N d| ≤ 1 := fun _ d => by
    simp only [pmPowerDampedRealWeight, abs_mul]
    have h1 : |moebiusReal d| ≤ 1 := by
      unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : |(d : ℝ) ^ (-ε)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · rcases eq_or_lt_of_le hε with h | h
        · subst h; simp
        · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; norm_num
      · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    nlinarith [abs_nonneg (moebiusReal d), abs_nonneg ((d : ℝ) ^ (-ε))]
  exact tendsto_sieveTotalPronicEnergy_of_pointwise hc (fun n hn => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    exact (sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hn hN).symm)

/-- `τ_ε(n) → [n = 1]` as `ε → 0⁺`. -/
private theorem tendsto_pmPowerDampedDivisorCoeff_zero {n : ℕ} (hn : 0 < n) :
    Tendsto (fun ε : ℝ => RHTower.pmPowerDampedDivisorCoeff ε n) (𝓝[>] 0)
      (𝓝 (if n = 1 then 1 else 0)) := by
  have hprod : ∀ ε, RHTower.pmPowerDampedDivisorCoeff ε n =
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-ε)) := fun ε =>
    RHTower.pmPowerDampedDivisorCoeff_eq_prod ε hn.ne'
  simp_rw [hprod]
  have hfac : ∀ p ∈ n.primeFactors, Tendsto (fun ε : ℝ => 1 - (p : ℝ) ^ (-ε)) (𝓝[>] 0) (𝓝 0) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hc : Continuous (fun ε : ℝ => (p : ℝ) ^ (-ε)) :=
      (Real.continuous_const_rpow hp0.ne').comp continuous_neg
    have := ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).const_sub 1
    simpa using this
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < n)
    rw [if_neg hn1]
    have hsplit : (fun ε : ℝ => ∏ q ∈ n.primeFactors, (1 - (q : ℝ) ^ (-ε))) =
        fun ε => (1 - (p : ℝ) ^ (-ε)) * ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ) ^ (-ε)) :=
      funext fun ε => (mul_prod_erase _ (fun q : ℕ => 1 - (q : ℝ) ^ (-ε)) hp).symm
    rw [hsplit]
    have hrest := tendsto_finsetProd (n.primeFactors.erase p) fun q hq => hfac q (mem_of_mem_erase hq)
    simpa using (hfac p hp).mul hrest

/-- **The pronic observable commutes with the damping limit.**
`lim_{ε→0} lim_N P(N; c_ε) = 1/2 = lim_N P(N; μ)`. -/
theorem tendsto_dampedPronicLimit_zero :
    Tendsto (fun ε : ℝ => ∑' m : ℕ, (RHTower.pmPowerDampedDivisorCoeff ε (2 * m + 1) ^ 2 /
          (pronicSeq (2 * m + 1) : ℝ) +
        RHTower.pmPowerDampedDivisorCoeff ε (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ)))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  set f : ℕ → ℝ := fun m => 1 / (pronicSeq (2 * m + 1) : ℝ) + 1 / (pronicSeq (2 * m + 2) : ℝ)
  have hf : Summable f := by
    have := (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)).comp_injective
      (add_left_injective 1)
    refine Summable.of_nonneg_of_le (fun m => by simp only [f, pronicSeq]; positivity)
      (fun m => ?_) (this.mul_left 2)
    simp only [f, pronicSeq, Function.comp_apply]
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have e1 : 1 / (((2 * m + 1) * (2 * m + 1 + 1) : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hm.le, Real.rpow_two, one_div]
      apply inv_anti₀ (by positivity)
      push_cast; nlinarith
    have e2 : 1 / (((2 * m + 2) * (2 * m + 2 + 1) : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hm.le, Real.rpow_two, one_div]
      apply inv_anti₀ (by positivity)
      push_cast; nlinarith
    push_cast at e1 e2 ⊢
    linarith
  have hlim : (1 : ℝ) / 2 = ∑' m : ℕ, ((if 2 * m + 1 = 1 then (1 : ℝ) else 0) ^ 2 /
      (pronicSeq (2 * m + 1) : ℝ) + (if 2 * m + 2 = 1 then (1 : ℝ) else 0) ^ 2 /
        (pronicSeq (2 * m + 2) : ℝ)) := by
    rw [tsum_eq_single 0 (fun m hm => by
      rw [if_neg (show 2 * m + 1 ≠ 1 by omega), if_neg (show 2 * m + 2 ≠ 1 by omega)]; simp)]
    simp [pronicSeq]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (bound := f) hf (fun m => ?_) ?_
  · exact (((tendsto_pmPowerDampedDivisorCoeff_zero (by omega)).pow 2).div_const _).add
      (((tendsto_pmPowerDampedDivisorCoeff_zero (by omega)).pow 2).div_const _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε m
    have hε0 : (0 : ℝ) ≤ ε := le_of_lt hε
    have q : ∀ n, RHTower.pmPowerDampedDivisorCoeff ε n ^ 2 ≤ 1 := fun n => by
      have h0 := RHTower.pmPowerDampedDivisorCoeff_nonneg hε0 n
      have h1 := RHTower.pmPowerDampedDivisorCoeff_le_one hε0 n
      nlinarith
    have p1 : (0 : ℝ) < (pronicSeq (2 * m + 1) : ℝ) := by unfold pronicSeq; positivity
    have p2 : (0 : ℝ) < (pronicSeq (2 * m + 2) : ℝ) := by unfold pronicSeq; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    exact add_le_add (div_le_div_of_nonneg_right (q _) p1.le) (div_le_div_of_nonneg_right (q _) p2.le)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
