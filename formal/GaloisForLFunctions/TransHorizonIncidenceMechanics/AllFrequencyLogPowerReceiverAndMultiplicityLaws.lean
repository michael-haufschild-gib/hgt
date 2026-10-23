import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheReceiverReadsTheZeroDivisorOfZetaOnTheOscillatingSpectrum

/-!
# All-frequency log-power receiver laws and global zero-multiplicity criteria

`TheReceiverReadsTheZeroDivisorOfZetaOnTheOscillatingSpectrum` proved the spectral law for
oscillating log-polynomials supported on positive frequencies `t > 0`. Here we remove the
positivity restriction and assemble the complete all-frequency and global multiplicity laws:

* **Non-opposite frequency sets (`receiverBounded_oscillatingLogPolynomial_iff_of_add_ne_zero`).**
  The multi-frequency window lower bound `sum_Ioc_oscSum_sq_div_ge` requires only that no two
  frequencies in `J` sum to zero (`∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0`). Consequently the spectral
  equivalence holds for any finite set `J ⊂ ℝ \ {0}` containing no opposite pair `{t, −t}`, and in
  particular for every non-zero singleton `{t}` (`t ≠ 0`, positive or negative).
* **Zero frequency (`not_receiverBounded_logPowerCosine_zero`).**
  At `t = 0`, `logPowerCosine ε 0 k d = d^{-ε} (log d)^k`. Since `Re ζ(1 − ε) < 0` on
  `0 < ε ≤ 1/2`, the top log-power `(log n)^k` in the centered prefix carries coefficient
  `ζ(1 − ε)/(1 − ε) ≠ 0`, so `logPowerCosine ε 0 k` is unpaid for every `k ∈ ℕ` while
  `ζ^{(0)}(1 − ε) = ζ(1 − ε) ≠ 0`.
* **All-frequency order detection (`receiverBounded_logPowerCosine_iff_all`).**
  For every `0 < ε ≤ 1/2`, every `t ∈ ℝ` (positive, negative, or zero), and every `k ∈ ℕ`,
  `ReceiverBounded (logPowerCosine ε t k) ↔ ∀ i ≤ k, ζ^{(i)}(1 − ε + it) = 0`.
* **Monotonicity in the log-degree (`receiverBounded_logPowerCosine_of_le`).**
  If `d^{-ε} cos(t log d) (log d)^k` is paid, then `d^{-ε} cos(t log d) (log d)^j` is paid for every
  `j ≤ k`: higher log-powers can only be paid when all lower log-powers at the same exponent are
  already paid.
* **Global zero-multiplicity criteria (`forall_strip_zero_order_le_iff`,
  `forall_critical_zero_order_le_iff`).**
  Every zero of `ζ` in the strip `1/2 ≤ Re s < 1` (respectively on the critical line `Re s = 1/2`)
  has multiplicity at most `k` iff no `logPowerCosine ε t k` with `0 < ε ≤ 1/2`, `t ∈ ℝ`
  (respectively `ε = 1/2`, `t ∈ ℝ`) has bounded receiver.
-/

open Finset Filter Topology Complex Metric
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Multi-frequency window energy and spectral law without opposite frequencies -/

/-- **Multi-frequency window energy for non-opposite frequencies.** If `t + s ≠ 0` for all
`t, s ∈ J`, then for `N ≤ T`,
`Σ_{N < n ≤ T} Re(Σ_{t ∈ J} c_t n^{it})² / n ≥ (Σ_{t ∈ J} |c_t|² / 2) Σ_{N < n ≤ T} 1/n − D(J, c)`. -/
theorem sum_Ioc_oscSum_sq_div_ge_of_add_ne_zero {J : Finset ℝ}
    (hJ : ∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0) (c : ℝ → ℂ) {N T : ℕ} (hNT : N ≤ T) :
    (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * ∑ n ∈ Ioc N T, 1 / (n : ℝ) - windowDefect J c ≤
      ∑ n ∈ Ioc N T, oscSum J c n ^ 2 / n := by
  set S : ℝ → ℂ := fun τ => ∑ n ∈ Ioc N T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ)
    with hS
  set H := ∑ n ∈ Ioc N T, 1 / (n : ℝ) with hH
  have hterm : ∀ n ∈ Ioc N T, oscSum J c n ^ 2 / n =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) *
          (((n : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ))).re +
        (c t * c s * (((n : ℝ) : ℂ) ^ (((t + s : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ))).re)) / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    rw [oscSum_sq_eq c hn1]
    simp only [← mul_div_assoc, Complex.div_ofReal_re, ← add_div, ← sum_div]
    ring
  have hexp : ∑ n ∈ Ioc N T, oscSum J c n ^ 2 / n =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) * S (t - s)).re +
        (c t * c s * S (t + s)).re)) / 2 := by
    rw [sum_congr rfl hterm, ← sum_div, sum_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, ← mul_sum, ← mul_sum]
  have hpair : ∀ t ∈ J, ∀ s ∈ J,
      (if t = s then ‖c t‖ ^ 2 * H else 0) -
          2 * (‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + oscHarmonicBound (t + s))) ≤
        (c t * (starRingEnd ℂ) (c s) * S (t - s)).re + (c t * c s * S (t + s)).re := by
    intro t ht s hs
    have hts : t + s ≠ 0 := hJ t ht s hs
    have hB1 := oscHarmonicBound_nonneg (t - s)
    have hS2 : ‖S (t + s)‖ ≤ 2 * oscHarmonicBound (t + s) := norm_sum_Ioc_cpow_div_le hts hNT
    have h2 : -(‖c t‖ * ‖c s‖ * (2 * oscHarmonicBound (t + s))) ≤ (c t * c s * S (t + s)).re := by
      refine neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans ?_)
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    split_ifs with hst
    · rw [← hst] at h2 hB1 ⊢
      have hS0 : S (t - t) = (H : ℂ) := by simp [hS, hH]
      have hcc : c t * (starRingEnd ℂ) (c t) = ((‖c t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hS0, hcc, ← Complex.ofReal_mul, Complex.ofReal_re]
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (c t)) (norm_nonneg (c t))) hB1]
    · have hne : t - s ≠ 0 := sub_ne_zero.mpr hst
      have hS1 : ‖S (t - s)‖ ≤ 2 * oscHarmonicBound (t - s) := norm_sum_Ioc_cpow_div_le hne hNT
      have h1 : -(‖c t‖ * ‖c s‖ * (2 * oscHarmonicBound (t - s))) ≤
          (c t * (starRingEnd ℂ) (c s) * S (t - s)).re := by
        refine neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hS1 (by positivity)
      linarith
  have hdiag : ∑ t ∈ J, ∑ s ∈ J, (if t = s then ‖c t‖ ^ 2 * H else 0) =
      (∑ t ∈ J, ‖c t‖ ^ 2) * H := by
    rw [sum_mul]
    exact sum_congr rfl fun t ht => by rw [sum_ite_eq, if_pos ht]
  have hdef : ∑ t ∈ J, ∑ s ∈ J,
      2 * (‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + oscHarmonicBound (t + s))) =
        2 * windowDefect J c := by
    rw [windowDefect, mul_sum]
    exact sum_congr rfl fun t _ => by rw [mul_sum]
  have hlow : (∑ t ∈ J, ‖c t‖ ^ 2) * H - 2 * windowDefect J c ≤
      ∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) * S (t - s)).re +
        (c t * c s * S (t + s)).re) := by
    rw [← hdiag, ← hdef, ← sum_sub_distrib]
    exact sum_le_sum fun t ht => by
      rw [← sum_sub_distrib]; exact sum_le_sum fun s hs => hpair t ht s hs
  rw [hexp]
  linarith

/-- If `∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0` and the main-term energy is bounded, the top log-coefficient
vanishes at every `t ∈ J`. -/
theorem top_coeff_eq_zero_of_add_ne_zero {J : Finset ℝ}
    (hJ : ∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0) (K : ℕ) (q : ℝ → ℕ → ℂ)
    {C : ℝ} (hC : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
      (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C) :
    ∀ t ∈ J, q t K = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨t₀, ht₀, hq₀⟩ := hne
  have hκ0 : 0 < (∑ t ∈ J, ‖q t K‖ ^ 2) / 2 := by
    have : 0 < ∑ t ∈ J, ‖q t K‖ ^ 2 :=
      sum_pos' (fun t _ => sq_nonneg _) ⟨t₀, ht₀, by positivity⟩
    positivity
  have hwin : ∀ N : ℕ, 1 ≤ N → (∑ t ∈ J, ‖q t K‖ ^ 2) / 2 * (Real.log N - 1) -
      windowDefect J (q · K) ≤ ∑ n ∈ Ioc N (N ^ 2), oscSum J (q · K) n ^ 2 / n := by
    intro N hN
    have h1 := sum_Ioc_oscSum_sq_div_ge_of_add_ne_zero hJ (q · K) (le_self_pow hN two_ne_zero)
    beta_reduce at h1
    have h2 := mul_le_mul_of_nonneg_left (log_sub_one_le_sum_Ioc_one_div hN) hκ0.le
    linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (1 + (|windowDefect J (q · 0)| + |C| + 1) /
      ((∑ t ∈ J, ‖q t 0‖ ^ 2) / 2)))
    have hN0 : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hN
    have hN1 : 1 ≤ N := Nat.cast_pos.mp hN0
    have hX := (Real.lt_log_iff_exp_lt hN0).mpr hN
    have h2 : (|windowDefect J (q · 0)| + |C| + 1) / ((∑ t ∈ J, ‖q t 0‖ ^ 2) / 2) <
        Real.log N - 1 := by linarith
    rw [div_lt_iff₀ hκ0] at h2
    have h1 := hwin N hN1
    have hsub : ∑ n ∈ Ioc N (N ^ 2), oscSum J (q · 0) n ^ 2 / n ≤
        ∑ n ∈ Icc 1 (N ^ 2), oscSum J (q · 0) n ^ 2 / n :=
      sum_le_sum_of_subset_of_nonneg
        (fun n hn => by rw [mem_Ioc] at hn; rw [mem_Icc]; omega) (fun n _ _ => by positivity)
    have h3 := hC (N ^ 2)
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul] at h3
    linarith [le_abs_self C, le_abs_self (windowDefect J (q · 0))]
  · have hw : ∀ n : ℕ, 3 ≤ n → |∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n| ≤
        (∑ m ∈ range K, ∑ t ∈ J, ‖q t m‖) * Real.log n ^ (K - 1) := by
      intro n hn
      have hn1 : 1 ≤ n := by omega
      have hL1 : 1 ≤ Real.log n := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have : (3 : ℝ) ≤ n := by exact_mod_cast hn
        linarith [Real.exp_one_lt_d9]
      calc |∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n|
          ≤ ∑ m ∈ range K, |Real.log n ^ m * oscSum J (q · m) n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ range K, Real.log n ^ (K - 1) * ∑ t ∈ J, ‖q t m‖ := sum_le_sum fun m hm => by
            rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith) m)]
            exact mul_le_mul (pow_le_pow_right₀ hL1 (by have := mem_range.mp hm; omega))
              (abs_oscSum_le (q · m) hn1) (abs_nonneg _) (pow_nonneg (by linarith) _)
        _ = (∑ m ∈ range K, ∑ t ∈ J, ‖q t m‖) * Real.log n ^ (K - 1) := by
            rw [← mul_sum, mul_comm]
    obtain ⟨T, hT⟩ := exists_lt_sum_sq_div_of_window_pow hK hκ0 hw hwin C
    have h := hC T
    have heq : ∀ n : ℕ, ∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n =
        Real.log n ^ K * oscSum J (q · K) n +
          ∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n :=
      fun n => by rw [Finset.sum_range_succ, add_comm]
    simp only [heq] at h
    linarith

/-- Descending by degree: if `∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0` and the main-term energy is bounded,
every coefficient `q(t, m)` (`m ≤ K`) vanishes. -/
theorem coeff_eq_zero_of_bounded_of_add_ne_zero {J : Finset ℝ}
    (hJ : ∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0) (K : ℕ) (q : ℝ → ℕ → ℂ)
    {C : ℝ} (hC : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
      (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C) :
    ∀ t ∈ J, ∀ m ≤ K, q t m = 0 := by
  induction K with
  | zero =>
    intro t ht m hm
    rw [Nat.le_zero.mp hm]
    exact top_coeff_eq_zero_of_add_ne_zero hJ 0 q hC t ht
  | succ K ih =>
    have htop := top_coeff_eq_zero_of_add_ne_zero hJ (K + 1) q hC
    have hv0 : ∀ n : ℕ, oscSum J (q · (K + 1)) n = 0 := fun n => by
      simp only [oscSum]
      rw [sum_eq_zero fun t ht => by rw [htop t ht, zero_mul], zero_re]
    have hC' : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
        (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C := by
      intro T
      have h := hC T
      simp only [Finset.sum_range_succ _ (K + 1), hv0, mul_zero, add_zero] at h
      exact h
    intro t ht m hm
    rcases Nat.lt_or_ge m (K + 1) with hlt | hge
    · exact ih hC' t ht m (by omega)
    · rw [show m = K + 1 by omega]
      exact htop t ht

/-- **Spectral law for any frequency set without opposite pairs.** For `0 < ε ≤ 1/2` and a finite
set `J ⊂ ℝ` with `∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0`, `oscillatingLogPolynomial ε J K p` has bounded
receiver iff for every `t ∈ J` and `k ≤ K` with `p(t, k) ≠ 0`, `ζ^{(i)}(1 − ε + it) = 0` for all
`i ≤ k`. -/
theorem receiverBounded_oscillatingLogPolynomial_iff_of_add_ne_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {J : Finset ℝ} (hJ : ∀ t ∈ J, ∀ s ∈ J, t + s ≠ 0)
    (K : ℕ) (p : ℝ → ℕ → ℂ) :
    ReceiverBounded (oscillatingLogPolynomial ε J K p) ↔
      ∀ t ∈ J, ∀ k ≤ K, p t k ≠ 0 → ∀ i ≤ k,
        iteratedDeriv i riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
  have hcoef : (∀ t ∈ J, ∀ m ≤ K, mainCoeff ε K p t m = 0) ↔
      ∀ t ∈ J, ∀ k ≤ K, p t k ≠ 0 → ∀ i ≤ k,
        iteratedDeriv i riemannZeta (oscillationExponent ε t) = 0 := by
    refine forall₂_congr fun t _ => ?_
    have hre : (oscillationExponent ε t).re = 1 - ε := oscillationExponent_re ε t
    have h0 : oscillationExponent ε t ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
    have h1 : oscillationExponent ε t ≠ 1 := fun h => by rw [h, one_re] at hre; linarith
    refine (forall_coeff_eq_zero_iff K (p t) (fun i =>
      iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t))).trans ?_
    exact forall₂_congr fun k _ => imp_congr_right fun _ =>
      forall_iteratedDeriv_zeta_div_eq_zero_iff h0 h1 k
  refine Iff.trans ?_ hcoef
  constructor
  · intro hB
    obtain ⟨C, hC⟩ := exists_sum_sq_div_le_of_receiverBounded hB hε2
      (by linarith : (0 : ℝ) < ε / 2)
      (fun n hn => abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le hε hε2 J K p hn)
    exact coeff_eq_zero_of_bounded_of_add_ne_zero hJ K (mainCoeff ε K p) hC
  · intro h
    refine ⟨spectralRate ε J K p ^ 2 * (1 + 1 / (ε / 2)), fun T => ?_⟩
    rw [weightPronicEnergy]
    refine sum_sq_le_of_abs_le_sqrt_rpow (ε := ε / 2) (by linarith) (fun n hn => ?_) T
    have hb := abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le hε hε2 J K p hn
    have hz : ∑ m ∈ range (K + 1), Real.log n ^ m *
        (∑ t ∈ J, mainCoeff ε K p t m * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re = 0 :=
      sum_eq_zero fun m hm => by
        rw [sum_eq_zero fun t ht => by
          rw [h t ht m (by have := mem_range.mp hm; omega), zero_mul], zero_re, mul_zero]
    rwa [hz, mul_zero, sub_zero] at hb

/-! ### Zero frequency and the all-frequency `logPowerCosine` equivalence -/

/-- At `t = 0`, `oscSum {0} c n = (c 0).re` for `n ≥ 1`. -/
theorem oscSum_singleton_zero (c : ℝ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    oscSum {0} c n = (c 0).re := by
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast this.ne'
  simp [oscSum]

/-- At `t = 0`, if the polynomial energy `Σ_{n ≤ T} (Σ_{m ≤ K} (log n)^m Re(q 0 m))² / n` is
bounded, the top real coefficient `(q 0 K).re` vanishes. -/
theorem top_re_coeff_zero_eq_zero (K : ℕ) (q : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
      (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum {0} (q · m) n) ^ 2 / n ≤ C) :
    (q 0 K).re = 0 := by
  by_contra hne
  have hκ0 : 0 < (q 0 K).re ^ 2 := sq_pos_of_ne_zero hne
  have hwin : ∀ N : ℕ, 1 ≤ N → (q 0 K).re ^ 2 * (Real.log N - 1) - 0 ≤
      ∑ n ∈ Ioc N (N ^ 2), oscSum {0} (q · K) n ^ 2 / n := by
    intro N hN
    have heq : ∑ n ∈ Ioc N (N ^ 2), oscSum {0} (q · K) n ^ 2 / (n : ℝ) =
        (q 0 K).re ^ 2 * ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      rw [oscSum_singleton_zero (q · K) hn1]
      ring
    rw [heq, sub_zero]
    exact mul_le_mul_of_nonneg_left (log_sub_one_le_sum_Ioc_one_div hN) hκ0.le
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (1 + (|C| + 1) / (q 0 0).re ^ 2))
    have hN0 : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hN
    have hN1 : 1 ≤ N := Nat.cast_pos.mp hN0
    have hX := (Real.lt_log_iff_exp_lt hN0).mpr hN
    have h2 : (|C| + 1) / (q 0 0).re ^ 2 < Real.log N - 1 := by linarith
    rw [div_lt_iff₀ hκ0] at h2
    have h1 := hwin N hN1
    have hsub : ∑ n ∈ Ioc N (N ^ 2), oscSum {0} (q · 0) n ^ 2 / n ≤
        ∑ n ∈ Icc 1 (N ^ 2), oscSum {0} (q · 0) n ^ 2 / n :=
      sum_le_sum_of_subset_of_nonneg
        (fun n hn => by rw [mem_Ioc] at hn; rw [mem_Icc]; omega) (fun n _ _ => by positivity)
    have h3 := hC (N ^ 2)
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul] at h3
    linarith [le_abs_self C]
  · have hw : ∀ n : ℕ, 3 ≤ n → |∑ m ∈ range K, Real.log n ^ m * oscSum {0} (q · m) n| ≤
        (∑ m ∈ range K, ‖q 0 m‖) * Real.log n ^ (K - 1) := by
      intro n hn
      have hn1 : 1 ≤ n := by omega
      have hL1 : 1 ≤ Real.log n := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have : (3 : ℝ) ≤ n := by exact_mod_cast hn
        linarith [Real.exp_one_lt_d9]
      calc |∑ m ∈ range K, Real.log n ^ m * oscSum {0} (q · m) n|
          ≤ ∑ m ∈ range K, |Real.log n ^ m * oscSum {0} (q · m) n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ range K, Real.log n ^ (K - 1) * ‖q 0 m‖ := sum_le_sum fun m hm => by
            rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith) m)]
            have hosc := abs_oscSum_le (J := {0}) (q · m) hn1
            rw [sum_singleton] at hosc
            exact mul_le_mul (pow_le_pow_right₀ hL1 (by have := mem_range.mp hm; omega))
              hosc (abs_nonneg _) (pow_nonneg (by linarith) _)
        _ = (∑ m ∈ range K, ‖q 0 m‖) * Real.log n ^ (K - 1) := by
            rw [← mul_sum, mul_comm]
    obtain ⟨T, hT⟩ := exists_lt_sum_sq_div_of_window_pow hK hκ0 hw hwin C
    have h := hC T
    have heq : ∀ n : ℕ, ∑ m ∈ range (K + 1), Real.log n ^ m * oscSum {0} (q · m) n =
        Real.log n ^ K * oscSum {0} (q · K) n +
          ∑ m ∈ range K, Real.log n ^ m * oscSum {0} (q · m) n :=
      fun n => by rw [Finset.sum_range_succ, add_comm]
    simp only [heq] at h
    linarith

/-- **Zero-frequency log-power probes are never paid below or at half damping.** For `0 < ε ≤ 1/2`
and every `k ∈ ℕ`, `¬ ReceiverBounded (logPowerCosine ε 0 k)`. -/
theorem not_receiverBounded_logPowerCosine_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (k : ℕ) : ¬ ReceiverBounded (logPowerCosine ε 0 k) := by
  rw [logPowerCosine_eq hε]
  intro hB
  set p : ℝ → ℕ → ℂ := fun _ j => if j = k then 1 else 0
  obtain ⟨C, hC⟩ := exists_sum_sq_div_le_of_receiverBounded hB hε2
    (by linarith : (0 : ℝ) < ε / 2)
    (fun n hn => abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le hε hε2 {0} k p hn)
  have htop := top_re_coeff_zero_eq_zero k (mainCoeff ε k p) hC
  have hmain : mainCoeff ε k p 0 k =
      riemannZeta (((1 - ε : ℝ) : ℂ)) / (((1 - ε : ℝ) : ℂ)) := by
    rw [mainCoeff, sum_eq_single k
      (fun j hj hjk => by
        have hlt : j < k + 1 := mem_range.mp hj
        rw [if_neg (by omega : ¬ k ≤ j)])
      (fun hk => absurd (mem_range.mpr (Nat.lt_succ_self k)) hk),
      if_pos le_rfl, Nat.sub_self, Nat.choose_self, Nat.cast_one, mul_one,
      iteratedDeriv_zero]
    simp [p, oscillationExponent]
  rw [hmain, Complex.div_ofReal_re] at htop
  have hzre : (riemannZeta (((1 - ε : ℝ) : ℂ))).re < 0 := by
    have hz := riemannZeta_re_le_of_lt_one (σ := 1 - ε) (by linarith) (by linarith)
    have hneg : -(1 - ε) / (1 - (1 - ε)) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  have hdiv : (riemannZeta (((1 - ε : ℝ) : ℂ))).re / (1 - ε) < 0 :=
    div_neg_of_neg_of_pos hzre (by linarith)
  linarith

/-- **The receiver reads the order of vanishing at every real frequency.** For `0 < ε ≤ 1/2`,
every `t ∈ ℝ`, and every `k ∈ ℕ`, the receiver of `d^{-ε} cos(t log d) (log d)^k` is bounded if and
only if `ζ^{(i)}(1 − ε + it) = 0` for all `i ≤ k`. -/
theorem receiverBounded_logPowerCosine_iff_all {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (t : ℝ) (k : ℕ) :
    ReceiverBounded (logPowerCosine ε t k) ↔
      ∀ i ≤ k, iteratedDeriv i riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · constructor
    · intro hB
      exact absurd hB (not_receiverBounded_logPowerCosine_zero hε hε2 k)
    · intro h
      exfalso
      have h0 := h 0 (Nat.zero_le k)
      rw [iteratedDeriv_zero] at h0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      have hz := riemannZeta_re_le_of_lt_one (σ := 1 - ε) (by linarith) (by linarith)
      rw [h0, zero_re] at hz
      have : -(1 - ε) / (1 - (1 - ε)) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
  · have hJ : ∀ t' ∈ ({t} : Finset ℝ), ∀ s' ∈ ({t} : Finset ℝ), t' + s' ≠ 0 := by
      intro t' ht' s' hs'
      rw [mem_singleton] at ht' hs'
      subst ht' hs'
      intro h0
      exact ht (by linarith)
    rw [logPowerCosine_eq hε,
      receiverBounded_oscillatingLogPolynomial_iff_of_add_ne_zero hε hε2 hJ k]
    constructor
    · intro h
      exact h t (mem_singleton_self t) k le_rfl (by simp)
    · intro h t' ht' j _ hp i hi
      rw [mem_singleton] at ht'
      subst ht'
      have hjk : j = k := by
        by_contra hne
        exact hp (if_neg hne)
      exact h i (hjk ▸ hi)

/-- `logPowerCosine ε t k` is even in the frequency `t`. -/
theorem logPowerCosine_neg (ε t : ℝ) (k : ℕ) :
    logPowerCosine ε (-t) k = logPowerCosine ε t k := by
  funext d
  simp only [logPowerCosine, oscillatingSmoothPower, neg_mul, Real.cos_neg]

/-- **Monotonicity in the log-degree.** If `d^{-ε} cos(t log d) (log d)^k` has bounded receiver
(`0 < ε ≤ 1/2`, `t ∈ ℝ`) and `j ≤ k`, then `d^{-ε} cos(t log d) (log d)^j` also has bounded
receiver. -/
theorem receiverBounded_logPowerCosine_of_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (t : ℝ) {j k : ℕ} (hjk : j ≤ k) (hB : ReceiverBounded (logPowerCosine ε t k)) :
    ReceiverBounded (logPowerCosine ε t j) := by
  rw [receiverBounded_logPowerCosine_iff_all hε hε2] at hB ⊢
  exact fun i hi => hB i (hi.trans hjk)

/-- **At half damping, the receiver of `d^{-1/2} cos(t log d) (log d)^k` reads the critical zero
multiplicity at every `t ∈ ℝ`.** -/
theorem receiverBounded_logPowerCosine_half_iff (t : ℝ) (k : ℕ) :
    ReceiverBounded (logPowerCosine (1 / 2) t k) ↔
      ∀ i ≤ k, iteratedDeriv i riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
  rw [receiverBounded_logPowerCosine_iff_all (by norm_num) le_rfl t k]
  norm_num

/-! ### Global zero-multiplicity criteria in the strip and on the critical line -/

/-- **Strip zero-multiplicity criterion of order `k`.** Every zero of `ζ` in the strip
`1/2 ≤ Re s < 1` has multiplicity at most `k` (i.e. `ζ` and its first `k` derivatives do not
simultaneously vanish at any `s` with `1/2 ≤ Re s < 1`) if and only if no `logPowerCosine ε t k`
with `0 < ε ≤ 1/2` and `t ∈ ℝ` has bounded receiver. -/
theorem forall_strip_zero_order_le_iff (k : ℕ) :
    (∀ s : ℂ, 1 / 2 ≤ s.re → s.re < 1 → ¬ ∀ i ≤ k, iteratedDeriv i riemannZeta s = 0) ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℝ, ¬ ReceiverBounded (logPowerCosine ε t k) := by
  constructor
  · intro h ε hε hε2 t hB
    have hz := (receiverBounded_logPowerCosine_iff_all hε hε2 t k).1 hB
    have hre : (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I).re = 1 - ε := oscillationExponent_re ε t
    exact h _ (by rw [hre]; linarith) (by rw [hre]; linarith) hz
  · intro h s hs1 hs2 hz
    have hε : 0 < 1 - s.re := by linarith
    have hε2 : 1 - s.re ≤ 1 / 2 := by linarith
    have hs : ((1 - (1 - s.re) : ℝ) : ℂ) + (s.im : ℂ) * I = s := by
      apply Complex.ext <;> simp
    apply h (1 - s.re) hε hε2 s.im
    rw [receiverBounded_logPowerCosine_iff_all hε hε2, hs]
    exact hz

/-- **Critical-line zero-multiplicity criterion of order `k`.** Every critical zero of `ζ` on
`Re s = 1/2` has multiplicity at most `k` if and only if no half-damped log-power cosine
`d^{-1/2} cos(t log d) (log d)^k` (`t ∈ ℝ`) has bounded receiver. -/
theorem forall_critical_zero_order_le_iff (k : ℕ) :
    (∀ t : ℝ, ¬ ∀ i ≤ k, iteratedDeriv i riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) = 0) ↔
      ∀ t : ℝ, ¬ ReceiverBounded (logPowerCosine (1 / 2) t k) :=
  forall_congr' fun t => not_congr (receiverBounded_logPowerCosine_half_iff t k).symm

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.sum_Ioc_oscSum_sq_div_ge_of_add_ne_zero
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_oscillatingLogPolynomial_iff_of_add_ne_zero
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.not_receiverBounded_logPowerCosine_zero
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_logPowerCosine_iff_all
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_logPowerCosine_of_le
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.receiverBounded_logPowerCosine_half_iff
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.forall_strip_zero_order_le_iff
#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.forall_critical_zero_order_le_iff
