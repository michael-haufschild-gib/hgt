import GaloisForLFunctions.BezoutValuationIncidence.ReturnWindowTwoMomentKernelsAndSharpZeroBlocks
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon

/-!
# Quantitative Recovery Conditioning, Stride Annihilation, and Translated-Phase Observability

This module addresses two foundational problems in finite-prefix and shifted-divisor recovery:
1. **Quantitative Conditioning of Exact Recovery:**
   Qualitative invertibility of initial-prefix observations (`SharpInitialPrefixObservabilityAndExactGramDeterminants`)
   and lag-schedule projections (`ArithmeticLagSchedulesAndSharpRecoveryHorizon`) does not by itself
   bound sensitivity to observation noise. Here we establish explicit, cutoff-tracked stability bounds
   for both mechanisms:
   - For initial-prefix reconstruction via `sievePrefixInterpolatingWeight n a`, a uniform prefix
     perturbation $|a(M) - b(M)| \le \varepsilon$ on $M \in [1, n]$ changes each interior divisor
     coefficient $c(d)$ ($2 \le d \le n$) by at most $2\,\tau(d)\,\varepsilon$
     (`abs_sievePrefixMobiusLift_sub_le`, `abs_coeff_sub_le_two_mul_card_divisors_of_prefix_close`).
   - For lag-schedule recovery, at each mode's visibility clock
     $h_q = \operatorname{lagVisibilityClock}(q) = q / \operatorname{rad}(q)$, the reduced modulus is
     $q / \gcd(q, h_q) = \operatorname{rad}(q)$ (`div_gcd_lagVisibilityClock_eq_primeRadical`), which is
     squarefree (`squarefree_div_gcd_lagVisibilityClock`), so the multiplier has exact magnitude
     $|\lambda_q(h_q)| = 1 / \varphi(\operatorname{rad}(q)) \ge 1 / \varphi(q)$
     (`abs_sieveLagMultiplier_lagVisibilityClock`). This yields the quantitative mode-by-mode
     stability inequality (`selbergModeEnergy_sub_le_radical_totient_sq_mul_predictor_diff`):
     $$\varphi(q)\,\bigl(Y_{N,c}(q) - Y_{N,b}(q)\bigr)^2 \le
       \varphi(\operatorname{rad}(q))^2\,\operatorname{selbergTotientDiagonalForm}\bigl(N,\, \mathcal{C}_{h_q}(c) - \mathcal{C}_{h_q}(b)\bigr).$$

2. **LCM-Return Periodicity, Stride Annihilation, and Arbitrary-Phase Observability:**
   - The prefix discrepancy `sievePrefixDiscrepancy N M c` is periodic with the minimal arithmetic
     period $\operatorname{sieveLcmPeriod}(N) = \operatorname{lcm}(1, \dots, N)$
     (`sievePrefixDiscrepancy_add_of_sieveLcmPeriod_dvd`), whose logarithm is Chebyshev's
     $\psi(N) \sim N$ rather than $\log(N!) \sim N \log N$.
   - For **every arbitrary starting phase $A \in \mathbb{N}$** (with no divisibility assumption on $A$),
     vanishing of `sievePrefixDiscrepancy N M c` on $[A, A + \operatorname{sieveLcmPeriod}(N) + N]$
     is equivalent to `sieveVariance N c = 0` (`sievePrefixDiscrepancy_arbitrary_phase_lcm_window_zero_iff`).
   - For short translated windows $I = [A + 1, A + 2N - 4]$ of length $2N - 4$ at arbitrary phase $A$,
     every divisor $d \in [1, N - 2]$ has at least two distinct multiples in $I$
     (`exists_two_multiples_in_window_of_le_sub_two`), any central single-hit candidate
     $m_1 \in [A + N - 2, A + N - 1]$ has both neighbors $m_1 - d, m_1 + d \in I$ for all
     $d \le N - 3$ (`central_single_hit_neighbors_in_window`), and any two divisors with
     $\operatorname{lcm}(d_1, d_2) \ge 2N - 4$ share at most one common multiple in $I$
     (`common_multiple_unique_in_window_of_lcm_ge`).
   - At levels $N = 3$ and $N = 4$, the sharp $2N - 3$ horizon holds unconditionally at **every
     arbitrary phase $A \in \mathbb{N}$** (`sievePrefixDiscrepancy_arbitrary_phase_three_zero_iff`,
     `sievePrefixDiscrepancy_arbitrary_phase_four_zero_iff`).
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-! ### 1. Quantitative Stability of Initial-Prefix Coefficient Reconstruction -/

/-- Pointwise stability of the differentiated prefix increment `sievePrefixDataIncrement`:
if $|a(M) - b(M)| \le \varepsilon$ on $[1, m]$, then
$|\operatorname{sievePrefixDataIncrement} a m - \operatorname{sievePrefixDataIncrement} b m| \le 2\varepsilon$. -/
theorem abs_sievePrefixDataIncrement_sub_le (a b : ℕ → ℝ) (m : ℕ) (ε : ℝ)
    (hm : 1 ≤ m) (hε : 0 ≤ ε)
    (hclose : ∀ M ∈ Finset.Icc 1 m, |a M - b M| ≤ ε) :
    |sievePrefixDataIncrement a m - sievePrefixDataIncrement b m| ≤ 2 * ε := by
  unfold sievePrefixDataIncrement
  by_cases hm1 : m = 1
  · subst hm1
    simp only [↓reduceIte]
    have h1 := hclose 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
    linarith
  · simp only [hm1, ↓reduceIte]
    have h_m := hclose m (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)
    have h_pred := hclose (m - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h_tri : |(a m - a (m - 1)) - (b m - b (m - 1))| ≤
        |a m - b m| + |a (m - 1) - b (m - 1)| := by
      have heq : (a m - a (m - 1)) - (b m - b (m - 1)) =
          (a m - b m) - (a (m - 1) - b (m - 1)) := by ring
      rw [heq]
      exact abs_sub _ _
    linarith

/-- The cardinality of `d.divisorsAntidiagonal` equals `d.divisors.card`. -/
theorem card_divisorsAntidiagonal_eq_card_divisors (d : ℕ) :
    d.divisorsAntidiagonal.card = d.divisors.card := by
  refine Finset.card_bij (fun p _ => p.1)
    (fun p hp => Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    (fun p₁ hp₁ p₂ hp₂ heq => ?_)
    (fun u hu => ⟨(u, d / u), ?_, rfl⟩)
  · have h1 := (Nat.mem_divisorsAntidiagonal.mp hp₁).1
    have h2 := (Nat.mem_divisorsAntidiagonal.mp hp₂).1
    have hp1_pos : 0 < p₁.1 :=
      Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp₁)
    ext
    · exact heq
    · apply Nat.eq_of_mul_eq_mul_left hp1_pos
      rw [h1, heq, h2]
  · rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hu),
      (Nat.mem_divisors.mp hu).2⟩

/-- Pointwise stability of the Möbius prefix lift `sievePrefixMobiusLift`:
if $|a(M) - b(M)| \le \varepsilon$ for all $M \in [1, d]$, then
$$|\operatorname{sievePrefixMobiusLift} a d - \operatorname{sievePrefixMobiusLift} b d| \le 2\,\tau(d)\,\varepsilon.$$ -/
theorem abs_sievePrefixMobiusLift_sub_le (a b : ℕ → ℝ) (d : ℕ) (ε : ℝ)
    (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hclose : ∀ M ∈ Finset.Icc 1 d, |a M - b M| ≤ ε) :
    |sievePrefixMobiusLift a d - sievePrefixMobiusLift b d| ≤
      2 * (d.divisors.card : ℝ) * ε := by
  unfold sievePrefixMobiusLift
  rw [← Finset.sum_sub_distrib]
  have h1 : |∑ p ∈ d.divisorsAntidiagonal,
      ((moebius p.1 : ℝ) * sievePrefixDataIncrement a p.2 -
        (moebius p.1 : ℝ) * sievePrefixDataIncrement b p.2)| ≤
      ∑ _p ∈ d.divisorsAntidiagonal, (2 * ε) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [← mul_sub, abs_mul]
    have h_mu : |(moebius p.1 : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or p.1 with h0 | h1 | hm1
      · simp [h0]
      · simp [h1]
      · simp [hm1]
    have hp_mul := Nat.mem_divisorsAntidiagonal.mp hp
    have hp2_pos : 1 ≤ p.2 := by
      have : p.2 ≠ 0 := fun hz => by
        rw [hz, mul_zero] at hp_mul
        exact hp_mul.2 hp_mul.1.symm
      omega
    have hp2_le : p.2 ≤ d := Nat.le_of_dvd (by omega) ⟨p.1, by linarith [hp_mul.1]⟩
    have h_inc := abs_sievePrefixDataIncrement_sub_le a b p.2 ε hp2_pos hε
      (fun M hM => hclose M (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hM).1,
        (Finset.mem_Icc.mp hM).2.trans hp2_le⟩))
    calc
      |(moebius p.1 : ℝ)| * |sievePrefixDataIncrement a p.2 - sievePrefixDataIncrement b p.2|
        ≤ 1 * (2 * ε) := mul_le_mul h_mu h_inc (abs_nonneg _) zero_le_one
      _ = 2 * ε := one_mul _
  refine h1.trans (le_of_eq ?_)
  simp only [Finset.sum_const, card_divisorsAntidiagonal_eq_card_divisors, nsmul_eq_mul]
  ring

/-- **Quantitative Stability of Interior Coefficient Recovery (`2 ≤ d ≤ n`):**
For any two sieve weights $c, b : \mathbb{N} \to \mathbb{R}$ at cutoff $N = n + 1$, if their prefix
discrepancies on $M \in [1, d]$ ($2 \le d \le n$) differ by at most $\varepsilon$, then
$$|c(d) - b(d)| \le 2\,\tau(d)\,\varepsilon.$$ -/
theorem abs_coeff_sub_le_two_mul_card_divisors_of_prefix_close (n d : ℕ) (c b : ℕ → ℝ) (ε : ℝ)
    (hd2 : 2 ≤ d) (hdn : d ≤ n) (hε : 0 ≤ ε)
    (hclose : ∀ M ∈ Finset.Icc 1 d,
      |sievePrefixDiscrepancy (n + 1) M c - sievePrefixDiscrepancy (n + 1) M b| ≤ ε) :
    |c d - b d| ≤ 2 * (d.divisors.card : ℝ) * ε := by
  have hd_mem : d ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.mpr ⟨hd2, by omega⟩
  rw [← sievePrefixInterpolatingWeight_recovers_tail n c d hd_mem,
    ← sievePrefixInterpolatingWeight_recovers_tail n b d hd_mem]
  unfold sievePrefixInterpolatingWeight
  rw [kerPEndpointWeight_eq_of_lt (by omega : d < n + 1),
    kerPEndpointWeight_eq_of_lt (by omega : d < n + 1)]
  exact abs_sievePrefixMobiusLift_sub_le
    (fun M => sievePrefixDiscrepancy (n + 1) M c)
    (fun M => sievePrefixDiscrepancy (n + 1) M b)
    d ε (by omega) hε hclose

/-! ### 2. Quantitative Conditioning of Lag-Schedule Recovery -/

/-- The squarefree radical $\operatorname{rad}(q) = \prod_{p \in q.\text{primeFactors}} p$. -/
def primeRadical (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors, p

/-- For every $q$, `lagVisibilityClock q` divides $q$. -/
theorem lagVisibilityClock_dvd_self (q : ℕ) : lagVisibilityClock q ∣ q :=
  Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd q)

/-- For every $q$, $\gcd(q, \operatorname{lagVisibilityClock} q) = \operatorname{lagVisibilityClock} q$. -/
theorem gcd_self_lagVisibilityClock (q : ℕ) :
    Nat.gcd q (lagVisibilityClock q) = lagVisibilityClock q :=
  Nat.gcd_eq_right (lagVisibilityClock_dvd_self q)

/-- At the visibility clock $h = \operatorname{lagVisibilityClock}(q)$, the reduced modulus
$q / \gcd(q, h)$ is `primeRadical q`. -/
theorem div_gcd_lagVisibilityClock_eq_primeRadical (q : ℕ) (hq : q ≠ 0) :
    q / Nat.gcd q (lagVisibilityClock q) = primeRadical q := by
  rw [gcd_self_lagVisibilityClock]
  have hmul : primeRadical q * lagVisibilityClock q = q :=
    Nat.mul_div_cancel' (Nat.prod_primeFactors_dvd q)
  have hclock0 : lagVisibilityClock q ≠ 0 :=
    fun hz => hq ((lagVisibilityClock_eq_zero_iff q).mp hz)
  have hclock_pos : 0 < lagVisibilityClock q := Nat.pos_of_ne_zero hclock0
  calc
    q / lagVisibilityClock q = (primeRadical q * lagVisibilityClock q) / lagVisibilityClock q := by
      rw [hmul]
    _ = primeRadical q := Nat.mul_div_cancel (primeRadical q) hclock_pos

/-- At $h = \operatorname{lagVisibilityClock}(q)$, the quotient $q / \gcd(q, h)$ is squarefree. -/
theorem squarefree_div_gcd_lagVisibilityClock (q : ℕ) (hq : 0 ≠ q) :
    Squarefree (q / Nat.gcd q (lagVisibilityClock q)) :=
  (squarefree_lag_quotient_iff q (lagVisibilityClock q)).mpr ⟨hq.symm, dvd_rfl⟩

/-- `primeRadical q` is squarefree for every $q \ne 0$. -/
theorem squarefree_primeRadical (q : ℕ) (hq : q ≠ 0) :
    Squarefree (primeRadical q) := by
  rw [← div_gcd_lagVisibilityClock_eq_primeRadical q hq]
  exact squarefree_div_gcd_lagVisibilityClock q hq.symm

/-- **Exact Magnitude of the Lag Multiplier at the Visibility Clock:**
For every $q > 0$, at $h = \operatorname{lagVisibilityClock}(q)$,
$$|\operatorname{sieveLagMultiplier}(q, \operatorname{lagVisibilityClock}(q))| =
  \frac{1}{\varphi(\operatorname{rad}(q))}.$$ -/
theorem abs_sieveLagMultiplier_lagVisibilityClock (q : ℕ) (hq : 0 < q) :
    |sieveLagMultiplier q (lagVisibilityClock q)| = 1 / ((primeRadical q).totient : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  rw [sieveLagMultiplier_eq_moebius_totient_quotient,
    div_gcd_lagVisibilityClock_eq_primeRadical q hq0, abs_div]
  have hsf : Squarefree (primeRadical q) := squarefree_primeRadical q hq0
  have hne : moebius (primeRadical q) ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
  have hmu_abs : |moebiusReal (primeRadical q)| = 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or (primeRadical q) with h0 | h1 | hm1
    · exact False.elim (hne h0)
    · simp [h1]
    · simp [hm1]
  have hrad_pos : 0 < primeRadical q :=
    Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
  have htot_pos : 0 < ((primeRadical q).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hrad_pos
  rw [hmu_abs, abs_of_pos htot_pos]

/-- **Quantitative Mode-by-Mode Lag-Recovery Conditioning Inequality:**
For every cutoff $N$, every active mode $q \in [1, N]$, and any two sieve weights $c, b : \mathbb{N} \to \mathbb{R}$,
setting $h_q = \operatorname{lagVisibilityClock}(q)$ yields
$$\varphi(q)\,\bigl(Y_{N,c}(q) - Y_{N,b}(q)\bigr)^2 \le
  \varphi(\operatorname{rad}(q))^2\,\operatorname{selbergTotientDiagonalForm}\bigl(N,\,
    \text{fun } d \Rightarrow \operatorname{sieveTranslationPredictor} N h_q c d -
      \operatorname{sieveTranslationPredictor} N h_q b d\bigr).$$ -/
theorem selbergModeEnergy_sub_le_radical_totient_sq_mul_predictor_diff
    (N q : ℕ) (hq : q ∈ Finset.Icc 1 N) (c b : ℕ → ℝ) :
    (q.totient : ℝ) * (selbergMultiplesCoord N c q - selbergMultiplesCoord N b q) ^ 2 ≤
      ((primeRadical q).totient : ℝ) ^ 2 *
        selbergTotientDiagonalForm N (fun d =>
          sieveTranslationPredictor N (lagVisibilityClock q) c d -
            sieveTranslationPredictor N (lagVisibilityClock q) b d) := by
  have hq_pos : 0 < q := (Finset.mem_Icc.mp hq).1
  have h_abs := abs_sieveLagMultiplier_lagVisibilityClock q hq_pos
  have h_sq : sieveLagMultiplier q (lagVisibilityClock q) ^ 2 =
      1 / ((primeRadical q).totient : ℝ) ^ 2 := by
    rw [← sq_abs, h_abs, div_pow, one_pow]
  have hrad_pos : 0 < primeRadical q :=
    Finset.prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
  have htot_rad_pos : (0 : ℝ) < ((primeRadical q).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hrad_pos
  have h_coord_c := selbergMultiplesCoord_translationPredictor N (lagVisibilityClock q) q c
  have h_coord_b := selbergMultiplesCoord_translationPredictor N (lagVisibilityClock q) q b
  rw [if_pos hq] at h_coord_c h_coord_b
  have h_coord_sub :
      selbergMultiplesCoord N (fun d =>
        sieveTranslationPredictor N (lagVisibilityClock q) c d -
          sieveTranslationPredictor N (lagVisibilityClock q) b d) q =
        sieveLagMultiplier q (lagVisibilityClock q) *
          (selbergMultiplesCoord N c q - selbergMultiplesCoord N b q) := by
    have h_lin :
        selbergMultiplesCoord N (fun d =>
          sieveTranslationPredictor N (lagVisibilityClock q) c d -
            sieveTranslationPredictor N (lagVisibilityClock q) b d) q =
          selbergMultiplesCoord N (sieveTranslationPredictor N (lagVisibilityClock q) c) q -
            selbergMultiplesCoord N (sieveTranslationPredictor N (lagVisibilityClock q) b) q := by
      unfold selbergMultiplesCoord
      simp only [sub_div, Finset.sum_sub_distrib]
    rw [h_lin, h_coord_c, h_coord_b, ← mul_sub]
  have h_single_le :
      (q.totient : ℝ) *
        (selbergMultiplesCoord N (fun d =>
          sieveTranslationPredictor N (lagVisibilityClock q) c d -
            sieveTranslationPredictor N (lagVisibilityClock q) b d) q) ^ 2 ≤
        selbergTotientDiagonalForm N (fun d =>
          sieveTranslationPredictor N (lagVisibilityClock q) c d -
            sieveTranslationPredictor N (lagVisibilityClock q) b d) := by
    unfold selbergTotientDiagonalForm
    exact Finset.single_le_sum
      (fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hq
  rw [h_coord_sub, mul_pow, h_sq] at h_single_le
  have h_eq :
      (q.totient : ℝ) * (selbergMultiplesCoord N c q - selbergMultiplesCoord N b q) ^ 2 =
        ((primeRadical q).totient : ℝ) ^ 2 *
          ((q.totient : ℝ) *
            (1 / ((primeRadical q).totient : ℝ) ^ 2 *
              (selbergMultiplesCoord N c q - selbergMultiplesCoord N b q) ^ 2)) := by
    field_simp
  rw [h_eq]
  exact mul_le_mul_of_nonneg_left h_single_le (sq_nonneg _)

/-! ### 3. Minimal Arithmetic Return Period `sieveLcmPeriod N` and Arbitrary-Phase LCM Windows -/

/-- The minimal common return period of all active divisors $d \in [1, N]$:
$$\operatorname{sieveLcmPeriod}(N) = \operatorname{lcm}_{d \in [1, N]} d.$$ -/
def sieveLcmPeriod (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).lcm id

/-- Every divisor $d \in [1, N]$ divides `sieveLcmPeriod N`. -/
theorem dvd_sieveLcmPeriod (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    d ∣ sieveLcmPeriod N :=
  Finset.dvd_lcm hd

/-- `sieveLcmPeriod N` is strictly positive for all $N \in \mathbb{N}$. -/
theorem sieveLcmPeriod_pos (N : ℕ) : 0 < sieveLcmPeriod N := by
  by_contra hnot
  have hz : sieveLcmPeriod N = 0 := by omega
  unfold sieveLcmPeriod at hz
  rw [Finset.lcm_eq_zero_iff] at hz
  obtain ⟨d, hd, hd0⟩ := hz
  have hd1 := (Finset.mem_Icc.mp hd).1
  change d = 0 at hd0
  omega

/-- Any multiple $P$ of `sieveLcmPeriod N` is an exact period of `sievePrefixDiscrepancy N`. -/
theorem sievePrefixDiscrepancy_add_of_sieveLcmPeriod_dvd (N P t : ℕ) (c : ℕ → ℝ)
    (hP : sieveLcmPeriod N ∣ P) :
    sievePrefixDiscrepancy N (P + t) c = sievePrefixDiscrepancy N t c := by
  have hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ P :=
    fun d hd => (dvd_sieveLcmPeriod N d hd).trans hP
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievedFractSum_eq_residueCombination, sievedFractSum_eq_residueCombination,
    DeletionPeriodCovariance.residueCombination, DeletionPeriodCovariance.residueCombination]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdvd d hd), zero_add, Nat.mod_mod]

/-- **Unconditional Arbitrary-Phase LCM-Window Observability Theorem:**
For **every** level $N \in \mathbb{N}$, **every** starting phase $A \in \mathbb{N}$ (with no
divisibility hypothesis on $A$), and **every** real weight $c : \mathbb{N} \to \mathbb{R}$,
vanishing of `sievePrefixDiscrepancy N M c` on $[A, A + \operatorname{sieveLcmPeriod}(N) + N]$
is equivalent to $\operatorname{sieveVariance}(N, c) = 0$. -/
theorem sievePrefixDiscrepancy_arbitrary_phase_lcm_window_zero_iff (N A : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc A (A + sieveLcmPeriod N + N), sievePrefixDiscrepancy N M c = 0) ↔
      sieveVariance N c = 0 := by
  constructor
  · intro hw
    rw [← sievePrefix_initial_zero_iff_variance_zero]
    intro t ht
    obtain ⟨ht1, htN⟩ := Finset.mem_Icc.mp ht
    let L := sieveLcmPeriod N
    have hL : 0 < L := sieveLcmPeriod_pos N
    let P := (A / L + 1) * L
    have hPL : L ∣ P := dvd_mul_left L (A / L + 1)
    have hAP : A < P := by
      have hdiv := Nat.lt_mul_div_succ A hL
      simpa [P, Nat.mul_comm] using hdiv
    have hPA : P ≤ A + L := by
      have hle : L * (A / L) ≤ A := Nat.mul_div_le A L
      calc
        P = L * (A / L) + L := by ring
        _ ≤ A + L := by omega
    have hPt_mem : P + t ∈ Finset.Icc A (A + L + N) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← sievePrefixDiscrepancy_add_of_sieveLcmPeriod_dvd N P t c hPL]
    exact hw (P + t) hPt_mem
  · intro hvar M _
    have htail := (sieveVariance_eq_zero_iff_tail_zero N c).mp hvar
    rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
      sievedFractSum_eq_residueCombination, DeletionPeriodCovariance.residueCombination]
    simp only [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hd1 : d = 1
    · subst hd1
      simp [Nat.mod_one]
    · have hd_mem : d ∈ Finset.Icc 2 N :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩
      rw [htail d hd_mem, zero_mul, zero_div]

/-! ### 4. Stride-Difference Annihilation & Short-Window Single-Hit Localization -/

/-- For any divisor $d$ and stride $L$ with $\neg(d \mid L)$, $d$ cannot divide both $m$ and
$m + L$ simultaneously. -/
theorem not_dvd_and_dvd_add_of_not_dvd {d L : ℕ} (hnot : ¬ d ∣ L) (m : ℕ) :
    ¬ (d ∣ m ∧ d ∣ (m + L)) := by
  rintro ⟨hm, hmL⟩
  exact hnot ((Nat.dvd_add_right hm).mp hmL)

/-- **Short-Window Double-Hit Guarantee for $d \le N - 2$:**
In any translated window $I = [A + 1, A + 2N - 4]$ of length $2N - 4$ at arbitrary phase $A \in \mathbb{N}$,
every divisor $d \in [1, N - 2]$ has **at least two distinct multiples** $m_1 < m_2$ inside $I$. -/
theorem exists_two_multiples_in_window_of_le_sub_two (N A d : ℕ)
    (hd1 : 1 ≤ d) (hdN : d ≤ N - 2) :
    ∃ m₁ ∈ Finset.Icc (A + 1) (A + 2 * N - 4),
      ∃ m₂ ∈ Finset.Icc (A + 1) (A + 2 * N - 4),
        m₁ < m₂ ∧ d ∣ m₁ ∧ d ∣ m₂ := by
  let m₁ := (A / d + 1) * d
  let m₂ := (A / d + 2) * d
  have hm₁_gt : A < m₁ := by
    have h := Nat.lt_mul_div_succ A hd1
    simpa [m₁, Nat.mul_comm] using h
  have hm₁_le : m₁ ≤ A + d := by
    have h := Nat.mul_div_le A d
    calc
      m₁ = d * (A / d) + d := by ring
      _ ≤ A + d := by omega
  have hm₂_eq : m₂ = m₁ + d := by ring
  refine ⟨m₁, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    m₂, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega,
    dvd_mul_left d (A / d + 1), dvd_mul_left d (A / d + 2)⟩

/-- **The Central Single-Hit Neighbor Law:**
If a point $m_1$ lies in the central single-hit zone $[A + N - 2, A + N - 1]$ of $d = N - 1$ inside
$I = [A + 1, A + 2N - 4]$, then for every $d \in [1, N - 3]$, **both** shifted neighbors
$m_1 - d$ and $m_1 + d$ lie inside the window $I = [A + 1, A + 2N - 4]$. -/
theorem central_single_hit_neighbors_in_window (N A m₁ d : ℕ)
    (hm₁ : m₁ ∈ Finset.Icc (A + N - 2) (A + N - 1))
    (hd1 : 1 ≤ d) (hdN : d ≤ N - 3) :
    m₁ - d ∈ Finset.Icc (A + 1) (A + 2 * N - 4) ∧
      m₁ + d ∈ Finset.Icc (A + 1) (A + 2 * N - 4) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm₁
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- **Short-Window Common-Multiple Uniqueness via LCM:**
In any translated window $I = [A + 1, A + K]$ of length $K$, if two divisors $d_1, d_2 \ge 1$
satisfy $\operatorname{lcm}(d_1, d_2) \ge K$, then they share **at most one common multiple** in $I$. -/
theorem common_multiple_unique_in_window_of_lcm_ge (A K d₁ d₂ m₁ m₂ : ℕ)
    (_hd₁ : 1 ≤ d₁) (hK : K ≤ Nat.lcm d₁ d₂)
    (hm₁ : m₁ ∈ Finset.Icc (A + 1) (A + K))
    (hm₂ : m₂ ∈ Finset.Icc (A + 1) (A + K))
    (h1 : d₁ ∣ m₁ ∧ d₂ ∣ m₁) (h2 : d₁ ∣ m₂ ∧ d₂ ∣ m₂) :
    m₁ = m₂ := by
  obtain ⟨hm₁_lo, hm₁_hi⟩ := Finset.mem_Icc.mp hm₁
  obtain ⟨hm₂_lo, hm₂_hi⟩ := Finset.mem_Icc.mp hm₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdvd1 : d₁ ∣ (m₂ - m₁) := Nat.dvd_sub h2.1 h1.1
    have hdvd2 : d₂ ∣ (m₂ - m₁) := Nat.dvd_sub h2.2 h1.2
    have hlcm_dvd : Nat.lcm d₁ d₂ ∣ (m₂ - m₁) := Nat.lcm_dvd hdvd1 hdvd2
    have hle : Nat.lcm d₁ d₂ ≤ m₂ - m₁ := Nat.le_of_dvd (by omega) hlcm_dvd
    omega
  · have hdvd1 : d₁ ∣ (m₁ - m₂) := Nat.dvd_sub h1.1 h2.1
    have hdvd2 : d₂ ∣ (m₁ - m₂) := Nat.dvd_sub h1.2 h2.2
    have hlcm_dvd : Nat.lcm d₁ d₂ ∣ (m₁ - m₂) := Nat.lcm_dvd hdvd1 hdvd2
    have hle : Nat.lcm d₁ d₂ ≤ m₁ - m₂ := Nat.le_of_dvd (by omega) hlcm_dvd
    omega

/-! ### 5. Unconditional Arbitrary-Phase $2N - 3$ Horizon at Levels $N = 3$ and $N = 4$ -/

private theorem sievePrefixDiscrepancy_three_eq (M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy 3 M c =
      -(c 2 * ((M % 2 : ℕ) : ℝ) / 2 + c 3 * ((M % 3 : ℕ) : ℝ) / 3) := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievedFractSum_eq_residueCombination, DeletionPeriodCovariance.residueCombination]
  have hIcc : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [hIcc]
  simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton, Nat.mod_one, Nat.cast_zero, mul_zero, zero_div, zero_add]
  norm_num

/-- **Unconditional Arbitrary-Phase $2N - 3$ Horizon at Level $N = 3$:**
For **every** starting phase $A \in \mathbb{N}$ and **every** real weight $c : \mathbb{N} \to \mathbb{R}$,
vanishing of `sievePrefixDiscrepancy 3 M c` on the $2(3) - 3 = 3$ consecutive samples
$M \in [A, A + 2]$ is equivalent to $\operatorname{sieveVariance}(3, c) = 0$. -/
theorem sievePrefixDiscrepancy_arbitrary_phase_three_zero_iff (A : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc A (A + 2), sievePrefixDiscrepancy 3 M c = 0) ↔
      sieveVariance 3 c = 0 := by
  rw [sieveVariance_eq_zero_iff_tail_zero]
  constructor
  · intro hw
    have h0 := hw A (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h1 := hw (A + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h2 := hw (A + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [sievePrefixDiscrepancy_three_eq] at h0 h1 h2
    have hm2_0 : A % 2 = (A % 6) % 2 := (Nat.mod_mod_of_dvd A (by decide : 2 ∣ 6)).symm
    have hm3_0 : A % 3 = (A % 6) % 3 := (Nat.mod_mod_of_dvd A (by decide : 3 ∣ 6)).symm
    have hm2_1 : (A + 1) % 2 = (A % 6 + 1) % 2 := by
      rw [Nat.add_mod, hm2_0, ← Nat.add_mod]
    have hm3_1 : (A + 1) % 3 = (A % 6 + 1) % 3 := by
      rw [Nat.add_mod, hm3_0, ← Nat.add_mod]
    have hm2_2 : (A + 2) % 2 = (A % 6 + 2) % 2 := by
      rw [Nat.add_mod, hm2_0, ← Nat.add_mod]
    have hm3_2 : (A + 2) % 3 = (A % 6 + 2) % 3 := by
      rw [Nat.add_mod, hm3_0, ← Nat.add_mod]
    rw [hm2_0, hm3_0] at h0
    rw [hm2_1, hm3_1] at h1
    rw [hm2_2, hm3_2] at h2
    have hlt6 : A % 6 < 6 := Nat.mod_lt A (by decide)
    have hc23 : c 2 = 0 ∧ c 3 = 0 := by
      interval_cases hr : A % 6 <;>
        (norm_num at h0 h1 h2; constructor <;> linarith)
    intro d hd
    have hd_cases : d = 2 ∨ d = 3 := by
      obtain ⟨h_lo, h_hi⟩ := Finset.mem_Icc.mp hd
      omega
    rcases hd_cases with rfl | rfl
    · exact hc23.1
    · exact hc23.2
  · intro htail M _
    rw [sievePrefixDiscrepancy_three_eq,
      htail 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
      htail 3 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    ring

private theorem sievePrefixDiscrepancy_four_eq (M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy 4 M c =
      -(c 2 * ((M % 2 : ℕ) : ℝ) / 2 + c 3 * ((M % 3 : ℕ) : ℝ) / 3 +
        c 4 * ((M % 4 : ℕ) : ℝ) / 4) := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    sievedFractSum_eq_residueCombination, DeletionPeriodCovariance.residueCombination]
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [hIcc]
  simp only [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)),
    Finset.sum_singleton, Nat.mod_one, Nat.cast_zero, mul_zero, zero_div, zero_add]
  ring_nf

/-- **Unconditional Arbitrary-Phase $2N - 3$ Horizon at Level $N = 4$:**
For **every** starting phase $A \in \mathbb{N}$ and **every** real weight $c : \mathbb{N} \to \mathbb{R}$,
vanishing of `sievePrefixDiscrepancy 4 M c` on the $2(4) - 3 = 5$ consecutive samples
$M \in [A, A + 4]$ is equivalent to $\operatorname{sieveVariance}(4, c) = 0$. -/
theorem sievePrefixDiscrepancy_arbitrary_phase_four_zero_iff (A : ℕ) (c : ℕ → ℝ) :
    (∀ M ∈ Finset.Icc A (A + 4), sievePrefixDiscrepancy 4 M c = 0) ↔
      sieveVariance 4 c = 0 := by
  rw [sieveVariance_eq_zero_iff_tail_zero]
  constructor
  · intro hw
    have h0 := hw A (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h1 := hw (A + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h2 := hw (A + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h3 := hw (A + 3) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h4 := hw (A + 4) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [sievePrefixDiscrepancy_four_eq] at h0 h1 h2 h3 h4
    have hm2 (k : ℕ) : (A + k) % 2 = (A % 12 + k) % 2 := by
      rw [Nat.add_mod, (Nat.mod_mod_of_dvd A (by decide : 2 ∣ 12)).symm, ← Nat.add_mod]
    have hm3 (k : ℕ) : (A + k) % 3 = (A % 12 + k) % 3 := by
      rw [Nat.add_mod, (Nat.mod_mod_of_dvd A (by decide : 3 ∣ 12)).symm, ← Nat.add_mod]
    have hm4 (k : ℕ) : (A + k) % 4 = (A % 12 + k) % 4 := by
      rw [Nat.add_mod, (Nat.mod_mod_of_dvd A (by decide : 4 ∣ 12)).symm, ← Nat.add_mod]
    have hm2_0 : A % 2 = (A % 12) % 2 := (Nat.mod_mod_of_dvd A (by decide : 2 ∣ 12)).symm
    have hm3_0 : A % 3 = (A % 12) % 3 := (Nat.mod_mod_of_dvd A (by decide : 3 ∣ 12)).symm
    have hm4_0 : A % 4 = (A % 12) % 4 := (Nat.mod_mod_of_dvd A (by decide : 4 ∣ 12)).symm
    rw [hm2_0, hm3_0, hm4_0] at h0
    rw [hm2 1, hm3 1, hm4 1] at h1
    rw [hm2 2, hm3 2, hm4 2] at h2
    rw [hm2 3, hm3 3, hm4 3] at h3
    rw [hm2 4, hm3 4, hm4 4] at h4
    have hlt12 : A % 12 < 12 := Nat.mod_lt A (by decide)
    have hc234 : c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 0 := by
      interval_cases hr : A % 12 <;>
        (norm_num at h0 h1 h2 h3 h4; refine ⟨by linarith, by linarith, by linarith⟩)
    intro d hd
    have hd_cases : d = 2 ∨ d = 3 ∨ d = 4 := by
      obtain ⟨h_lo, h_hi⟩ := Finset.mem_Icc.mp hd
      omega
    rcases hd_cases with rfl | rfl | rfl
    · exact hc234.1
    · exact hc234.2.1
    · exact hc234.2.2
  · intro htail M _
    rw [sievePrefixDiscrepancy_four_eq,
      htail 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
      htail 3 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
      htail 4 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    ring

end

end GaloisForLFunctions.BezoutValuationIncidence
