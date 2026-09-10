import GaloisForLFunctions.RHTower.Sieve.FullPrimeCofactorBoundary
import GaloisForLFunctions.RHTower.EulerDeletionWeightedPrimeCancellation
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.FiniteFamilyObstruction

/-!
# Prime-count damping amplifies the literal physical Möbius source

Let `H_N(u) = sum_(n<=N) mu(n) u^omega(n) b_n` in the complete Báez-Duarte
carrier, and let `P_N` be the positive packet of every prime up to `N`.
Every remaining nonzero coefficient has at least two distinct prime factors.
Consequently the full remainder satisfies
`norm(H_N(u) + u P_N) <= 4 u^2 sqrt(N)` for `0 <= u <= 1`.

The source-selected value `t_N = norm(P_N)/(8 sqrt(N))` lies in `[0,1/2]`
and gives a full energy lower bound of order `N/(log N)^4`. The already
proved undamped energy is smaller than this by every fixed logarithmic
power. Thus no uniform multiplicative damping budget holds even on the
literal arithmetic source. The proof retains every physical tail and cross
term. It uses no numerical experiment and does not prove RH or exclude
an estimate that preserves the cancellation at `u=1`.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower.PrimeCountDamping

/-- The full physical source, damped by the number of distinct prime factors. -/
def source (N : ℕ) (u : ℝ) : BDCarrier :=
  ∑ n ∈ Icc 1 N, (Sieve.fullPrimeDampedMoebius u n : ℂ) • bdGen (1/(n : ℝ))

/-- Every prime below the actual source cutoff, with its positive physical generator. -/
def primePacket (N : ℕ) : BDCarrier :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, bdGen (1/(p : ℝ))

/-- A damping value selected from the literal prime packet. -/
def aperture (N : ℕ) : ℝ := ‖primePacket N‖/(8*Real.sqrt N)

theorem source_one (N : ℕ) : source N 1 = -bdMobiusModularApproximantVec N := by
  rw [bdMobiusModularApproximantVec_eq_generatorCombination, bdMobiusGeneratorCombination]
  simp [source, Sieve.fullPrimeDampedMoebius, ← Finset.sum_neg_distrib]

theorem generator_norm_le {n : ℕ} (hn : 1 ≤ n) :
    ‖bdGen (1/(n : ℝ))‖ ≤ 2/Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hb := DeletionMobiusGram.gram_self_le_two_div hn
  rw [bdGram_self] at hb
  have hsq : (2/Real.sqrt n)^2 = 4/(n : ℝ) := by
    rw [div_pow, Real.sq_sqrt hn0.le]
    norm_num
  have ht : ‖bdGen (1/(n : ℝ))‖^2 ≤ (2/Real.sqrt n)^2 := by
    rw [hsq]
    exact hb.trans (div_le_div_of_nonneg_right (by norm_num) hn0.le)
  nlinarith [norm_nonneg (bdGen (1/(n : ℝ))), div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le]

theorem sum_generator_norm_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ‖bdGen (1/(n : ℝ))‖ ≤ 4*Real.sqrt N := by
  calc _ ≤ ∑ n ∈ Icc 1 N, 2/Real.sqrt n :=
      Finset.sum_le_sum (fun n hn => generator_norm_le (Finset.mem_Icc.mp hn).1)
    _ = 2 * ∑ n ∈ Icc 1 N, 1/Real.sqrt n := by rw [Finset.mul_sum]; congr 1; funext n; ring
    _ ≤ 2*(2*Real.sqrt N) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by norm_num)
    _ = _ := by ring

theorem primePacket_norm_le (N : ℕ) : ‖primePacket N‖ ≤ 4*Real.sqrt N := by
  calc _ ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, ‖bdGen (1/(p : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Icc 1 N, ‖bdGen (1/(p : ℝ))‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => norm_nonneg _)
    _ ≤ _ := sum_generator_norm_le N

private theorem two_le_count_of_nonprime {n : ℕ} (_hn : 1 ≤ n) (hn1 : n ≠ 1)
    (hp : ¬ n.Prime) (hmu : ArithmeticFunction.moebius n ≠ 0) :
    2 ≤ n.primeFactors.card := by
  have hsf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
  have hc0 : n.primeFactors.card ≠ 0 := by
    intro hc
    have he := Finset.card_eq_zero.mp hc
    have hprod := Nat.prod_primeFactors_of_squarefree hsf
    rw [he, Finset.prod_empty] at hprod
    exact hn1 hprod.symm
  have hc1 : n.primeFactors.card ≠ 1 := by
    intro hc
    exact hp (Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsf, isPrimePow_iff_card_primeFactors_eq_one.mpr hc⟩)
  omega

private theorem remainder_coefficient_le {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {n : ℕ} (hn : 1 ≤ n) (hn1 : n ≠ 1) :
    |Sieve.fullPrimeDampedMoebius u n + if n.Prime then u else 0| ≤ u^2 := by
  by_cases hp : n.Prime
  · simp [hp, Sieve.fullPrimeDampedMoebius, ArithmeticFunction.moebius_apply_prime hp,
      sq_nonneg u]
  · rw [if_neg hp, add_zero]
    by_cases hz : ArithmeticFunction.moebius n = 0
    · simp [Sieve.fullPrimeDampedMoebius, hz, sq_nonneg u]
    · have hcount := two_le_count_of_nonprime hn hn1 hp hz
      have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      rw [Sieve.fullPrimeDampedMoebius, abs_mul, abs_of_nonneg (pow_nonneg hu.1 _)]
      calc _ ≤ u^n.primeFactors.card := mul_le_of_le_one_left (pow_nonneg hu.1 _) hmu
        _ ≤ u^2 := pow_le_pow_of_le_one hu.1 hu.2 hcount

/-- Every higher-factor term, with the complete tail, is a quadratic remainder in damping. -/
theorem source_add_prime_norm_le {u : ℝ} (hu : u ∈ Set.Icc 0 1) (N : ℕ) :
    ‖source N u + (u : ℂ) • primePacket N‖ ≤ 4*u^2*Real.sqrt N := by
  have he : source N u + (u : ℂ) • primePacket N =
      ∑ n ∈ Icc 1 N,
        ((Sieve.fullPrimeDampedMoebius u n + if n.Prime then u else 0 : ℝ) : ℂ) •
          bdGen (1/(n : ℝ)) := by
    rw [source, primePacket, Finset.smul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [hp, add_smul]
  rw [he]
  calc _ ≤ ∑ n ∈ Icc 1 N,
        ‖((Sieve.fullPrimeDampedMoebius u n + if n.Prime then u else 0 : ℝ) : ℂ) •
          bdGen (1/(n : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, u^2 * ‖bdGen (1/(n : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn1 : n = 1
      · simp [hn1, bdGen_one]
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (remainder_coefficient_le hu (Finset.mem_Icc.mp hn).1 hn1) (norm_nonneg _)
    _ = u^2 * ∑ n ∈ Icc 1 N, ‖bdGen (1/(n : ℝ))‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ u^2*(4*Real.sqrt N) := mul_le_mul_of_nonneg_left (sum_generator_norm_le N) (sq_nonneg _)
    _ = _ := by ring


theorem aperture_mem (N : ℕ) : aperture N ∈ Set.Icc 0 (1/2) := by
  by_cases hN : N=0
  · simp [hN, aperture, primePacket]
  · have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
    refine ⟨div_nonneg (norm_nonneg _) (by positivity), ?_⟩
    apply (div_le_iff₀ (show 0 < 8*Real.sqrt (N : ℝ) by positivity)).mpr
    have h := primePacket_norm_le N
    linarith

/-- A quantitative amplification point inside the actual damping path. -/
theorem aperture_norm_lower (N : ℕ) :
    ‖primePacket N‖^2 ≤ 16*Real.sqrt N*‖source N (aperture N)‖ := by
  by_cases hN : N=0
  · simp [hN, primePacket]
  · have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
    have hu := aperture_mem N
    have hr := source_add_prime_norm_le (show aperture N ∈ Set.Icc 0 1 from ⟨hu.1, by linarith [hu.2]⟩) N
    have ht := norm_sub_le (source N (aperture N) + (aperture N : ℂ) • primePacket N)
      (source N (aperture N))
    rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu.1] at ht
    have hb : aperture N*‖primePacket N‖ - 4*(aperture N)^2*Real.sqrt N ≤
        ‖source N (aperture N)‖ := by linarith
    calc
      ‖primePacket N‖^2 =
          (aperture N*‖primePacket N‖ - 4*(aperture N)^2*Real.sqrt N)*(16*Real.sqrt N) := by
        dsimp [aperture]
        field_simp [ne_of_gt hs]
        ring
      _ ≤ ‖source N (aperture N)‖*(16*Real.sqrt N) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring

/-- The amplification lower bound before inserting any prime-number estimate. -/
theorem aperture_energy_lower (N : ℕ) :
    ‖primePacket N‖^4 ≤ 256*(N : ℝ)*‖source N (aperture N)‖^2 := by
  have h := pow_le_pow_left₀ (sq_nonneg ‖primePacket N‖) (aperture_norm_lower N) 2
  norm_num only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ← pow_mul, Nat.reduceMul, OfNat.ofNat] at h ⊢
  nlinarith [h]

private theorem gram_nonneg {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    0 ≤ bdGram (1/(m : ℝ)) (1/(n : ℝ)) := by
  simpa using (DeletionPrimePacket.gram_lower_of_common_head hm hn
    (show 0 < m by omega) (show 0 < n by omega))

/-- Positive physical Gram entries make the upper-half packet a lower bound for all primes. -/
theorem packet_energy_le (N : ℕ) : ‖DeletionPrimePacket.packet N‖^2 ≤ ‖primePacket N‖^2 := by
  let S := (Icc 1 N).filter Nat.Prime
  have hsub : DeletionPeriodGrowth.upperPrimes N ⊆ S := by
    intro p hp
    obtain ⟨hpI,hpPrime,hpN⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpI,hpPrime⟩
  have hg (p q : ℕ) (hp : p ∈ S) (hq : q ∈ S) :
      0 ≤ bdGram (1/(p : ℝ)) (1/(q : ℝ)) :=
    gram_nonneg (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hid (T : Finset ℕ) := bdGram_quadraticForm_eq_norm_sq T
    (fun p => 1/(p : ℝ)) (fun _ => (1 : ℝ))
  simp only [one_mul, Complex.ofReal_one, one_smul] at hid
  rw [DeletionPrimePacket.packet, primePacket, ← hid, ← hid]
  calc
    _ ≤ ∑ p ∈ DeletionPeriodGrowth.upperPrimes N, ∑ q ∈ S,
        bdGram (1/(p : ℝ)) (1/(q : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hg p q (hsub hp) hq)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => Finset.sum_nonneg (fun q hq => hg p q hp hq))

/-- Fixed denominator for the explicit physical amplification floor. -/
def amplificationConstant : ℝ := 256*(8*(32768 : ℝ)^2)^2

theorem amplificationConstant_pos : 0 < amplificationConstant := by
  norm_num [amplificationConstant]

/-- Unconditional full energy of order at least N/log^4 N at the selected damping value. -/
theorem aperture_energy_eventually_lower :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ)/(amplificationConstant*Real.log (N : ℝ)^4) ≤ ‖source N (aperture N)‖^2 := by
  filter_upwards [DeletionPrimePacket.packet_norm_sq_eventually_lower,
    eventually_ge_atTop 2] with N hp hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hprime := hp.trans (packet_energy_le N)
  have hsq := pow_le_pow_left₀
    (show 0 ≤ (N : ℝ)/(8*(32768 : ℝ)^2*Real.log (N : ℝ)^2) by positivity) hprime 2
  rw [div_pow, ← pow_mul] at hsq
  have h := hsq.trans (aperture_energy_lower N)
  have hclear := (div_le_iff₀
    (show 0 < (8*(32768 : ℝ)^2*Real.log (N : ℝ)^2)^2 by positivity)).mp h
  apply (div_le_iff₀ (mul_pos amplificationConstant_pos (pow_pos hlog _))).mpr
  apply (mul_le_mul_iff_right₀ hN0).mp
  dsimp [amplificationConstant]
  nlinarith [hclear]


/-- No division-by-zero convention occurs at sufficiently late amplification points. -/
theorem aperture_source_norm_eventually_pos :
    ∀ᶠ N : ℕ in atTop, 0 < ‖source N (aperture N)‖ := by
  filter_upwards [aperture_energy_eventually_lower, eventually_ge_atTop 2] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hp : 0 < (N : ℝ)/(amplificationConstant*Real.log (N : ℝ)^4) := by
    exact div_pos (by linarith) (mul_pos amplificationConstant_pos (pow_pos hlog _))
  nlinarith [norm_nonneg (source N (aperture N))]

/-- The undamped source is smaller than the amplified source by every fixed log power. -/
theorem source_relative_energy_log_pow_tendsto_zero (q : ℕ) :
    Tendsto (fun N : ℕ => ‖source N 1‖^2*Real.log (N : ℝ)^q /
      ‖source N (aperture N)‖^2) atTop (𝓝 0) := by
  simp only [source_one, norm_neg]
  have hlim := (DeletionMobiusGlobal.modular_norm_log_pow_div_tendsto_zero (q+4)).const_mul
    amplificationConstant
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (Real.log_pos hN1).le q)) (sq_nonneg _)
  · filter_upwards [aperture_energy_eventually_lower, aperture_source_norm_eventually_pos,
      eventually_ge_atTop 2] with N hN hp hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hmul := (div_le_iff₀
      (mul_pos amplificationConstant_pos (pow_pos hlog 4))).mp hN
    calc
      _ ≤ (amplificationConstant*‖bdMobiusModularApproximantVec N‖^2*
          Real.log (N : ℝ)^(q+4))/(N : ℝ) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hp) hN0).mpr
        rw [pow_add]
        nlinarith [mul_le_mul_of_nonneg_left hmul
          (show 0 ≤ ‖bdMobiusModularApproximantVec N‖^2*Real.log (N : ℝ)^q by positivity)]
      _ = _ := by ring

/-- Every fixed amplification factor is exceeded at every sufficiently large cutoff. -/
theorem eventually_amplifies (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K*‖source N 1‖^2 < ‖source N (aperture N)‖^2 := by
  have hlim := source_relative_energy_log_pow_tendsto_zero 0
  simp only [pow_zero, mul_one] at hlim
  have he := hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1/(|K|+1) by positivity))
  filter_upwards [he, aperture_source_norm_eventually_pos] with N hN hp
  have hcross := (div_lt_div_iff₀ (sq_pos_of_pos hp)
    (show (0 : ℝ) < |K|+1 by positivity)).mp hN
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg ‖source N 1‖),
    sq_nonneg ‖source N 1‖]

/-- Uniform prime-count contraction fails on the literal Möbius source itself. -/
theorem not_exists_uniform_damping_budget :
    ¬ ∃ K : ℝ, ∀ N : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖source N u‖^2 ≤ K*‖source N 1‖^2 := by
  rintro ⟨K,hK⟩
  obtain ⟨N,hN⟩ := (eventually_amplifies K).exists
  have hu := aperture_mem N
  exact (not_lt_of_ge (hK N (aperture N) ⟨hu.1, by linarith [hu.2]⟩)) hN

end RHTower.PrimeCountDamping
