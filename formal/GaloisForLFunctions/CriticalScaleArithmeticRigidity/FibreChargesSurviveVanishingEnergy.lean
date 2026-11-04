import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PhysicalHorizonCharges
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.CoprimeModeTransport
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryLowConductorSeesTheFlipSet
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments

/-!
# Fibre charges survive vanishing energy

`exists_harmonic_neutral_physical_vanishing_charge` keeps a constant output `t` with vanishing
adjunction energy and physical input. This module answers the same question one conductor up: for a
fixed conductor `m`, inputs supported on the conductors `m p` (`p ∤ m` prime) retain the
**nonconstant** output `t·e_m`.

* **Fibre transport** (`normalizedConductorPacket_fibre`, `arithmeticPrimeGenerator_fibre`). For
  coefficients `b_p` on `m p`, the packet is `e_m · P_b` and, by the derivation law of the generator,
  `G = e_m · G(b) + S_m · P_b`, with `S_m` the generator image of the mode `e_m` and `P_b`, `G(b)` the
  prime packet of `b` and its generator image.
* **The residual.** On coherent coefficients `b_p = (t/B_m) √φ(p)/p`, `B_m = Σ_{p ≤ Q, p ∤ m} log p/p`,
  the prime decomposition gives `G(b) = t − X`, `X` the diagonal prime rows; hence
  `G − t e_m = −e_m X + S_m P_b`. Both `e_m` and `S_m` are `m`-periodic, so bounded.
* **Exact retention** (`packetMean_fibre_retains`). `X` and `P_b` have period `Π p`, prime to `m`,
  and period mean zero; the period mean factors over the coprime moduli, so the `e_m`-component of
  the output is exactly `t`.
* **Vanishing energies** (`fibreCharge_bounds`). The adjunction mass, the residual mean square, the
  physical input and the physical residual output are all at most `K_m t²/B_m`.
* **The test** (`exists_fibre_charge_vanishing_energy`). For every `m`, `t` and `ε > 0` there are
  harmonic-pole-neutral inputs on `{1} ∪ {m p}` with all four energies below `ε`, uniformly over
  horizons `N ≥ mQ`, whose output has `e_m`-component exactly `t`.

So every fixed nonconstant mode carries a receiving charge that energy and physical-input norms
erase: energy limits cannot detect receiving charges in any conductor.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SelectiveMultiscaleArithmeticPositivity ArithmeticIntersectionTheory
open RenormalizedArithmeticPotentialTheory (normalizedRamanujanMode normalizedRamanujanMode_periodic
  normalizedRamanujanMode_mul_of_coprime normalizedRamanujanMode_eq_coefficient
  sum_range_mul_of_periodic)

/-! ### Fibre coefficients -/

/-- The fibre primes of `m` below `Q`: primes `p ≤ Q` with `p ∤ m`. -/
def fibrePrimes (m Q : ℕ) : Finset ℕ := (Icc 1 Q).filter fun p => p.Prime ∧ ¬ p ∣ m

/-- Prime coefficients restricted to the fibre primes of `m`. -/
def fibreRestrict (m : ℕ) (b : ℕ → ℝ) (p : ℕ) : ℝ := if p.Prime ∧ ¬ p ∣ m then b p else 0

/-- The fibre input: coefficient `b_p` at the conductor `m p`, for the fibre primes `p`. -/
def fibreCoefficients (m Q : ℕ) (b : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ p ∈ fibrePrimes m Q, if c = m * p then b p else 0

theorem mem_fibrePrimes {m Q p : ℕ} :
    p ∈ fibrePrimes m Q ↔ p ∈ Icc 1 Q ∧ p.Prime ∧ ¬ p ∣ m := by
  rw [fibrePrimes, mem_filter]

theorem coprime_of_mem_fibrePrimes {m Q p : ℕ} (hp : p ∈ fibrePrimes m Q) : m.Coprime p :=
  Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (mem_fibrePrimes.mp hp).2.1).mpr
    (mem_fibrePrimes.mp hp).2.2)

theorem fibreCoefficients_mul {m Q : ℕ} (hm : 0 < m) (b : ℕ → ℝ) {p : ℕ}
    (hp : p ∈ fibrePrimes m Q) : fibreCoefficients m Q b (m * p) = b p := by
  unfold fibreCoefficients
  rw [sum_eq_single p (fun q _ hqp => if_neg fun h => hqp (Nat.eq_of_mul_eq_mul_left hm h).symm)
    (fun h => absurd hp h), if_pos rfl]

/-- Sums over the conductors `≤ mQ` of a fibre input are sums over the fibre primes. -/
theorem sum_fibreCoefficients {m Q : ℕ} (hm : 0 < m) (b : ℕ → ℝ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ c, F c 0 = 0) :
    ∑ c ∈ Icc 1 (m * Q), F c (fibreCoefficients m Q b c) =
      ∑ p ∈ fibrePrimes m Q, F (m * p) (b p) := by
  have hsub : (fibrePrimes m Q).image (fun p => m * p) ⊆ Icc 1 (m * Q) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hc
    obtain ⟨hpI, -, -⟩ := mem_fibrePrimes.mp hp
    obtain ⟨hp1, hpQ⟩ := mem_Icc.mp hpI
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' (by omega)),
      Nat.mul_le_mul_left m hpQ⟩
  rw [← sum_subset hsub fun c _ hc => by
      rw [show fibreCoefficients m Q b c = 0 from sum_eq_zero fun p hp =>
        if_neg fun h => hc (mem_image.mpr ⟨p, hp, h.symm⟩), hF],
    sum_image fun p _ q _ h => Nat.eq_of_mul_eq_mul_left hm h]
  exact sum_congr rfl fun p hp => by rw [fibreCoefficients_mul hm b hp]

/-- Sums against the restricted coefficients run over the fibre primes. -/
theorem sum_fibreRestrict (m Q : ℕ) (b f : ℕ → ℝ) :
    ∑ p ∈ Icc 1 Q, fibreRestrict m b p * f p = ∑ p ∈ fibrePrimes m Q, b p * f p := by
  rw [fibrePrimes, sum_filter]
  exact sum_congr rfl fun p _ => by unfold fibreRestrict; split_ifs <;> simp

theorem primeOnly_fibreRestrict (m : ℕ) (b : ℕ → ℝ) : primeOnly (fibreRestrict m b) = fibreRestrict m b := by
  funext p
  unfold primeOnly fibreRestrict
  by_cases hp : p.Prime <;> simp [hp]

/-! ### Fibre transport -/

/-- **The fibre packet is `e_m · P_b`.** -/
theorem normalizedConductorPacket_fibre {m : ℕ} (hm : 0 < m) (Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket (m * Q) (fibreCoefficients m Q b) n =
      normalizedRamanujanMode m n * normalizedConductorPacket Q (fibreRestrict m b) n := by
  rw [normalizedConductorPacket, sum_fibreCoefficients hm b (fun c x => x * normalizedRamanujanMode c n)
    (fun _ => zero_mul _), normalizedConductorPacket, sum_fibreRestrict, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [normalizedRamanujanMode_mul_of_coprime hm (mem_fibrePrimes.mp hp).2.1.pos
    (coprime_of_mem_fibrePrimes hp)]
  ring

/-- **The generator on a fibre.** `G(fibre b) = e_m · G(b) + S_m · P_b`. -/
theorem arithmeticPrimeGenerator_fibre {m : ℕ} (hm : 0 < m) (Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q b) n =
      normalizedRamanujanMode m n * arithmeticPrimeGenerator Q (fibreRestrict m b) n +
        normalizedPrimeModeSource m n * normalizedConductorPacket Q (fibreRestrict m b) n := by
  rw [arithmeticPrimeGenerator_eq_modeSource, sum_fibreCoefficients hm b
      (fun c x => x * normalizedPrimeModeSource c n) (fun _ => zero_mul _),
    arithmeticPrimeGenerator_eq_modeSource, sum_fibreRestrict, normalizedConductorPacket,
    sum_fibreRestrict, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [normalizedPrimeModeSource_mul_of_coprime hm (mem_fibrePrimes.mp hp).2.1.pos
    (coprime_of_mem_fibrePrimes hp)]
  ring

/-! ### Periodicity and boundedness -/

theorem normalizedPrimeModeSource_periodic {m : ℕ} (hm : 0 < m) :
    Function.Periodic (normalizedPrimeModeSource m) m := by
  intro n
  simp only [normalizedPrimeModeSource]
  rw [SuccessorShellArithmetic.ramanujanLogDivisorJet_periodic m n,
    normalizedRamanujanMode_periodic hm n]

/-- A periodic sequence is bounded by its absolute mass over one period. -/
theorem abs_le_periodSum {f : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hf : Function.Periodic f P) (n : ℕ) :
    |f n| ≤ ∑ j ∈ range P, |f j| := by
  rw [← hf.map_mod_nat n]
  exact single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _)
    (mem_range.mpr (Nat.mod_lt n hP))

/-- The mode bound `C_m`. -/
def modeBound (m : ℕ) : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|

/-- The source bound `C'_m`. -/
def sourceBound (m : ℕ) : ℝ := ∑ j ∈ range m, |normalizedPrimeModeSource m j|

theorem sq_mode_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    normalizedRamanujanMode m n ^ 2 ≤ modeBound m ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_periodSum hm (normalizedRamanujanMode_periodic hm) n) 2

theorem sq_source_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    normalizedPrimeModeSource m n ^ 2 ≤ sourceBound m ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_periodSum hm (normalizedPrimeModeSource_periodic hm) n) 2

/-- A packet whose conductors divide `L` has period `L`. -/
theorem normalizedConductorPacket_periodic {Q L : ℕ} {a : ℕ → ℝ}
    (ha : ∀ c ∈ Icc 1 Q, a c ≠ 0 → c ∣ L) :
    Function.Periodic (normalizedConductorPacket Q a) L := by
  intro n
  refine sum_congr rfl fun c hc => ?_
  by_cases h0 : a c = 0
  · rw [h0, zero_mul, zero_mul]
  · obtain ⟨k, hk⟩ := ha c hc h0
    have hper := (normalizedRamanujanMode_periodic (mem_Icc.mp hc).1).nat_mul k n
    rw [Nat.cast_id] at hper
    rw [hk, mul_comm c k, hper]

/-- Extending a packet's cutoff by zero coefficients. -/
theorem normalizedConductorPacket_extend {Q Q' : ℕ} (hQ : Q ≤ Q') (a : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q a n =
      normalizedConductorPacket Q' (fun c => if c ≤ Q then a c else 0) n := by
  unfold normalizedConductorPacket
  have hfilt : (Icc 1 Q').filter (· ≤ Q) = Icc 1 Q := by
    ext c; simp only [mem_filter, mem_Icc]; omega
  rw [← hfilt, sum_filter]
  exact sum_congr rfl fun c _ => by by_cases h : c ≤ Q <;> simp [h]

theorem sum_sq_extend {Q Q' : ℕ} (hQ : Q ≤ Q') (a : ℕ → ℝ) :
    ∑ c ∈ Icc 1 Q', (if c ≤ Q then a c else 0) ^ 2 = ∑ c ∈ Icc 1 Q, a c ^ 2 := by
  have hfilt : (Icc 1 Q').filter (· ≤ Q) = Icc 1 Q := by
    ext c; simp only [mem_filter, mem_Icc]; omega
  rw [← hfilt, sum_filter]
  exact sum_congr rfl fun c _ => by by_cases h : c ≤ Q <;> simp [h]

/-- The mean square of a packet over any larger complete period is its coefficient mass. -/
theorem packetMean_packet_sq_of_le {Q Q' : ℕ} (hQ : Q ≤ Q') (a : ℕ → ℝ) :
    packetMean Q' (fun n => normalizedConductorPacket Q a n ^ 2) = ∑ c ∈ Icc 1 Q, a c ^ 2 := by
  simp only [normalizedConductorPacket_extend hQ a]
  rw [packetMean_normalizedPacket_sq, sum_sq_extend hQ]

/-! ### Period means over coprime moduli -/

/-- **A product with a mean-zero factor of coprime period has zero complete mean.** -/
theorem packetMean_mul_eq_zero_of_coprime {Q' m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (hmL : m.Coprime L) (hdvd : m * L ∣ Q'.factorial) {f g : ℕ → ℝ}
    (hf : Function.Periodic f m) (hg : Function.Periodic g L)
    (hg0 : ∑ n ∈ range L, g n = 0) :
    packetMean Q' (fun n => f n * g n) = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  have hfg : Function.Periodic (fun n => f n * g n) (m * L) := by
    intro n
    have h1 := (hf.nat_mul L) n
    have h2 := (hg.nat_mul m) n
    rw [Nat.cast_id, mul_comm] at h1
    rw [Nat.cast_id] at h2
    show f (n + m * L) * g (n + m * L) = f n * g n
    rw [h1, h2]
  have hsum : ∑ n ∈ range Q'.factorial, f n * g n = 0 := by
    rw [hk, mul_comm (m * L) k, sum_range_mul_of_periodic hfg k,
      _root_.RHTower.DeletionCoprimeWords.coprime_period_sum_mul hm hL hmL hf hg, hg0, mul_zero,
      mul_zero]
  rw [packetMean, hsum, zero_div]

/-- The product of the fibre primes. -/
def fibreModulus (m Q : ℕ) : ℕ := ∏ p ∈ fibrePrimes m Q, p

theorem fibreModulus_pos (m Q : ℕ) : 0 < fibreModulus m Q :=
  prod_pos fun _ hp => (mem_fibrePrimes.mp hp).2.1.pos

theorem coprime_fibreModulus (m Q : ℕ) : m.Coprime (fibreModulus m Q) :=
  Nat.Coprime.prod_right fun _ hp => coprime_of_mem_fibrePrimes hp

theorem fibreModulus_dvd_factorial (m Q : ℕ) : fibreModulus m Q ∣ Q.factorial :=
  prod_primes_dvd _ (fun _ hp => (mem_fibrePrimes.mp hp).2.1.prime)
    fun _ hp => Nat.dvd_factorial (mem_Icc.mp (mem_fibrePrimes.mp hp).1).1
      (mem_Icc.mp (mem_fibrePrimes.mp hp).1).2

theorem mul_fibreModulus_dvd {m Q : ℕ} (hm : 0 < m) (hQ : 1 ≤ Q) :
    m * fibreModulus m Q ∣ (m * Q).factorial :=
  (coprime_fibreModulus m Q).mul_dvd_of_dvd_of_dvd
    (Nat.dvd_factorial hm (Nat.le_mul_of_pos_right m hQ))
    ((fibreModulus_dvd_factorial m Q).trans (Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_left Q hm)))

/-- A fibre packet has period the fibre modulus. -/
theorem fibrePacket_periodic {m Q : ℕ} {a : ℕ → ℝ}
    (ha : ∀ c ∈ Icc 1 Q, a c ≠ 0 → c ∈ fibrePrimes m Q) :
    Function.Periodic (normalizedConductorPacket Q a) (fibreModulus m Q) :=
  normalizedConductorPacket_periodic fun c hc h0 => dvd_prod_of_mem _ (ha c hc h0)

/-- A prime-supported packet has zero sum over any of its periods dividing `Q!`. -/
theorem sum_range_primePacket_eq_zero {Q L : ℕ} (hLQ : L ∣ Q.factorial)
    (a : ℕ → ℝ) (hper : Function.Periodic (normalizedConductorPacket Q (primeOnly a)) L) :
    ∑ n ∈ range L, normalizedConductorPacket Q (primeOnly a) n = 0 := by
  obtain ⟨k, hk⟩ := hLQ
  have hmean := packetMean_primeOnly_eq_zero Q a
  rw [packetMean, div_eq_zero_iff] at hmean
  rcases hmean with h | h
  · rw [hk, mul_comm, sum_range_mul_of_periodic hper k] at h
    have hk0 : (k : ℝ) ≠ 0 := by
      have : k ≠ 0 := by rintro rfl; simp at hk; exact (Nat.factorial_ne_zero Q) hk
      exact_mod_cast this
    exact (mul_eq_zero.mp h).resolve_left hk0
  · exact absurd h (by exact_mod_cast (Nat.factorial_ne_zero Q))

/-! ### Coherent fibre charge -/

/-- The fibre Mertens mass `B_m(Q) = Σ_{p ≤ Q, p ∤ m} log p/p`. -/
def fibreScale (m Q : ℕ) : ℝ := ∑ p ∈ fibrePrimes m Q, Real.log p / p

/-- The coherent fibre coefficients `b_p = (t/B_m(Q)) √φ(p)/p`. -/
def fibreCharge (m Q : ℕ) (t : ℝ) (p : ℕ) : ℝ := t / fibreScale m Q * primePoleWitness p

/-- The constant `Σ_{p ∣ m} log p/p` lost by the fibre. -/
def fibreLoss (m : ℕ) : ℝ := ∑ p ∈ m.primeFactors, Real.log p / p

theorem fibreScale_ge {m : ℕ} (hm : 0 < m) (Q : ℕ) :
    primePoleScale Q - fibreLoss m ≤ fibreScale m Q := by
  have hsplit := sum_filter_add_sum_filter_not ((Icc 1 Q).filter Nat.Prime) (fun p => p ∣ m)
    (fun p => Real.log p / p)
  have hfib : ((Icc 1 Q).filter Nat.Prime).filter (fun p => ¬ p ∣ m) = fibrePrimes m Q := by
    ext p; simp only [mem_filter, fibrePrimes]; tauto
  rw [hfib] at hsplit
  have hsub : ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ∣ m) ⊆ m.primeFactors := by
    intro p hp
    simp only [mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨hp.1.2, hp.2, hm.ne'⟩
  have hle : ∑ p ∈ ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ∣ m), Real.log p / p ≤
      fibreLoss m :=
    sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => div_nonneg (Real.log_natCast_nonneg p)
      (Nat.cast_nonneg p)
  unfold primePoleScale fibreScale
  linarith

theorem fibreScale_tendsto_atTop {m : ℕ} (hm : 0 < m) : Tendsto (fibreScale m) atTop atTop :=
  tendsto_atTop_mono (fibreScale_ge hm) (tendsto_atTop_add_const_right _ _ primePoleScale_tendsto_atTop)

/-- `√φ(p)` for a prime. -/
theorem sqrt_totient_prime_pos {p : ℕ} (hp : p.Prime) : 0 < Real.sqrt (p.totient : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)

/-- The coherent fibre charge has response exactly `t`. -/
theorem primePoleResponse_fibreCharge {m Q : ℕ} (t : ℝ) (hB : fibreScale m Q ≠ 0) :
    primePoleResponse Q (fibreRestrict m (fibreCharge m Q t)) = t := by
  have h : primePoleResponse Q (fibreRestrict m (fibreCharge m Q t)) =
      ∑ p ∈ fibrePrimes m Q, Real.log p / Real.sqrt (p.totient : ℝ) * fibreCharge m Q t p := by
    unfold primePoleResponse fibrePrimes fibreRestrict
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime <;> by_cases hpm : p ∣ m <;> simp [hp, hpm]
  rw [h]
  have hterm : ∀ p ∈ fibrePrimes m Q, Real.log p / Real.sqrt (p.totient : ℝ) *
      fibreCharge m Q t p = t / fibreScale m Q * (Real.log p / p) := by
    intro p hp
    have hs := (sqrt_totient_prime_pos (mem_fibrePrimes.mp hp).2.1).ne'
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_fibrePrimes.mp hp).2.1.ne_zero
    unfold fibreCharge primePoleWitness
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  change t / fibreScale m Q * fibreScale m Q = t
  exact div_mul_cancel₀ _ hB

/-- For a prime, `(log p + τ(p)) w_p² = log p/p`. -/
theorem adjunctionWeight_mul_witness_sq {p : ℕ} (hp : p.Prime) :
    (Real.log p + tameDifferent p) * primePoleWitness p ^ 2 = Real.log p / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have ht := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
  simp only [pow_one] at ht
  rw [ht, primePoleWitness, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  field_simp
  ring

/-- `w_p² ≤ 2 log p/p`. -/
theorem witness_sq_le {p : ℕ} (hp : p.Prime) : primePoleWitness p ^ 2 ≤ 2 * (Real.log p / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl2 := Real.log_two_gt_d9
  rw [primePoleWitness, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hp0 : (0 : ℝ) < p := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * (Real.log p / p) * (p : ℝ) ^ 2 = 2 * Real.log p * p := by field_simp
  rw [this]
  nlinarith

/-- `τ(p)² ≤ 1` for a prime. -/
theorem tameDifferent_prime_sq_le {p : ℕ} (hp : p.Prime) : tameDifferent p ^ 2 ≤ 1 := by
  have ht := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
  simp only [pow_one] at ht
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < p)
  have hl0 := Real.log_natCast_nonneg p
  rw [ht]
  have h0 : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg hl0 (by linarith)
  have h1 : Real.log p / ((p : ℝ) - 1) ≤ 1 := (div_le_one (by linarith)).mpr hlog
  nlinarith

theorem tameDifferent_nonneg (n : ℕ) : 0 ≤ tameDifferent n := by
  unfold tameDifferent
  exact sum_nonneg fun p hp => div_nonneg (Real.log_natCast_nonneg p)
    (sub_nonneg.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))

/-- The restricted squares are the fibre squares. -/
theorem sum_fibreRestrict_sq (m Q : ℕ) (b : ℕ → ℝ) :
    ∑ p ∈ Icc 1 Q, fibreRestrict m b p ^ 2 = ∑ p ∈ fibrePrimes m Q, b p ^ 2 := by
  rw [fibrePrimes, sum_filter]
  exact sum_congr rfl fun p _ => by unfold fibreRestrict; split_ifs <;> simp

/-- The coefficient mass of the coherent fibre charge is at most `2t²/B`. -/
theorem sum_fibreCharge_sq_le {m Q : ℕ} (t : ℝ) (hB : 0 < fibreScale m Q) :
    ∑ p ∈ fibrePrimes m Q, fibreCharge m Q t p ^ 2 ≤ 2 * (t ^ 2 / fibreScale m Q) := by
  have hterm : ∀ p ∈ fibrePrimes m Q, fibreCharge m Q t p ^ 2 ≤
      (t / fibreScale m Q) ^ 2 * (2 * (Real.log p / p)) := fun p hp => by
    rw [fibreCharge, mul_pow]
    exact mul_le_mul_of_nonneg_left (witness_sq_le (mem_fibrePrimes.mp hp).2.1) (sq_nonneg _)
  calc ∑ p ∈ fibrePrimes m Q, fibreCharge m Q t p ^ 2
      ≤ ∑ p ∈ fibrePrimes m Q, (t / fibreScale m Q) ^ 2 * (2 * (Real.log p / p)) :=
        sum_le_sum hterm
    _ = 2 * (t ^ 2 / fibreScale m Q) := by
        rw [← mul_sum, ← mul_sum]
        change (t / fibreScale m Q) ^ 2 * (2 * fibreScale m Q) = _
        field_simp

/-- The diagonal prime rows carry no more mass than the input. -/
theorem sum_tame_fibre_sq_le (m Q : ℕ) (b : ℕ → ℝ) :
    ∑ c ∈ Icc 1 Q, primeOnly (fun p => tameDifferent p * fibreRestrict m b p) c ^ 2 ≤
      ∑ c ∈ Icc 1 Q, fibreRestrict m b c ^ 2 := by
  refine sum_le_sum fun c _ => ?_
  unfold primeOnly
  split_ifs with hc
  · rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (tameDifferent_prime_sq_le hc)
  · rw [sq, zero_mul]; exact sq_nonneg _

/-- The adjunction mass of the coherent fibre charge. -/
theorem primeAdjunctionMass_fibreCharge {m Q : ℕ} (hm : 0 < m) (t : ℝ)
    (hB : 0 < fibreScale m Q) :
    primeAdjunctionMass (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) ≤
      (2 * (Real.log m + tameDifferent m) + 1) * (t ^ 2 / fibreScale m Q) := by
  rw [primeAdjunctionMass, sum_fibreCoefficients hm _
    (fun c x => (Real.log c + tameDifferent c) * x ^ 2) (fun _ => by simp)]
  have hsplit : ∀ p ∈ fibrePrimes m Q,
      (Real.log (m * p : ℕ) + tameDifferent (m * p)) * fibreCharge m Q t p ^ 2 =
        (Real.log m + tameDifferent m) * fibreCharge m Q t p ^ 2 +
          (t / fibreScale m Q) ^ 2 * (Real.log p / p) := by
    intro p hp
    rw [adjunctionWeight_mul_of_coprime hm (mem_fibrePrimes.mp hp).2.1.pos
      (coprime_of_mem_fibrePrimes hp), add_mul, fibreCharge, mul_pow,
      ← adjunctionWeight_mul_witness_sq (mem_fibrePrimes.mp hp).2.1]
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum, ← mul_sum]
  change (Real.log m + tameDifferent m) * ∑ p ∈ fibrePrimes m Q, fibreCharge m Q t p ^ 2 +
    (t / fibreScale m Q) ^ 2 * fibreScale m Q ≤ _
  have hmass := sum_fibreCharge_sq_le (m := m) (Q := Q) t hB
  have hw : 0 ≤ Real.log m + tameDifferent m := by
    linarith [Real.log_natCast_nonneg m, tameDifferent_nonneg m]
  have hq : (t / fibreScale m Q) ^ 2 * fibreScale m Q = t ^ 2 / fibreScale m Q := by
    field_simp
  rw [hq]
  nlinarith [mul_le_mul_of_nonneg_left hmass hw]

/-! ### The residual -/

/-- The diagonal prime rows of the restricted input. -/
def fibreRows (m Q : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * fibreRestrict m b p)) n

/-- On the restricted input the generator is the response minus the diagonal prime rows. -/
theorem arithmeticPrimeGenerator_fibreRestrict (m Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q (fibreRestrict m b) n =
      primePoleResponse Q (fibreRestrict m b) - fibreRows m Q b n := by
  conv_lhs => rw [← primeOnly_fibreRestrict m b]
  rw [arithmeticPrimeGenerator_primeOnly_decomposition, fibreRows]

/-- **The fibre residual.** `G − t e_m = −e_m X + S_m P_b` on the coherent fibre charge. -/
theorem fibre_residual {m Q : ℕ} (hm : 0 < m) (t : ℝ) (hB : fibreScale m Q ≠ 0) (n : ℕ) :
    arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n -
        t * normalizedRamanujanMode m n =
      -(normalizedRamanujanMode m n * fibreRows m Q (fibreCharge m Q t) n) +
        normalizedPrimeModeSource m n *
          normalizedConductorPacket Q (fibreRestrict m (fibreCharge m Q t)) n := by
  rw [arithmeticPrimeGenerator_fibre hm, arithmeticPrimeGenerator_fibreRestrict,
    primePoleResponse_fibreCharge t hB]
  ring

/-- Pointwise bound of the residual square. -/
theorem fibre_residual_sq_le {m Q : ℕ} (hm : 0 < m) (t : ℝ) (hB : fibreScale m Q ≠ 0) (n : ℕ) :
    (arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n -
        t * normalizedRamanujanMode m n) ^ 2 ≤
      2 * modeBound m ^ 2 * fibreRows m Q (fibreCharge m Q t) n ^ 2 +
        2 * sourceBound m ^ 2 *
          normalizedConductorPacket Q (fibreRestrict m (fibreCharge m Q t)) n ^ 2 := by
  rw [fibre_residual hm t hB]
  set e := normalizedRamanujanMode m n
  set S := normalizedPrimeModeSource m n
  set X := fibreRows m Q (fibreCharge m Q t) n
  set P := normalizedConductorPacket Q (fibreRestrict m (fibreCharge m Q t)) n
  have he := sq_mode_le hm n
  have hS := sq_source_le hm n
  have h1 : (-(e * X) + S * P) ^ 2 ≤ 2 * (e ^ 2 * X ^ 2) + 2 * (S ^ 2 * P ^ 2) := by
    nlinarith [sq_nonneg (e * X + S * P)]
  have h2 : e ^ 2 * X ^ 2 ≤ modeBound m ^ 2 * X ^ 2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
  have h3 : S ^ 2 * P ^ 2 ≤ sourceBound m ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right hS (sq_nonneg _)
  nlinarith

/-! ### Complete means -/

theorem packetMean_mono {Q : ℕ} {f g : ℕ → ℝ} (h : ∀ n, f n ≤ g n) :
    packetMean Q f ≤ packetMean Q g :=
  div_le_div_of_nonneg_right (sum_le_sum fun n _ => h n) (Nat.cast_nonneg _)

/-- The square-mean of the mode is one over every complete period containing it. -/
theorem packetMean_mode_sq {m Q' : ℕ} (hm : 0 < m) (hmQ : m ≤ Q') :
    packetMean Q' (fun n => normalizedRamanujanMode m n ^ 2) = 1 := by
  have hmem : m ∈ Icc 1 Q' := mem_Icc.mpr ⟨hm, hmQ⟩
  have hpk : ∀ n, normalizedRamanujanMode m n =
      normalizedConductorPacket Q' (fun c => if c = m then 1 else 0) n := fun n => by
    simp only [normalizedConductorPacket, ite_mul, one_mul, zero_mul, sum_ite_eq', if_pos hmem]
  simp only [hpk]
  rw [packetMean_normalizedPacket_sq]
  simp only [ite_pow, one_pow, zero_pow two_ne_zero, sum_ite_eq', if_pos hmem]

/-- **Exact retention.** The `e_m`-component of the output is exactly `t`. -/
theorem packetMean_fibre_retains {m Q : ℕ} (hm : 0 < m) (hQ : 1 ≤ Q) (t : ℝ)
    (hB : fibreScale m Q ≠ 0) :
    packetMean (m * Q) (fun n =>
      arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n *
        normalizedRamanujanMode m n) = t := by
  set L := fibreModulus m Q
  set fR := fibreRestrict m (fibreCharge m Q t)
  have hLQ := fibreModulus_dvd_factorial m Q
  have hdvd := mul_fibreModulus_dvd hm hQ
  have hpoint : ∀ n,
      arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n *
          normalizedRamanujanMode m n =
        t * normalizedRamanujanMode m n ^ 2 +
          (-(normalizedRamanujanMode m n ^ 2) * fibreRows m Q (fibreCharge m Q t) n +
            (normalizedPrimeModeSource m n * normalizedRamanujanMode m n) *
              normalizedConductorPacket Q (primeOnly fR) n) := by
    intro n
    have h := fibre_residual hm t hB n
    rw [primeOnly_fibreRestrict]
    linear_combination normalizedRamanujanMode m n * h
  simp only [hpoint]
  rw [packetMean_add, packetMean_add, packetMean_const_mul, packetMean_mode_sq hm
    (Nat.le_mul_of_pos_right m hQ)]
  -- Both remaining factors have coprime periods and a mean-zero factor.
  have hsuppX : ∀ c ∈ Icc 1 Q,
      primeOnly (fun p => tameDifferent p * fR p) c ≠ 0 → c ∈ fibrePrimes m Q := by
    intro c hc h0
    unfold primeOnly at h0
    split_ifs at h0 with hcp
    · have : fR c ≠ 0 := fun h => h0 (by simp only [h, mul_zero])
      unfold fR fibreRestrict at this
      split_ifs at this with hcm
      · exact mem_fibrePrimes.mpr ⟨hc, hcm⟩
      · exact absurd rfl this
    · exact absurd rfl h0
  have hsuppP : ∀ c ∈ Icc 1 Q, primeOnly fR c ≠ 0 → c ∈ fibrePrimes m Q := by
    intro c hc h0
    rw [primeOnly_fibreRestrict] at h0
    unfold fibreRestrict at h0
    split_ifs at h0 with hcm
    · exact mem_fibrePrimes.mpr ⟨hc, hcm⟩
    · exact absurd rfl h0
  have hperX := fibrePacket_periodic hsuppX
  have hperP := fibrePacket_periodic hsuppP
  have hmodeSq : Function.Periodic (fun n => -(normalizedRamanujanMode m n ^ 2)) m := fun n => by
    simp only [normalizedRamanujanMode_periodic hm n]
  have hSe : Function.Periodic
      (fun n => normalizedPrimeModeSource m n * normalizedRamanujanMode m n) m := fun n => by
    simp only [normalizedPrimeModeSource_periodic hm n, normalizedRamanujanMode_periodic hm n]
  have h1 := packetMean_mul_eq_zero_of_coprime hm (fibreModulus_pos m Q) (coprime_fibreModulus m Q)
    hdvd hmodeSq hperX (sum_range_primePacket_eq_zero hLQ _ hperX)
  have h2 := packetMean_mul_eq_zero_of_coprime hm (fibreModulus_pos m Q) (coprime_fibreModulus m Q)
    hdvd hSe hperP (sum_range_primePacket_eq_zero hLQ _ hperP)
  unfold fibreRows at h1 ⊢
  rw [h1, h2]
  ring

/-! ### Vanishing energies -/

/-- The fibre constant `K_m`. -/
def fibreConstant (m : ℕ) : ℝ :=
  2 * (Real.log m + tameDifferent m) + 1 + 208 * (modeBound m ^ 2 + sourceBound m ^ 2)

theorem fibreConstant_nonneg (m : ℕ) : 0 ≤ fibreConstant m := by
  unfold fibreConstant
  have := Real.log_natCast_nonneg m
  have := tameDifferent_nonneg m
  positivity

/-- **Quantitative fibre bounds.** On the harmonic-pole-neutral coherent fibre charge, every
energy is at most `K_m t²/B_m(Q)` and the `e_m`-component of the output is exactly `t`. -/
theorem fibreCharge_bounds {m Q N : ℕ} (hm : 0 < m) (hQ : 2 ≤ Q) (hQN : m * Q ≤ N) (t : ℝ)
    (hB : 0 < fibreScale m Q) :
    let a := harmonicCenteredCoefficients (m * Q) N (fibreCoefficients m Q (fibreCharge m Q t))
    (∀ c, a c ≠ 0 → c = 1 ∨ ∃ p ∈ fibrePrimes m Q, c = m * p) ∧
    harmonicSum N (conductorHorizonProfile (m * Q) a) = 0 ∧
    primeAdjunctionMass (m * Q) a ≤ fibreConstant m * (t ^ 2 / fibreScale m Q) ∧
    packetMean (m * Q) (fun n =>
      arithmeticPrimeGenerator (m * Q) a n * normalizedRamanujanMode m n) = t ∧
    packetMean (m * Q) (fun n =>
      (arithmeticPrimeGenerator (m * Q) a n - t * normalizedRamanujanMode m n) ^ 2) ≤
        fibreConstant m * (t ^ 2 / fibreScale m Q) ∧
    (∑ n ∈ Icc 1 N, conductorHorizonProfile (m * Q) a n ^ 2) / Real.log N ≤
        fibreConstant m * (t ^ 2 / fibreScale m Q) ∧
    (∑ n ∈ Icc 1 N, (arithmeticPrimeGenerator (m * Q) a n - t * normalizedRamanujanMode m n) ^ 2 /
        (n : ℝ)) / Real.log N ≤ fibreConstant m * (t ^ 2 / fibreScale m Q) := by
  intro a
  set b := fibreCharge m Q t
  set fR := fibreRestrict m b
  set μ := t ^ 2 / fibreScale m Q with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (sq_nonneg _) hB.le
  have hQ1 : 1 ≤ Q := by omega
  have hmQ : 1 ≤ m * Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' (by omega))
  have hN : 1 ≤ N := hmQ.trans hQN
  have hQN' : Q ≤ N := (Nat.le_mul_of_pos_left Q hm).trans hQN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hG : ∀ n, arithmeticPrimeGenerator (m * Q) a n =
      arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q b) n := fun n =>
    arithmeticPrimeGenerator_harmonicCentered _ _ _ n
  have hmass : ∑ p ∈ Icc 1 Q, fR p ^ 2 ≤ 2 * μ := by
    rw [sum_fibreRestrict_sq]; exact sum_fibreCharge_sq_le t hB
  have htame := sum_tame_fibre_sq_le m Q b
  have hCm : 0 ≤ modeBound m ^ 2 := sq_nonneg _
  have hSm : 0 ≤ sourceBound m ^ 2 := sq_nonneg _
  have hw : 0 ≤ Real.log m + tameDifferent m := by
    linarith [Real.log_natCast_nonneg m, tameDifferent_nonneg m]
  have hK1 : 2 * (Real.log m + tameDifferent m) + 1 ≤ fibreConstant m := by
    unfold fibreConstant; nlinarith
  have hK2 : 208 * (modeBound m ^ 2 + sourceBound m ^ 2) ≤ fibreConstant m := by
    unfold fibreConstant; nlinarith
  refine ⟨?_, harmonicSum_centeredCoefficients hmQ hN _, ?_, ?_, ?_, ?_, ?_⟩
  · -- Support.
    intro c hc
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · right
      have : fibreCoefficients m Q b c ≠ 0 := by
        simpa [a, harmonicCenteredCoefficients, addConstantConductor, hc1] using hc
      obtain ⟨p, hp, hne⟩ := exists_ne_zero_of_sum_ne_zero this
      exact ⟨p, hp, by by_contra h; exact hne (if_neg h)⟩
  · -- Adjunction.
    rw [primeAdjunctionMass_harmonicCentered]
    exact (primeAdjunctionMass_fibreCharge hm t hB).trans (mul_le_mul_of_nonneg_right hK1 hμ0)
  · -- Retention.
    simp only [hG]
    exact packetMean_fibre_retains hm hQ1 t hB.ne'
  · -- Residual mean square.
    simp only [hG]
    calc packetMean (m * Q) (fun n =>
          (arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q b) n -
            t * normalizedRamanujanMode m n) ^ 2)
        ≤ packetMean (m * Q) (fun n => 2 * modeBound m ^ 2 * fibreRows m Q b n ^ 2 +
            2 * sourceBound m ^ 2 * normalizedConductorPacket Q fR n ^ 2) :=
          packetMean_mono fun n => fibre_residual_sq_le hm t hB.ne' n
      _ = 2 * modeBound m ^ 2 * ∑ c ∈ Icc 1 Q,
            primeOnly (fun p => tameDifferent p * fR p) c ^ 2 +
          2 * sourceBound m ^ 2 * ∑ c ∈ Icc 1 Q, fR c ^ 2 := by
          rw [packetMean_add, packetMean_const_mul, packetMean_const_mul]
          unfold fibreRows
          rw [packetMean_packet_sq_of_le (Nat.le_mul_of_pos_left Q hm),
            packetMean_packet_sq_of_le (Nat.le_mul_of_pos_left Q hm)]
      _ ≤ 2 * modeBound m ^ 2 * (2 * μ) + 2 * sourceBound m ^ 2 * (2 * μ) := by
          gcongr
          exact htame.trans hmass
      _ ≤ fibreConstant m * μ := by nlinarith
  · -- Physical input.
    have hprof := harmonicCentered_profile_sq_le hmQ hN (fibreCoefficients m Q b)
    have hpt : ∀ n ∈ Icc 1 N, conductorHorizonProfile (m * Q) (fibreCoefficients m Q b) n ^ 2 ≤
        modeBound m ^ 2 * (normalizedConductorPacket Q fR n ^ 2 / (n : ℝ)) := by
      intro n _
      rw [conductorHorizonProfile, normalizedConductorPacket_fibre hm, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (sq_mode_le hm n) (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    have hharm := harmonicPacket_sq_div_log_le_mass hQ hQN' fR
    calc (∑ n ∈ Icc 1 N, conductorHorizonProfile (m * Q) a n ^ 2) / Real.log N
        ≤ (∑ n ∈ Icc 1 N, conductorHorizonProfile (m * Q) (fibreCoefficients m Q b) n ^ 2) /
            Real.log N := div_le_div_of_nonneg_right hprof hL.le
      _ ≤ (modeBound m ^ 2 * ∑ n ∈ Icc 1 N, normalizedConductorPacket Q fR n ^ 2 / (n : ℝ)) /
            Real.log N := by
          rw [mul_sum]; exact div_le_div_of_nonneg_right (sum_le_sum hpt) hL.le
      _ = modeBound m ^ 2 * ((∑ n ∈ Icc 1 N, normalizedConductorPacket Q fR n ^ 2 / (n : ℝ)) /
            Real.log N) := by ring
      _ ≤ modeBound m ^ 2 * (52 * (2 * μ)) := by
          gcongr
          exact hharm.trans (by linarith)
      _ ≤ fibreConstant m * μ := by nlinarith
  · -- Physical residual output.
    simp only [hG]
    have hpt : ∀ n ∈ Icc 1 N,
        (arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q b) n -
            t * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) ≤
          2 * modeBound m ^ 2 * (fibreRows m Q b n ^ 2 / (n : ℝ)) +
            2 * sourceBound m ^ 2 * (normalizedConductorPacket Q fR n ^ 2 / (n : ℝ)) := by
      intro n _
      have h := div_le_div_of_nonneg_right (fibre_residual_sq_le hm t hB.ne' n)
        (Nat.cast_nonneg (α := ℝ) n)
      rw [add_div, mul_div_assoc, mul_div_assoc] at h
      exact h
    have hX := harmonicPacket_sq_div_log_le_mass hQ hQN'
      (primeOnly (fun p => tameDifferent p * fR p))
    have hP := harmonicPacket_sq_div_log_le_mass hQ hQN' fR
    unfold fibreRows at hpt
    calc (∑ n ∈ Icc 1 N, (arithmeticPrimeGenerator (m * Q) (fibreCoefficients m Q b) n -
            t * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) / Real.log N
        ≤ (2 * modeBound m ^ 2 * ∑ n ∈ Icc 1 N, normalizedConductorPacket Q
              (primeOnly (fun p => tameDifferent p * fR p)) n ^ 2 / (n : ℝ) +
            2 * sourceBound m ^ 2 * ∑ n ∈ Icc 1 N, normalizedConductorPacket Q fR n ^ 2 /
              (n : ℝ)) / Real.log N := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact div_le_div_of_nonneg_right (sum_le_sum hpt) hL.le
      _ = 2 * modeBound m ^ 2 * ((∑ n ∈ Icc 1 N, normalizedConductorPacket Q
              (primeOnly (fun p => tameDifferent p * fR p)) n ^ 2 / (n : ℝ)) / Real.log N) +
            2 * sourceBound m ^ 2 * ((∑ n ∈ Icc 1 N, normalizedConductorPacket Q fR n ^ 2 /
              (n : ℝ)) / Real.log N) := by ring
      _ ≤ 2 * modeBound m ^ 2 * (52 * (2 * μ)) + 2 * sourceBound m ^ 2 * (52 * (2 * μ)) := by
          gcongr
          · exact hX.trans (by linarith [htame.trans hmass])
          · exact hP.trans (by linarith)
      _ ≤ fibreConstant m * μ := by nlinarith

/-- **Fibre charges survive vanishing energy.** For every conductor `m`, every charge `t` and every
`ε > 0` there is a cutoff `Q ≥ R` such that for every horizon `N ≥ mQ` some harmonic-pole-neutral
input supported on `{1} ∪ {m p : p ∤ m}` has adjunction mass, residual mean square, physical input
and physical residual output all `< ε`, while the `e_m`-component of its output is exactly `t`. -/
theorem exists_fibre_charge_vanishing_energy {m : ℕ} (hm : 0 < m) (R : ℕ) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ, R ≤ Q ∧ 2 ≤ Q ∧ ∀ N : ℕ, m * Q ≤ N → ∃ a : ℕ → ℝ,
      (∀ c, a c ≠ 0 → c = 1 ∨ ∃ p ∈ fibrePrimes m Q, c = m * p) ∧
      harmonicSum N (conductorHorizonProfile (m * Q) a) = 0 ∧
      primeAdjunctionMass (m * Q) a < ε ∧
      packetMean (m * Q) (fun n =>
        arithmeticPrimeGenerator (m * Q) a n * normalizedRamanujanMode m n) = t ∧
      packetMean (m * Q) (fun n =>
        (arithmeticPrimeGenerator (m * Q) a n - t * normalizedRamanujanMode m n) ^ 2) < ε ∧
      (∑ n ∈ Icc 1 N, conductorHorizonProfile (m * Q) a n ^ 2) / Real.log N < ε ∧
      (∑ n ∈ Icc 1 N, (arithmeticPrimeGenerator (m * Q) a n - t * normalizedRamanujanMode m n) ^ 2 /
        (n : ℝ)) / Real.log N < ε := by
  have hK := fibreConstant_nonneg m
  obtain ⟨Q, hQR, hQ2, hBlarge⟩ := ((eventually_ge_atTop R).and ((eventually_ge_atTop 2).and
    ((fibreScale_tendsto_atTop hm).eventually_ge_atTop (fibreConstant m * t ^ 2 / ε + 1)))).exists
  have hB : 0 < fibreScale m Q := by
    have : 0 ≤ fibreConstant m * t ^ 2 / ε := div_nonneg (mul_nonneg hK (sq_nonneg _)) hε.le
    linarith
  have hsmall : fibreConstant m * (t ^ 2 / fibreScale m Q) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hB]
    have h := (div_le_iff₀ hε).mp (by linarith : fibreConstant m * t ^ 2 / ε ≤ fibreScale m Q - 1)
    nlinarith
  refine ⟨Q, hQR, hQ2, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fibreCharge_bounds hm hQ2 hN t hB
  exact ⟨_, h1, h2, h3.trans_lt hsmall, h4, h5.trans_lt hsmall, h6.trans_lt hsmall,
    h7.trans_lt hsmall⟩

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
