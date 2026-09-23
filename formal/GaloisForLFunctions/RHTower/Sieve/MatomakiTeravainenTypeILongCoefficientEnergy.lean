import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierCanonicalLongEnergyMoment
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment

/-!
# Divisor-bounded energy for the Type-I long factor

The literal coefficient hypothesis from Proposition 2.2 bounds the exact dyadic `ell^(2 : ℕ)` energy
in the long fourth-moment receiver.  A fixed divisor moment supplies a polylogarithmic loss, with
no pointwise positive power of the height.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Explicit fixed-polylog multiplier for one divisor-bounded dyadic coefficient block. -/
def mtTypeILongCoefficientPolylogFactor (C : ℝ) (w : ℕ) (T : ℝ) : ℝ :=
  2 * C ^ 2 *
    (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * w) - 1)

/-- Exact dyadic coefficient energy under a polynomial divisor bound. -/
theorem sum_normSq_mtTypeILongCoefficient_le_polylog
    {T C : ℝ} (hT : 1 ≤ T)
    {A w : ℕ} (hA : 1 ≤ A) (hAT : (A : ℝ) ≤ T)
    (a : ℕ → ℂ)
    (hpoint : ∀ {n : ℕ}, 0 < n →
      ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) :
    ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 ≤
      mtTypeILongCoefficientPolylogFactor C w T * (A : ℝ) := by
  let E : ℕ := 2 ^ (2 * w) - 1
  have hpointSq : ∀ n ∈ Finset.Ioc A (2 * A),
      ‖a n‖ ^ 2 ≤ C ^ 2 * (n.divisors.card : ℝ) ^ (2 * w) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnpos : 0 < n := by omega
    have hb := hpoint hnpos
    have hsquare := pow_le_pow_left₀ (norm_nonneg (a n)) hb 2
    calc
      ‖a n‖ ^ 2 ≤ (C * (n.divisors.card : ℝ) ^ w) ^ 2 := hsquare
      _ = C ^ 2 * (n.divisors.card : ℝ) ^ (2 * w) := by ring
  have hsubset : Finset.Ioc A (2 * A) ⊆ Finset.Icc 1 (2 * A) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  have hdiv := sum_card_divisors_pow_le_polylog (2 * w) (2 * A) (by omega)
  have hsource :
      ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 ≤
        C ^ 2 * ((2 * A : ℕ) : ℝ) *
          (1 + Real.log ((2 * A : ℕ) : ℝ)) ^ E := by
    calc
      ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 ≤
          ∑ n ∈ Finset.Ioc A (2 * A),
            C ^ 2 * (n.divisors.card : ℝ) ^ (2 * w) :=
        Finset.sum_le_sum hpointSq
      _ = C ^ 2 * ∑ n ∈ Finset.Ioc A (2 * A),
            (n.divisors.card : ℝ) ^ (2 * w) := by rw [Finset.mul_sum]
      _ ≤ C ^ 2 * ∑ n ∈ Finset.Icc 1 (2 * A),
            (n.divisors.card : ℝ) ^ (2 * w) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
      _ ≤ C ^ 2 * (((2 * A : ℕ) : ℝ) *
            (1 + Real.log ((2 * A : ℕ) : ℝ)) ^ E) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        simpa only [E] using hdiv
      _ = C ^ 2 * ((2 * A : ℕ) : ℝ) *
            (1 + Real.log ((2 * A : ℕ) : ℝ)) ^ E := by ring
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have htwoApos : (0 : ℝ) < ((2 * A : ℕ) : ℝ) := by positivity
  have htwoAle : ((2 * A : ℕ) : ℝ) ≤ 2 * T := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    gcongr
  have hlog := Real.log_le_log htwoApos htwoAle
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogMul : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  have hlogBound :
      1 + Real.log ((2 * A : ℕ) : ℝ) ≤ 2 * (1 + |Real.log T|) := by
    rw [hlogMul] at hlog
    linarith [le_abs_self (Real.log T), abs_nonneg (Real.log T)]
  have hlogNonneg : 0 ≤ 1 + Real.log ((2 * A : ℕ) : ℝ) := by
    have : 0 ≤ Real.log ((2 * A : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * A by omega))
    linarith
  have hpow :
      (1 + Real.log ((2 * A : ℕ) : ℝ)) ^ E ≤
        (2 * (1 + |Real.log T|)) ^ E :=
    pow_le_pow_left₀ hlogNonneg hlogBound E
  calc
    ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 ≤
        C ^ 2 * ((2 * A : ℕ) : ℝ) *
          (1 + Real.log ((2 * A : ℕ) : ℝ)) ^ E := hsource
    _ ≤ C ^ 2 * ((2 * A : ℕ) : ℝ) *
          (2 * (1 + |Real.log T|)) ^ E := by gcongr
    _ = (2 * C ^ 2 * (2 * (1 + |Real.log T|)) ^ E) * (A : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = _ := by rfl

/-- Long fourth-moment envelope after the literal coefficient energy is replaced by its
fixed-polylogarithmic divisor bound. -/
def mtTypeILongFourthDivisorBound
    (C₀ eta C : ℝ) (w A : ℕ) (T : ℝ) : ℝ :=
  C₀ * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta *
    (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2) +
      (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2) * T) *
    (mtTypeILongCoefficientPolylogFactor C w T * (A : ℝ)) ^ 2

/-- The source-energy fourth-moment bound is no larger than its explicit divisor envelope. -/
theorem mtTypeILongFourthRpowEnergyBound_le_divisorBound
    {C₀ eta T C : ℝ} (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    {A w : ℕ} (hA : 1 ≤ A) (hAT : (A : ℝ) ≤ T)
    (a : ℕ → ℂ)
    (hpoint : ∀ {n : ℕ}, 0 < n →
      ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) :
    mtTypeILongFourthRpowEnergyBound C₀ eta a A T ≤
      mtTypeILongFourthDivisorBound C₀ eta C w A T := by
  have henergy := sum_normSq_mtTypeILongCoefficient_le_polylog
    hT hA hAT a hpoint
  have henergy0 : 0 ≤ ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by positivity
  have henergySq := pow_le_pow_left₀ henergy0 henergy 2
  rw [mtTypeILongFourthRpowEnergyBound, mtTypeILongFourthDivisorBound]
  gcongr

/-- Canonical Type-I block with long coefficient energy fully replaced by the divisor envelope. -/
noncomputable def mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
    (C₀ eta C epsilon alpha : ℝ) (w A P ell N : ℕ) (T : ℝ)
    (_r : Fin ell) : ℝ :=
  (ell : ℝ) * (((P ^ ell : ℕ) : ℝ)) ^ (epsilon / 10) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) *
    Real.sqrt (mtTypeILongFourthDivisorBound C₀ eta C w A T)

/-- One canonical source-energy block is absorbed by the literal divisor envelope. -/
theorem mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound_le_divisor
    {C₀ eta T C epsilon alpha : ℝ}
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    (a : ℕ → ℂ) {w A P ell N : ℕ} (hA : 1 ≤ A) (hAT : (A : ℝ) ≤ T)
    (hpoint : ∀ {n : ℕ}, 0 < n →
      ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w))
    (r : Fin ell) :
    mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
        C₀ eta epsilon alpha a A P ell N T r ≤
      mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
        C₀ eta C epsilon alpha w A P ell N T r := by
  have hlong := mtTypeILongFourthRpowEnergyBound_le_divisorBound
    (eta := eta) hC₀ hT hA hAT a hpoint
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound,
    mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Source-facing height dichotomy with all long coefficient energy replaced by an explicit
fixed-polylog divisor envelope. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceDivisorHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C₀ D : ℝ, 0 < C₀ ∧ 0 < D ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T C : ℝ) (w : ℕ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        (∀ {n : ℕ}, 0 < n → ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) →
        1 ≤ A → (A : ℝ) ≤ T → 2 ≤ N → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
                C₀ (epsilon / 100) C epsilon alpha w A P ell N T r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound D epsilon a A P ell N T
                ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r := by
  obtain ⟨C₀, D, hC₀, hD, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceLongEnergyHeightDichotomy
      hepsilon
  refine ⟨C₀, D, hC₀, hD, ?_⟩
  filter_upwards [hsource] with X hsourceX
  intro alpha T C w a A N N' halpha halpha2 hXT hTX hpoint hA hAT hN hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX hA hN hNN' hN'le
  dsimp only at hbase
  by_cases hNT : (N : ℝ) ≤ T
  · have hT : (1 : ℝ) ≤ T := by
      calc
        (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        _ ≤ T := hNT
    calc
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
            C₀ (epsilon / 100) epsilon alpha a A
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r := by
        simpa only [hNT, if_true] using hbase
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
            C₀ (epsilon / 100) C epsilon alpha w A
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r :=
        Finset.sum_le_sum fun r _ =>
          mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound_le_divisor
            hC₀.le hT a hA hAT hpoint r
      _ = _ := by rw [if_pos hNT]
  · simpa only [hNT, if_false] using hbase

end

end RHTower.Sieve
