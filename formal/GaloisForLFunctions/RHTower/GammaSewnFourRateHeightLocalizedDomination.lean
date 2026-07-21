import GaloisForLFunctions.RHTower.GammaSewnFourRatePluckerConnector
import GaloisForLFunctions.RHTower.GammaSewnEulerCalibratedExterior

/-!
# Valuation-depth transition in the four-rate Gamma-sewn cell

The four-rate Schur curvature has two source channels: selected midpoint-height dispersion and
the cumulant-corrected complementary Fisher mass.  They react differently to valuation height.
Putting all four prime cells at one common depth `e` leaves the Cauchy boundary probabilities and
the prime-only Fisher clock unchanged, while multiplying every selected prime-log pair sum by
`e + 1/2`.

This gives an exact local transition law.  If `D` is the strictly positive base prime-log
dispersion and `F` is the strictly positive complementary Fisher mass, then

`dispersion(e) - correctedFisher(e) = (e + 1/2)^2 D - F`.

Consequently the *Rees-boundary coordinate packet* crosses the finite scale `sqrt(F / D)`.  This
does **not** give a physical height-localized contraction.  The literal Euler amplitude depends on
depth and conductor, so deep safe-half-plane packets concentrate on the least conductor and the
boundary probability used here is not their physical probability.  The exact transition laws
below are retained as the sharp no-go witness.  The positive survivor is the normalized all-depth
synchronized law in `GammaSewnSynchronizedEulerFisherBarycenter`, not selection of a large depth.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Four source primes placed at one common valuation depth. -/
def gammaSewnFourRateCommonDepthCell
    (prime : Fin 4 → Nat.Primes) (e : ℕ) (i : Fin 4) : Nat.Primes × ℕ :=
  (prime i, e)

/-- Pair-sum of the four source prime logarithms. -/
def gammaSewnFourRateSelectedPrimeLog
    (prime : Fin 4 → Nat.Primes) (s : Fin 6) : ℝ :=
  fourRateSelectedSum (fun i => Real.log (prime i : ℝ)) s

/-- Prime-log dispersion of the boundary-minor packet before valuation-height amplification. -/
def gammaSewnFourRateBoundaryPrimeLogDispersion
    (a : ℝ) (rate : Fin 4 → ℝ) (prime : Fin 4 → Nat.Primes) : ℝ :=
  normalizedFinitePairDispersion
    (gammaSewnFourRateBoundaryPairProbability a rate
      (gammaSewnFourRateCommonDepthCell prime 0))
    (gammaSewnFourRateSelectedPrimeLog prime)

/-- Complementary Fisher mass of the same boundary-minor packet. -/
def gammaSewnFourRateBoundaryComplementaryFisherMass
    (a : ℝ) (rate : Fin 4 → ℝ) (prime : Fin 4 → Nat.Primes) : ℝ :=
  complementaryFisherMean
    (gammaSewnFourRateBoundaryPairProbability a rate
      (gammaSewnFourRateCommonDepthCell prime 0))
    (gammaSewnFourRateComplementaryFisher
      (gammaSewnFourRateCommonDepthCell prime 0))

theorem gammaSewnFourRateBoundaryPairProbability_commonDepth
    (a : ℝ) (rate : Fin 4 → ℝ) (prime : Fin 4 → Nat.Primes)
    (e f : ℕ) (s : Fin 6) :
    gammaSewnFourRateBoundaryPairProbability a rate
        (gammaSewnFourRateCommonDepthCell prime e) s =
      gammaSewnFourRateBoundaryPairProbability a rate
        (gammaSewnFourRateCommonDepthCell prime f) s := by
  rfl

theorem gammaSewnFourRateSelectedHeight_commonDepth
    (prime : Fin 4 → Nat.Primes) (e : ℕ) (s : Fin 6) :
    gammaSewnFourRateSelectedHeight
        (gammaSewnFourRateCommonDepthCell prime e) s =
      ((e : ℝ) + 1 / 2) * gammaSewnFourRateSelectedPrimeLog prime s := by
  unfold gammaSewnFourRateSelectedHeight gammaSewnFourRateSelectedPrimeLog
    fourRateSelectedSum gammaSewnMobiusApertureCellMidHeight
    gammaSewnFourRateCommonDepthCell
  ring

/-- Common valuation depth amplifies only the midpoint-height channel, by the exact square of
`e + 1/2`; the boundary probability packet itself is unchanged. -/
theorem gammaSewnFourRateCommonDepth_dispersion_eq
    (a : ℝ) (rate : Fin 4 → ℝ) (prime : Fin 4 → Nat.Primes) (e : ℕ) :
    normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e))
        (gammaSewnFourRateSelectedHeight
          (gammaSewnFourRateCommonDepthCell prime e)) =
      ((e : ℝ) + 1 / 2) ^ 2 *
        gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime := by
  simp only [gammaSewnFourRateBoundaryPrimeLogDispersion,
    normalizedFinitePairDispersion]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [gammaSewnFourRateBoundaryPairProbability_commonDepth a rate prime e 0 s,
    gammaSewnFourRateBoundaryPairProbability_commonDepth a rate prime e 0 t,
    gammaSewnFourRateSelectedHeight_commonDepth,
    gammaSewnFourRateSelectedHeight_commonDepth]
  ring

/-- The cumulant-corrected Fisher channel is exactly depth-blind. -/
theorem gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (hpartition :
      ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate
        (gammaSewnFourRateCommonDepthCell prime e) s ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate
        (gammaSewnFourRateCommonDepthCell prime e) =
      gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime := by
  rw [gammaSewnFourRateSchurCorrectedFisher_eq hpartition]
  unfold gammaSewnFourRateBoundaryComplementaryFisherMass complementaryFisherMean
  apply Finset.sum_congr rfl
  intro s _hs
  rw [gammaSewnFourRateBoundaryPairProbability_commonDepth a rate prime e 0 s]
  rfl

theorem gammaSewnFourRateBoundaryComplementaryFisherMass_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    0 < gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime := by
  unfold gammaSewnFourRateBoundaryComplementaryFisherMass complementaryFisherMean
  apply Finset.sum_pos
  · intro s _hs
    apply mul_pos
    · exact gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s
    · unfold gammaSewnFourRateComplementaryFisher fourRateComplementarySum
      exact add_pos
        (gammaSewnMobiusApertureBoundaryFisherClock_pos _)
        (gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  · exact Finset.univ_nonempty

private theorem gammaSewnFourRate_primeLog_one_ne_two
    {prime : Fin 4 → Nat.Primes} (hprime : Function.Injective prime) :
    Real.log (prime 1 : ℝ) ≠ Real.log (prime 2 : ℝ) := by
  have hpne : prime 1 ≠ prime 2 := hprime.ne (by decide)
  intro hlog
  apply hpne
  apply Subtype.ext
  apply Nat.cast_injective (R := ℝ)
  have hp1 : 0 < (prime 1 : ℝ) := by exact_mod_cast (prime 1).2.pos
  have hp2 : 0 < (prime 2 : ℝ) := by exact_mod_cast (prime 2).2.pos
  calc
    ((prime 1 : ℕ) : ℝ) = Real.exp (Real.log (prime 1 : ℝ)) :=
      (Real.exp_log hp1).symm
    _ = Real.exp (Real.log (prime 2 : ℝ)) := congrArg Real.exp hlog
    _ = ((prime 2 : ℕ) : ℝ) := Real.exp_log hp2

/-- Every nondegenerate four-prime boundary packet has genuine prime-log pair dispersion. -/
theorem gammaSewnFourRateBoundaryPrimeLogDispersion_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
    (hprime : Function.Injective prime) :
    0 < gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime := by
  unfold gammaSewnFourRateBoundaryPrimeLogDispersion
    normalizedFinitePairDispersion
  apply Finset.sum_pos'
  · intro s _hs
    apply Finset.sum_nonneg
    intro t _ht
    exact mul_nonneg
      (mul_nonneg
        (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
        (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary t).le)
      (sq_nonneg _)
  · refine ⟨(0 : Fin 6), Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro t _ht
      exact mul_nonneg
        (mul_nonneg
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary 0).le
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary t).le)
        (sq_nonneg _)
    · refine ⟨(1 : Fin 6), Finset.mem_univ _, ?_⟩
      apply mul_pos
      · exact mul_pos
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary 0)
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary 1)
      · apply sq_pos_of_ne_zero
        have hlog := gammaSewnFourRate_primeLog_one_ne_two hprime
        simp only [gammaSewnFourRateSelectedPrimeLog, fourRateSelectedSum,
          fourRatePairLeft, fourRatePairRight, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        intro hzero
        apply hlog
        linarith

/-- Exact local depth law: the height-localized response surplus is a quadratic depth amplifier
times the positive prime-log dispersion, minus one fixed complementary Fisher mass. -/
theorem gammaSewnFourRateCommonDepth_dispersion_sub_correctedFisher_eq
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (hpartition :
      ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate
        (gammaSewnFourRateCommonDepthCell prime e) s ≠ 0) :
    normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e))
        (gammaSewnFourRateSelectedHeight
          (gammaSewnFourRateCommonDepthCell prime e)) -
      gammaSewnFourRateSchurCorrectedFisher a rate
        (gammaSewnFourRateCommonDepthCell prime e) =
      ((e : ℝ) + 1 / 2) ^ 2 *
          gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime -
        gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime := by
  rw [gammaSewnFourRateCommonDepth_dispersion_eq,
    gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition]

/-- Exact critical scale for the local valuation-depth transition. -/
theorem gammaSewnFourRateCommonDepth_correctedFisher_lt_dispersion_iff
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
    (hprime : Function.Injective prime) :
    gammaSewnFourRateSchurCorrectedFisher a rate
          (gammaSewnFourRateCommonDepthCell prime e) <
        normalizedFinitePairDispersion
          (gammaSewnFourRateBoundaryPairProbability a rate
            (gammaSewnFourRateCommonDepthCell prime e))
          (gammaSewnFourRateSelectedHeight
            (gammaSewnFourRateCommonDepthCell prime e)) ↔
      Real.sqrt
          (gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime /
            gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime) <
        (e : ℝ) + 1 / 2 := by
  let D := gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime
  let F := gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime
  have hD : 0 < D := gammaSewnFourRateBoundaryPrimeLogDispersion_pos
    ha hrate hboundary hprime
  have hF : 0 < F := gammaSewnFourRateBoundaryComplementaryFisherMass_pos
    ha hrate hboundary
  have hpartition := gammaSewnFourRateBoundaryPairPartition_pos
    (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  rw [gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition.ne',
    gammaSewnFourRateCommonDepth_dispersion_eq]
  change F < ((e : ℝ) + 1 / 2) ^ 2 * D ↔ Real.sqrt (F / D) < (e : ℝ) + 1 / 2
  have hquot : 0 ≤ F / D := div_nonneg hF.le hD.le
  have hsqrt : Real.sqrt (F / D) ^ 2 = F / D := Real.sq_sqrt hquot
  have hsqrt0 := Real.sqrt_nonneg (F / D)
  have hdepth : 0 < (e : ℝ) + 1 / 2 := by positivity
  constructor
  · intro hdom
    have hsquare : F / D < ((e : ℝ) + 1 / 2) ^ 2 :=
      (div_lt_iff₀ hD).2 hdom
    nlinarith
  · intro hscale
    apply (div_lt_iff₀ hD).1
    nlinarith

/-- **Rees-coordinate transition/no-go witness.**  In every nondegenerate four-prime boundary
coordinate packet, some common depth makes midpoint-height dispersion dominate corrected Fisher
charge.  This theorem is not a literal-Euler probability statement; conductor-dependent physical
amplitudes invalidate selected-depth transfer. -/
theorem exists_gammaSewnFourRateCommonDepth_correctedFisher_lt_dispersion
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
    (hprime : Function.Injective prime) :
    ∃ e : ℕ,
      gammaSewnFourRateSchurCorrectedFisher a rate
          (gammaSewnFourRateCommonDepthCell prime e) <
        normalizedFinitePairDispersion
          (gammaSewnFourRateBoundaryPairProbability a rate
            (gammaSewnFourRateCommonDepthCell prime e))
          (gammaSewnFourRateSelectedHeight
            (gammaSewnFourRateCommonDepthCell prime e)) := by
  let D := gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime
  let F := gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime
  have hD : 0 < D := gammaSewnFourRateBoundaryPrimeLogDispersion_pos
    ha hrate hboundary hprime
  have hF : 0 < F := gammaSewnFourRateBoundaryComplementaryFisherMass_pos
    ha hrate hboundary
  obtain ⟨e, he⟩ := exists_nat_gt (Real.sqrt (F / D))
  refine ⟨e, ?_⟩
  have hquot : 0 ≤ F / D := div_nonneg hF.le hD.le
  have hsqrt : Real.sqrt (F / D) ^ 2 = F / D := Real.sq_sqrt hquot
  have hscale : Real.sqrt (F / D) < (e : ℝ) + 1 / 2 := by
    exact he.trans (by norm_num)
  have hsquare : F / D < ((e : ℝ) + 1 / 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (F / D)]
  have hdom : F < ((e : ℝ) + 1 / 2) ^ 2 * D :=
    (div_lt_iff₀ hD).mp hsquare
  have hpartition := gammaSewnFourRateBoundaryPairPartition_pos
    (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  rw [gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition.ne',
    gammaSewnFourRateCommonDepth_dispersion_eq]
  exact hdom

/-! ## The literal Euler-calibrated height channel -/

/-- Pair-sum of the literal von Mangoldt--Gamma Euler half-heights at common valuation depth. -/
def gammaSewnFourRateSelectedEulerHeight
    (prime : Fin 4 → Nat.Primes) (e : ℕ) (s : Fin 6) : ℝ :=
  fourRateSelectedSum (fun i => xiGammaEulerBoundaryHalfHeight (prime i) e) s

theorem gammaSewnFourRateSelectedEulerHeight_commonDepth
    (prime : Fin 4 → Nat.Primes) (e : ℕ) (s : Fin 6) :
    gammaSewnFourRateSelectedEulerHeight prime e s =
      (((e : ℝ) + 1) / 2) * gammaSewnFourRateSelectedPrimeLog prime s := by
  unfold gammaSewnFourRateSelectedEulerHeight gammaSewnFourRateSelectedPrimeLog
    fourRateSelectedSum xiGammaEulerBoundaryHalfHeight
  ring

/-- The forced half-plus-quarter Euler calibration changes the exact depth amplifier from
`e + 1/2` to `(e + 1) / 2`; it still leaves the boundary probability packet unchanged. -/
theorem gammaSewnFourRateCommonDepth_eulerDispersion_eq
    (a : ℝ) (rate : Fin 4 → ℝ) (prime : Fin 4 → Nat.Primes) (e : ℕ) :
    normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e))
        (gammaSewnFourRateSelectedEulerHeight prime e) =
      (((e : ℝ) + 1) / 2) ^ 2 *
        gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime := by
  simp only [gammaSewnFourRateBoundaryPrimeLogDispersion,
    normalizedFinitePairDispersion]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [gammaSewnFourRateBoundaryPairProbability_commonDepth a rate prime e 0 s,
    gammaSewnFourRateBoundaryPairProbability_commonDepth a rate prime e 0 t,
    gammaSewnFourRateSelectedEulerHeight_commonDepth,
    gammaSewnFourRateSelectedEulerHeight_commonDepth]
  ring

/-- Exact literal-Euler version of the local height transition law. -/
theorem gammaSewnFourRateCommonDepth_eulerDispersion_sub_correctedFisher_eq
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (hpartition :
      ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate
        (gammaSewnFourRateCommonDepthCell prime e) s ≠ 0) :
    normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateCommonDepthCell prime e))
        (gammaSewnFourRateSelectedEulerHeight prime e) -
      gammaSewnFourRateSchurCorrectedFisher a rate
        (gammaSewnFourRateCommonDepthCell prime e) =
      (((e : ℝ) + 1) / 2) ^ 2 *
          gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime -
        gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime := by
  rw [gammaSewnFourRateCommonDepth_eulerDispersion_eq,
    gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition]

/-- The literal Euler channel crosses the complementary Fisher charge exactly beyond its
source-computable critical valuation scale. -/
theorem gammaSewnFourRateCommonDepth_correctedFisher_lt_eulerDispersion_iff
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes} (e : ℕ)
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
    (hprime : Function.Injective prime) :
    gammaSewnFourRateSchurCorrectedFisher a rate
          (gammaSewnFourRateCommonDepthCell prime e) <
        normalizedFinitePairDispersion
          (gammaSewnFourRateBoundaryPairProbability a rate
            (gammaSewnFourRateCommonDepthCell prime e))
          (gammaSewnFourRateSelectedEulerHeight prime e) ↔
      Real.sqrt
          (gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime /
            gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime) <
        ((e : ℝ) + 1) / 2 := by
  let D := gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime
  let F := gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime
  have hD : 0 < D := gammaSewnFourRateBoundaryPrimeLogDispersion_pos
    ha hrate hboundary hprime
  have hF : 0 < F := gammaSewnFourRateBoundaryComplementaryFisherMass_pos
    ha hrate hboundary
  have hpartition := gammaSewnFourRateBoundaryPairPartition_pos
    (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  rw [gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition.ne',
    gammaSewnFourRateCommonDepth_eulerDispersion_eq]
  change F < (((e : ℝ) + 1) / 2) ^ 2 * D ↔
    Real.sqrt (F / D) < ((e : ℝ) + 1) / 2
  have hquot : 0 ≤ F / D := div_nonneg hF.le hD.le
  have hsqrt : Real.sqrt (F / D) ^ 2 = F / D := Real.sq_sqrt hquot
  have hsqrt0 := Real.sqrt_nonneg (F / D)
  have hdepth : 0 < ((e : ℝ) + 1) / 2 := by positivity
  constructor
  · intro hdom
    have hsquare : F / D < (((e : ℝ) + 1) / 2) ^ 2 :=
      (div_lt_iff₀ hD).2 hdom
    nlinarith
  · intro hscale
    apply (div_lt_iff₀ hD).1
    nlinarith

/-- **Euler-height coordinate transition/no-go witness.**  The calibrated height formula crosses
the corrected Fisher charge under the depth-blind Rees boundary probability.  Literal Euler
amplitudes do not preserve that probability at large depth, so this is not the physical producer. -/
theorem exists_gammaSewnFourRateCommonDepth_correctedFisher_lt_eulerDispersion
    {a : ℝ} {rate : Fin 4 → ℝ} {prime : Fin 4 → Nat.Primes}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0)
    (hprime : Function.Injective prime) :
    ∃ e : ℕ,
      gammaSewnFourRateSchurCorrectedFisher a rate
          (gammaSewnFourRateCommonDepthCell prime e) <
        normalizedFinitePairDispersion
          (gammaSewnFourRateBoundaryPairProbability a rate
            (gammaSewnFourRateCommonDepthCell prime e))
          (gammaSewnFourRateSelectedEulerHeight prime e) := by
  let D := gammaSewnFourRateBoundaryPrimeLogDispersion a rate prime
  let F := gammaSewnFourRateBoundaryComplementaryFisherMass a rate prime
  have hD : 0 < D := gammaSewnFourRateBoundaryPrimeLogDispersion_pos
    ha hrate hboundary hprime
  have hF : 0 < F := gammaSewnFourRateBoundaryComplementaryFisherMass_pos
    ha hrate hboundary
  obtain ⟨e, he⟩ := exists_nat_gt (2 * Real.sqrt (F / D))
  refine ⟨e, ?_⟩
  have hquot : 0 ≤ F / D := div_nonneg hF.le hD.le
  have hsqrt : Real.sqrt (F / D) ^ 2 = F / D := Real.sq_sqrt hquot
  have hsqrt0 := Real.sqrt_nonneg (F / D)
  have hscale : Real.sqrt (F / D) < ((e : ℝ) + 1) / 2 := by
    nlinarith
  have hsquare : F / D < (((e : ℝ) + 1) / 2) ^ 2 := by
    nlinarith
  have hdom : F < (((e : ℝ) + 1) / 2) ^ 2 * D :=
    (div_lt_iff₀ hD).mp hsquare
  have hpartition := gammaSewnFourRateBoundaryPairPartition_pos
    (cell := gammaSewnFourRateCommonDepthCell prime e) ha hrate hboundary
  rw [gammaSewnFourRateSchurCorrectedFisher_commonDepth_eq e hpartition.ne',
    gammaSewnFourRateCommonDepth_eulerDispersion_eq]
  exact hdom

end

end RHTower
