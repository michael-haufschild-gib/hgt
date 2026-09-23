import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalPhysicalPluckerChiralityGain

/-!
# Universal ordered-prime Pluecker chirality gain

P-G80 generalizes P-G79 from primes `2<3` to every ordered pair of actual primes. For a common
physical aperture `0<a<log(p)/2`, the consecutive-depth same-prime Pluecker minor is strictly
anti-monotone in prime scale. The proof is source-exact: all four positive denominator factors
increase from `p` to `q`—prime amplitude denominator, logarithmic clock, and both normalized
aperture gaps.

On the ordered cell `(p,0),(p,1),(q,0),(q,1)`, all mixed complement-chirality Fisher terms cancel.
The remaining moment is the product of decreasing physical minor mass and increasing Fisher clock.
Thus every ordered two-prime physical Schur fraction lies strictly in `(1/2,1)`. Its residual is
positive coefficientwise and strictly below the symmetrized half residual. No complement averaging,
fitted scalar, Xi zero, or RH premise enters.

This is a universal finite-packet source law. Cofinal packetization through the weak Kothe kernel
and completed Gamma/polar moment identification remain open.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight (a : ℝ) (p : Nat.Primes) : ℝ :=
  RHTower.twoBoundaryCauchyPairPluckerSq a
      (Real.log (p : ℝ) / 2) (3 * Real.log (p : ℝ) / 2) *
    (RHTower.gammaSewnMobiusApertureBoundaryAmplitude p ^ (2 : ℕ)) ^ (2 : ℕ)

theorem gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_eq
    {a : ℝ} {p : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) :
    gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a p =
      4 * a ^ (2 : ℕ) /
        (((p : ℝ) + 1) ^ (4 : ℕ) * Real.log (p : ℝ) ^ (2 : ℕ) *
          ((1 / 4 : ℝ) - (a / Real.log (p : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ) *
          ((9 / 4 : ℝ) - (a / Real.log (p : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  let L := Real.log (p : ℝ)
  let u := a / L
  let A := (1 / 4 : ℝ) - u ^ (2 : ℕ)
  let B := (9 / 4 : ℝ) - u ^ (2 : ℕ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hu : 0 < u := div_pos ha hL
  have huhalf : u < 1 / 2 := by
    apply (div_lt_iff₀ hL).2
    simpa [L, div_eq_mul_inv, mul_comm] using hap
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [sq_nonneg u]
  unfold gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight RHTower.twoBoundaryCauchyPairPluckerSq
    RHTower.twoBoundaryCauchyPairPlucker
  rw [gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
  dsimp [L, u, A, B] at *
  field_simp [hL.ne', hA.ne', hB.ne']
  ring

theorem gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_pos
    {a : ℝ} {p : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) :
    0 < gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a p := by
  rw [gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_eq ha hap]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hu : 0 < a / Real.log (p : ℝ) := div_pos ha hL
  have huhalf : a / Real.log (p : ℝ) < 1 / 2 := by
    apply (div_lt_iff₀ hL).2
    simpa [div_eq_mul_inv, mul_comm] using hap
  have hA : 0 < (1 / 4 : ℝ) - (a / Real.log (p : ℝ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a / Real.log (p : ℝ) - 1 / 2)]
  have hB : 0 < (9 / 4 : ℝ) - (a / Real.log (p : ℝ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a / Real.log (p : ℝ))]
  positivity

theorem gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_strictAnti
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hpq : (p : ℕ) < (q : ℕ)) (hap : a < Real.log (p : ℝ) / 2) :
    gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a q < gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a p := by
  let Lp := Real.log (p : ℝ)
  let Lq := Real.log (q : ℝ)
  let up := a / Lp
  let uq := a / Lq
  let Ap := (1 / 4 : ℝ) - up ^ (2 : ℕ)
  let Aq := (1 / 4 : ℝ) - uq ^ (2 : ℕ)
  let Bp := (9 / 4 : ℝ) - up ^ (2 : ℕ)
  let Bq := (9 / 4 : ℝ) - uq ^ (2 : ℕ)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.one_lt
  have hLp : 0 < Lp := Real.log_pos hp1
  have hLq : 0 < Lq := Real.log_pos hq1
  have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hLpq : Lp < Lq :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ)))
      (Set.mem_Ioi.mpr (by exact_mod_cast q.2.pos : (0 : ℝ) < (q : ℝ))) hpqR
  have hup : 0 < up := div_pos ha hLp
  have huq : 0 < uq := div_pos ha hLq
  have huq_up : uq < up := by
    apply (div_lt_div_iff₀ hLq hLp).2
    exact mul_lt_mul_of_pos_left hLpq ha
  have hup_half : up < 1 / 2 := by
    apply (div_lt_iff₀ hLp).2
    simpa [Lp, div_eq_mul_inv, mul_comm] using hap
  have huqsq_upsq : uq ^ (2 : ℕ) < up ^ (2 : ℕ) :=
    (sq_lt_sq₀ huq.le hup.le).2 huq_up
  have hAp : 0 < Ap := by
    dsimp [Ap]
    nlinarith [sq_nonneg (up - 1 / 2)]
  have hAq : 0 < Aq := by
    dsimp [Aq]
    nlinarith
  have hApq : Ap < Aq := by dsimp [Ap, Aq]; linarith
  have hBp : 0 < Bp := by dsimp [Bp]; nlinarith [sq_nonneg up]
  have hBq : 0 < Bq := by dsimp [Bq]; nlinarith [sq_nonneg uq]
  have hBpq : Bp < Bq := by dsimp [Bp, Bq]; linarith
  have hpqOne : (p : ℝ) + 1 < (q : ℝ) + 1 := by linarith
  have hpqOnePos : 0 < (p : ℝ) + 1 := by positivity
  have hpqFour : ((p : ℝ) + 1) ^ (4 : ℕ) < ((q : ℝ) + 1) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hpqOne hpqOnePos.le (by norm_num)
  have hLsq : Lp ^ (2 : ℕ) < Lq ^ (2 : ℕ) :=
    (sq_lt_sq₀ hLp.le hLq.le).2 hLpq
  have hAsq : Ap ^ (2 : ℕ) < Aq ^ (2 : ℕ) :=
    (sq_lt_sq₀ hAp.le hAq.le).2 hApq
  have hBsq : Bp ^ (2 : ℕ) < Bq ^ (2 : ℕ) :=
    (sq_lt_sq₀ hBp.le hBq.le).2 hBpq
  let Dp := ((p : ℝ) + 1) ^ (4 : ℕ) * Lp ^ (2 : ℕ) * Ap ^ (2 : ℕ) * Bp ^ (2 : ℕ)
  let Dq := ((q : ℝ) + 1) ^ (4 : ℕ) * Lq ^ (2 : ℕ) * Aq ^ (2 : ℕ) * Bq ^ (2 : ℕ)
  have hDp : 0 < Dp := by dsimp [Dp]; positivity
  have hDq : 0 < Dq := by dsimp [Dq]; positivity
  have hD : Dp < Dq := by
    dsimp [Dp, Dq]
    have h1 := mul_lt_mul hpqFour hLsq.le (sq_pos_of_pos hLp)
      (pow_nonneg (by positivity) 4)
    have h2 := mul_lt_mul h1 hAsq.le (sq_pos_of_pos hAp)
      (mul_nonneg (pow_nonneg (by positivity) 4) (sq_nonneg Lq))
    exact mul_lt_mul h2 hBsq.le (sq_pos_of_pos hBp)
      (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) 4) (sq_nonneg Lq))
        (sq_nonneg Aq))
  have haq : a < Lq / 2 := lt_trans hap (by nlinarith)
  rw [gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_eq ha haq,
    gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_eq ha hap]
  change 4 * a ^ (2 : ℕ) / Dq < 4 * a ^ (2 : ℕ) / Dp
  exact (div_lt_div_iff₀ hDq hDp).2
    (mul_lt_mul_of_pos_left hD (mul_pos (by norm_num) (sq_pos_of_pos ha)))

def gammaSewnCriticalOrderedPrimePlucker_Cell (p q : Nat.Primes) : Fin 4 → Nat.Primes × ℕ :=
  ![(p, 0), (p, 1), (q, 0), (q, 1)]

def gammaSewnCriticalOrderedPrimePlucker_Rate (p q : Nat.Primes) (i : Fin 4) : ℝ :=
  RHTower.gammaSewnMobiusApertureCellMidHeight
    (gammaSewnCriticalOrderedPrimePlucker_Cell p q i).1 (gammaSewnCriticalOrderedPrimePlucker_Cell p q i).2

theorem gammaSewnCriticalOrderedPrimePlucker_rawWeight_zero_eq
    (a : ℝ) (p q : Nat.Primes) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnCriticalOrderedPrimePlucker_Rate p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) 0 =
      gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a p := by
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnCriticalOrderedPrimePlucker_Rate, gammaSewnCriticalOrderedPrimePlucker_Cell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight]
  ring_nf

theorem gammaSewnCriticalOrderedPrimePlucker_rawWeight_five_eq
    (a : ℝ) (p q : Nat.Primes) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnCriticalOrderedPrimePlucker_Rate p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) 5 =
      gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight a q := by
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnCriticalOrderedPrimePlucker_Rate, gammaSewnCriticalOrderedPrimePlucker_Cell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight]
  ring_nf

theorem gammaSewnCriticalOrderedPrimePlucker_rawWeight_nonneg
    (a : ℝ) (p q : Nat.Primes) (s : Fin 6) :
    0 ≤ RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnCriticalOrderedPrimePlucker_Rate p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
  unfold RHTower.gammaSewnFourRateBoundaryPairRawWeight
    RHTower.twoBoundaryCauchyPairPluckerSq
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem gammaSewnCriticalOrderedPrimePlucker_partition_pos
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) :
    0 < ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnCriticalOrderedPrimePlucker_Rate p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
  apply Finset.sum_pos'
  · intro s _hs
    exact gammaSewnCriticalOrderedPrimePlucker_rawWeight_nonneg a p q s
  · refine ⟨0, Finset.mem_univ 0, ?_⟩
    rw [gammaSewnCriticalOrderedPrimePlucker_rawWeight_zero_eq]
    exact gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_pos ha hap

def gammaSewnCriticalOrderedPrimePlucker_Probability (a : ℝ) (p q : Nat.Primes) : Fin 6 → ℝ :=
  RHTower.gammaSewnFourRateBoundaryPairProbability a
    (gammaSewnCriticalOrderedPrimePlucker_Rate p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q)

theorem gammaSewnCriticalOrderedPrimePlucker_probability_five_lt_zero
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hpq : (p : ℕ) < (q : ℕ)) (hap : a < Real.log (p : ℝ) / 2) :
    gammaSewnCriticalOrderedPrimePlucker_Probability a p q 5 < gammaSewnCriticalOrderedPrimePlucker_Probability a p q 0 := by
  unfold gammaSewnCriticalOrderedPrimePlucker_Probability RHTower.gammaSewnFourRateBoundaryPairProbability
  rw [gammaSewnCriticalOrderedPrimePlucker_rawWeight_zero_eq, gammaSewnCriticalOrderedPrimePlucker_rawWeight_five_eq]
  exact div_lt_div_of_pos_right (gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_strictAnti ha hpq hap)
    (gammaSewnCriticalOrderedPrimePlucker_partition_pos ha hap)

theorem gammaSewnCriticalOrderedPrimePlucker_fisher_lt
    {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    RHTower.gammaSewnMobiusApertureBoundaryFisherClock p <
      RHTower.gammaSewnMobiusApertureBoundaryFisherClock q := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
  have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hLp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hLq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlog : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hp0) (Set.mem_Ioi.mpr hq0) hpqR
  unfold RHTower.gammaSewnMobiusApertureBoundaryFisherClock
  nlinarith [mul_pos (sub_pos.mpr hlog) (add_pos hLq hLp)]

theorem gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_eq
    (a : ℝ) (p q : Nat.Primes) :
    (∑ s, gammaSewnCriticalPlucker_complementChirality
          (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) s *
        RHTower.gammaSewnFourRateComplementaryFisher
          (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s) =
      2 * (gammaSewnCriticalOrderedPrimePlucker_Probability a p q 0 -
          gammaSewnCriticalOrderedPrimePlucker_Probability a p q 5) *
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock q -
          RHTower.gammaSewnMobiusApertureBoundaryFisherClock p) := by
  simp [Fin.sum_univ_succ, gammaSewnCriticalPlucker_complementChirality,
    gammaSewnCriticalPlucker_complementIndex,
    RHTower.gammaSewnFourRateComplementaryFisher,
    RHTower.fourRateComplementarySum,
    RHTower.fourRatePairComplementLeft,
    RHTower.fourRatePairComplementRight,
    gammaSewnCriticalOrderedPrimePlucker_Cell]
  ring

theorem gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_pos
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hpq : (p : ℕ) < (q : ℕ)) (hap : a < Real.log (p : ℝ) / 2) :
    0 < ∑ s, gammaSewnCriticalPlucker_complementChirality
          (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) s *
        RHTower.gammaSewnFourRateComplementaryFisher
          (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
  rw [gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_eq]
  exact mul_pos
    (mul_pos (by norm_num)
      (sub_pos.mpr (gammaSewnCriticalOrderedPrimePlucker_probability_five_lt_zero ha hpq hap)))
    (sub_pos.mpr (gammaSewnCriticalOrderedPrimePlucker_fisher_lt hpq))

theorem gammaSewnCriticalOrderedPrimePlucker_schurFraction_gt_half
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hpq : (p : ℕ) < (q : ℕ)) (hap : a < Real.log (p : ℝ) / 2) :
    (1 / 2 : ℝ) < gammaSewnCriticalPlucker_schurFraction
      (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) := by
  have hpart := gammaSewnCriticalOrderedPrimePlucker_partition_pos (q := q) ha hap
  have hsum : ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s = 1 :=
    RHTower.sum_gammaSewnFourRateBoundaryPairProbability hpart.ne'
  have hdecomp :=
    gammaSewnCriticalPlucker_complementaryFisherMean_eq_half_add_chirality
      (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) hsum
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher
      (gammaSewnCriticalOrderedPrimePlucker_Cell p q) := by
    unfold RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
    exact add_pos
      (add_pos
        (add_pos
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  unfold gammaSewnCriticalPlucker_schurFraction
  apply (lt_div_iff₀ htotal).2
  nlinarith [gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_pos ha hpq hap]

theorem gammaSewnCriticalOrderedPrimePlucker_complementaryFisherMean_lt_total
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) :
    RHTower.complementaryFisherMean (gammaSewnCriticalOrderedPrimePlucker_Probability a p q)
        (RHTower.gammaSewnFourRateComplementaryFisher
          (gammaSewnCriticalOrderedPrimePlucker_Cell p q)) <
      RHTower.gammaSewnFourRateTotalFisher (gammaSewnCriticalOrderedPrimePlucker_Cell p q) := by
  have hpart := gammaSewnCriticalOrderedPrimePlucker_partition_pos (q := q) ha hap
  have hsum : ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s = 1 :=
    RHTower.sum_gammaSewnFourRateBoundaryPairProbability hpart.ne'
  have hwnonneg : ∀ s, 0 ≤ gammaSewnCriticalOrderedPrimePlucker_Probability a p q s := by
    intro s
    unfold gammaSewnCriticalOrderedPrimePlucker_Probability
      RHTower.gammaSewnFourRateBoundaryPairProbability
    exact div_nonneg (gammaSewnCriticalOrderedPrimePlucker_rawWeight_nonneg a p q s) hpart.le
  have hwzero : 0 < gammaSewnCriticalOrderedPrimePlucker_Probability a p q 0 := by
    unfold gammaSewnCriticalOrderedPrimePlucker_Probability
      RHTower.gammaSewnFourRateBoundaryPairProbability
    rw [gammaSewnCriticalOrderedPrimePlucker_rawWeight_zero_eq]
    exact div_pos (gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_pos ha hap) hpart
  have hselpos :
      0 < ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
        RHTower.gammaSewnFourRateSelectedFisher
          (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
    apply Finset.sum_pos'
    · intro s _hs
      exact mul_nonneg (hwnonneg s) (by
        unfold RHTower.gammaSewnFourRateSelectedFisher RHTower.fourRateSelectedSum
        exact add_nonneg
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _).le
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _).le)
    · refine ⟨0, Finset.mem_univ 0, ?_⟩
      exact mul_pos hwzero (by
        unfold RHTower.gammaSewnFourRateSelectedFisher RHTower.fourRateSelectedSum
        exact add_pos
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
  have htotal :=
    RHTower.gammaSewnFourRateSelectedFisher_add_complementaryFisher
      (gammaSewnCriticalOrderedPrimePlucker_Cell p q)
  unfold RHTower.complementaryFisherMean
  have hid :
      (∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
          RHTower.gammaSewnFourRateComplementaryFisher
            (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s) =
        RHTower.gammaSewnFourRateTotalFisher (gammaSewnCriticalOrderedPrimePlucker_Cell p q) -
          ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
            RHTower.gammaSewnFourRateSelectedFisher
              (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
    calc
      (∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
          RHTower.gammaSewnFourRateComplementaryFisher
            (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s) =
        ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
          (RHTower.gammaSewnFourRateTotalFisher (gammaSewnCriticalOrderedPrimePlucker_Cell p q) -
            RHTower.gammaSewnFourRateSelectedFisher
              (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s) := by
          apply Finset.sum_congr rfl
          intro s _hs
          rw [← htotal s]
          ring
      _ = RHTower.gammaSewnFourRateTotalFisher (gammaSewnCriticalOrderedPrimePlucker_Cell p q) *
            (∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s) -
          ∑ s, gammaSewnCriticalOrderedPrimePlucker_Probability a p q s *
            RHTower.gammaSewnFourRateSelectedFisher
              (gammaSewnCriticalOrderedPrimePlucker_Cell p q) s := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s _hs
          ring
      _ = _ := by rw [hsum]; ring
  rw [hid]
  linarith

theorem gammaSewnCriticalOrderedPrimePlucker_schurFraction_lt_one
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) :
    gammaSewnCriticalPlucker_schurFraction
        (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) < 1 := by
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher
      (gammaSewnCriticalOrderedPrimePlucker_Cell p q) := by
    unfold RHTower.gammaSewnFourRateTotalFisher RHTower.fourRateTotalSum
    exact add_pos
      (add_pos
        (add_pos
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
          (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _))
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  unfold gammaSewnCriticalPlucker_schurFraction
  rw [div_lt_iff₀ htotal]
  simpa using gammaSewnCriticalOrderedPrimePlucker_complementaryFisherMean_lt_total (q := q) ha hap

theorem gammaSewnCriticalOrderedPrimePlucker_reducedWeight_pos
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hap : a < Real.log (p : ℝ) / 2) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnCriticalPlucker_reducedWeight
      (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) pk := by
  unfold gammaSewnCriticalPlucker_reducedWeight
  exact mul_pos (sub_pos.mpr (gammaSewnCriticalOrderedPrimePlucker_schurFraction_lt_one (q := q) ha hap))
    (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk)

theorem gammaSewnCriticalOrderedPrimePlucker_reducedWeight_lt_half
    {a : ℝ} {p q : Nat.Primes} (ha : 0 < a)
    (hpq : (p : ℕ) < (q : ℕ)) (hap : a < Real.log (p : ℝ) / 2)
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalPlucker_reducedWeight
        (gammaSewnCriticalOrderedPrimePlucker_Probability a p q) (gammaSewnCriticalOrderedPrimePlucker_Cell p q) pk <
      (1 / 2 : ℝ) *
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
  unfold gammaSewnCriticalPlucker_reducedWeight
  apply mul_lt_mul_of_pos_right _
    (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk)
  linarith [gammaSewnCriticalOrderedPrimePlucker_schurFraction_gt_half ha hpq hap]

end RHTower.HedenmalmThetaSource
