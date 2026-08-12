import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalOrderedPrimePluckerChirality

/-!
# Ordered-prime physical Pluecker chirality at every valuation depth

P-G81 removes P-G80's depth-zero restriction.  At every depth e, each ordered prime pair p < q
carries the same exact anti-monotone physical-minor/Fisher-clock covariance on the four-cell
(p,e),(p,e+1),(q,e),(q,e+1).  Consequently the literal physical Schur fraction lies strictly in
(1/2,1), and every residual prime-power coefficient stays positive and strictly below the
symmetrized half residual.  No Kummer depth is discarded.
-/


open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnOrderedPrimeDepthPlucker_cell (e : ℕ) (p q : Nat.Primes) : Fin 4 → Nat.Primes × ℕ :=
  ![(p, e), (p, e + 1), (q, e), (q, e + 1)]

def gammaSewnOrderedPrimeDepthPlucker_rate (e : ℕ) (p q : Nat.Primes) (i : Fin 4) : ℝ :=
  RHTower.gammaSewnMobiusApertureCellMidHeight
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q i).1 (gammaSewnOrderedPrimeDepthPlucker_cell e p q i).2

theorem gammaSewnOrderedPrimeDepthPlucker_lowerConsecutiveRawWeight_eq {a : ℝ} (e : ℕ) (p q : Nat.Primes)
    (ha : 0 < a)
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 0 =
      4 * a ^ 2 /
        ((((p : ℝ) + 1) ^ 4 * Real.log (p : ℝ) ^ 2 *
          (((e : ℝ) + 1 / 2) ^ 2 - (a / Real.log (p : ℝ)) ^ 2) ^ 2) *
          (((e : ℝ) + 3 / 2) ^ 2 - (a / Real.log (p : ℝ)) ^ 2) ^ 2) := by
  let L := Real.log (p : ℝ)
  let c := (e : ℝ) + 1 / 2
  let d := (e : ℝ) + 3 / 2
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : c < d := by dsimp [c, d]; linarith
  have hu : a / L < c := (div_lt_iff₀ hL).2 (by simpa [L, c] using halt)
  have hu0 : 0 < a / L := div_pos ha hL
  have hA : 0 < c ^ 2 - (a / L) ^ 2 :=
    sub_pos.mpr ((sq_lt_sq₀ hu0.le hc.le).2 hu)
  have hB : 0 < d ^ 2 - (a / L) ^ 2 := by
    apply sub_pos.mpr
    exact (sq_lt_sq₀ hu0.le (hc.trans hcd).le).2 (lt_trans hu hcd)
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.twoBoundaryCauchyPairPluckerSq,
    RHTower.twoBoundaryCauchyPairPlucker,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnOrderedPrimeDepthPlucker_rate, gammaSewnOrderedPrimeDepthPlucker_cell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
  field_simp [L, c, d, hL.ne', hA.ne', hB.ne']
  ring

theorem gammaSewnOrderedPrimeDepthPlucker_upperConsecutiveRawWeight_eq {a : ℝ} (e : ℕ) (p q : Nat.Primes)
    (ha : 0 < a)
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (q : ℝ)) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 5 =
      4 * a ^ 2 /
        ((((q : ℝ) + 1) ^ 4 * Real.log (q : ℝ) ^ 2 *
          (((e : ℝ) + 1 / 2) ^ 2 - (a / Real.log (q : ℝ)) ^ 2) ^ 2) *
          (((e : ℝ) + 3 / 2) ^ 2 - (a / Real.log (q : ℝ)) ^ 2) ^ 2) := by
  let L := Real.log (q : ℝ)
  let c := (e : ℝ) + 1 / 2
  let d := (e : ℝ) + 3 / 2
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.one_lt
  have hL : 0 < L := Real.log_pos hq1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : c < d := by dsimp [c, d]; linarith
  have hu : a / L < c := (div_lt_iff₀ hL).2 (by simpa [L, c] using halt)
  have hu0 : 0 < a / L := div_pos ha hL
  have hA : 0 < c ^ 2 - (a / L) ^ 2 :=
    sub_pos.mpr ((sq_lt_sq₀ hu0.le hc.le).2 hu)
  have hB : 0 < d ^ 2 - (a / L) ^ 2 := by
    apply sub_pos.mpr
    exact (sq_lt_sq₀ hu0.le (hc.trans hcd).le).2 (lt_trans hu hcd)
  simp [RHTower.gammaSewnFourRateBoundaryPairRawWeight,
    RHTower.twoBoundaryCauchyPairPluckerSq,
    RHTower.twoBoundaryCauchyPairPlucker,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
    gammaSewnOrderedPrimeDepthPlucker_rate, gammaSewnOrderedPrimeDepthPlucker_cell,
    RHTower.gammaSewnMobiusApertureCellMidHeight,
    gammaSewnCriticalPhysicalPlucker_boundaryAmplitude_eq]
  field_simp [L, c, d, hL.ne', hA.ne', hB.ne']
  ring

theorem gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 5 <
      RHTower.gammaSewnFourRateBoundaryPairRawWeight a
        (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 0 := by
  let Lp := Real.log (p : ℝ)
  let Lq := Real.log (q : ℝ)
  let Pp := (p : ℝ) + 1
  let Pq := (q : ℝ) + 1
  let c := (e : ℝ) + 1 / 2
  let d := (e : ℝ) + 3 / 2
  let up := a / Lp
  let uq := a / Lq
  let Ap := c ^ 2 - up ^ 2
  let Aq := c ^ 2 - uq ^ 2
  let Bp := d ^ 2 - up ^ 2
  let Bq := d ^ 2 - uq ^ 2
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.one_lt
  have hLp : 0 < Lp := Real.log_pos hp1
  have hLq : 0 < Lq := Real.log_pos hq1
  have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
  have hLpq : Lp < Lq := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using hp0)
    (by simpa only [Set.mem_Ioi] using hq0) hpqR
  have hPpq : Pp < Pq := by dsimp [Pp, Pq]; linarith
  have hPp : 0 < Pp := by dsimp [Pp]; positivity
  have hPq : 0 < Pq := by dsimp [Pq]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : c < d := by dsimp [c, d]; linarith
  have hup : 0 < up := div_pos ha hLp
  have huq : 0 < uq := div_pos ha hLq
  have huqup : uq < up := by
    apply (div_lt_div_iff₀ hLq hLp).2
    exact mul_lt_mul_of_pos_left hLpq ha
  have hupc : up < c := by
    apply (div_lt_iff₀ hLp).2
    change a < c * Lp at halt
    exact halt
  have huqsq_upsq : uq ^ 2 < up ^ 2 :=
    (sq_lt_sq₀ huq.le hup.le).2 huqup
  have hAp : 0 < Ap := by
    dsimp [Ap]
    exact sub_pos.mpr ((sq_lt_sq₀ hup.le hc.le).2 hupc)
  have hAq : 0 < Aq := by dsimp [Aq]; nlinarith
  have hApq : Ap < Aq := by dsimp [Ap, Aq]; linarith
  have hBp : 0 < Bp := by
    dsimp [Bp]
    exact sub_pos.mpr ((sq_lt_sq₀ hup.le (hc.trans hcd).le).2 (hupc.trans hcd))
  have hBq : 0 < Bq := by dsimp [Bq]; nlinarith
  have hBpq : Bp < Bq := by dsimp [Bp, Bq]; linarith
  have hApqsq : Ap ^ 2 < Aq ^ 2 := (sq_lt_sq₀ hAp.le hAq.le).2 hApq
  have hBpqsq : Bp ^ 2 < Bq ^ 2 := (sq_lt_sq₀ hBp.le hBq.le).2 hBpq
  have hLpqsq : Lp ^ 2 < Lq ^ 2 := (sq_lt_sq₀ hLp.le hLq.le).2 hLpq
  have hPpq4 : Pp ^ 4 < Pq ^ 4 := pow_lt_pow_left₀ hPpq hPp.le (by norm_num)
  have hbase : Pp ^ 4 * Lp ^ 2 < Pq ^ 4 * Lq ^ 2 :=
    mul_lt_mul hPpq4 hLpqsq.le (sq_pos_of_pos hLp) (pow_nonneg hPq.le 4)
  have hbaseq : 0 < Pq ^ 4 * Lq ^ 2 := mul_pos (pow_pos hPq _) (sq_pos_of_pos hLq)
  have hbaseA : (Pp ^ 4 * Lp ^ 2) * Ap ^ 2 < (Pq ^ 4 * Lq ^ 2) * Aq ^ 2 :=
    mul_lt_mul hbase hApqsq.le (sq_pos_of_pos hAp) hbaseq.le
  have hden :
      ((Pp ^ 4 * Lp ^ 2) * Ap ^ 2) * Bp ^ 2 <
        ((Pq ^ 4 * Lq ^ 2) * Aq ^ 2) * Bq ^ 2 :=
    mul_lt_mul hbaseA hBpqsq.le (sq_pos_of_pos hBp)
      (mul_nonneg hbaseq.le (sq_nonneg Aq))
  have hdenp : 0 < ((Pp ^ 4 * Lp ^ 2) * Ap ^ 2) * Bp ^ 2 := by positivity
  have hdenq : 0 < ((Pq ^ 4 * Lq ^ 2) * Aq ^ 2) * Bq ^ 2 := by positivity
  have haltq : a < ((e : ℝ) + 1 / 2) * Real.log (q : ℝ) := by
    change a < c * Lp at halt
    change a < c * Lq
    exact halt.trans (mul_lt_mul_of_pos_left hLpq hc)
  rw [gammaSewnOrderedPrimeDepthPlucker_lowerConsecutiveRawWeight_eq e p q ha halt, gammaSewnOrderedPrimeDepthPlucker_upperConsecutiveRawWeight_eq e p q ha haltq]
  change 4 * a ^ 2 / (((Pq ^ 4 * Lq ^ 2) * Aq ^ 2) * Bq ^ 2) <
    4 * a ^ 2 / (((Pp ^ 4 * Lp ^ 2) * Ap ^ 2) * Bp ^ 2)
  apply (div_lt_div_iff₀ hdenq hdenp).2
  exact mul_lt_mul_of_pos_left hden (mul_pos (by norm_num) (sq_pos_of_pos ha))

theorem gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg (a : ℝ) (e : ℕ) (p q : Nat.Primes) (s : Fin 6) :
    0 ≤ RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
  unfold RHTower.gammaSewnFourRateBoundaryPairRawWeight
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem gammaSewnOrderedPrimeDepthPlucker_partition_pos {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    0 < ∑ s, RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
  have hraw := gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti ha hpq halt
  have h0 : 0 < RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 0 :=
    lt_of_le_of_lt (gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 5) hraw
  have h1 := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 1
  have h2 := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 2
  have h3 := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 3
  have h4 := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 4
  have h5 := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 5
  simp [Fin.sum_univ_succ]
  linarith

def gammaSewnOrderedPrimeDepthPlucker_probability (a : ℝ) (e : ℕ) (p q : Nat.Primes) : Fin 6 → ℝ :=
  RHTower.gammaSewnFourRateBoundaryPairProbability a
    (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q)

theorem gammaSewnOrderedPrimeDepthPlucker_probability_five_lt_zero {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    gammaSewnOrderedPrimeDepthPlucker_probability a e p q 5 < gammaSewnOrderedPrimeDepthPlucker_probability a e p q 0 := by
  unfold gammaSewnOrderedPrimeDepthPlucker_probability RHTower.gammaSewnFourRateBoundaryPairProbability
  have hpart := gammaSewnOrderedPrimeDepthPlucker_partition_pos ha hpq halt
  apply (div_lt_div_iff₀ hpart hpart).2
  exact mul_lt_mul_of_pos_right (gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti ha hpq halt) hpart

theorem gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_eq (a : ℝ) (e : ℕ) (p q : Nat.Primes) :
    (∑ s, gammaSewnCriticalPlucker_complementChirality
          (gammaSewnOrderedPrimeDepthPlucker_probability a e p q) s *
        RHTower.gammaSewnFourRateComplementaryFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s) =
      2 * (gammaSewnOrderedPrimeDepthPlucker_probability a e p q 0 - gammaSewnOrderedPrimeDepthPlucker_probability a e p q 5) *
        (RHTower.gammaSewnMobiusApertureBoundaryFisherClock q -
          RHTower.gammaSewnMobiusApertureBoundaryFisherClock p) := by
  simp [Fin.sum_univ_succ, gammaSewnCriticalPlucker_complementChirality,
    gammaSewnCriticalPlucker_complementIndex,
    RHTower.gammaSewnFourRateComplementaryFisher,
    RHTower.fourRateComplementarySum,
    RHTower.fourRatePairComplementLeft,
    RHTower.fourRatePairComplementRight,
    gammaSewnOrderedPrimeDepthPlucker_cell]
  ring

theorem gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_pos {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    0 < ∑ s, gammaSewnCriticalPlucker_complementChirality
          (gammaSewnOrderedPrimeDepthPlucker_probability a e p q) s *
        RHTower.gammaSewnFourRateComplementaryFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
  rw [gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_eq]
  exact mul_pos
    (mul_pos (by norm_num) (sub_pos.mpr (gammaSewnOrderedPrimeDepthPlucker_probability_five_lt_zero ha hpq halt)))
    (sub_pos.mpr (gammaSewnCriticalOrderedPrimePlucker_fisher_lt hpq))

theorem gammaSewnOrderedPrimeDepthPlucker_schurFraction_gt_half {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    (1 / 2 : ℝ) < gammaSewnCriticalPlucker_schurFraction
      (gammaSewnOrderedPrimeDepthPlucker_probability a e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) := by
  have hsum : ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s = 1 :=
    RHTower.sum_gammaSewnFourRateBoundaryPairProbability
      (gammaSewnOrderedPrimeDepthPlucker_partition_pos ha hpq halt).ne'
  have hdecomp := gammaSewnCriticalPlucker_complementaryFisherMean_eq_half_add_chirality
    (gammaSewnOrderedPrimeDepthPlucker_probability a e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) hsum
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) := by
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
  nlinarith [gammaSewnOrderedPrimeDepthPlucker_chiralityFisherMoment_pos ha hpq halt]

theorem gammaSewnOrderedPrimeDepthPlucker_probability_nonneg {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) (s : Fin 6) :
    0 ≤ gammaSewnOrderedPrimeDepthPlucker_probability a e p q s := by
  unfold gammaSewnOrderedPrimeDepthPlucker_probability RHTower.gammaSewnFourRateBoundaryPairProbability
  exact div_nonneg (gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q s) (gammaSewnOrderedPrimeDepthPlucker_partition_pos ha hpq halt).le

theorem gammaSewnOrderedPrimeDepthPlucker_probability_zero_pos {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    0 < gammaSewnOrderedPrimeDepthPlucker_probability a e p q 0 := by
  have hraw := gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti ha hpq halt
  have hraw0 : 0 < RHTower.gammaSewnFourRateBoundaryPairRawWeight a
      (gammaSewnOrderedPrimeDepthPlucker_rate e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) 0 :=
    lt_of_le_of_lt (gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg a e p q 5) hraw
  unfold gammaSewnOrderedPrimeDepthPlucker_probability RHTower.gammaSewnFourRateBoundaryPairProbability
  exact div_pos hraw0 (gammaSewnOrderedPrimeDepthPlucker_partition_pos ha hpq halt)

theorem gammaSewnOrderedPrimeDepthPlucker_complementaryFisherMean_lt_total {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    RHTower.complementaryFisherMean (gammaSewnOrderedPrimeDepthPlucker_probability a e p q)
        (RHTower.gammaSewnFourRateComplementaryFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q)) <
      RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) := by
  have hsum : ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s = 1 :=
    RHTower.sum_gammaSewnFourRateBoundaryPairProbability
      (gammaSewnOrderedPrimeDepthPlucker_partition_pos ha hpq halt).ne'
  have hselected (s : Fin 6) :
      0 < RHTower.gammaSewnFourRateSelectedFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
    unfold RHTower.gammaSewnFourRateSelectedFisher RHTower.fourRateSelectedSum
    exact add_pos
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
      (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _)
  have hselpos : 0 < ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s *
      RHTower.gammaSewnFourRateSelectedFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
    apply Finset.sum_pos'
    · intro s _hs
      exact mul_nonneg (gammaSewnOrderedPrimeDepthPlucker_probability_nonneg ha hpq halt s) (hselected s).le
    · exact ⟨0, Finset.mem_univ _, mul_pos (gammaSewnOrderedPrimeDepthPlucker_probability_zero_pos ha hpq halt)
        (hselected 0)⟩
  have htotal := RHTower.gammaSewnFourRateSelectedFisher_add_complementaryFisher
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q)
  unfold RHTower.complementaryFisherMean
  have hid :
      (∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s *
          RHTower.gammaSewnFourRateComplementaryFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s) =
        RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) -
          ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s *
            RHTower.gammaSewnFourRateSelectedFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
    calc
      _ = ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s *
          (RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) -
            RHTower.gammaSewnFourRateSelectedFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s) := by
          apply Finset.sum_congr rfl
          intro s _hs
          rw [← htotal s]
          ring
      _ = RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) *
            (∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s) -
          ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability a e p q s *
            RHTower.gammaSewnFourRateSelectedFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) s := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro s _hs
          ring
      _ = _ := by rw [hsum]; ring
  rw [hid]
  linarith

theorem gammaSewnOrderedPrimeDepthPlucker_schurFraction_lt_one {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)) :
    gammaSewnCriticalPlucker_schurFraction
        (gammaSewnOrderedPrimeDepthPlucker_probability a e p q) (gammaSewnOrderedPrimeDepthPlucker_cell e p q) < 1 := by
  have htotal : 0 < RHTower.gammaSewnFourRateTotalFisher (gammaSewnOrderedPrimeDepthPlucker_cell e p q) := by
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
  simpa using gammaSewnOrderedPrimeDepthPlucker_complementaryFisherMean_lt_total ha hpq halt

theorem gammaSewnOrderedPrimeDepthPlucker_reducedWeight_mem_Ioo_half {a : ℝ} {e : ℕ} {p q : Nat.Primes}
    (ha : 0 < a) (hpq : (p : ℕ) < (q : ℕ))
    (halt : a < ((e : ℝ) + 1 / 2) * Real.log (p : ℝ))
    (pk : Nat.Primes × ℕ) :
    gammaSewnCriticalPlucker_reducedWeight (gammaSewnOrderedPrimeDepthPlucker_probability a e p q)
        (gammaSewnOrderedPrimeDepthPlucker_cell e p q) pk ∈
      Set.Ioo 0 ((1 / 2 : ℝ) *
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) := by
  constructor
  · unfold gammaSewnCriticalPlucker_reducedWeight
    exact mul_pos (sub_pos.mpr (gammaSewnOrderedPrimeDepthPlucker_schurFraction_lt_one ha hpq halt))
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk)
  · unfold gammaSewnCriticalPlucker_reducedWeight
    apply mul_lt_mul_of_pos_right _
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk)
    linarith [gammaSewnOrderedPrimeDepthPlucker_schurFraction_gt_half ha hpq halt]

end RHTower.HedenmalmThetaSource
