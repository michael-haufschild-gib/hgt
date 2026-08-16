import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalDiagonalTransferNoGo

/-!
# Physical Pluecker covariance operator

P-G90 forces Route P beyond every positive diagonal transfer on the bare reciprocal-gap nodes.
This file recovers the source object discarded by scalar Schur fractions: the full covariance of
the six physical two-label Pluecker incidences in each ordered-prime depth packet.

Prime-power uniqueness proves the four physical log-clock rates are injective. Consequently all
six Pluecker probabilities are strictly positive. Their covariance form is positive semidefinite,
has kernel exactly the constant direction, and necessarily has a nonzero off-diagonal entry. Thus
the literal source already supplies a canonical rank-three quotient coupling capable of moving
spectral poles. No target moment, Xi zero, fitted coefficient, computation, or added axiom enters.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

private theorem prime_nat_mul_log_ne
    {p q : Nat.Primes} {m n : ℕ}
    (hpq : p ≠ q) (hm : 0 < m) :
    (m : ℝ) * Real.log (p : ℝ) ≠ (n : ℝ) * Real.log (q : ℝ) := by
  intro hlog
  have hexp := congrArg Real.exp hlog
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
  have hpowR : ((p : ℝ) ^ m) = (q : ℝ) ^ n := by
    simpa [Real.exp_nat_mul, Real.exp_log hp0,
      Real.exp_log hq0] using hexp
  have hpowN : (p : ℕ) ^ m = (q : ℕ) ^ n := by exact_mod_cast hpowR
  have hdvd : (p : ℕ) ∣ (q : ℕ) ^ n := by
    rw [← hpowN]
    exact dvd_pow_self (p : ℕ) hm.ne'
  have hpqVal : (p : ℕ) = (q : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (p.2.dvd_of_dvd_pow hdvd)
  exact hpq (Subtype.ext hpqVal)

theorem gammaSewnOrderedPrimeDepthPlucker_rate_injective
    (e : ℕ) {p q : Nat.Primes} (hpq : p ≠ q) :
    Function.Injective (gammaSewnOrderedPrimeDepthPlucker_rate e p q) := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hq2 : 2 ≤ (q : ℕ) := q.2.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
  have hlog_ne : Real.log (p : ℝ) ≠ Real.log (q : ℝ) := by
    intro h
    apply hpq
    apply Subtype.ext
    have hpqR : (p : ℝ) = (q : ℝ) := by
      rw [← Real.exp_log hp0, ← Real.exp_log hq0, h]
    exact_mod_cast hpqR
  have h03 := prime_nat_mul_log_ne (p := p) (q := q)
    (m := 2 * e + 1) (n := 2 * e + 3) hpq (by omega)
  have h12 := prime_nat_mul_log_ne (p := p) (q := q)
    (m := 2 * e + 3) (n := 2 * e + 1) hpq (by omega)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [gammaSewnOrderedPrimeDepthPlucker_rate,
      gammaSewnOrderedPrimeDepthPlucker_cell,
      RHTower.gammaSewnMobiusApertureCellMidHeight] at hij ⊢
  · rcases hij with h | h | h
    · omega
    · omega
    · linarith
  · rcases hij with h | h
    · exact hlog_ne h
    · have he0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
      norm_num at h
      linarith
  · apply h03
    push_cast
    nlinarith [hij]
  · rcases hij with h | h | h
    · omega
    · omega
    · linarith
  · apply h12
    push_cast
    nlinarith [hij]
  · rcases hij with h | h
    · exact hlog_ne h
    · have he0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
      norm_num at h
      linarith
  · rcases hij with h | h
    · exact hlog_ne h.symm
    · have he0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
      norm_num at h
      linarith
  · apply h12
    push_cast
    nlinarith [hij]
  · rcases hij with h | h | h
    · omega
    · omega
    · linarith
  · apply h03
    push_cast
    nlinarith [hij]
  · rcases hij with h | h
    · exact hlog_ne h.symm
    · have he0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
      norm_num at h
      linarith
  · rcases hij with h | h | h
    · omega
    · omega
    · linarith

theorem gammaSewnCriticalPrimeDepthPacket_rate_boundary_ne
    {e : ℕ} {p q : Nat.Primes} (i : Fin 4) :
    gammaSewnOrderedPrimeDepthPlucker_rate e p q i ^ 2 -
      gammaSewnCriticalFinitePacket_aperture ^ 2 ≠ 0 := by
  have ha0 := gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
  have hpe := gammaSewnCriticalFinitePacket_aperture_admissible e p
  have hpe1 := gammaSewnCriticalFinitePacket_aperture_admissible (e + 1) p
  have hqe := gammaSewnCriticalFinitePacket_aperture_admissible e q
  have hqe1 := gammaSewnCriticalFinitePacket_aperture_admissible (e + 1) q
  fin_cases i <;>
    simp [gammaSewnOrderedPrimeDepthPlucker_rate,
      gammaSewnOrderedPrimeDepthPlucker_cell,
      RHTower.gammaSewnMobiusApertureCellMidHeight] at hpe hpe1 hqe hqe1 ⊢
  · nlinarith [mul_pos (sub_pos.mpr hpe) (add_pos ha0 (ha0.trans hpe))]
  · nlinarith [mul_pos (sub_pos.mpr hpe1) (add_pos ha0 (ha0.trans hpe1))]
  · nlinarith [mul_pos (sub_pos.mpr hqe) (add_pos ha0 (ha0.trans hqe))]
  · nlinarith [mul_pos (sub_pos.mpr hqe1) (add_pos ha0 (ha0.trans hqe1))]

theorem gammaSewnCriticalPrimeDepthPacket_probability_pos
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) (s : Fin 6) :
    0 < gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q s := by
  unfold gammaSewnOrderedPrimeDepthPlucker_probability
  apply RHTower.gammaSewnFourRateBoundaryPairProbability_pos
  · exact gammaSewnCriticalPlucker_hostileHarmonicAperture_pos.ne'
  · exact gammaSewnOrderedPrimeDepthPlucker_rate_injective e
      (fun h => (ne_of_lt hpq) (congrArg Subtype.val h))
  · exact gammaSewnCriticalPrimeDepthPacket_rate_boundary_ne

def fourRatePluckerCovariance
    (weight : Fin 6 → ℝ) (x y : Fin 4 → ℝ) : ℝ :=
  (∑ s, weight s * RHTower.fourRateSelectedSum x s *
      RHTower.fourRateSelectedSum y s) -
    (∑ s, weight s * RHTower.fourRateSelectedSum x s) *
      (∑ s, weight s * RHTower.fourRateSelectedSum y s)

theorem fourRatePluckerCovariance_self_eq_variance
    (weight : Fin 6 → ℝ) (x : Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x x =
      RHTower.normalizedFiniteVariance weight
        (RHTower.fourRateSelectedSum x) := by
  unfold fourRatePluckerCovariance RHTower.normalizedFiniteVariance
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    ring
  · ring

theorem fourRatePluckerCovariance_nonneg
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (hsum : ∑ s, weight s = 1) (x : Fin 4 → ℝ) :
    0 ≤ fourRatePluckerCovariance weight x x := by
  rw [fourRatePluckerCovariance_self_eq_variance]
  have hpair := HTGeometry.normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    weight (RHTower.fourRateSelectedSum x) hsum
  have hnonneg : 0 ≤ ∑ s, ∑ t,
      weight s * weight t *
        (RHTower.fourRateSelectedSum x s -
          RHTower.fourRateSelectedSum x t) ^ 2 := by
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ =>
      mul_nonneg (mul_nonneg (hweight s) (hweight t)) (sq_nonneg _)
  rw [hpair] at hnonneg
  unfold RHTower.normalizedFiniteVariance
  linarith

theorem fourRatePluckerCovariance_constant_right
    (weight : Fin 6 → ℝ) (hsum : ∑ s, weight s = 1)
    (x : Fin 4 → ℝ) (c : ℝ) :
    fourRatePluckerCovariance weight x (fun _ => c) = 0 := by
  unfold fourRatePluckerCovariance
  have hconst : ∀ s : Fin 6,
      RHTower.fourRateSelectedSum (fun _ : Fin 4 => c) s = 2 * c := by
    intro s
    unfold RHTower.fourRateSelectedSum
    ring
  simp_rw [hconst]
  rw [← Finset.sum_mul]
  simp_rw [mul_comm (weight _) (2 * c)]
  rw [← Finset.mul_sum, hsum, mul_one]
  ring

theorem fourRatePluckerCovariance_self_eq_zero_iff_constant
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 < weight s)
    (hsum : ∑ s, weight s = 1) (x : Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x x = 0 ↔
      ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hzero
    have hpair := HTGeometry.normalizedWeight_pairwiseSqGap_eq_two_mul_variance
      weight (RHTower.fourRateSelectedSum x) hsum
    have hvariance : RHTower.normalizedFiniteVariance weight
        (RHTower.fourRateSelectedSum x) = 0 := by
      rw [← fourRatePluckerCovariance_self_eq_variance]
      exact hzero
    have hpairZero : (∑ s, ∑ t,
        weight s * weight t *
          (RHTower.fourRateSelectedSum x s -
            RHTower.fourRateSelectedSum x t) ^ 2) = 0 := by
      rw [hpair]
      unfold RHTower.normalizedFiniteVariance at hvariance
      rw [hvariance]
      ring
    have hsel : ∀ s t : Fin 6,
        RHTower.fourRateSelectedSum x s = RHTower.fourRateSelectedSum x t := by
      intro s t
      have houterNonneg : ∀ u ∈ (Finset.univ : Finset (Fin 6)),
          0 ≤ ∑ v, weight u * weight v *
            (RHTower.fourRateSelectedSum x u -
              RHTower.fourRateSelectedSum x v) ^ 2 := by
        intro u _
        exact Finset.sum_nonneg fun v _ =>
          mul_nonneg (mul_nonneg (hweight u).le (hweight v).le) (sq_nonneg _)
      have hrow := (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp hpairZero
        s (Finset.mem_univ s)
      have hinnerNonneg : ∀ v ∈ (Finset.univ : Finset (Fin 6)),
          0 ≤ weight s * weight v *
            (RHTower.fourRateSelectedSum x s -
              RHTower.fourRateSelectedSum x v) ^ 2 := by
        intro v _
        exact mul_nonneg (mul_nonneg (hweight s).le (hweight v).le) (sq_nonneg _)
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg hinnerNonneg).mp hrow
        t (Finset.mem_univ t)
      have hwt : 0 < weight s * weight t := mul_pos (hweight s) (hweight t)
      have hsq : (RHTower.fourRateSelectedSum x s -
          RHTower.fourRateSelectedSum x t) ^ 2 = 0 := by
        exact (mul_eq_zero.mp hterm).resolve_left hwt.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    have h01 := hsel 0 1
    have h02 := hsel 0 2
    have h13 := hsel 1 3
    simp [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
      RHTower.fourRatePairRight] at h01 h02 h13
    refine ⟨x 0, funext fun i => ?_⟩
    fin_cases i <;> simp <;> linarith
  · rintro ⟨c, rfl⟩
    exact fourRatePluckerCovariance_constant_right weight hsum (fun _ => c) c

def fourRateCoordinateDelta (i j : Fin 4) : ℝ := if j = i then 1 else 0

/-- A selected-pair coordinate observable is an indicator: a pair contains a fixed coordinate
exactly zero or one times. -/
theorem fourRateSelectedSum_coordinateDelta_sq
    (i : Fin 4) (s : Fin 6) :
    RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s ^ 2 =
      RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s := by
  fin_cases i <;> fin_cases s <;>
    simp [RHTower.fourRateSelectedSum, RHTower.fourRatePairLeft,
      RHTower.fourRatePairRight, fourRateCoordinateDelta]

/-- The diagonal coordinate covariance is exactly the Bernoulli variance of pair inclusion.
No normalization hypothesis is needed: it is an algebraic consequence of the indicator law. -/
theorem fourRatePluckerCovariance_coordinateDelta_self_eq_bernoulliVariance
    (weight : Fin 6 → ℝ) (i : Fin 4) :
    fourRatePluckerCovariance weight
        (fourRateCoordinateDelta i) (fourRateCoordinateDelta i) =
      (∑ s, weight s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s) *
        (1 - ∑ s, weight s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s) := by
  unfold fourRatePluckerCovariance
  have hsecond :
      (∑ s, weight s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s *
            RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s) =
        ∑ s, weight s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s := by
    apply Finset.sum_congr rfl
    intro s _
    calc
      weight s * RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s *
          RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s =
          weight s *
            RHTower.fourRateSelectedSum (fourRateCoordinateDelta i) s ^ 2 := by
              ring
      _ = _ := by rw [fourRateSelectedSum_coordinateDelta_sq]
  rw [hsecond]
  ring

theorem fourRatePluckerCovariance_add_right
    (weight : Fin 6 → ℝ) (x y z : Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x (y + z) =
      fourRatePluckerCovariance weight x y +
        fourRatePluckerCovariance weight x z := by
  have hselected : ∀ s : Fin 6,
      RHTower.fourRateSelectedSum (y + z) s =
        RHTower.fourRateSelectedSum y s +
          RHTower.fourRateSelectedSum z s := by
    intro s
    simp [RHTower.fourRateSelectedSum]
    ring
  unfold fourRatePluckerCovariance
  simp_rw [hselected]
  rw [show (∑ s, weight s * RHTower.fourRateSelectedSum x s *
        (RHTower.fourRateSelectedSum y s + RHTower.fourRateSelectedSum z s)) =
      (∑ s, weight s * RHTower.fourRateSelectedSum x s *
        RHTower.fourRateSelectedSum y s) +
      ∑ s, weight s * RHTower.fourRateSelectedSum x s *
        RHTower.fourRateSelectedSum z s by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring]
  rw [show (∑ s, weight s *
        (RHTower.fourRateSelectedSum y s + RHTower.fourRateSelectedSum z s)) =
      (∑ s, weight s * RHTower.fourRateSelectedSum y s) +
      ∑ s, weight s * RHTower.fourRateSelectedSum z s by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring]
  ring

theorem fourRatePluckerCovariance_finset_sum_right
    {ι : Type*} [DecidableEq ι]
    (weight : Fin 6 → ℝ) (hsum : ∑ s, weight s = 1)
    (x : Fin 4 → ℝ) (S : Finset ι) (y : ι → Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x (∑ i ∈ S, y i) =
      ∑ i ∈ S, fourRatePluckerCovariance weight x (y i) := by
  induction S using Finset.induction_on with
  | empty =>
      change fourRatePluckerCovariance weight x (fun _ => 0) = 0
      exact fourRatePluckerCovariance_constant_right weight hsum x 0
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        fourRatePluckerCovariance_add_right, ih]

theorem sum_fourRatePluckerCovariance_coordinateDelta_right
    (weight : Fin 6 → ℝ) (hsum : ∑ s, weight s = 1)
    (x : Fin 4 → ℝ) :
    ∑ j, fourRatePluckerCovariance weight x (fourRateCoordinateDelta j) = 0 := by
  have hone : (∑ j : Fin 4, fourRateCoordinateDelta j) = fun _ => (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [fourRateCoordinateDelta]
  calc
    (∑ j, fourRatePluckerCovariance weight x (fourRateCoordinateDelta j)) =
        fourRatePluckerCovariance weight x
          (∑ j, fourRateCoordinateDelta j) := by
      symm
      simpa using
        fourRatePluckerCovariance_finset_sum_right weight hsum x
          Finset.univ fourRateCoordinateDelta
    _ = fourRatePluckerCovariance weight x (fun _ => 1) := by rw [hone]
    _ = 0 := fourRatePluckerCovariance_constant_right weight hsum x 1

theorem exists_fourRatePluckerCovariance_offDiagonal_ne_zero
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 < weight s)
    (hsum : ∑ s, weight s = 1) :
    ∃ i j : Fin 4, i ≠ j ∧
      fourRatePluckerCovariance weight
        (fourRateCoordinateDelta i) (fourRateCoordinateDelta j) ≠ 0 := by
  have hself : fourRatePluckerCovariance weight
      (fourRateCoordinateDelta 0) (fourRateCoordinateDelta 0) ≠ 0 := by
    intro hzero
    obtain ⟨c, hc⟩ :=
      (fourRatePluckerCovariance_self_eq_zero_iff_constant weight hweight hsum
        (fourRateCoordinateDelta 0)).mp hzero
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [fourRateCoordinateDelta] at h0 h1
    linarith
  have hrow := sum_fourRatePluckerCovariance_coordinateDelta_right weight hsum
    (fourRateCoordinateDelta 0)
  by_contra hnone
  push Not at hnone
  have h1 := hnone 0 1 (by decide)
  have h2 := hnone 0 2 (by decide)
  have h3 := hnone 0 3 (by decide)
  simp [Fin.sum_univ_succ, h1, h2, h3] at hrow
  exact hself hrow

theorem sum_gammaSewnCriticalPrimeDepthPacket_probability
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    ∑ s, gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q s = 1 := by
  exact RHTower.sum_gammaSewnFourRateBoundaryPairProbability
    (gammaSewnOrderedPrimeDepthPlucker_partition_pos
      gammaSewnCriticalPlucker_hostileHarmonicAperture_pos hpq
      (gammaSewnCriticalFinitePacket_aperture_admissible e p)).ne'

/-- Full physical six-minor covariance on one four-label ordered-prime depth packet. -/
def gammaSewnCriticalPrimeDepthPacket_PluckerCovariance
    (e : ℕ) (p q : Nat.Primes) (x y : Fin 4 → ℝ) : ℝ :=
  fourRatePluckerCovariance
    (gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q) x y

theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_nonneg
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    0 ≤ gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q x x := by
  apply fourRatePluckerCovariance_nonneg
  · intro s
    exact (gammaSewnCriticalPrimeDepthPacket_probability_pos hpq s).le
  · exact sum_gammaSewnCriticalPrimeDepthPacket_probability hpq

/-- **P-G91 quotient rigidity.** Physical covariance vanishes exactly on common-mode vectors. -/
theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_self_eq_zero_iff_constant
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q x x = 0 ↔
      ∃ c : ℝ, x = fun _ => c := by
  exact fourRatePluckerCovariance_self_eq_zero_iff_constant
    (gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q)
    (gammaSewnCriticalPrimeDepthPacket_probability_pos hpq)
    (sum_gammaSewnCriticalPrimeDepthPacket_probability hpq) x

/-- Every physical packet is genuinely coupled: some cross-label covariance is nonzero. -/
theorem exists_gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_offDiagonal_ne_zero
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    ∃ i j : Fin 4, i ≠ j ∧
      gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q
        (fourRateCoordinateDelta i) (fourRateCoordinateDelta j) ≠ 0 := by
  exact exists_fourRatePluckerCovariance_offDiagonal_ne_zero
    (gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q)
    (gammaSewnCriticalPrimeDepthPacket_probability_pos hpq)
    (sum_gammaSewnCriticalPrimeDepthPacket_probability hpq)

end RHTower.HedenmalmThetaSource
