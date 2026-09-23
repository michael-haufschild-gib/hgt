import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalFinitePacketFeshbachAssembly

/-!
# Complete interaction graph multiplicity no-go

P-G83 disproves the naive cofinal completion of P-G82 over every ordered prime pair.  Fixing one
depth and the lower prime at `2` repeats the same strictly positive within-prime Pluecker minor on
every edge `(2,q)`.  Consequently the physical denominator terms have a uniform positive cofinite
floor and do not even tend to zero.  The complete interaction graph is therefore not summable.

The obstruction is incidence multiplicity, not failure of local chirality or valuation decay.
Any source-faithful infinite assembly must give every same-prime minor finite total incidence;
bounded-degree prime matchings survive this necessary test without changing physical packet
weights.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

abbrev gammaSewnCriticalCompleteGraph_primeTwo : Nat.Primes := ⟨2, by norm_num⟩
abbrev gammaSewnCriticalCompleteGraph_primeThree : Nat.Primes := ⟨3, by norm_num⟩

/-- Physical denominator mass of the complete ordered-prime graph.  Non-edges are zero. -/
def gammaSewnCriticalCompleteGraph_DenominatorTerm
    (z : Nat.Primes × Nat.Primes × ℕ) : ℝ :=
  if ((z.1 : Nat.Primes) : ℕ) < (z.2.1 : ℕ) then
    gammaSewnCriticalPrimeDepthPacket_Partition z.2.2 z.1 z.2.1 *
      gammaSewnCriticalPrimeDepthPacket_Total z.2.2 z.1 z.2.1
  else 0

/-- The repeated prime-`2`, depth-zero same-prime Pluecker mass. -/
def gammaSewnCriticalCompleteGraph_anchorRaw : ℝ :=
  4 * gammaSewnCriticalFinitePacket_aperture ^ (2 : ℕ) /
    ((((gammaSewnCriticalCompleteGraph_primeTwo : ℝ) + 1) ^ (4 : ℕ) *
        Real.log (gammaSewnCriticalCompleteGraph_primeTwo : ℝ) ^ (2 : ℕ) *
        (((0 : ℝ) + 1 / 2) ^ (2 : ℕ) -
          (gammaSewnCriticalFinitePacket_aperture /
            Real.log (gammaSewnCriticalCompleteGraph_primeTwo : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ)) *
      (((0 : ℝ) + 3 / 2) ^ (2 : ℕ) -
        (gammaSewnCriticalFinitePacket_aperture /
          Real.log (gammaSewnCriticalCompleteGraph_primeTwo : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ))

theorem gammaSewnCriticalCompleteGraph_lowerRaw_eq_anchor (q : Nat.Primes) :
    RHTower.gammaSewnFourRateBoundaryPairRawWeight gammaSewnCriticalFinitePacket_aperture
        (gammaSewnOrderedPrimeDepthPlucker_rate 0 gammaSewnCriticalCompleteGraph_primeTwo q)
        (gammaSewnOrderedPrimeDepthPlucker_cell 0 gammaSewnCriticalCompleteGraph_primeTwo q) 0 =
      gammaSewnCriticalCompleteGraph_anchorRaw := by
  simpa [gammaSewnCriticalCompleteGraph_anchorRaw] using
    (gammaSewnOrderedPrimeDepthPlucker_lowerConsecutiveRawWeight_eq
      0 gammaSewnCriticalCompleteGraph_primeTwo q
        gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
        (gammaSewnCriticalFinitePacket_aperture_admissible 0
          gammaSewnCriticalCompleteGraph_primeTwo))

theorem gammaSewnCriticalCompleteGraph_anchorRaw_pos :
    0 < gammaSewnCriticalCompleteGraph_anchorRaw := by
  have hanti := gammaSewnOrderedPrimeDepthPlucker_rawWeight_strictAnti
    gammaSewnCriticalPlucker_hostileHarmonicAperture_pos
    (show (gammaSewnCriticalCompleteGraph_primeTwo : ℕ) <
      (gammaSewnCriticalCompleteGraph_primeThree : ℕ) by norm_num)
    (gammaSewnCriticalFinitePacket_aperture_admissible 0
      gammaSewnCriticalCompleteGraph_primeTwo)
  have hnonneg := gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg
    gammaSewnCriticalFinitePacket_aperture 0 gammaSewnCriticalCompleteGraph_primeTwo
      gammaSewnCriticalCompleteGraph_primeThree 5
  rw [gammaSewnCriticalCompleteGraph_lowerRaw_eq_anchor
    gammaSewnCriticalCompleteGraph_primeThree] at hanti
  exact lt_of_le_of_lt hnonneg hanti

/-- Uniform floor forced by one repeated same-prime minor and one positive Fisher clock. -/
def gammaSewnCriticalCompleteGraph_anchorFloor : ℝ :=
  gammaSewnCriticalCompleteGraph_anchorRaw *
    RHTower.gammaSewnMobiusApertureBoundaryFisherClock
      gammaSewnCriticalCompleteGraph_primeTwo

theorem gammaSewnCriticalCompleteGraph_anchorFloor_pos :
    0 < gammaSewnCriticalCompleteGraph_anchorFloor := by
  exact mul_pos gammaSewnCriticalCompleteGraph_anchorRaw_pos
    (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos
      gammaSewnCriticalCompleteGraph_primeTwo)

theorem gammaSewnCriticalCompleteGraph_anchorFloor_le_slice
    {q : Nat.Primes} (hq : q ≠ gammaSewnCriticalCompleteGraph_primeTwo) :
    gammaSewnCriticalCompleteGraph_anchorFloor ≤
      gammaSewnCriticalCompleteGraph_DenominatorTerm
        (gammaSewnCriticalCompleteGraph_primeTwo, q, 0) := by
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    apply hq
    exact Subtype.ext (by simpa using h)
  have horder : (gammaSewnCriticalCompleteGraph_primeTwo : ℕ) < (q : ℕ) := by
    have hqge : 2 ≤ (q : ℕ) := q.2.two_le
    change 2 < (q : ℕ)
    omega
  have hrawle : gammaSewnCriticalCompleteGraph_anchorRaw ≤
      gammaSewnCriticalPrimeDepthPacket_Partition 0
        gammaSewnCriticalCompleteGraph_primeTwo q := by
    rw [← gammaSewnCriticalCompleteGraph_lowerRaw_eq_anchor q]
    unfold gammaSewnCriticalPrimeDepthPacket_Partition
    exact Finset.single_le_sum
      (fun s _ => gammaSewnOrderedPrimeDepthPlucker_rawWeight_nonneg
        gammaSewnCriticalFinitePacket_aperture 0
          gammaSewnCriticalCompleteGraph_primeTwo q s)
      (Finset.mem_univ 0)
  have hpart0 : 0 ≤ gammaSewnCriticalPrimeDepthPacket_Partition 0
      gammaSewnCriticalCompleteGraph_primeTwo q :=
    (gammaSewnCriticalPrimeDepthPacket_Partition_pos horder).le
  have hclock0 : 0 ≤ RHTower.gammaSewnMobiusApertureBoundaryFisherClock
      gammaSewnCriticalCompleteGraph_primeTwo :=
    (RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos _).le
  have htotal : RHTower.gammaSewnMobiusApertureBoundaryFisherClock
      gammaSewnCriticalCompleteGraph_primeTwo ≤
      gammaSewnCriticalPrimeDepthPacket_Total 0
        gammaSewnCriticalCompleteGraph_primeTwo q := by
    simp [gammaSewnCriticalPrimeDepthPacket_Total,
      RHTower.gammaSewnFourRateTotalFisher, RHTower.fourRateTotalSum,
      gammaSewnOrderedPrimeDepthPlucker_cell]
    have hp := RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos
      gammaSewnCriticalCompleteGraph_primeTwo
    have hq' := RHTower.gammaSewnMobiusApertureBoundaryFisherClock_pos q
    linarith
  unfold gammaSewnCriticalCompleteGraph_anchorFloor
  rw [gammaSewnCriticalCompleteGraph_DenominatorTerm, if_pos horder]
  exact mul_le_mul hrawle htotal hclock0 hpart0

/-- The fixed-anchor slice has a positive cofinite floor. -/
theorem gammaSewnCriticalCompleteGraph_anchorFloor_eventually :
    ∀ᶠ q : Nat.Primes in cofinite,
      gammaSewnCriticalCompleteGraph_anchorFloor ≤
        gammaSewnCriticalCompleteGraph_DenominatorTerm
          (gammaSewnCriticalCompleteGraph_primeTwo, q, 0) := by
  filter_upwards [Filter.eventually_cofinite_ne gammaSewnCriticalCompleteGraph_primeTwo] with q hq
  exact gammaSewnCriticalCompleteGraph_anchorFloor_le_slice hq

/-- The physical complete-graph denominator already diverges on the prime-`2` anchor slice. -/
theorem not_summable_gammaSewnCriticalCompleteGraph_anchorSlice :
    ¬ Summable (fun q : Nat.Primes =>
      gammaSewnCriticalCompleteGraph_DenominatorTerm
        (gammaSewnCriticalCompleteGraph_primeTwo, q, 0)) := by
  intro hsum
  have hsmall : ∀ᶠ q : Nat.Primes in cofinite,
      gammaSewnCriticalCompleteGraph_DenominatorTerm
          (gammaSewnCriticalCompleteGraph_primeTwo, q, 0) <
        gammaSewnCriticalCompleteGraph_anchorFloor :=
    hsum.tendsto_cofinite_zero.eventually_lt_const
      gammaSewnCriticalCompleteGraph_anchorFloor_pos
  obtain ⟨q, hfloor, hlt⟩ :=
    (gammaSewnCriticalCompleteGraph_anchorFloor_eventually.and hsmall).exists
  exact (not_lt_of_ge hfloor) hlt

/-- **P-G83 complete-graph no-go.**  Summability fails before taking any quotient or Schur ratio. -/
theorem not_summable_gammaSewnCriticalCompleteGraph_DenominatorTerm :
    ¬ Summable gammaSewnCriticalCompleteGraph_DenominatorTerm := by
  intro hsum
  apply not_summable_gammaSewnCriticalCompleteGraph_anchorSlice
  exact hsum.comp_injective (fun _ _ h => by simpa using congrArg Prod.snd h)

end RHTower.HedenmalmThetaSource
