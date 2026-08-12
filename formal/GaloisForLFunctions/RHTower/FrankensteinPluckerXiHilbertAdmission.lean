import GaloisForLFunctions.RHTower.FrankensteinPluckerXiHorizontalLanding
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness

/-!
# Xi admission to the faithful physical Pluecker Hilbert space

The two fixed positive reporters from the coefficient-faithful Xi horizontal landing are genuine
vectors in P-G95's physical ell-two space.  P-G84 denominator summability absorbs the reporter
scales, while every actual Xi centered Bockstein coefficient is uniformly bounded by one throughout
the open critical strip.

Both admitted vectors retain the exact critical-line zero radical and reflection oddness.  Applying
the faithful P-G95 operator gives a strictly positive quadratic detector exactly off the critical
line.  This closes Hilbert admission, not source annihilation or RH.
-/

open Real Set Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section
namespace RHTower.HedenmalmThetaSource

theorem frankensteinPluckerProbability_le_one
    (z : ℕ × ℕ) (s : Fin 6) :
    frankensteinPluckerProbability z s ≤ 1 := by
  rw [← sum_frankensteinPluckerProbability z]
  exact Finset.single_le_sum
    (fun i _ => (frankensteinPluckerProbability_pos z i).le)
    (Finset.mem_univ s)

theorem abs_sourceZeroHorizontalPrimeCarrier_le_one
    (q : RHTower.XiZeroCopy) (p : Nat.Primes) :
    |RHTower.sourceZeroHorizontalPrimeCarrier q p| ≤ 1 := by
  let t := RHTower.primeDepthBVWoldXiCenteredRate q.1
  have ht : |t| < 1 := by
    exact RHTower.xiCenteredPrimeIdealRate_abs_lt_one q.1
  have hmag := (RHTower.primeGammaCofinalBocksteinMagnitude_bounds t p).2
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hexp : |t| - 1 ≤ 0 := by linarith
  have hpow : (p : ℝ) ^ (|t| - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 hexp
  change |RHTower.primeGammaCofinalBocksteinCoefficient t p| ≤ 1
  exact hmag.trans hpow

theorem frankensteinPluckerReporterScale_sq_le
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerReporterScale z s t i ^ 2 ≤
      gammaSewnCriticalAdjacentPrime_DenominatorTerm z *
        gammaSewnCriticalPlucker_nodeBound := by
  have hD0 := (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z).le
  have hps0 := (frankensteinPluckerProbability_pos z s).le
  have hpt0 := (frankensteinPluckerProbability_pos z t).le
  have hps1 := frankensteinPluckerProbability_le_one z s
  have hpt1 := frankensteinPluckerProbability_le_one z t
  have hnode0 := (gammaSewnCriticalPrimeDepthPacket_node_pos z.1
    (gammaSewnCriticalAdjacentPrime_lower z.2)
    (gammaSewnCriticalAdjacentPrime_upper z.2) i).le
  have hnodeB : gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i ≤
      gammaSewnCriticalPlucker_nodeBound := by
    exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
      (by norm_num) (by norm_num) _
  rw [frankensteinPluckerReporterScale]
  simp only [mul_pow]
  rw [
    Real.sq_sqrt hD0,
    Real.sq_sqrt (div_nonneg (mul_nonneg hps0 hpt0) (by norm_num)),
    Real.sq_sqrt hnode0]
  have hprob : frankensteinPluckerProbability z s *
      frankensteinPluckerProbability z t / 2 ≤ 1 := by
    nlinarith [mul_nonneg hps0 hpt0,
      mul_le_mul hps1 hpt1 hpt0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hinner : (frankensteinPluckerProbability z s *
        frankensteinPluckerProbability z t / 2) *
      gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i ≤
      gammaSewnCriticalPlucker_nodeBound :=
    (mul_le_of_le_one_left hnode0 hprob).trans hnodeB
  calc
    gammaSewnCriticalAdjacentPrime_DenominatorTerm z *
          (frankensteinPluckerProbability z s *
            frankensteinPluckerProbability z t / 2) *
        gammaSewnCriticalPrimeDepthPacket_node z.1
          (gammaSewnCriticalAdjacentPrime_lower z.2)
          (gammaSewnCriticalAdjacentPrime_upper z.2) i =
        gammaSewnCriticalAdjacentPrime_DenominatorTerm z *
          ((frankensteinPluckerProbability z s *
            frankensteinPluckerProbability z t / 2) *
            gammaSewnCriticalPrimeDepthPacket_node z.1
              (gammaSewnCriticalAdjacentPrime_lower z.2)
              (gammaSewnCriticalAdjacentPrime_upper z.2) i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinner hD0

theorem summable_sq_frankensteinPluckerReporterScale
    (s t : Fin 6) (i : Fin 4) :
    Summable (fun z : ℕ × ℕ =>
      frankensteinPluckerReporterScale z s t i ^ 2) := by
  exact Summable.of_nonneg_of_le
    (fun _ => sq_nonneg _)
    (fun z => frankensteinPluckerReporterScale_sq_le z s t i)
    (summable_gammaSewnCriticalAdjacentPrime_DenominatorTerm.mul_right
      gammaSewnCriticalPlucker_nodeBound)

theorem summable_norm_sq_frankensteinXiLowerPrimeCarrier
    (q : RHTower.XiZeroCopy) :
    Summable (fun z : ℕ × ℕ =>
      ‖frankensteinXiLowerPrimeCarrier q z.1 z.2‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun z => ?_)
    (summable_sq_frankensteinPluckerReporterScale 1 4 0)
  rw [frankensteinXiLowerPrimeCarrier,
    frankensteinPluckerLowerVertexReporter_one_four_eq_scale,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc := abs_sourceZeroHorizontalPrimeCarrier_le_one q
    (RHTower.nthPrimeSubtype z.2)
  have hs0 := (frankensteinPluckerReporterScale_pos z 1 4 0).le
  have hc0 : 0 ≤ |RHTower.sourceZeroHorizontalPrimeCarrier q
      (RHTower.nthPrimeSubtype z.2)| := abs_nonneg _
  have hprod : frankensteinPluckerReporterScale z 1 4 0 *
      |RHTower.sourceZeroHorizontalPrimeCarrier q
        (RHTower.nthPrimeSubtype z.2)| ≤
      frankensteinPluckerReporterScale z 1 4 0 := by
    simpa using mul_le_mul_of_nonneg_left hc hs0
  simp only [abs_of_nonneg hs0, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [mul_nonneg hs0 hc0]

theorem summable_norm_sq_frankensteinXiUpperPrimeCarrier
    (q : RHTower.XiZeroCopy) :
    Summable (fun z : ℕ × ℕ =>
      ‖frankensteinXiUpperPrimeCarrier q z.1 z.2‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun z => ?_)
    (summable_sq_frankensteinPluckerReporterScale 4 1 1)
  rw [frankensteinXiUpperPrimeCarrier,
    frankensteinPluckerUpperVertexReporter_four_one_eq_scale,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc := abs_sourceZeroHorizontalPrimeCarrier_le_one q
    (RHTower.nthPrimeSubtype z.2)
  have hs0 := (frankensteinPluckerReporterScale_pos z 4 1 1).le
  have hc0 : 0 ≤ |RHTower.sourceZeroHorizontalPrimeCarrier q
      (RHTower.nthPrimeSubtype z.2)| := abs_nonneg _
  have hprod : frankensteinPluckerReporterScale z 4 1 1 *
      |RHTower.sourceZeroHorizontalPrimeCarrier q
        (RHTower.nthPrimeSubtype z.2)| ≤
      frankensteinPluckerReporterScale z 4 1 1 := by
    simpa using mul_le_mul_of_nonneg_left hc hs0
  simp only [abs_of_nonneg hs0, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [mul_nonneg hs0 hc0]

def frankensteinXiLowerPhysicalPluckerHilbertCarrier
    (q : RHTower.XiZeroCopy) :
    GammaSewnCriticalPhysicalPluckerHilbert :=
  ⟨fun z => frankensteinXiLowerPrimeCarrier q z.1 z.2,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_frankensteinXiLowerPrimeCarrier q)⟩

def frankensteinXiUpperPhysicalPluckerHilbertCarrier
    (q : RHTower.XiZeroCopy) :
    GammaSewnCriticalPhysicalPluckerHilbert :=
  ⟨fun z => frankensteinXiUpperPrimeCarrier q z.1 z.2,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_frankensteinXiUpperPrimeCarrier q)⟩

@[simp] theorem frankensteinXiLowerPhysicalPluckerHilbertCarrier_apply
    (q : RHTower.XiZeroCopy) (z : ℕ × ℕ) :
    frankensteinXiLowerPhysicalPluckerHilbertCarrier q z =
      frankensteinXiLowerPrimeCarrier q z.1 z.2 := rfl

@[simp] theorem frankensteinXiUpperPhysicalPluckerHilbertCarrier_apply
    (q : RHTower.XiZeroCopy) (z : ℕ × ℕ) :
    frankensteinXiUpperPhysicalPluckerHilbertCarrier q z =
      frankensteinXiUpperPrimeCarrier q z.1 z.2 := rfl

theorem frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    frankensteinXiLowerPhysicalPluckerHilbertCarrier q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have h00 := congrArg
      (fun x : GammaSewnCriticalPhysicalPluckerHilbert => x (0, 0)) hzero
    exact (frankensteinXiLowerPrimeCarrier_eq_zero_iff q 0 0).1 (by simpa using h00)
  · intro hline
    ext z
    exact (frankensteinXiLowerPrimeCarrier_eq_zero_iff q z.1 z.2).2 hline

theorem frankensteinXiUpperPhysicalPluckerHilbertCarrier_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    frankensteinXiUpperPhysicalPluckerHilbertCarrier q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have h00 := congrArg
      (fun x : GammaSewnCriticalPhysicalPluckerHilbert => x (0, 0)) hzero
    exact (frankensteinXiUpperPrimeCarrier_eq_zero_iff q 0 0).1 (by simpa using h00)
  · intro hline
    ext z
    exact (frankensteinXiUpperPrimeCarrier_eq_zero_iff q z.1 z.2).2 hline

theorem frankensteinXiLowerPhysicalPluckerHilbertCarrier_reflection
    (q : RHTower.XiZeroCopy) :
    frankensteinXiLowerPhysicalPluckerHilbertCarrier
        (RHTower.xiZeroCopyLineConjEquiv q) =
      -frankensteinXiLowerPhysicalPluckerHilbertCarrier q := by
  ext z
  exact frankensteinXiLowerPrimeCarrier_reflection q z.1 z.2

theorem frankensteinXiUpperPhysicalPluckerHilbertCarrier_reflection
    (q : RHTower.XiZeroCopy) :
    frankensteinXiUpperPhysicalPluckerHilbertCarrier
        (RHTower.xiZeroCopyLineConjEquiv q) =
      -frankensteinXiUpperPhysicalPluckerHilbertCarrier q := by
  ext z
  exact frankensteinXiUpperPrimeCarrier_reflection q z.1 z.2

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiLower_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff,
    frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff]

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_xiLower_energy_pos_iff
    (q : RHTower.XiZeroCopy) :
    0 < (inner ℂ
        (frankensteinXiLowerPhysicalPluckerHilbertCarrier q)
        (gammaSewnCriticalPhysicalPluckerSpectralOperator
          (frankensteinXiLowerPhysicalPluckerHilbertCarrier q))).re ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [gammaSewnCriticalPhysicalPluckerSpectralOperator_re_inner_pos_iff]
  exact not_congr
    (frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff q)

end RHTower.HedenmalmThetaSource
