import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyLogSmooth
import GaloisForLFunctions.RHTower.DeningerAbsGenerator
import GaloisForLFunctions.RHTower.DeningerBoundarySpace

/-!
# Deninger boundary grade of the Route-T Wold residual

The activation-Fisher square root turns the centered Wold holonomy residual into an honest
boundary `ell^2` coefficient.  Doubling every prime into frequencies `+log p` and `-log p`
produces an even reflected vector.  Deninger's canonical boundary Hodge operator `i sign(mu)`
then sends it to an odd reflected vector, with opposite `+i` and `-i` values on the two sheets.

Both vectors belong to every maximal polynomial domain of the signed prime-log generator.  Thus
the source-selected residual admits a genuine, unitary Boolean grade change without entering the
much smaller multiplicative-height Kothe domain.  This is a residual-domain theorem; it does not
identify the Hodge-transformed vector with the full propagated Wold half-density layer.
-/

open Complex
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Two reflected frequency sheets over every prime. -/
abbrev XiHeatCassiniWoldPrimeSheet := Bool × Nat.Primes

/-- Exterior reflection exchanges the positive and negative frequency sheets. -/
def xiHeatCassiniWoldPrimeSheetReflect
    (i : XiHeatCassiniWoldPrimeSheet) : XiHeatCassiniWoldPrimeSheet :=
  (!i.1, i.2)

@[simp]
theorem xiHeatCassiniWoldPrimeSheetReflect_involutive
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldPrimeSheetReflect
        (xiHeatCassiniWoldPrimeSheetReflect i) = i := by
  rcases i with ⟨b, p⟩
  simp [xiHeatCassiniWoldPrimeSheetReflect]

/-- Signed prime-log frequency, positive on `true` and negative on `false`. -/
def xiHeatCassiniWoldPrimeSheetFrequency
    (i : XiHeatCassiniWoldPrimeSheet) : ℝ :=
  match i.1 with
  | true => Real.log (i.2 : ℝ)
  | false => -Real.log (i.2 : ℝ)

theorem xiHeatCassiniWoldPrimeSheetFrequency_reflect
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldPrimeSheetFrequency
        (xiHeatCassiniWoldPrimeSheetReflect i) =
      -xiHeatCassiniWoldPrimeSheetFrequency i := by
  rcases i with ⟨b, p⟩
  cases b <;> simp [xiHeatCassiniWoldPrimeSheetFrequency,
    xiHeatCassiniWoldPrimeSheetReflect]

theorem abs_xiHeatCassiniWoldPrimeSheetFrequency
    (i : XiHeatCassiniWoldPrimeSheet) :
    |xiHeatCassiniWoldPrimeSheetFrequency i| = Real.log (i.2 : ℝ) := by
  rcases i with ⟨b, p⟩
  cases b <;> simp [xiHeatCassiniWoldPrimeSheetFrequency,
    (log_prime_pos p).le]

theorem xiHeatCassiniWoldPrimeSheetFrequency_ne_zero
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldPrimeSheetFrequency i ≠ 0 := by
  intro h
  have habs := congrArg abs h
  rw [abs_xiHeatCassiniWoldPrimeSheetFrequency] at habs
  have hzero : Real.log (i.2 : ℝ) = 0 := by
    simpa only [abs_zero] using habs
  exact (log_prime_pos i.2).ne' hzero

/-- Activation-Fisher square-root coefficient of the Wold residual, copied to both sheets. -/
def xiHeatCassiniWoldActivationFisherAmplitude
    (i : XiHeatCassiniWoldPrimeSheet) : ℝ :=
  Real.sqrt (primeActivationOccupancyFisherDensity i.2) *
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy i.2

theorem xiHeatCassiniWoldActivationFisherAmplitude_sq
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherAmplitude i ^ 2 =
      primeActivationOccupancyFisherDensity i.2 *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy i.2 ^ 2 := by
  rw [xiHeatCassiniWoldActivationFisherAmplitude, mul_pow,
    Real.sq_sqrt]
  exact (by positivity : 0 ≤ 1 / (4 * (i.2 : ℝ))).trans
    (primeActivationOccupancyFisherDensity_bounds i.2).1

/-- The coefficient after `k` applications of the signed prime-log generator. -/
def xiHeatCassiniWoldActivationFisherGraphAmplitude
    (k : ℕ) (i : XiHeatCassiniWoldPrimeSheet) : ℝ :=
  xiHeatCassiniWoldPrimeSheetFrequency i ^ k *
    xiHeatCassiniWoldActivationFisherAmplitude i

theorem xiHeatCassiniWoldActivationFisherGraphAmplitude_sq
    (k : ℕ) (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherGraphAmplitude k i ^ 2 =
      Real.log (i.2 : ℝ) ^ (2 * k) *
        primeActivationOccupancyFisherDensity i.2 *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy i.2 ^ 2 := by
  rw [xiHeatCassiniWoldActivationFisherGraphAmplitude, ← sq_abs,
    abs_mul, abs_pow, abs_xiHeatCassiniWoldPrimeSheetFrequency,
    mul_pow, ← pow_mul, Nat.mul_comm k 2, sq_abs,
    xiHeatCassiniWoldActivationFisherAmplitude_sq]
  ring

/-- Every polynomial generator image of the doubled residual is square summable. -/
theorem summable_xiHeatCassiniWoldActivationFisherGraphAmplitude_sq
    (k : ℕ) :
    Summable (fun i : XiHeatCassiniWoldPrimeSheet =>
      xiHeatCassiniWoldActivationFisherGraphAmplitude k i ^ 2) := by
  have hbase :=
    summable_xiHeatCassiniPrimeWoldResidual_activationFisherLogPowEnergy k
  refine (summable_prod_of_nonneg (fun i => sq_nonneg
    (xiHeatCassiniWoldActivationFisherGraphAmplitude k i))).2 ⟨?_, ?_⟩
  · intro b
    exact hbase.congr fun p => by
      rw [xiHeatCassiniWoldActivationFisherGraphAmplitude_sq]
  · exact Summable.of_finite

/-- The doubled Route-T residual as a genuine Deninger boundary `ell^2` coefficient. -/
def xiHeatCassiniWoldActivationFisherL2 :
    DiagonalL2 XiHeatCassiniWoldPrimeSheet :=
  ⟨fun i => (xiHeatCassiniWoldActivationFisherAmplitude i : ℂ), by
    apply memℓp_gen
    simpa [xiHeatCassiniWoldActivationFisherGraphAmplitude,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      summable_xiHeatCassiniWoldActivationFisherGraphAmplitude_sq 0⟩

@[simp]
theorem xiHeatCassiniWoldActivationFisherL2_apply
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherL2 i =
      (xiHeatCassiniWoldActivationFisherAmplitude i : ℂ) :=
  rfl

/-- The untransformed Route-T residual is even under sheet reflection. -/
theorem xiHeatCassiniWoldActivationFisherL2_reflect
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherL2
        (xiHeatCassiniWoldPrimeSheetReflect i) =
      xiHeatCassiniWoldActivationFisherL2 i := by
  rcases i with ⟨b, p⟩
  cases b <;> rfl

/-- **All-orders maximal-domain landing.**  The doubled residual belongs to every polynomial
domain of the signed prime-log phase generator. -/
theorem xiHeatCassiniWoldActivationFisherL2_mem_phaseGeneratorPowerDomain
    (k : ℕ) :
    xiHeatCassiniWoldActivationFisherL2 ∈
      (deningerPhaseGenerator
        (fun i : XiHeatCassiniWoldPrimeSheet =>
          xiHeatCassiniWoldPrimeSheetFrequency i ^ k)).domain := by
  change Memℓp (fun i : XiHeatCassiniWoldPrimeSheet =>
    ((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
      xiHeatCassiniWoldActivationFisherL2 i) 2
  apply memℓp_gen
  have hsum :=
    summable_xiHeatCassiniWoldActivationFisherGraphAmplitude_sq k
  rw [show (2 : ENNReal).toReal = 2 by norm_num]
  refine hsum.congr fun i => ?_
  rw [xiHeatCassiniWoldActivationFisherGraphAmplitude,
    xiHeatCassiniWoldActivationFisherL2_apply,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_two]
  exact (sq_abs
    (xiHeatCassiniWoldPrimeSheetFrequency i ^ k *
      xiHeatCassiniWoldActivationFisherAmplitude i)).symm

/-- Canonical Deninger Hodge image of the doubled residual. -/
def xiHeatCassiniWoldActivationFisherHodgeL2 :
    DiagonalL2 XiHeatCassiniWoldPrimeSheet :=
  deningerBoundaryHodgeOperator xiHeatCassiniWoldPrimeSheetFrequency
    xiHeatCassiniWoldActivationFisherL2

/-- Hodge multiplication changes even Route-T residual into odd sheet grade. -/
theorem xiHeatCassiniWoldActivationFisherHodgeL2_reflect
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherHodgeL2
        (xiHeatCassiniWoldPrimeSheetReflect i) =
      -xiHeatCassiniWoldActivationFisherHodgeL2 i := by
  rw [xiHeatCassiniWoldActivationFisherHodgeL2,
    deningerBoundaryHodgeOperator_apply,
    deningerBoundaryHodgeOperator_apply,
    xiHeatCassiniWoldActivationFisherL2_reflect]
  have hsign :
      deningerSignFamily xiHeatCassiniWoldPrimeSheetFrequency
          (xiHeatCassiniWoldPrimeSheetReflect i) =
        -deningerSignFamily xiHeatCassiniWoldPrimeSheetFrequency i := by
    unfold deningerSignFamily
    rw [xiHeatCassiniWoldPrimeSheetFrequency_reflect,
      deningerFreqSign_neg
        (xiHeatCassiniWoldPrimeSheetFrequency_ne_zero i)]
    push_cast
    ring
  rw [hsign]
  ring

/-- The positive sheet carries `+i` times the original residual coefficient. -/
theorem xiHeatCassiniWoldActivationFisherHodgeL2_true
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) =
      Complex.I * xiHeatCassiniWoldActivationFisherL2 (true, p) := by
  rw [xiHeatCassiniWoldActivationFisherHodgeL2,
    deningerBoundaryHodgeOperator_apply, deningerSignFamily,
    xiHeatCassiniWoldPrimeSheetFrequency, deningerFreqSign,
    if_pos (log_prime_pos p)]
  push_cast
  ring

/-- The reflected sheet carries `-i` times the same residual coefficient. -/
theorem xiHeatCassiniWoldActivationFisherHodgeL2_false
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherHodgeL2 (false, p) =
      -Complex.I * xiHeatCassiniWoldActivationFisherL2 (false, p) := by
  have hodd :=
    xiHeatCassiniWoldActivationFisherHodgeL2_reflect (true, p)
  have heven :=
    xiHeatCassiniWoldActivationFisherL2_reflect (true, p)
  have heven' :
      xiHeatCassiniWoldActivationFisherL2 (false, p) =
        xiHeatCassiniWoldActivationFisherL2 (true, p) := by
    simpa [xiHeatCassiniWoldPrimeSheetReflect] using heven
  calc
    xiHeatCassiniWoldActivationFisherHodgeL2 (false, p) =
        -xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) := by
      simpa [xiHeatCassiniWoldPrimeSheetReflect] using hodd
    _ = -(Complex.I * xiHeatCassiniWoldActivationFisherL2 (true, p)) := by
      rw [xiHeatCassiniWoldActivationFisherHodgeL2_true]
    _ = -Complex.I * xiHeatCassiniWoldActivationFisherL2 (false, p) := by
      rw [heven']
      ring

/-- Even linear sheet observer applied to the Hodge-changed residual. -/
def xiHeatCassiniWoldActivationFisherEvenHodgeSheetAtom
    (p : Nat.Primes) : ℂ :=
  xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) +
    xiHeatCassiniWoldActivationFisherHodgeL2 (false, p)

/-- Every even linear sheet observer is blind to the grade change prime by prime. -/
theorem xiHeatCassiniWoldActivationFisherEvenHodgeSheetAtom_eq_zero
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherEvenHodgeSheetAtom p = 0 := by
  rw [xiHeatCassiniWoldActivationFisherEvenHodgeSheetAtom,
    xiHeatCassiniWoldActivationFisherHodgeL2_true,
    xiHeatCassiniWoldActivationFisherHodgeL2_false,
    xiHeatCassiniWoldActivationFisherL2_apply,
    xiHeatCassiniWoldActivationFisherL2_apply]
  change Complex.I *
      (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ) +
    -Complex.I *
      (xiHeatCassiniWoldActivationFisherAmplitude (false, p) : ℂ) = 0
  simp only [xiHeatCassiniWoldActivationFisherAmplitude]
  ring

/-- Odd linear sheet observer applied to the Hodge-changed residual. -/
def xiHeatCassiniWoldActivationFisherOddHodgeSheetAtom
    (p : Nat.Primes) : ℂ :=
  xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) -
    xiHeatCassiniWoldActivationFisherHodgeL2 (false, p)

/-- **Odd observer preserves unsquared residual.**  Sheet contrast extracts twice the original
activation-Fisher amplitude with its sign intact, rotated by `i`. -/
theorem xiHeatCassiniWoldActivationFisherOddHodgeSheetAtom_eq
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherOddHodgeSheetAtom p =
      2 * Complex.I *
        (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ) := by
  rw [xiHeatCassiniWoldActivationFisherOddHodgeSheetAtom,
    xiHeatCassiniWoldActivationFisherHodgeL2_true,
    xiHeatCassiniWoldActivationFisherHodgeL2_false,
    xiHeatCassiniWoldActivationFisherL2_apply,
    xiHeatCassiniWoldActivationFisherL2_apply]
  change Complex.I *
      (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ) -
    (-Complex.I *
      (xiHeatCassiniWoldActivationFisherAmplitude (false, p) : ℂ)) =
    2 * Complex.I *
      (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ)
  simp only [xiHeatCassiniWoldActivationFisherAmplitude]
  ring

/-- Same-grade Boolean contraction of the residual with its Hodge image at one prime. -/
def xiHeatCassiniWoldActivationFisherEvenHodgePairAtom
    (p : Nat.Primes) : ℂ :=
  (starRingEnd ℂ) (xiHeatCassiniWoldActivationFisherL2 (true, p)) *
      xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) +
    (starRingEnd ℂ) (xiHeatCassiniWoldActivationFisherL2 (false, p)) *
      xiHeatCassiniWoldActivationFisherHodgeL2 (false, p)

/-- **Even-observer blindness is pointwise.**  Same-grade quadratic contraction annihilates the
Hodge-changed residual separately at every prime, before any infinite summation. -/
theorem xiHeatCassiniWoldActivationFisherEvenHodgePairAtom_eq_zero
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherEvenHodgePairAtom p = 0 := by
  rw [xiHeatCassiniWoldActivationFisherEvenHodgePairAtom,
    xiHeatCassiniWoldActivationFisherHodgeL2_true,
    xiHeatCassiniWoldActivationFisherHodgeL2_false,
    xiHeatCassiniWoldActivationFisherL2_apply,
    xiHeatCassiniWoldActivationFisherL2_apply]
  have hstar (r : ℝ) :
      (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    simp
  rw [hstar, hstar]
  simp only [xiHeatCassiniWoldActivationFisherAmplitude]
  ring

/-- Cross-grade Boolean contraction, with reflected sheet subtracted rather than added. -/
def xiHeatCassiniWoldActivationFisherOddHodgePairAtom
    (p : Nat.Primes) : ℂ :=
  (starRingEnd ℂ) (xiHeatCassiniWoldActivationFisherL2 (true, p)) *
      xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) -
    (starRingEnd ℂ) (xiHeatCassiniWoldActivationFisherL2 (false, p)) *
      xiHeatCassiniWoldActivationFisherHodgeL2 (false, p)

/-- **Odd observer recovers exact Fisher density.**  Cross-grade contraction retains twice the
activation-Fisher residual energy, rotated by the canonical Hodge phase `i`. -/
theorem xiHeatCassiniWoldActivationFisherOddHodgePairAtom_eq
    (p : Nat.Primes) :
    xiHeatCassiniWoldActivationFisherOddHodgePairAtom p =
      2 * Complex.I *
        (primeActivationOccupancyFisherDensity p *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 : ℝ) := by
  rw [xiHeatCassiniWoldActivationFisherOddHodgePairAtom,
    xiHeatCassiniWoldActivationFisherHodgeL2_true,
    xiHeatCassiniWoldActivationFisherHodgeL2_false,
    xiHeatCassiniWoldActivationFisherL2_apply,
    xiHeatCassiniWoldActivationFisherL2_apply]
  have hstar (r : ℝ) :
      (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    simp
  rw [hstar, hstar]
  have hsame :
      xiHeatCassiniWoldActivationFisherAmplitude (false, p) =
        xiHeatCassiniWoldActivationFisherAmplitude (true, p) := rfl
  rw [hsame]
  calc
    (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ) *
          (Complex.I *
            (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ)) -
        (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ) *
          (-Complex.I *
            (xiHeatCassiniWoldActivationFisherAmplitude (true, p) : ℂ)) =
        2 * Complex.I *
          ((xiHeatCassiniWoldActivationFisherAmplitude (true, p) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = 2 * Complex.I *
          (primeActivationOccupancyFisherDensity p *
            xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 : ℝ) := by
      rw [xiHeatCassiniWoldActivationFisherAmplitude_sq]

/-- The surviving cross-grade Fisher flux is summable over all primes. -/
theorem summable_xiHeatCassiniWoldActivationFisherOddHodgeFlux :
    Summable (fun p : Nat.Primes =>
      2 * primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  simpa only [mul_assoc] using
    summable_xiHeatCassiniPrimeWoldResidual_activationFisherEnergy.mul_left 2

/-- Hodge grade change is unitary on the concrete Route-T residual. -/
theorem norm_xiHeatCassiniWoldActivationFisherHodgeL2 :
    ‖xiHeatCassiniWoldActivationFisherHodgeL2‖ =
      ‖xiHeatCassiniWoldActivationFisherL2‖ :=
  deningerBoundaryHodgeOperator_isometry
    xiHeatCassiniWoldPrimeSheetFrequency
    xiHeatCassiniWoldActivationFisherL2

/-- Applying the grade change twice gives minus the original residual. -/
theorem xiHeatCassiniWoldActivationFisherHodgeL2_sq :
    deningerBoundaryHodgeOperator xiHeatCassiniWoldPrimeSheetFrequency
        xiHeatCassiniWoldActivationFisherHodgeL2 =
      -xiHeatCassiniWoldActivationFisherL2 :=
  deningerBoundaryHodgeOperator_sq
    xiHeatCassiniWoldPrimeSheetFrequency
    xiHeatCassiniWoldActivationFisherL2

/-- Hodge image retains every finite prime-log graph order. -/
theorem xiHeatCassiniWoldActivationFisherHodgeL2_mem_phaseGeneratorPowerDomain
    (k : ℕ) :
    xiHeatCassiniWoldActivationFisherHodgeL2 ∈
      (deningerPhaseGenerator
        (fun i : XiHeatCassiniWoldPrimeSheet =>
          xiHeatCassiniWoldPrimeSheetFrequency i ^ k)).domain := by
  change Memℓp (fun i : XiHeatCassiniWoldPrimeSheet =>
    ((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
      xiHeatCassiniWoldActivationFisherHodgeL2 i) 2
  apply memℓp_gen
  have hdomain :=
    xiHeatCassiniWoldActivationFisherL2_mem_phaseGeneratorPowerDomain k
  have hbase := (hdomain : Memℓp (fun i : XiHeatCassiniWoldPrimeSheet =>
    ((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
      xiHeatCassiniWoldActivationFisherL2 i) 2).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  refine hbase.congr fun i => ?_
  have hnorm :
      ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
          xiHeatCassiniWoldActivationFisherHodgeL2 i‖ =
        ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
          xiHeatCassiniWoldActivationFisherL2 i‖ := by
    calc
      ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
          xiHeatCassiniWoldActivationFisherHodgeL2 i‖ =
        ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ)‖ *
          ‖xiHeatCassiniWoldActivationFisherHodgeL2 i‖ := norm_mul _ _
      _ = ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ)‖ *
          (‖deningerSignFamily xiHeatCassiniWoldPrimeSheetFrequency i‖ *
            ‖xiHeatCassiniWoldActivationFisherL2 i‖) := by
        rw [xiHeatCassiniWoldActivationFisherHodgeL2,
          deningerBoundaryHodgeOperator_apply, norm_mul]
      _ = ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ)‖ *
          ‖xiHeatCassiniWoldActivationFisherL2 i‖ := by
        rw [deningerSignFamily_norm, one_mul]
      _ = ‖((xiHeatCassiniWoldPrimeSheetFrequency i ^ k : ℝ) : ℂ) *
          xiHeatCassiniWoldActivationFisherL2 i‖ := (norm_mul _ _).symm
  exact congrArg (fun r : ℝ => r ^ (2 : ENNReal).toReal) hnorm.symm

/-- Physical boundary datum whose Dirichlet energy is the activation-Fisher residual energy. -/
def xiHeatCassiniWoldActivationFisherBoundaryDatum
    (i : XiHeatCassiniWoldPrimeSheet) : ℂ :=
  deningerBoundaryDatum xiHeatCassiniWoldPrimeSheetFrequency
    xiHeatCassiniWoldActivationFisherL2 i

/-- The concrete physical boundary energy is summable. -/
theorem summable_xiHeatCassiniWoldActivationFisherBoundaryEnergy :
    Summable (fun i : XiHeatCassiniWoldPrimeSheet =>
      |xiHeatCassiniWoldPrimeSheetFrequency i| *
        ‖xiHeatCassiniWoldActivationFisherBoundaryDatum i‖ ^ 2) := by
  have hL2 := (lp.memℓp xiHeatCassiniWoldActivationFisherL2).summable
    (by norm_num : 0 < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hL2
  refine hL2.congr fun i => ?_
  simpa only [xiHeatCassiniWoldActivationFisherBoundaryDatum] using
    (deningerBoundary_term xiHeatCassiniWoldPrimeSheetFrequency
      xiHeatCassiniWoldPrimeSheetFrequency_ne_zero
      xiHeatCassiniWoldActivationFisherL2 i).symm

/-- Physical boundary datum remains even before Hodge grade change. -/
theorem xiHeatCassiniWoldActivationFisherBoundaryDatum_reflect
    (i : XiHeatCassiniWoldPrimeSheet) :
    xiHeatCassiniWoldActivationFisherBoundaryDatum
        (xiHeatCassiniWoldPrimeSheetReflect i) =
      xiHeatCassiniWoldActivationFisherBoundaryDatum i := by
  simp only [xiHeatCassiniWoldActivationFisherBoundaryDatum,
    deningerBoundaryDatum,
    xiHeatCassiniWoldActivationFisherL2_reflect,
    xiHeatCassiniWoldPrimeSheetFrequency_reflect, abs_neg]

end

end RHTower
