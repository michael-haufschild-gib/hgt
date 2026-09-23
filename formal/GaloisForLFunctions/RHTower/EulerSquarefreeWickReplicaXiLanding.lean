import GaloisForLFunctions.RHTower.EulerSquarefreeWickArtinInteractionNoGo
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.HTGeometry.PrimeDepthHadamardFusion

/-!
# Two-replica Euler--Wick landing on completed Xi

The single Euler--Wick interaction carrier is the nontrivial quadratic character modulo twelve,
so an invariant scalar reader kills it.  A replica diagonal changes the representation sector.
At prime-power depth `k`, apply the valuation number operator to one Euler-log replica and contract
it coefficientwise with a second replica:

`(k * (χ(p)^k / k)) * (χ(p)^k / k) = χ(p)^(2k) / k = 1 / k`.

Both residue legs are evaluated on units, hence their product squares to one at every prime label.
The contraction therefore recovers every coefficient of the canonical Euler logarithm, not only
the degree-one prime column.  Its analytic exponential is exactly zeta on `Re s > 1`, and adding
the corpus's archimedean factor lands exactly on completed `xi` before any divisor is selected.
-/

namespace GaloisForLFunctions.RHTower

open Complex
open ArithmeticFunction
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

noncomputable section

/-- The literal EWQ prime coefficient is an involution at every prime label. -/
theorem quadraticResidueProductPrimeCoefficient_sq (p : Nat.Primes) :
    quadraticResidueProductPrimeCoefficient p ^ (2 : ℕ) = 1 := by
  rw [quadraticResidueProductPrimeCoefficient,
    quadraticResidueFstObservable, quadraticResidueSndObservable, mul_pow,
    quadraticCharacterThreeUnit_sq, quadraticCharacterFourUnit_sq, one_mul]

/-- Prime-power depth character of the Euler--Wick joint quadratic gauge. -/
def eulerWickQuadraticDepthCharacter (x : PrimePowerClockIndex) : ℂ :=
  quadraticResidueProductPrimeCoefficient x.1 ^ (x.2 + 1)

/-- Euler-log copy of the joint depth character. -/
def eulerWickQuadraticEulerLogReplica (x : PrimePowerClockIndex) : ℂ :=
  eulerWickQuadraticDepthCharacter x / ((x.2 + 1 : ℕ) : ℂ)

/-- Valuation number operator applied to one Euler-log replica. -/
def eulerWickQuadraticNumberReplica (x : PrimePowerClockIndex) : ℂ :=
  ((x.2 + 1 : ℕ) : ℂ) * eulerWickQuadraticEulerLogReplica x

/-- The number insertion removes exactly one Euler-log depth denominator. -/
theorem eulerWickQuadraticNumberReplica_eq_depthCharacter
    (x : PrimePowerClockIndex) :
    eulerWickQuadraticNumberReplica x = eulerWickQuadraticDepthCharacter x := by
  have hn : (((x.2 + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero x.2
  unfold eulerWickQuadraticNumberReplica eulerWickQuadraticEulerLogReplica
  exact mul_div_cancel₀ _ hn

/-- **Replica coefficient landing.**  The number-inserted two-copy diagonal is the canonical
Euler-log coefficient `1/(k+1)` at every prime and every valuation depth. -/
theorem eulerWickQuadraticReplicaDiagonalCoefficient_eq_eulerLog
    (x : PrimePowerClockIndex) :
    eulerWickQuadraticNumberReplica x * eulerWickQuadraticEulerLogReplica x =
      eulerLogValuationProfile x.2 := by
  rw [eulerWickQuadraticNumberReplica_eq_depthCharacter]
  unfold eulerWickQuadraticEulerLogReplica eulerWickQuadraticDepthCharacter
  rw [div_eq_mul_inv]
  let c := quadraticResidueProductPrimeCoefficient x.1
  let n := x.2 + 1
  have hc : c ^ (2 : ℕ) = 1 := quadraticResidueProductPrimeCoefficient_sq x.1
  change c ^ n * (c ^ n * (((n : ℕ) : ℂ))⁻¹) = eulerLogValuationProfile x.2
  calc
    c ^ n * (c ^ n * (((n : ℕ) : ℂ))⁻¹) =
        c ^ (n + n) * (((n : ℕ) : ℂ))⁻¹ := by
      rw [pow_add]
      ring
    _ = c ^ (2 * n) * (((n : ℕ) : ℂ))⁻¹ := by rw [two_mul]
    _ = (c ^ (2 : ℕ)) ^ n * (((n : ℕ) : ℂ))⁻¹ := by rw [pow_mul]
    _ = (((n : ℕ) : ℂ))⁻¹ := by rw [hc, one_pow, one_mul]
    _ = eulerLogValuationProfile x.2 := by
      simp [eulerLogValuationProfile, n]

/-- Two-copy EWQ diagonal after the valuation-number insertion. -/
def eulerWickQuadraticReplicaDiagonalSource : ArithmeticFunction ℂ :=
  primeDepthHadamardFusion eulerWickQuadraticNumberReplica
    eulerWickQuadraticEulerLogReplica

/-- The complete prime-power source is exactly the replicated Euler-log profile. -/
theorem eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogProfile :
    eulerWickQuadraticReplicaDiagonalSource =
      scalarReplicatedPrimeProfile eulerLogValuationProfile := by
  change arithmeticFunctionOfPrimePowerProfile
      (fun x => eulerWickQuadraticNumberReplica x *
        eulerWickQuadraticEulerLogReplica x) =
    arithmeticFunctionOfPrimePowerProfile
      (fun x => eulerLogValuationProfile x.2)
  congr 1
  funext x
  exact eulerWickQuadraticReplicaDiagonalCoefficient_eq_eulerLog x

/-- The diagonal source is coefficient-for-coefficient `Λ(n)/log n`. -/
theorem eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogDirichletCoeff :
    (eulerWickQuadraticReplicaDiagonalSource : ℕ → ℂ) =
      _root_.RHTower.eulerLogDirichletCoeff := by
  funext n
  calc
    eulerWickQuadraticReplicaDiagonalSource n =
        scalarReplicatedPrimeProfile eulerLogValuationProfile n :=
      congrArg (fun f : ArithmeticFunction ℂ => f n)
        eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogProfile
    _ = _root_.RHTower.eulerLogDirichletCoeff n :=
      congrFun scalarReplicatedPrimeProfile_eulerLogValuationProfile n

/-- Finite-abscissa analytic source supplied by the exact replica diagonal. -/
def eulerWickQuadraticReplicaDiagonalFiniteAbscissa :
    finiteAbscissaArithmeticSubalgebra :=
  boundedScalarReplicatedFiniteAbscissa eulerLogValuationProfile 1
    eulerLogValuationProfile_norm_le_one

/-- The bundled analytic source retains the literal replica-diagonal coefficient stream. -/
theorem eulerWickQuadraticReplicaDiagonalFiniteAbscissa_val_eq_source :
    (eulerWickQuadraticReplicaDiagonalFiniteAbscissa.1 : ℕ → ℂ) =
      eulerWickQuadraticReplicaDiagonalSource := by
  funext n
  exact (congrArg (fun f : ArithmeticFunction ℂ => f n)
    eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogProfile).symm

theorem eulerWickQuadraticReplicaDiagonalFiniteAbscissa_eq_eulerLog :
    eulerWickQuadraticReplicaDiagonalFiniteAbscissa =
      boundedScalarReplicatedFiniteAbscissa eulerLogValuationProfile 1
        eulerLogValuationProfile_norm_le_one := by
  rfl

/-- Actual meromorphic EWQ two-replica carrier. -/
def eulerWickQuadraticReplicaDiagonalAnalyticCarrier : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    eulerWickQuadraticReplicaDiagonalFiniteAbscissa

/-- The EWQ replica carrier is exactly the corpus's analytic Euler-log carrier. -/
theorem eulerWickQuadraticReplicaDiagonalAnalyticCarrier_eq_eulerLog :
    eulerWickQuadraticReplicaDiagonalAnalyticCarrier =
      analyticEulerLogReplicatedCarrier := by
  rw [eulerWickQuadraticReplicaDiagonalAnalyticCarrier,
    analyticEulerLogReplicatedCarrier, analyticScalarReplicatedCarrier,
    eulerWickQuadraticReplicaDiagonalFiniteAbscissa_eq_eulerLog]

/-- Exponentiating the coefficient-faithful diagonal gives zeta on its Euler half-plane. -/
theorem exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries eulerWickQuadraticReplicaDiagonalSource s) =
      riemannZeta s := by
  rw [eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogDirichletCoeff]
  exact _root_.RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs

/-- **Completed Xi landing before divisor selection.**  Archimedean completion of the EWQ
replica diagonal is the actual corpus `xi` on the whole Euler half-plane. -/
theorem archFactor_mul_exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_xi
    {s : ℂ} (hs : 1 < s.re) :
    _root_.RHTower.archFactor s *
        Complex.exp (LSeries eulerWickQuadraticReplicaDiagonalSource s) =
      _root_.RHTower.xi s := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs]
  exact (_root_.RHTower.xi_eq_archFactor_mul_zeta h0 h1 hG).symm

end


end GaloisForLFunctions.RHTower
