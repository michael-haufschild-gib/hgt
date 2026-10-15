import GaloisForLFunctions.HTGeometry.MarkedMeromorphicKTwo
import GaloisForLFunctions.RHTower.PrimeRotationXiRelativeKTwo

/-!
# Xi's relative source with the prime clock retained

The native irrational prime clock has infinite multiplicative order. Its marked tame subgroup
therefore has a concrete integer degree. Literal Xi clock corrections and isolated Xi dipoles
land in this subgroup, and their degree is the full analytic multiplicity. The integer degree
cannot extend to all complex meromorphic K2: the ambient constant symbols are divisible.

This fixes the domain of a prospective topological realization. It does not construct a rotation
K0 class or identify this integer degree with a completed-algebra Chern pairing.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- The fixed native clock, as a complex unit. -/
def primeClockComplexUnit (p : Nat.Primes) (q : ℕ) : ℂˣ :=
  Units.mk0
    (Complex.exp (-((Real.log p : ℝ) : ℂ) * primeAlgebraicClockStep q))
    (Complex.exp_ne_zero _)

theorem primeClockComplexUnit_pow_eq_phase (p : Nat.Primes) (q d : ℕ) :
    ((primeClockComplexUnit p q ^ d : ℂˣ) : ℂ) =
      primeAlgebraicWeylDeterminantPhase p d q :=
  primeAlgebraicWeylMultiplier_pow_eq_phase p d q

/-- The marked clock has no hidden torsion; its integer powers are distinct. -/
theorem primeClockComplexUnit_zpow_injective (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    Function.Injective (fun n : ℤ => primeClockComplexUnit p q ^ n) := by
  apply injective_zpow_iff_not_isOfFinOrder.mpr
  intro hfin
  obtain ⟨d, hd, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hphase : primeAlgebraicWeylDeterminantPhase p d q = 1 := by
    rw [← primeClockComplexUnit_pow_eq_phase]
    exact congrArg (fun u : ℂˣ => (u : ℂ)) he
  have htrans := primeAlgebraicWeylDeterminantPhase_transcendental p (Nat.ne_of_gt hd) hq
  rw [hphase] at htrans
  exact htrans (by simpa using isAlgebraic_natComplex 1)

/-- The actual fixed-clock source group, before any rotation-projective realization. -/
abbrev PrimeClockMarkedK2 (p : Nat.Primes) (q : ℕ) := markedTameK2 (primeClockComplexUnit p q)

/-- Integer boundary degree attached to the actual native clock. -/
def primeClockMarkedDegree (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    PrimeClockMarkedK2 p q →+ ℤ :=
  markedTameDegree (primeClockComplexUnit p q) (primeClockComplexUnit_zpow_injective p hq)

/-- The literal Xi clock correction belongs to the fixed-clock source without any descent premise. -/
def xiPrimeMarkedClockCorrection (p : Nat.Primes) (q : ℕ) (rho : ℂ) :
    PrimeClockMarkedK2 p q :=
  markedTameSymbol (primeClockComplexUnit p q)
    (xiMeroGermUnit (rho + primeAlgebraicClockStep q))

@[simp] theorem xiPrimeMarkedClockCorrection_val (p : Nat.Primes) (q : ℕ) (rho : ℂ) :
    (xiPrimeMarkedClockCorrection p q rho).val =
      xiPrimeK2ClockCorrection p (primeAlgebraicClockStep q) rho := rfl

/-- The marked source recovers the full multiplicity at the transported point. -/
theorem xiPrimeMarkedClockCorrection_degree (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) (rho : ℂ) :
    primeClockMarkedDegree p hq (xiPrimeMarkedClockCorrection p q rho) =
      ((analyticOrderAt xi (rho + primeAlgebraicClockStep q)).toNat : ℤ) := by
  rw [primeClockMarkedDegree, xiPrimeMarkedClockCorrection,
    markedTameDegree_symbol, xiMeroGermUnit_order]

/-- Ambient integer readouts lose this same source correction completely. -/
theorem xiPrimeK2ClockCorrection_integerHom_zero
    (F : MilnorKDeg MeroGerm 2 →+ ℤ) (p : Nat.Primes) (q : ℕ) (rho : ℂ) :
    F (xiPrimeK2ClockCorrection p (primeAlgebraicClockStep q) rho) = 0 :=
  constantMeroSymbol_integerHom_zero F (primeClockComplexUnit p q)
    (xiMeroGermUnit (rho + primeAlgebraicClockStep q))

/-- The actual Xi dipole has a retained-clock representative of exactly its analytic multiplicity.
    The representative is the literal source K2 class, not a declared integer coordinate. -/
theorem xiPrimeDipole_marked_source (p : Nat.Primes) (rho : ℂ) :
    ∃ (q : ℕ) (hq : 0 < q) (x : PrimeClockMarkedK2 p q),
      x.val = xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho ∧
      primeClockMarkedDegree p (Nat.ne_of_gt hq) x = ((analyticOrderAt xi rho).toNat : ℤ) := by
  obtain ⟨q, hq, he⟩ := xiPrimeDipoleK2Class_clock_boundary p rho
  have hb : meroGermTameBoundary
      (xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho) =
      Additive.ofMul (primeClockComplexUnit p q ^ ((analyticOrderAt xi rho).toNat : ℤ)) := by
    apply Additive.toMul.injective
    apply Units.ext
    change meroGermTameBoundaryValue
      (xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho) =
        ((primeClockComplexUnit p q ^ ((analyticOrderAt xi rho).toNat : ℤ) : ℂˣ) : ℂ)
    rw [zpow_natCast, primeClockComplexUnit_pow_eq_phase]
    exact he
  let x : PrimeClockMarkedK2 p q :=
    ⟨xiPrimeDipoleK2Class p (primeAlgebraicClockStep q) rho,
      ((analyticOrderAt xi rho).toNat : ℤ), hb⟩
  refine ⟨q, hq, x, rfl, ?_⟩
  exact markedTameExponent_eq (primeClockComplexUnit p q)
    (primeClockComplexUnit_zpow_injective p (Nat.ne_of_gt hq)) x _ hb

/-- The native marked source has an exact integer quotient by its degree kernel. -/
def primeClockMarkedQuotientEquiv (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    (PrimeClockMarkedK2 p q ⧸ (primeClockMarkedDegree p hq).ker) ≃+ ℤ :=
  markedTameDegreeQuotientEquiv (primeClockComplexUnit p q)
    (primeClockComplexUnit_zpow_injective p hq)

/-- A degree-preserving map must retain the clock-marked domain. It cannot be an integer map
    on the full ambient complex meromorphic K2 group. -/
theorem primeClockMarkedDegree_not_extend (p : Nat.Primes) {q : ℕ} (hq : q ≠ 0) :
    ¬ ∃ F : MilnorKDeg MeroGerm 2 →+ ℤ,
      ∀ x : PrimeClockMarkedK2 p q, F x.val = primeClockMarkedDegree p hq x :=
  markedTameDegree_not_extend (primeClockComplexUnit p q)
    (primeClockComplexUnit_zpow_injective p hq)

/-- Refining the native denominator gives the coherent root of the original clock multiplier. -/
theorem primeClockComplexUnit_refinement (p : Nat.Primes) (q : ℕ) {k : ℕ} (hk : k ≠ 0) :
    primeClockComplexUnit p (k * q) ^ k = primeClockComplexUnit p q := by
  apply Units.ext
  change Complex.exp (-((Real.log p : ℝ) : ℂ) * primeAlgebraicClockStep (k * q)) ^ k =
    Complex.exp (-((Real.log p : ℝ) : ℂ) * primeAlgebraicClockStep q)
  rw [← Complex.exp_nat_mul]
  congr 1
  unfold primeAlgebraicClockStep
  push_cast
  by_cases hq : q = 0
  · simp [hq]
  · field_simp

/-- Source refinement keeps the literal K2 class while retaining the finer native clock. -/
def primeClockMarkedRefinement (p : Nat.Primes) (q : ℕ) {k : ℕ} (hk : k ≠ 0) :
    PrimeClockMarkedK2 p q →+ PrimeClockMarkedK2 p (k * q) :=
  markedTameClockChange (primeClockComplexUnit p q) (primeClockComplexUnit p (k * q)) (k : ℤ)
    (by rw [zpow_natCast, primeClockComplexUnit_refinement p q hk])

/-- The source integer degree obeys the exact native covering law under clock refinement. -/
theorem primeClockMarkedDegree_refinement (p : Nat.Primes) {q k : ℕ}
    (hq : q ≠ 0) (hk : k ≠ 0) (x : PrimeClockMarkedK2 p q) :
    primeClockMarkedDegree p (mul_ne_zero hk hq) (primeClockMarkedRefinement p q hk x) =
      (k : ℤ) * primeClockMarkedDegree p hq x :=
  markedTameDegree_clockChange _ _ _ _
    (primeClockComplexUnit_zpow_injective p hq)
    (primeClockComplexUnit_zpow_injective p (mul_ne_zero hk hq)) x

end
end RHTower
