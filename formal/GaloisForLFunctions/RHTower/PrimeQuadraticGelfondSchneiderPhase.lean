import GaloisForLFunctions.RHTower.QuadraticCircleFreeOrbitCharge
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.RHTower.PiTranscendenceSetup

/-!
# Algebraic prime phases exclude free Xi reflection orbits

The irrational-circle route asks a completed source holonomy to equal one.  A substantially weaker
arithmetic condition suffices.  For a prime `p` and a nonzero natural number `m`, the principal
power

`p ^ (m * I)`

is transcendental by Gelfond--Schneider.  Consequently, merely proving this phase algebraic forces
`m = 0`.

The reflection-safe phase uses the nonnegative quadratic free-orbit index
`2 * ∑ m_i^2`.  Algebraicity of its single prime phase therefore excludes every free reflection
orbit without requiring the phase to be trivial.  This file proves the transcendence collision and
the conditional RH endpoint.  It does not construct the missing algebraic prime--Gamma monodromy
whose phase has this local index.
-/

namespace RHTower

noncomputable section

/-- Principal prime power carrying a nonnegative integral winding in the imaginary exponent. -/
def primeImaginaryOrderPhase (p : Nat.Primes) (m : ℕ) : ℂ :=
  (p : ℂ) ^ ((m : ℂ) * Complex.I)

theorem isAlgebraic_natComplex (n : ℕ) : IsAlgebraic ℚ (n : ℂ) := by
  have h : IsAlgebraic ℚ (algebraMap ℚ ℂ (n : ℚ)) :=
    (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (n : ℚ))).isAlgebraic
  simpa using h

/-- Any nontrivial algebraic base raised to a nonzero integral imaginary exponent is
transcendental.  The source base may therefore be an algebraic norm or monodromy eigenvalue; it
need not literally be prime. -/
theorem algebraicBase_imaginaryNatPower_transcendental
    (alpha : ℂ) (halpha : IsAlgebraic ℚ alpha)
    (halpha0 : alpha ≠ 0) (halpha1 : alpha ≠ 1)
    {m : ℕ} (hm : m ≠ 0) :
    Transcendental ℚ (alpha ^ ((m : ℂ) * Complex.I)) := by
  apply GaloisForLFunctions.RHTower.GelfondSchneiderProof.Setup.transcendental_cpow_of_isAlgebraic_of_irrational
      alpha ((m : ℂ) * Complex.I)
  · exact halpha
  · exact (isAlgebraic_natComplex m).mul
      GaloisForLFunctions.RHTower.isAlgebraic_I
  · exact ⟨halpha0, halpha1⟩
  · intro i j hij
    have him := congrArg Complex.im hij
    simp at him
    exact hm (by exact_mod_cast him)

/-- **Gelfond--Schneider prime-phase obstruction.**  A nonzero integral imaginary exponent at an
algebraic prime base produces a transcendental principal power. -/
theorem primeImaginaryOrderPhase_transcendental
    (p : Nat.Primes) {m : ℕ} (hm : m ≠ 0) :
    Transcendental ℚ (primeImaginaryOrderPhase p m) := by
  apply algebraicBase_imaginaryNatPower_transcendental
      (p : ℂ) (isAlgebraic_natComplex p)
  · exact_mod_cast p.2.ne_zero
  · exact_mod_cast p.2.ne_one
  · exact hm

/-- Algebraicity, rather than triviality, of one prime phase detects zero winding exactly. -/
theorem primeImaginaryOrderPhase_isAlgebraic_iff
    (p : Nat.Primes) (m : ℕ) :
    IsAlgebraic ℚ (primeImaginaryOrderPhase p m) ↔ m = 0 := by
  constructor
  · intro hphase
    by_contra hm
    exact primeImaginaryOrderPhase_transcendental p hm hphase
  · rintro rfl
    simpa [primeImaginaryOrderPhase] using isAlgebraic_natComplex 1

/-- The reflection-safe prime phase of a finite list of free-orbit multiplicities. -/
def freeOrbitQuadraticAlgebraicPhase (p : Nat.Primes) (ms : List ℕ) : ℂ :=
  primeImaginaryOrderPhase p (freeOrbitQuadraticIndex ms)

/-- **Finite free-orbit exclusion.**  The quadratic prime phase is algebraic exactly when every
free-orbit multiplicity vanishes. -/
theorem freeOrbitQuadraticAlgebraicPhase_isAlgebraic_iff
    (p : Nat.Primes) (ms : List ℕ) :
    IsAlgebraic ℚ (freeOrbitQuadraticAlgebraicPhase p ms) ↔
      ∀ m ∈ ms, m = 0 := by
  rw [freeOrbitQuadraticAlgebraicPhase,
    primeImaginaryOrderPhase_isAlgebraic_iff,
    freeOrbitQuadraticIndex_eq_zero_iff]

/-- Quadratic algebraic phase of the reflected local Xi pair through `rho`. -/
def xiReflectionPairQuadraticAlgebraicPhase (p : Nat.Primes) (rho : ℂ) : ℂ :=
  primeImaginaryOrderPhase p
    (2 * (analyticOrderAt xi rho).toNat ^ 2)

/-- The local reflected phase is algebraic exactly when the local Xi order is zero. -/
theorem xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff
    (p : Nat.Primes) (rho : ℂ) :
    IsAlgebraic ℚ (xiReflectionPairQuadraticAlgebraicPhase p rho) ↔
      (analyticOrderAt xi rho).toNat = 0 := by
  rw [xiReflectionPairQuadraticAlgebraicPhase,
    primeImaginaryOrderPhase_isAlgebraic_iff]
  simp

/-- **Quadratic algebraic-monodromy criterion for RH.**  If one fixed prime phase attached to
every hypothetical right-half reflected Xi pair is algebraic, then no such pair exists. -/
theorem riemannHypothesis_iff_xiReflectionPairQuadraticPhases_algebraic
    (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ rho ∈ rightHalf, xi rho = 0 →
        IsAlgebraic ℚ (xiReflectionPairQuadraticAlgebraicPhase p rho) := by
  constructor
  · intro hRH rho hrho hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hrho hzero).elim
  · intro halg
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have horder :=
      (xiReflectionPairQuadraticAlgebraicPhase_isAlgebraic_iff p rho).mp
        (halg rho hrho hzero)
    exact (xi_order_toNat_ne_zero hzero horder).elim

end

end RHTower
