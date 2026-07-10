/-
# A finite-support semilocal Sonin relative trace

The principal/residual linear cross term is Hilbert--Schmidt but need not itself be trace class.
The exact Sonin projection correction is also Hilbert--Schmidt.  Pairing the two therefore gives a
canonical trace-class product and a basis-independent scalar.  A finitely supported prime-power
test function produces a finite additive trace functional, with no prime ordering or exhaustion.

This constructs the Sonin-side scalarization.  Identifying it with the already proved
prime--archimedean source trace remains the source-specific open identity.
-/
import GaloisForLFunctions.RHTower.SoninRelativeGramDefect
import GaloisForLFunctions.HilbertSchmidtTrace

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- The part of the prime-power relative Gram defect which is linear in the unsquared logarithmic
Euler coefficient. -/
def centralSoninPrimePowerRelativeGramLinearCross
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  let p := soninPrimePowerScale pk
  let hp := one_lt_soninPrimePowerScale pk
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninPrimePowerResidual a pk
  let c := soninLogPrimePowerCoefficient pk
  c • (ContinuousLinearMap.adjoint P * R) +
    star c • (ContinuousLinearMap.adjoint R * P)

/-- The prime-power linear cross is unconditionally Hilbert--Schmidt. -/
theorem centralSoninPrimePowerRelativeGramLinearCross_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsHilbertSchmidt (centralSoninPrimePowerRelativeGramLinearCross a pk) := by
  have hR := centralSoninPrimePowerResidual_isHilbertSchmidt a ha pk
  exact ((hR.comp_left (ContinuousLinearMap.adjoint
      (centralSoninPrincipalDilationCorner a (soninPrimePowerScale pk)
        (one_lt_soninPrimePowerScale pk)))).smul
          (soninLogPrimePowerCoefficient pk)).add
    ((hR.adjoint.comp_right
      (centralSoninPrincipalDilationCorner a (soninPrimePowerScale pk)
        (one_lt_soninPrimePowerScale pk))).smul
          (star (soninLogPrimePowerCoefficient pk)))

/-- The scalar density obtained by pairing the prime-power linear cross with the canonical exact
Sonin projection correction.  The displayed `opTrace` is legitimate because both factors are
Hilbert--Schmidt. -/
def soninPrimePowerRelativeTraceDensity (a : ℝ) (pk : Nat.Primes × ℕ) : ℂ :=
  opTrace (ContinuousLinearMap.adjoint (centralSoninProjectionCorrection a) ∘L
    centralSoninPrimePowerRelativeGramLinearCross a pk)

/-- The density is exactly a Hilbert--Schmidt pairing, hence is basis-independent. -/
theorem soninPrimePowerRelativeTraceDensity_eq_hsInner
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninPrimePowerRelativeTraceDensity a pk =
      hsInner (centralSoninProjectionCorrection a)
        (centralSoninPrimePowerRelativeGramLinearCross a pk) := by
  rw [soninPrimePowerRelativeTraceDensity, opTrace_comp_eq_hsInner, adjoint_adjoint]

/-- Explicit trace-class certificate for the operator whose trace defines the density. -/
theorem soninPrimePowerRelativeTraceDensity_isTraceClass
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsTraceClass
      (ContinuousLinearMap.adjoint (centralSoninProjectionCorrection a) ∘L
        centralSoninPrimePowerRelativeGramLinearCross a pk) := by
  exact (centralSoninProjectionCorrection_isHilbertSchmidt a ha).adjoint.comp_isTraceClass
    (centralSoninPrimePowerRelativeGramLinearCross_isHilbertSchmidt a ha pk)

/-! ### All positive modes for compact-support semilocal tests -/

/-- The full prime-power scale `p^(k+1)`.  Unlike the all-prime Hilbert--Schmidt tail, a
compact-support semilocal test may and must retain the principal `k=0`, exponent-one mode. -/
def soninSemilocalPrimePowerScale (pk : Nat.Primes × ℕ) : ℝ :=
  (pk.1 : ℝ) ^ (pk.2 + 1)

theorem one_lt_soninSemilocalPrimePowerScale (pk : Nat.Primes × ℕ) :
    1 < soninSemilocalPrimePowerScale pk := by
  apply one_lt_pow₀ (by exact_mod_cast pk.1.prop.one_lt)
  omega

/-- The unsquared logarithmic coefficient `p^(-(k+1)/2)/(k+1)` for every positive mode. -/
def soninSemilocalLogPrimePowerCoefficient (pk : Nat.Primes × ℕ) : ℂ :=
  (((Real.sqrt (pk.1 : ℝ))⁻¹ ^ (pk.2 + 1) /
    (pk.2 + 1 : ℝ) : ℝ) : ℂ)

/-- The actual principal-subtracted Sonin residual at every positive prime-power scale. -/
def centralSoninSemilocalPrimePowerResidual
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  centralSoninDilationCornerResidual a (soninSemilocalPrimePowerScale pk)
    (one_lt_soninSemilocalPrimePowerScale pk)

theorem centralSoninSemilocalPrimePowerResidual_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsHilbertSchmidt (centralSoninSemilocalPrimePowerResidual a pk) := by
  exact centralSoninDilationCornerResidual_isHilbertSchmidt a
    (soninSemilocalPrimePowerScale pk) ha (one_lt_soninSemilocalPrimePowerScale pk)

/-- The full semilocal linear cross, including the principal exponent-one prime shell. -/
def centralSoninSemilocalRelativeGramLinearCross
    (a : ℝ) (pk : Nat.Primes × ℕ) : SoninL2 →L[Complex] SoninL2 :=
  let p := soninSemilocalPrimePowerScale pk
  let hp := one_lt_soninSemilocalPrimePowerScale pk
  let P := centralSoninPrincipalDilationCorner a p hp
  let R := centralSoninSemilocalPrimePowerResidual a pk
  let c := soninSemilocalLogPrimePowerCoefficient pk
  c • (ContinuousLinearMap.adjoint P * R) +
    star c • (ContinuousLinearMap.adjoint R * P)

theorem centralSoninSemilocalRelativeGramLinearCross_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsHilbertSchmidt (centralSoninSemilocalRelativeGramLinearCross a pk) := by
  have hR := centralSoninSemilocalPrimePowerResidual_isHilbertSchmidt a ha pk
  exact ((hR.comp_left (ContinuousLinearMap.adjoint
      (centralSoninPrincipalDilationCorner a (soninSemilocalPrimePowerScale pk)
        (one_lt_soninSemilocalPrimePowerScale pk)))).smul
          (soninSemilocalLogPrimePowerCoefficient pk)).add
    ((hR.adjoint.comp_right
      (centralSoninPrincipalDilationCorner a (soninSemilocalPrimePowerScale pk)
        (one_lt_soninSemilocalPrimePowerScale pk))).smul
          (star (soninSemilocalLogPrimePowerCoefficient pk)))

/-- Canonical trace density for every positive prime-power mode. -/
def soninSemilocalRelativeTraceDensity (a : ℝ) (pk : Nat.Primes × ℕ) : ℂ :=
  opTrace (ContinuousLinearMap.adjoint (centralSoninProjectionCorrection a) ∘L
    centralSoninSemilocalRelativeGramLinearCross a pk)

theorem soninSemilocalRelativeTraceDensity_eq_hsInner
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninSemilocalRelativeTraceDensity a pk =
      hsInner (centralSoninProjectionCorrection a)
        (centralSoninSemilocalRelativeGramLinearCross a pk) := by
  rw [soninSemilocalRelativeTraceDensity, opTrace_comp_eq_hsInner, adjoint_adjoint]

theorem soninSemilocalRelativeTraceDensity_isTraceClass
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    IsTraceClass
      (ContinuousLinearMap.adjoint (centralSoninProjectionCorrection a) ∘L
        centralSoninSemilocalRelativeGramLinearCross a pk) := by
  exact (centralSoninProjectionCorrection_isHilbertSchmidt a ha).adjoint.comp_isTraceClass
    (centralSoninSemilocalRelativeGramLinearCross_isHilbertSchmidt a ha pk)

/-- Compact-support test functions on the discrete prime-power carrier. -/
abbrev SoninPrimePowerTest := (Nat.Primes × ℕ) →₀ ℂ

/-- The finite-support semilocal Sonin relative trace.  `Finsupp.sum` makes the definition
intrinsically independent of an ordering of its prime-power support. -/
def finiteSoninSemilocalRelativeTrace (a : ℝ) (f : SoninPrimePowerTest) : ℂ :=
  f.sum fun pk w => w * soninSemilocalRelativeTraceDensity a pk

@[simp] theorem finiteSoninSemilocalRelativeTrace_single (a : ℝ)
    (pk : Nat.Primes × ℕ) (w : ℂ) :
    finiteSoninSemilocalRelativeTrace a (Finsupp.single pk w) =
      w * soninSemilocalRelativeTraceDensity a pk := by
  simp [finiteSoninSemilocalRelativeTrace]

@[simp] theorem finiteSoninSemilocalRelativeTrace_zero (a : ℝ) :
    finiteSoninSemilocalRelativeTrace a 0 = 0 := by
  simp [finiteSoninSemilocalRelativeTrace]

/-- Additivity is the finite-site descent law for compact-support prime-power tests. -/
theorem finiteSoninSemilocalRelativeTrace_add (a : ℝ)
    (f g : SoninPrimePowerTest) :
    finiteSoninSemilocalRelativeTrace a (f + g) =
      finiteSoninSemilocalRelativeTrace a f + finiteSoninSemilocalRelativeTrace a g := by
  classical
  simp only [finiteSoninSemilocalRelativeTrace]
  apply Finsupp.sum_add_index
  · intro
    simp
  · intro _ _ _ _
    ring

/-- Unit scale removes the remaining geometric normalization parameter. -/
def canonicalFiniteSoninSemilocalRelativeTrace (f : SoninPrimePowerTest) : ℂ :=
  finiteSoninSemilocalRelativeTrace 1 f

end RHTower
