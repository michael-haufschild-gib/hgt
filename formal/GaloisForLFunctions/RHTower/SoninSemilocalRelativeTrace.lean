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
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

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

theorem soninSemilocalLogPrimePowerCoefficient_ne_zero (pk : Nat.Primes × ℕ) :
    soninSemilocalLogPrimePowerCoefficient pk ≠ 0 := by
  rw [soninSemilocalLogPrimePowerCoefficient]
  norm_cast
  apply div_ne_zero
  · apply pow_ne_zero
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast pk.1.prop.pos)))
  · positivity

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

private theorem adjoint_smul_soninL2 (c : Complex)
    (T : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.adjoint (c • T) =
      star c • ContinuousLinearMap.adjoint T := by
  change star (c • T) = star c • star T
  rw [star_smul]

/-- The full semilocal linear cross is self-adjoint. -/
theorem adjoint_centralSoninSemilocalRelativeGramLinearCross
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.adjoint (centralSoninSemilocalRelativeGramLinearCross a pk) =
      centralSoninSemilocalRelativeGramLinearCross a pk := by
  rw [centralSoninSemilocalRelativeGramLinearCross, adjoint_add_soninL2,
    adjoint_smul_soninL2, adjoint_smul_soninL2, adjoint_mul_soninL2,
    adjoint_mul_soninL2, adjoint_adjoint, adjoint_adjoint]
  simp only [star_star]
  abel

/-- The exact Sonin projection correction is self-adjoint. -/
theorem adjoint_centralSoninProjectionCorrection (a : ℝ) :
    ContinuousLinearMap.adjoint (centralSoninProjectionCorrection a) =
      centralSoninProjectionCorrection a := by
  let adj : (SoninL2 →L[Complex] SoninL2) ≃ₗᵢ⋆[Complex]
      (SoninL2 →L[Complex] SoninL2) := ContinuousLinearMap.adjoint
  have hQ : ContinuousLinearMap.adjoint (centralSoninProjection a) =
      centralSoninProjection a := by
    exact (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
  have hsub (S T : SoninL2 →L[Complex] SoninL2) :
      ContinuousLinearMap.adjoint (S - T) =
        ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T := adj.map_sub S T
  simp only [centralSoninProjectionCorrection, hsub, hQ,
    ContinuousLinearMap.adjoint_one, adjoint_indicatorCutoff_central,
    adjoint_fourierCutoff_central]

/-- The canonical local trace density is real.  This is a necessary compatibility with the real
semilocal Weil test-functional and follows from self-adjointness plus trace cyclicity. -/
theorem soninSemilocalRelativeTraceDensity_im_eq_zero
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    (soninSemilocalRelativeTraceDensity a pk).im = 0 := by
  rw [soninSemilocalRelativeTraceDensity_eq_hsInner]
  have hC := centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hL := centralSoninSemilocalRelativeGramLinearCross_isHilbertSchmidt a ha pk
  have had := hsInner_adjoint_adjoint hC hL
  rw [adjoint_centralSoninProjectionCorrection,
    adjoint_centralSoninSemilocalRelativeGramLinearCross] at had
  apply Complex.conj_eq_iff_im.mp
  calc
    star (hsInner (centralSoninProjectionCorrection a)
        (centralSoninSemilocalRelativeGramLinearCross a pk)) =
        hsInner (centralSoninSemilocalRelativeGramLinearCross a pk)
          (centralSoninProjectionCorrection a) := (hsInner_conj_symm _ _).symm
    _ = hsInner (centralSoninProjectionCorrection a)
          (centralSoninSemilocalRelativeGramLinearCross a pk) := had.symm

/-- The coefficient-free geometric response of the Sonin principal/residual pairing. -/
def soninSemilocalGeometricTraceResponse
    (a : ℝ) (pk : Nat.Primes × ℕ) : ℂ :=
  hsInner (centralSoninProjectionCorrection a)
    (centralSoninRelativeGramLinearCross a (soninSemilocalPrimePowerScale pk)
      (one_lt_soninSemilocalPrimePowerScale pk))

/-- The weighted semilocal linear cross is the unsquared Euler coefficient times the purely
geometric unweighted cross. -/
theorem centralSoninSemilocalRelativeGramLinearCross_eq_coefficient_smul
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    centralSoninSemilocalRelativeGramLinearCross a pk =
      soninSemilocalLogPrimePowerCoefficient pk •
        centralSoninRelativeGramLinearCross a (soninSemilocalPrimePowerScale pk)
          (one_lt_soninSemilocalPrimePowerScale pk) := by
  rw [centralSoninSemilocalRelativeGramLinearCross,
    centralSoninRelativeGramLinearCross]
  have hc : star (soninSemilocalLogPrimePowerCoefficient pk) =
      soninSemilocalLogPrimePowerCoefficient pk := by
    simp [soninSemilocalLogPrimePowerCoefficient]
  rw [hc, smul_add]
  rfl

/-- **Exact density factorization.** All arithmetic dependence in the local Sonin trace density
is the unsquared logarithmic Euler coefficient.  The remaining factor is a coefficient-free
geometric response, isolating the source-specific identity that still has to be proved. -/
theorem soninSemilocalRelativeTraceDensity_eq_coefficient_mul_response
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninSemilocalRelativeTraceDensity a pk =
      soninSemilocalLogPrimePowerCoefficient pk *
        soninSemilocalGeometricTraceResponse a pk := by
  rw [soninSemilocalRelativeTraceDensity_eq_hsInner,
    centralSoninSemilocalRelativeGramLinearCross_eq_coefficient_smul,
    hsInner_smul_right, soninSemilocalGeometricTraceResponse]

/-- **Exact source-identity gate.** Matching the local arithmetic coefficient is equivalent to
the coefficient-free Sonin geometric response being exactly one.  Since the coefficient never
vanishes, no analytic or convergence premise remains hidden in this equivalence. -/
theorem soninSemilocalRelativeTraceDensity_eq_coefficient_iff_response_eq_one
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninSemilocalRelativeTraceDensity a pk =
        soninSemilocalLogPrimePowerCoefficient pk ↔
      soninSemilocalGeometricTraceResponse a pk = 1 := by
  rw [soninSemilocalRelativeTraceDensity_eq_coefficient_mul_response]
  constructor
  · intro h
    apply (mul_left_cancel₀ (soninSemilocalLogPrimePowerCoefficient_ne_zero pk))
    simpa using h
  · intro h
    rw [h, mul_one]

/-- The static logarithmic length of the scale `p^(k+1)`. -/
def soninSemilocalLogScaleLength (pk : Nat.Primes × ℕ) : ℂ :=
  (((pk.2 + 1 : ℝ) * Real.log (pk.1 : ℝ) : ℝ) : ℂ)

/-- The unsymmetrized von-Mangoldt flux coefficient `log(p) p^(-(k+1)/2)`, expressed as
logarithmic Euler coefficient times logarithmic scale length. -/
def soninSemilocalPrimeFluxCoefficient (pk : Nat.Primes × ℕ) : ℂ :=
  soninSemilocalLogPrimePowerCoefficient pk * soninSemilocalLogScaleLength pk

theorem soninSemilocalPrimeFluxCoefficient_eq (pk : Nat.Primes × ℕ) :
    soninSemilocalPrimeFluxCoefficient pk =
      (((Real.sqrt (pk.1 : ℝ))⁻¹ ^ (pk.2 + 1) *
        Real.log (pk.1 : ℝ) : ℝ) : ℂ) := by
  rw [soninSemilocalPrimeFluxCoefficient, soninSemilocalLogScaleLength,
    soninSemilocalLogPrimePowerCoefficient]
  norm_cast
  have hm : (pk.2 + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem soninSemilocalLogScaleLength_eq_log_scale (pk : Nat.Primes × ℕ) :
    soninSemilocalLogScaleLength pk =
      (Real.log (soninSemilocalPrimePowerScale pk) : ℂ) := by
  rw [soninSemilocalLogScaleLength, soninSemilocalPrimePowerScale,
    Real.log_pow]
  norm_cast

/-- **Exact flux source-identity gate.** The local Sonin trace density has the von-Mangoldt
coefficient exactly when the coefficient-free geometric response equals the static logarithmic
scale length `log(p^(k+1))`.  This isolates the remaining theorem without introducing a scaling
flow or a limiting cutoff. -/
theorem soninSemilocalRelativeTraceDensity_eq_fluxCoefficient_iff_response_eq_logScale
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninSemilocalRelativeTraceDensity a pk =
        soninSemilocalPrimeFluxCoefficient pk ↔
      soninSemilocalGeometricTraceResponse a pk =
        soninSemilocalLogScaleLength pk := by
  rw [soninSemilocalRelativeTraceDensity_eq_coefficient_mul_response,
    soninSemilocalPrimeFluxCoefficient]
  constructor
  · intro h
    apply (mul_left_cancel₀ (soninSemilocalLogPrimePowerCoefficient_ne_zero pk))
    exact h
  · intro h
    rw [h]

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

/-- The finite arithmetic prime-flux functional on the same compact-support carrier. -/
def finitePrimeFluxTrace (f : SoninPrimePowerTest) : ℂ :=
  f.sum fun pk w => w * soninSemilocalPrimeFluxCoefficient pk

/-- The single remaining geometric normalization statement.  It contains no convergence,
ordering, cutoff, zero-divisor, or spectral hypothesis. -/
def SoninSemilocalFluxNormalization : Prop :=
  ∀ pk : Nat.Primes × ℕ,
    soninSemilocalGeometricTraceResponse 1 pk = soninSemilocalLogScaleLength pk

/-- **Exact finite-support source identity gate.** The geometric normalization is equivalent to
equality of the canonical Sonin and arithmetic flux traces on every compact-support prime-power
test.  The converse already follows from the one-mode tests, so no limiting family is hidden. -/
theorem soninSemilocalFluxNormalization_iff_finiteTrace_eq :
    SoninSemilocalFluxNormalization ↔
      ∀ f : SoninPrimePowerTest,
        canonicalFiniteSoninSemilocalRelativeTrace f = finitePrimeFluxTrace f := by
  constructor
  · intro h f
    rw [canonicalFiniteSoninSemilocalRelativeTrace,
      finiteSoninSemilocalRelativeTrace, finitePrimeFluxTrace]
    apply Finsupp.sum_congr
    intro pk hpk
    rw [soninSemilocalRelativeTraceDensity_eq_coefficient_mul_response,
      h pk, soninSemilocalPrimeFluxCoefficient]
  · intro h pk
    have hs := h (Finsupp.single pk 1)
    simp only [canonicalFiniteSoninSemilocalRelativeTrace,
      finiteSoninSemilocalRelativeTrace_single, one_mul,
      finitePrimeFluxTrace, Finsupp.sum_single_index, zero_mul] at hs
    exact (soninSemilocalRelativeTraceDensity_eq_fluxCoefficient_iff_response_eq_logScale
      1 pk).mp hs

end RHTower
