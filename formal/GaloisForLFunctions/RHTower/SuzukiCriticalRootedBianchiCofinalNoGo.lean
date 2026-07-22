import GaloisForLFunctions.RHTower.VonMangoldtGammaConormalEulerBoundary
import GaloisForLFunctions.RHTower.PrimeClockScaleFactor

/-!
# Critical rooted Bianchi cofinal no-go

The raw pointed Gamma--Bianchi feature has prime diagonal mass

`Lambda(p)/p * exp(-x*log p)`.

Matching Suzuki's critical screw coefficient `Lambda(p)/sqrt(p)` forces the
inverse displacement `x = -1/2`.  This module proves that normalization
prime by prime, then proves that its critical mass is not summable.  Hence a
raw rooted Bianchi feature cannot be passed cofinally as an ordinary Hilbert
Gram at critical weight.  Finite cutoffs and positive absolute-Euler
displacements are unaffected; cancellation or renormalization must occur
before the critical cofinal limit.

No prime-number theorem, estimate, RH premise, or computation is used.  The
only divergence input is Euler's prime harmonic theorem.
-/

namespace RHTower

noncomputable section

/-- Raw pointed-Bianchi diagonal mass restricted to one prime coordinate at
displacement `x`. -/
def suzukiRootedBianchiPrimeMassAt
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  (ArithmeticFunction.vonMangoldt p / (p : ℝ)) *
    Real.exp (-x * Real.log (p : ℝ))

/-- Critical prime mass appearing in Suzuki's screw source. -/
def suzukiCriticalRootedBianchiPrimeMass
    (p : Nat.Primes) : ℝ :=
  ArithmeticFunction.vonMangoldt p / Real.sqrt (p : ℝ)

/-- **Critical inverse-translation identity.**  Transporting the raw
Bianchi normalization from `Lambda(p)/p` to Suzuki's critical coefficient is
exactly displacement `x=-1/2`. -/
theorem suzukiRootedBianchiPrimeMassAt_neg_half
    (p : Nat.Primes) :
    suzukiRootedBianchiPrimeMassAt (-1 / 2) p =
      suzukiCriticalRootedBianchiPrimeMass p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hsqrt :
      Real.exp (Real.log (p : ℝ) / 2) = Real.sqrt (p : ℝ) := by
    rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]
  rw [suzukiRootedBianchiPrimeMassAt,
    suzukiCriticalRootedBianchiPrimeMass]
  rw [show -(-1 / 2 : ℝ) * Real.log (p : ℝ) =
      Real.log (p : ℝ) / 2 by ring, hsqrt]
  field_simp [hp.ne', Real.sqrt_ne_zero'.mpr hp]
  rw [Real.sq_sqrt hp.le]

theorem suzukiCriticalRootedBianchiPrimeMass_nonneg
    (p : Nat.Primes) :
    0 ≤ suzukiCriticalRootedBianchiPrimeMass p := by
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.sqrt_nonneg _)

/-- Critical rooted mass dominates a fixed positive multiple of the prime
harmonic mass. -/
theorem log_two_mul_primeHarmonic_le_suzukiCriticalRootedBianchiPrimeMass
    (p : Nat.Primes) :
    Real.log 2 * (1 / (p : ℝ)) ≤
      suzukiCriticalRootedBianchiPrimeMass p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hp : 0 < (p : ℝ) := by positivity
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp hp2
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hsqrtLe : Real.sqrt (p : ℝ) ≤ (p : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  rw [suzukiCriticalRootedBianchiPrimeMass,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  calc
    Real.log 2 * (1 / (p : ℝ)) = Real.log 2 / (p : ℝ) := by ring
    _ ≤ Real.log (p : ℝ) / (p : ℝ) :=
      div_le_div_of_nonneg_right hlog hp.le
    _ ≤ Real.log (p : ℝ) / Real.sqrt (p : ℝ) :=
      div_le_div_of_nonneg_left hlogp hsqrtPos hsqrtLe

/-- **Critical rooted Bianchi divergence.**  The unrenormalized critical raw
diagonal has no finite cofinal sum. -/
theorem not_summable_suzukiCriticalRootedBianchiPrimeMass :
    ¬ Summable suzukiCriticalRootedBianchiPrimeMass := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes =>
      Real.log 2 * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · exact log_two_mul_primeHarmonic_le_suzukiCriticalRootedBianchiPrimeMass
    · exact hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (Real.log_pos one_lt_two).ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Canonical square-root coordinate whose Gram diagonal is the critical raw
Bianchi mass. -/
def suzukiCriticalRootedBianchiPrimeAmplitude
    (p : Nat.Primes) : ℝ :=
  Real.sqrt (suzukiCriticalRootedBianchiPrimeMass p)

theorem suzukiCriticalRootedBianchiPrimeAmplitude_sq
    (p : Nat.Primes) :
    suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2 =
      suzukiCriticalRootedBianchiPrimeMass p := by
  exact Real.sq_sqrt (suzukiCriticalRootedBianchiPrimeMass_nonneg p)

/-- **Source connector.**  The canonical critical rooted amplitude is not an
invented proxy: it is exactly the existing uniquely renormalized complete
Gamma-conormal boundary coordinate, specialized to one prime at inverse
displacement `-1/2`. -/
theorem vonMangoldtGammaRenormalizedBoundaryCoordinate_neg_half_prime
    (p : Nat.Primes) :
    vonMangoldtGammaRenormalizedBoundaryCoordinate (-1 / 2) p =
      suzukiCriticalRootedBianchiPrimeAmplitude p := by
  rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq p.prop.two_le]
  rw [suzukiCriticalRootedBianchiPrimeAmplitude,
    ← suzukiRootedBianchiPrimeMassAt_neg_half]
  rfl

/-- **Hilbert realization no-go.**  The canonical critical rooted feature has
divergent squared norm, so it cannot be an unrenormalized cofinal `ell^2`
Gram vector. -/
theorem not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude :
    ¬ Summable (fun p : Nat.Primes =>
      suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2) := by
  intro hsum
  apply not_summable_suzukiCriticalRootedBianchiPrimeMass
  exact hsum.congr (fun p =>
    suzukiCriticalRootedBianchiPrimeAmplitude_sq p)

/-- **Scalar-renormalization rigidity.**  A prime-independent residual
multiple of the critical rooted coordinate is square-summable exactly when
that residual vanishes.  Thus no nonzero scalar subtraction, rescaling, or
finite-dimensional border can repair the critical diagonal: the leading
prime coordinate must cancel exactly before the cofinal limit. -/
theorem summable_const_mul_sq_suzukiCriticalRootedBianchiPrimeAmplitude_iff
    (c : ℝ) :
    Summable (fun p : Nat.Primes =>
      (c * suzukiCriticalRootedBianchiPrimeAmplitude p) ^ 2) ↔
      c = 0 := by
  constructor
  · intro hsum
    by_contra hc
    have hscaled : Summable (fun p : Nat.Primes =>
        c ^ 2 * suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2) :=
      hsum.congr (fun p => by ring)
    have hraw : Summable (fun p : Nat.Primes =>
        suzukiCriticalRootedBianchiPrimeAmplitude p ^ 2) :=
      (summable_mul_left_iff (pow_ne_zero 2 hc)).mp hscaled
    exact not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude hraw
  · rintro rfl
    simp

/-- The actual uniquely renormalized Gamma-conormal boundary coordinates have
divergent squared norm at critical inverse displacement.  Thus the no-go lands
on the corpus source connector itself, not merely on an abstractly matched
weight. -/
theorem not_summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_neg_half_prime :
    ¬ Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate (-1 / 2) p ^ 2) := by
  intro hsum
  apply not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude
  exact hsum.congr (fun p => by
    rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_neg_half_prime])

end

end RHTower
