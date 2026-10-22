import GaloisForLFunctions.RHTower.Suzuki.SuzukiFullFrequencyNeumannHolonomy

/-!
# Projective affine-secant tensor for Suzuki two-shift sewing

Suzuki's jump uses the affine intercept `(beta*q_alpha-alpha*q_beta)/(beta-alpha)`, not merely
the projective chord `q_beta-q_alpha`.  Alternating Plücker data determine the chord but forget the
additive affine chart: replacing numerator observation `B` by `B+delta*D` fixes every Plücker
minor while shifting the affine intercept by `delta`.

This file proves the exact division-free replacement.  In the common two-resolvent coordinates
`x=B(v)`, `X=B(Av)`, `y=D(v)`, `Y=D(Av)`, with homogeneous Neumann coordinate `c`, the sewn source
is carried by marked tensor

`(X+c)Y-(alpha+beta)xY+alpha*beta*x*y`.

It contains diagonal and symmetric-pair information absent from exterior square.  Theorems below
also formalize gauge no-go, opposite-shift blindness of alternating sector, and physical rank-one
recovery.  No RH assumption, positivity premise, Xi divisor, estimate, or computation occurs.
-/

namespace RHTower

noncomputable section

/-- Marked affine-secant tensor in common product-resolvent coordinates. -/
def suzukiProjectiveAffineSecantTensor
    {F : Type*} [CommRing F]
    (alpha beta x X y Y c : F) : F :=
  (X + c) * Y - (alpha + beta) * x * Y + alpha * beta * x * y

/-- Two endpoint denominators in the common secant chart. -/
def suzukiProjectiveAffineSecantDenominator
    {F : Type*} [CommRing F]
    (alpha beta y Y : F) : F :=
  (Y - beta * y) * (Y - alpha * y)

/-- **Division-free affine-secant identity.**  This is exact source carrier for the weighted affine
intercept used in Suzuki jump sewing. -/
theorem suzukiProjectiveAffineSecant_cross_identity
    {F : Type*} [CommRing F] (alpha beta x X y Y c : F) :
    beta * (X - beta * x + c) * (Y - alpha * y) -
        alpha * (X - alpha * x + c) * (Y - beta * y) =
      (beta - alpha) *
        suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  simp only [suzukiProjectiveAffineSecantTensor]
  ring

/-- Quotient form of the affine-secant identity away from explicit endpoint divisors. -/
theorem suzukiProjectiveAffineSecant_quotient_identity
    {F : Type*} [Field F] {alpha beta x X y Y c : F}
    (hab : alpha ≠ beta) (hAlpha : Y - beta * y ≠ 0)
    (hBeta : Y - alpha * y ≠ 0) :
    (beta * ((X - beta * x + c) / (Y - beta * y)) -
        alpha * ((X - alpha * x + c) / (Y - alpha * y))) /
          (beta - alpha) =
      suzukiProjectiveAffineSecantTensor alpha beta x X y Y c /
        suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  simp only [suzukiProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantDenominator]
  have hAlpha' : Y - y * beta ≠ 0 := by simpa [mul_comm] using hAlpha
  have hBeta' : Y - y * alpha ≠ 0 := by simpa [mul_comm] using hBeta
  rw [div_eq_iff (sub_ne_zero.mpr hab.symm)]
  field_simp [hAlpha, hBeta, hAlpha', hBeta']
  ring

/-- Adding a multiple of denominator observation leaves every Plücker minor unchanged. -/
theorem suzukiProjectiveMinor_affineGauge_invariant
    {F : Type*} [CommRing F] (delta x X y Y : F) :
    (x + delta * y) * Y - (X + delta * Y) * y = x * Y - X * y := by
  ring

/-- Marked secant tensor remembers affine chart: gauge shift adds `delta` times full denominator. -/
theorem suzukiProjectiveAffineSecantTensor_gauge_covariance
    {F : Type*} [CommRing F] (alpha beta delta x X y Y c : F) :
    suzukiProjectiveAffineSecantTensor alpha beta
        (x + delta * y) (X + delta * Y) y Y c =
      suzukiProjectiveAffineSecantTensor alpha beta x X y Y c +
        delta * suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  simp only [suzukiProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantDenominator]
  ring

/-- One endpoint quotient shifts by `delta` under numerator chart change. -/
theorem suzukiProjectiveResponse_affineGauge_shift
    {F : Type*} [Field F] {shift delta x X y Y c : F}
    (hden : Y - shift * y ≠ 0) :
    ((X + delta * Y) - shift * (x + delta * y) + c) /
        (Y - shift * y) =
      (X - shift * x + c) / (Y - shift * y) + delta := by
  field_simp [hden]
  ring

/-- **Plücker-only no-go witness.**  Under a nontrivial affine gauge, chord is identical while
marked secant tensor changes.  Therefore exterior data alone cannot determine affine intercept. -/
theorem suzukiProjectiveMinor_same_affineTensor_different
    {F : Type*} [Field F] {alpha beta delta x X y Y c : F}
    (hdelta : delta ≠ 0)
    (hden : suzukiProjectiveAffineSecantDenominator alpha beta y Y ≠ 0) :
    ((x + delta * y) * Y - (X + delta * Y) * y = x * Y - X * y) ∧
      suzukiProjectiveAffineSecantTensor alpha beta
          (x + delta * y) (X + delta * Y) y Y c ≠
        suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  constructor
  · exact suzukiProjectiveMinor_affineGauge_invariant delta x X y Y
  · rw [suzukiProjectiveAffineSecantTensor_gauge_covariance]
    exact add_ne_left.mpr (mul_ne_zero hdelta hden)

/-! ## Complex source-boundary specialization -/

/-- Complex linear-map form used by Suzuki Fourier boundary observations.  Endpoint resolvent
states are substituted before any characteristic division. -/
theorem suzukiProjectiveAffineSecant_linearMap_cross_identity
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) (B D : V →ₗ[ℂ] ℂ)
    (alpha beta c : ℂ) (uAlpha uBeta v : V)
    (hAlpha : uAlpha = A v - beta • v)
    (hBeta : uBeta = A v - alpha • v) :
    beta * (B uAlpha + c) * D uBeta -
        alpha * (B uBeta + c) * D uAlpha =
      (beta - alpha) *
        suzukiProjectiveAffineSecantTensor alpha beta
          (B v) (B (A v)) (D v) (D (A v)) c := by
  rw [hAlpha, hBeta]
  simp only [map_sub, map_smul, smul_eq_mul]
  exact suzukiProjectiveAffineSecant_cross_identity
    alpha beta (B v) (B (A v)) (D v) (D (A v)) c

/-- Exact two-mode symmetric/alternating split of off-diagonal marked tensor contribution. -/
theorem suzukiProjectiveAffineSecant_twoMode_pair_decomposition
    (alpha beta t0 t1 v0 v1 b0 b1 d0 d1 : ℝ) :
    v0 * v1 *
        (b0 * d1 * (t0 * t1 - (alpha + beta) * t1 + alpha * beta) +
          b1 * d0 * (t0 * t1 - (alpha + beta) * t0 + alpha * beta)) =
      v0 * v1 *
        (((2 * t0 * t1 - (alpha + beta) * (t0 + t1) +
              2 * (alpha * beta)) / 2) * (b0 * d1 + b1 * d0) -
          (((alpha + beta) * (t1 - t0)) / 2) * (b0 * d1 - b1 * d0)) := by
  ring

/-- At opposite shifts, alternating Plücker pair sector vanishes identically while symmetric
pair coefficient survives. -/
theorem suzukiProjectiveAffineSecant_oppositeShift_pair_is_symmetric
    (shift t0 t1 v0 v1 b0 b1 d0 d1 : ℝ) :
    v0 * v1 *
        (b0 * d1 * (t0 * t1 - ((-shift) + shift) * t1 + (-shift) * shift) +
          b1 * d0 * (t0 * t1 - ((-shift) + shift) * t0 + (-shift) * shift)) =
      v0 * v1 * (t0 * t1 - shift ^ (2 : ℕ)) * (b0 * d1 + b1 * d0) := by
  ring

/-- Physical rank-one check.  With `B=L-KA` and `c=K(e)`, marked secant quotient recovers affine
intercept `L/D`; Plücker chord alone only sees slope. -/
theorem suzukiProjectiveAffineSecant_rankOne_recovers_intercept
    {alpha beta t L K D : ℝ}
    (hD : D ≠ 0) (htAlpha : t ≠ alpha) (htBeta : t ≠ beta) :
    suzukiProjectiveAffineSecantTensor alpha beta
        (L - t * K) (t * (L - t * K)) D (t * D)
        ((t - alpha) * (t - beta) * K) /
      suzukiProjectiveAffineSecantDenominator alpha beta D (t * D) =
        L / D := by
  simp only [suzukiProjectiveAffineSecantTensor,
    suzukiProjectiveAffineSecantDenominator]
  field_simp [hD, htAlpha, htBeta]
  ring

end

end RHTower
