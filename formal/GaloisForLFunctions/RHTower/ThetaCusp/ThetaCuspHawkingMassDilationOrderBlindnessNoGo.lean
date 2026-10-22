import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullMirrorBogoliubovEndpoint

/-!
# Exact Schwarzschild mass dilation and Hawking order-blindness

This endpoint tests the complete-evaporation selector against the actual dilation symmetry of a
Davies--Fulling mirror.  For the tilted theta trajectory

`p(v) = v + lambda * thetaCuspTiltedSource a v`,

the Schwarzschild mass-`M` realization is not obtained by replacing the dimensionless mirror
coupling by surface gravity.  It is the spacetime dilation

`p_M(u) = M * p(u / M)
        = u + lambda * M * thetaCuspTiltedSource a (u / M)`.

The formal consequences are exact:

* `p_M` remains a genuine timelike mirror whenever the unit-mass theta mirror is timelike;
* the full inertial-subtracted Davies--Fulling numerator is invariant at comoving frequencies;
* its Bogoliubov coefficient has the standard homogeneous weight `M`;
* every coupling jet, hence every first nonzero coupling order, is unchanged;
* peeling has weight `M⁻¹` and Schwarzian conformal flux has weight `M⁻²`;
* multiplying by the exact Schwarzschild shell time `M³` gives shell load proportional to `M`,
  summable on every dyadic terminal shell.

**[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC]** These are source-faithful identities for the
actual tilted theta ray and its complete nonlinear mirror integrand, not analogies attached to a
Fourier transform.

**[FALSIFIED PRODUCER]** Coupling order `m` is an analytic order in the dimensionless mirror
coupling.  It is not a mass scaling dimension.  Therefore the proposed replacement of its
intensity by `kappa(M)^(2*m)` double-counts Schwarzschild dilation.  Exact mass covariance gives
one universal `M⁻²` flux law and finite terminal load for all onset orders.  Complete evaporation
alone cannot select order one and cannot prove RH.

**[POSITIVE SURVIVOR]** Any Hawking producer capable of excluding the negative cubic chamber must
break self-similar mass dilation in a coefficient-faithful way: for example through dynamical
mass-dependent greybody mixing, horizon-memory/nonlocal semiclassical backreaction, or a genuine
singularity boundary condition.  Stationary KMS, CCR, inverse, Krein, late-time passivity, and
self-similar evaporation remain order-blind.

Physical provenance: Anderson--Good--Evans, arXiv:1507.03489, gives the exact black-hole/moving-
mirror correspondence with `kappa = (4M)⁻¹`.  Akal--Kusuki--Shiba--Takayanagi--Wei,
arXiv:2106.11179, develops the moving-mirror CFT flux and explicitly identifies the black-hole
singularity as missing from the mirror model.  The exact `M³` shell time is imported from the
semiclassical evaporation endpoint.
-/

open Complex Real MeasureTheory

noncomputable section

namespace RHTower

/-- Theta source stretched by the Schwarzschild mass scale. -/
def thetaCuspHawkingMassDilatedSource (a M u : ℝ) : ℝ :=
  M * thetaCuspTiltedSource a (u / M)

/-- Exact mass-dilated tilted theta ray `p_M(u) = M p(u/M)`. -/
def thetaCuspHawkingMassDilatedTimelikeRay
    (a M lambda u : ℝ) : ℝ :=
  u + lambda * thetaCuspHawkingMassDilatedSource a M u

theorem thetaCuspHawkingMassDilatedTimelikeRay_comoving
    (a M lambda v : ℝ) :
    thetaCuspHawkingMassDilatedTimelikeRay a M lambda (M * v) =
      M * thetaCuspHawkingTiltedTimelikeRay a lambda v := by
  rw [thetaCuspHawkingMassDilatedTimelikeRay,
    thetaCuspHawkingMassDilatedSource,
    thetaCuspHawkingTiltedTimelikeRay]
  by_cases hM : M = 0
  · simp [hM]
  · field_simp

theorem hasDerivAt_thetaCuspHawkingMassDilatedSource
    (a u : ℝ) {M : ℝ} (hM : M ≠ 0) :
    HasDerivAt (thetaCuspHawkingMassDilatedSource a M)
      (deriv (thetaCuspTiltedSource a) (u / M)) u := by
  have hs : HasDerivAt (thetaCuspTiltedSource a)
      (deriv (thetaCuspTiltedSource a) (u / M)) (u / M) :=
    ((contDiff_thetaCuspTiltedSource a).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => x / M) (1 / M) u :=
    (hasDerivAt_id u).div_const M
  have hc := hs.comp u hi
  have hm := hc.const_mul M
  have hcoef : M *
      (deriv (thetaCuspTiltedSource a) (u / M) * (1 / M)) =
      deriv (thetaCuspTiltedSource a) (u / M) := by
    field_simp
  rw [hcoef] at hm
  change HasDerivAt (fun y : ℝ =>
    M * thetaCuspTiltedSource a (y / M))
      (deriv (thetaCuspTiltedSource a) (u / M)) u
  exact hm

theorem deriv_thetaCuspHawkingMassDilatedSource
    (a u : ℝ) {M : ℝ} (hM : M ≠ 0) :
    deriv (thetaCuspHawkingMassDilatedSource a M) u =
      deriv (thetaCuspTiltedSource a) (u / M) :=
  (hasDerivAt_thetaCuspHawkingMassDilatedSource a u hM).deriv

theorem hasDerivAt_thetaCuspHawkingMassDilatedTimelikeRay
    (a lambda u : ℝ) {M : ℝ} (hM : M ≠ 0) :
    HasDerivAt (thetaCuspHawkingMassDilatedTimelikeRay a M lambda)
      (thetaCuspHawkingTiltedTimelikeRayDerivative a lambda (u / M)) u := by
  have hs := hasDerivAt_thetaCuspHawkingMassDilatedSource a u hM
  have hsum := (hasDerivAt_id u).add (hs.const_mul lambda)
  unfold thetaCuspHawkingMassDilatedTimelikeRay
    thetaCuspHawkingTiltedTimelikeRayDerivative
  convert hsum using 1 <;> rfl

theorem thetaCuspHawkingMassDilatedTimelikeRayDerivative_pos
    {a lambda : ℝ} (ha : |a| < 1)
    (hlambda : |lambda| < thetaCuspHawkingTiltedCouplingRadius a)
    {M : ℝ} (hM : M ≠ 0) (u : ℝ) :
    0 < deriv (thetaCuspHawkingMassDilatedTimelikeRay a M lambda) u := by
  rw [(hasDerivAt_thetaCuspHawkingMassDilatedTimelikeRay
    a lambda u hM).deriv]
  exact thetaCuspHawkingTiltedTimelikeRayDerivative_pos ha hlambda (u / M)

/-- Complete inertial-subtracted Davies--Fulling integrand of the mass-dilated theta ray. -/
def thetaCuspHawkingMassDilatedFullMirrorIntegrand
    (a M lambda outgoing incoming u : ℝ) : ℂ :=
  let k := thetaCuspHawkingMassDilatedSource a M u
  let k' := deriv (thetaCuspHawkingMassDilatedSource a M) u
  let total := incoming + outgoing
  Complex.exp (((-total * u : ℝ) : ℂ) * Complex.I) *
    (Complex.exp (Complex.I * ((-lambda * outgoing * k : ℝ) : ℂ)) *
        (((outgoing - incoming : ℝ) : ℂ) +
          ((lambda * outgoing * k' : ℝ) : ℂ)) -
      ((outgoing - incoming : ℝ) : ℂ))

theorem thetaCuspHawkingMassDilatedFullMirrorIntegrand_comoving
    (a lambda outgoing incoming v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedFullMirrorIntegrand a M lambda
        (outgoing / M) (incoming / M) (M * v) =
      ((M : ℂ)⁻¹) *
        thetaCuspHawkingFullMirrorIntegrand a lambda outgoing incoming v := by
  rw [thetaCuspHawkingMassDilatedFullMirrorIntegrand]
  rw [deriv_thetaCuspHawkingMassDilatedSource a (M * v) hM]
  unfold thetaCuspHawkingMassDilatedSource thetaCuspHawkingFullMirrorIntegrand
  dsimp only
  have hdiv : M * v / M = v := by field_simp
  rw [hdiv]
  have hosc : -(incoming / M + outgoing / M) * (M * v) =
      -(incoming + outgoing) * v := by
    field_simp
  have heik : -lambda * (outgoing / M) *
      (M * thetaCuspTiltedSource a v) =
      -lambda * outgoing * thetaCuspTiltedSource a v := by
    field_simp
  rw [hosc, heik]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hM]

def thetaCuspHawkingMassDilatedFullMirrorAmplitude
    (a M lambda outgoing incoming : ℝ) : ℂ :=
  ∫ u : ℝ,
    thetaCuspHawkingMassDilatedFullMirrorIntegrand
      a M lambda outgoing incoming u

/-- The complete nonlinear Davies--Fulling numerator is exactly invariant at comoving frequencies. -/
theorem thetaCuspHawkingMassDilatedFullMirrorAmplitude_comoving
    (a lambda outgoing incoming : ℝ) {M : ℝ} (hM : 0 < M) :
    thetaCuspHawkingMassDilatedFullMirrorAmplitude a M lambda
        (outgoing / M) (incoming / M) =
      thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming := by
  let g : ℝ → ℂ := fun u =>
    thetaCuspHawkingMassDilatedFullMirrorIntegrand a M lambda
      (outgoing / M) (incoming / M) u
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g M
  rw [abs_of_pos (inv_pos.mpr hM), Complex.real_smul,
    Complex.ofReal_inv] at hscale
  have hpoint : (fun v : ℝ => g (M * v)) = fun v : ℝ =>
      ((M : ℂ)⁻¹) *
        thetaCuspHawkingFullMirrorIntegrand a lambda outgoing incoming v := by
    funext v
    exact thetaCuspHawkingMassDilatedFullMirrorIntegrand_comoving
      a lambda outgoing incoming v hM.ne'
  rw [hpoint, integral_const_mul] at hscale
  unfold thetaCuspHawkingMassDilatedFullMirrorAmplitude
    thetaCuspHawkingFullMirrorAmplitude
  dsimp only [g] at hscale
  have hMinv : (M : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne')
  apply (mul_left_cancel₀ hMinv)
  exact hscale.symm

def thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude
    (a M lambda omega : ℝ) : ℂ :=
  thetaCuspHawkingMassDilatedFullMirrorAmplitude
    a M lambda (omega / 2) (omega / 2)

theorem thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude_comoving
    (a lambda omega : ℝ) {M : ℝ} (hM : 0 < M) :
    thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude
        a M lambda (omega / M) =
      thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega := by
  have hhalf : omega / M / 2 = omega / 2 / M := by ring
  rw [thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude,
    thetaCuspHawkingBalancedFullMirrorAmplitude, hhalf]
  exact thetaCuspHawkingMassDilatedFullMirrorAmplitude_comoving
    a lambda (omega / 2) (omega / 2) hM

def thetaCuspHawkingMassDilatedFullMirrorBogoliubovBeta
    (a M lambda omega : ℝ) : ℂ :=
  (((-1 / (2 * Real.pi * omega) : ℝ) : ℂ)) *
    thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude
      a M lambda omega

/-- The standard Bogoliubov coefficient has homogeneous mass weight one. -/
theorem thetaCuspHawkingMassDilatedFullMirrorBogoliubovBeta_comoving
    (a lambda omega : ℝ) {M : ℝ} (hM : 0 < M) (homega : omega ≠ 0) :
    thetaCuspHawkingMassDilatedFullMirrorBogoliubovBeta
        a M lambda (omega / M) =
      (M : ℂ) * thetaCuspHawkingFullMirrorBogoliubovBeta
        a lambda omega := by
  rw [thetaCuspHawkingMassDilatedFullMirrorBogoliubovBeta,
    thetaCuspHawkingMassDilatedBalancedFullMirrorAmplitude_comoving
      a lambda omega hM,
    thetaCuspHawkingFullMirrorBogoliubovBeta]
  push_cast
  field_simp [hM.ne', homega, Real.pi_ne_zero]

/-- Exact least-positive coupling-jet predicate for a nonlinear scattering amplitude. -/
def ThetaCuspHawkingHasPositiveCouplingOnsetOrder (F : ℝ → ℂ) (m : ℕ) : Prop :=
  1 ≤ m ∧ iteratedDeriv m F 0 ≠ 0 ∧
    ∀ n : ℕ, 1 ≤ n → n < m → iteratedDeriv n F 0 = 0

/-- Schwarzschild mass dilation preserves every full-mirror coupling onset order. -/
theorem thetaCuspHawkingMassDilation_preserves_fullMirrorCouplingOnsetOrder
    (a outgoing incoming : ℝ) {M : ℝ} (hM : 0 < M) (m : ℕ) :
    ThetaCuspHawkingHasPositiveCouplingOnsetOrder
        (fun lambda : ℝ =>
          thetaCuspHawkingMassDilatedFullMirrorAmplitude a M lambda
            (outgoing / M) (incoming / M)) m ↔
      ThetaCuspHawkingHasPositiveCouplingOnsetOrder
        (fun lambda : ℝ =>
          thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming) m := by
  rw [show (fun lambda : ℝ =>
      thetaCuspHawkingMassDilatedFullMirrorAmplitude a M lambda
        (outgoing / M) (incoming / M)) =
      fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming by
    funext lambda
    exact thetaCuspHawkingMassDilatedFullMirrorAmplitude_comoving
      a lambda outgoing incoming hM]

private theorem iteratedDeriv_comp_mul_left_real
    (f : ℝ → ℝ) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => f (c * y)) x =
      c ^ n * iteratedDeriv n f (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv n (fun y => f (c * y)) =
          fun y => c ^ n * iteratedDeriv n f (c * y) from funext ih]
      rw [deriv_const_mul_field,
        deriv_comp_mul_left c (iteratedDeriv n f) x, smul_eq_mul,
        ← iteratedDeriv_succ]
      ring

private theorem iteratedDeriv_const_mul_real
    (f : ℝ → ℝ) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => c * f y) x =
      c * iteratedDeriv n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv n (fun y => c * f y) =
          fun y => c * iteratedDeriv n f y from funext ih]
      rw [deriv_const_mul_field, ← iteratedDeriv_succ]

theorem iteratedDeriv_thetaCuspHawkingMassDilatedSource
    (a M u : ℝ) (n : ℕ) :
    iteratedDeriv n (thetaCuspHawkingMassDilatedSource a M) u =
      M * M⁻¹ ^ n *
        iteratedDeriv n (thetaCuspTiltedSource a) (M⁻¹ * u) := by
  change iteratedDeriv n
    (fun u : ℝ => M * thetaCuspTiltedSource a (u / M)) u = _
  rw [show (fun u : ℝ => M * thetaCuspTiltedSource a (u / M)) =
      fun u : ℝ => M * thetaCuspTiltedSource a (M⁻¹ * u) by
    funext u
    rw [div_eq_inv_mul]]
  rw [iteratedDeriv_const_mul_real,
    iteratedDeriv_comp_mul_left_real]
  ring

/-- Every actual null-ray jet transforms with its geometric mass weight. -/
theorem iteratedDeriv_thetaCuspHawkingMassDilatedTimelikeRay
    (a lambda u : ℝ) {M : ℝ} (hM : M ≠ 0) (n : ℕ) :
    iteratedDeriv n (thetaCuspHawkingMassDilatedTimelikeRay a M lambda) u =
      M * M⁻¹ ^ n *
        iteratedDeriv n (thetaCuspHawkingTiltedTimelikeRay a lambda)
          (M⁻¹ * u) := by
  have hray : thetaCuspHawkingMassDilatedTimelikeRay a M lambda =
      fun x : ℝ =>
        M * thetaCuspHawkingTiltedTimelikeRay a lambda (M⁻¹ * x) := by
    funext x
    rw [thetaCuspHawkingMassDilatedTimelikeRay,
      thetaCuspHawkingMassDilatedSource,
      thetaCuspHawkingTiltedTimelikeRay]
    field_simp
  rw [hray, iteratedDeriv_const_mul_real,
    iteratedDeriv_comp_mul_left_real]
  ring

def thetaCuspHawkingRayJetOne (a lambda v : ℝ) : ℝ :=
  iteratedDeriv 1 (thetaCuspHawkingTiltedTimelikeRay a lambda) v

def thetaCuspHawkingRayJetTwo (a lambda v : ℝ) : ℝ :=
  iteratedDeriv 2 (thetaCuspHawkingTiltedTimelikeRay a lambda) v

def thetaCuspHawkingRayJetThree (a lambda v : ℝ) : ℝ :=
  iteratedDeriv 3 (thetaCuspHawkingTiltedTimelikeRay a lambda) v

def thetaCuspHawkingMassDilatedRayJetOne (a M lambda u : ℝ) : ℝ :=
  iteratedDeriv 1 (thetaCuspHawkingMassDilatedTimelikeRay a M lambda) u

def thetaCuspHawkingMassDilatedRayJetTwo (a M lambda u : ℝ) : ℝ :=
  iteratedDeriv 2 (thetaCuspHawkingMassDilatedTimelikeRay a M lambda) u

def thetaCuspHawkingMassDilatedRayJetThree (a M lambda u : ℝ) : ℝ :=
  iteratedDeriv 3 (thetaCuspHawkingMassDilatedTimelikeRay a M lambda) u

theorem thetaCuspHawkingMassDilatedRayJetOne_comoving
    (a lambda v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedRayJetOne a M lambda (M * v) =
      thetaCuspHawkingRayJetOne a lambda v := by
  rw [thetaCuspHawkingMassDilatedRayJetOne,
    thetaCuspHawkingRayJetOne,
    iteratedDeriv_thetaCuspHawkingMassDilatedTimelikeRay a lambda
      (M * v) hM]
  field_simp

theorem thetaCuspHawkingMassDilatedRayJetTwo_comoving
    (a lambda v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedRayJetTwo a M lambda (M * v) =
      M⁻¹ * thetaCuspHawkingRayJetTwo a lambda v := by
  rw [thetaCuspHawkingMassDilatedRayJetTwo,
    thetaCuspHawkingRayJetTwo,
    iteratedDeriv_thetaCuspHawkingMassDilatedTimelikeRay a lambda
      (M * v) hM]
  field_simp

theorem thetaCuspHawkingMassDilatedRayJetThree_comoving
    (a lambda v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedRayJetThree a M lambda (M * v) =
      M⁻¹ ^ (2 : ℕ) * thetaCuspHawkingRayJetThree a lambda v := by
  rw [thetaCuspHawkingMassDilatedRayJetThree,
    thetaCuspHawkingRayJetThree,
    iteratedDeriv_thetaCuspHawkingMassDilatedTimelikeRay a lambda
      (M * v) hM]
  field_simp

def thetaCuspHawkingSchwarzianFromThreeJets (p1 p2 p3 : ℝ) : ℝ :=
  p3 / p1 - (3 / 2 : ℝ) * (p2 / p1) ^ (2 : ℕ)

def thetaCuspHawkingSchwarzian (a lambda v : ℝ) : ℝ :=
  thetaCuspHawkingSchwarzianFromThreeJets
    (thetaCuspHawkingRayJetOne a lambda v)
    (thetaCuspHawkingRayJetTwo a lambda v)
    (thetaCuspHawkingRayJetThree a lambda v)

def thetaCuspHawkingMassDilatedSchwarzian
    (a M lambda u : ℝ) : ℝ :=
  thetaCuspHawkingSchwarzianFromThreeJets
    (thetaCuspHawkingMassDilatedRayJetOne a M lambda u)
    (thetaCuspHawkingMassDilatedRayJetTwo a M lambda u)
    (thetaCuspHawkingMassDilatedRayJetThree a M lambda u)

/-- Schwarzian conformal anomaly has universal mass weight minus two. -/
theorem thetaCuspHawkingMassDilatedSchwarzian_comoving
    (a lambda v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedSchwarzian a M lambda (M * v) =
      M⁻¹ ^ (2 : ℕ) * thetaCuspHawkingSchwarzian a lambda v := by
  rw [thetaCuspHawkingMassDilatedSchwarzian,
    thetaCuspHawkingSchwarzian,
    thetaCuspHawkingMassDilatedRayJetOne_comoving a lambda v hM,
    thetaCuspHawkingMassDilatedRayJetTwo_comoving a lambda v hM,
    thetaCuspHawkingMassDilatedRayJetThree_comoving a lambda v hM]
  unfold thetaCuspHawkingSchwarzianFromThreeJets
  ring

def thetaCuspHawkingMassDilatedConformalFlux
    (C a M lambda u : ℝ) : ℝ :=
  -C * thetaCuspHawkingMassDilatedSchwarzian a M lambda u

def thetaCuspHawkingConformalFlux
    (C a lambda v : ℝ) : ℝ :=
  -C * thetaCuspHawkingSchwarzian a lambda v

theorem thetaCuspHawkingMassDilatedConformalFlux_comoving
    (C a lambda v : ℝ) {M : ℝ} (hM : M ≠ 0) :
    thetaCuspHawkingMassDilatedConformalFlux C a M lambda (M * v) =
      M⁻¹ ^ (2 : ℕ) * thetaCuspHawkingConformalFlux C a lambda v := by
  rw [thetaCuspHawkingMassDilatedConformalFlux,
    thetaCuspHawkingConformalFlux,
    thetaCuspHawkingMassDilatedSchwarzian_comoving a lambda v hM]
  ring

/-- Exact shell time times the comoving Schwarzian flux of the mass-dilated theta mirror. -/
def thetaCuspHawkingMassDilationDyadicShellLoad
    (C alpha a lambda v : ℝ) (n : ℕ) : ℝ :=
  let M := schwarzschildEvaporationDyadicMass n
  schwarzschildEvaporationDyadicShellDuration alpha n *
    thetaCuspHawkingMassDilatedConformalFlux C a M lambda (M * v)

theorem schwarzschildEvaporationDyadicMass_pos (n : ℕ) :
    0 < schwarzschildEvaporationDyadicMass n := by
  rw [schwarzschildEvaporationDyadicMass]
  positivity

theorem thetaCuspHawkingMassDilationDyadicShellLoad_eq
    (C a lambda v : ℝ) {alpha : ℝ} (halpha : alpha ≠ 0) (n : ℕ) :
    thetaCuspHawkingMassDilationDyadicShellLoad C alpha a lambda v n =
      (7 / (24 * alpha) *
          thetaCuspHawkingConformalFlux C a lambda v) *
        schwarzschildEvaporationDyadicMass n := by
  let M := schwarzschildEvaporationDyadicMass n
  have hM : 0 < M := schwarzschildEvaporationDyadicMass_pos n
  rw [thetaCuspHawkingMassDilationDyadicShellLoad]
  rw [schwarzschildEvaporationDyadicShellDuration_eq halpha,
    thetaCuspHawkingMassDilatedConformalFlux_comoving
      C a lambda v hM.ne']
  change 7 / (24 * alpha) * M ^ (3 : ℕ) *
      (M⁻¹ ^ (2 : ℕ) * thetaCuspHawkingConformalFlux C a lambda v) = _
  field_simp
  ring

/-- Exact mass-dilation load is geometric and summable through complete evaporation. -/
theorem summable_thetaCuspHawkingMassDilationDyadicShellLoad
    (C alpha a lambda v : ℝ) (halpha : alpha ≠ 0) :
    Summable (thetaCuspHawkingMassDilationDyadicShellLoad
      C alpha a lambda v) := by
  rw [show thetaCuspHawkingMassDilationDyadicShellLoad
      C alpha a lambda v = fun n : ℕ =>
        (7 / (24 * alpha) *
          thetaCuspHawkingConformalFlux C a lambda v) *
            (1 / 2 : ℝ) ^ n by
    funext n
    rw [thetaCuspHawkingMassDilationDyadicShellLoad_eq
      C a lambda v halpha n,
      schwarzschildEvaporationDyadicMass]]
  exact (summable_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _

/-- A genuine mass dilation leaves finite anomaly load even when one labels the sector delayed. -/
theorem exists_delayedOrder_with_summable_thetaCuspHawkingMassDilationDyadicShellLoad
    (C alpha a lambda v : ℝ) (halpha : alpha ≠ 0) :
    ∃ m : ℕ, 2 ≤ m ∧
      Summable (thetaCuspHawkingMassDilationDyadicShellLoad
        C alpha a lambda v) := by
  exact ⟨2, by norm_num,
    summable_thetaCuspHawkingMassDilationDyadicShellLoad
      C alpha a lambda v halpha⟩

theorem thetaCuspHawkingSurfaceGravityOrderPowerLoad_disagrees_with_exactMassDilation
    (C alpha a lambda v : ℝ) (halpha : alpha ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) :
    ¬ Summable (schwarzschildEvaporationDyadicEndpointShellLoad m) ∧
      Summable (thetaCuspHawkingMassDilationDyadicShellLoad
        C alpha a lambda v) := by
  exact ⟨not_summable_schwarzschildEvaporationDyadicEndpointShellLoad hm,
    summable_thetaCuspHawkingMassDilationDyadicShellLoad
      C alpha a lambda v halpha⟩

/-- **No-go.** Finite exact mass-dilation load cannot select coupling onset order one. -/
theorem thetaCuspHawkingMassDilationFiniteLoad_doesNotForceOrderOne
    (C alpha a lambda v : ℝ) (halpha : alpha ≠ 0) :
    ¬ (∀ m : ℕ,
      Summable (thetaCuspHawkingMassDilationDyadicShellLoad
        C alpha a lambda v) → m = 1) := by
  intro h
  have htwo := h 2
    (summable_thetaCuspHawkingMassDilationDyadicShellLoad
      C alpha a lambda v halpha)
  norm_num at htwo

end RHTower
