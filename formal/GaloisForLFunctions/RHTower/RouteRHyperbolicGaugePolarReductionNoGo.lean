import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.RadialAffineTorsor
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldPositiveStokesPolarization

/-!
# Route R hyperbolic-gauge polar-reduction no-go

The retained forward/reciprocal source atom is the actual two-sector complex
plane.  Its horizontal character acts with weights `(+1,-1)`.  This module
proves, without an Xi or critical-line hypothesis, that the action preserves
both source pairings but erases every linear landing into a fixed trivially
gauged target.  The fixed positive metric is not invariant; its transported
version is positive and agrees with the fixed metric only at neutral boost.

This is the formal C33 obstruction.  It does not rule out an externally
selected positive polar/compression handoff.
-/

open Complex

namespace RHTower

noncomputable section

private theorem routeR_exp_mul_exp_neg (a : ℝ) :
    (((Real.exp a : ℝ) : ℂ) * ((Real.exp (-a) : ℝ) : ℂ)) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

private theorem routeR_exp_neg_mul_exp (a : ℝ) :
    (((Real.exp (-a) : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ)) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

/-- Actual retained forward/reciprocal Route-R source plane. -/
abbrev RouteRHyperbolicSourcePlane := ℂ × ℂ

/-- Horizontal character gauge, with forward weight `+1` and reciprocal
weight `-1`. -/
def routeRHyperbolicSourceGauge (a : ℝ) :
    RouteRHyperbolicSourcePlane ≃ₗ[ℂ] RouteRHyperbolicSourcePlane where
  toFun z := (((Real.exp a : ℝ) : ℂ) * z.1,
    ((Real.exp (-a) : ℝ) : ℂ) * z.2)
  invFun z := (((Real.exp (-a) : ℝ) : ℂ) * z.1,
    ((Real.exp a : ℝ) : ℂ) * z.2)
  map_add' z w := by
    apply Prod.ext <;> dsimp <;> ring
  map_smul' c z := by
    apply Prod.ext <;> dsimp <;> ring
  left_inv z := by
    apply Prod.ext <;> dsimp
    · calc
        ((Real.exp (-a) : ℝ) : ℂ) *
            (((Real.exp a : ℝ) : ℂ) * z.1) =
            ((((Real.exp (-a) : ℝ) : ℂ) *
              ((Real.exp a : ℝ) : ℂ)) * z.1) := by ring
        _ = z.1 := by rw [routeR_exp_neg_mul_exp]; simp
    · calc
        ((Real.exp a : ℝ) : ℂ) *
            (((Real.exp (-a) : ℝ) : ℂ) * z.2) =
            ((((Real.exp a : ℝ) : ℂ) *
              ((Real.exp (-a) : ℝ) : ℂ)) * z.2) := by ring
        _ = z.2 := by rw [routeR_exp_mul_exp_neg]; simp
  right_inv z := by
    apply Prod.ext <;> dsimp
    · calc
        ((Real.exp a : ℝ) : ℂ) *
            (((Real.exp (-a) : ℝ) : ℂ) * z.1) =
            ((((Real.exp a : ℝ) : ℂ) *
              ((Real.exp (-a) : ℝ) : ℂ)) * z.1) := by ring
        _ = z.1 := by rw [routeR_exp_mul_exp_neg]; simp
    · calc
        ((Real.exp (-a) : ℝ) : ℂ) *
            (((Real.exp a : ℝ) : ℂ) * z.2) =
            ((((Real.exp (-a) : ℝ) : ℂ) *
              ((Real.exp a : ℝ) : ℂ)) * z.2) := by ring
        _ = z.2 := by rw [routeR_exp_neg_mul_exp]; simp

@[simp] theorem routeRHyperbolicSourceGauge_apply (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicSourceGauge a z =
      (((Real.exp a : ℝ) : ℂ) * z.1,
        ((Real.exp (-a) : ℝ) : ℂ) * z.2) := rfl

@[simp] theorem routeRHyperbolicSourceGauge_zero
    (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicSourceGauge 0 z = z := by
  rcases z with ⟨z, w⟩
  simp

theorem routeRHyperbolicSourceGauge_add (a b : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicSourceGauge (a + b) z =
      routeRHyperbolicSourceGauge a (routeRHyperbolicSourceGauge b z) := by
  rcases z with ⟨z, w⟩
  apply Prod.ext <;> simp only [routeRHyperbolicSourceGauge_apply, Real.exp_add]
  · push_cast
    ring
  · rw [show -(a + b) = -a + -b by ring, Real.exp_add]
    push_cast
    ring

/-- Split Poincare evaluation pairing. -/
def routeRSplitPoincarePairing
    (z w : RouteRHyperbolicSourcePlane) : ℂ :=
  z.1 * w.2 + z.2 * w.1

/-- Alternating double of the two retained orientations. -/
def routeRSplitAlternatingPairing
    (z w : RouteRHyperbolicSourcePlane) : ℂ :=
  z.1 * w.2 - z.2 * w.1

theorem routeRSplitPoincarePairing_gauge (a : ℝ)
    (z w : RouteRHyperbolicSourcePlane) :
    routeRSplitPoincarePairing (routeRHyperbolicSourceGauge a z)
        (routeRHyperbolicSourceGauge a w) =
      routeRSplitPoincarePairing z w := by
  rw [routeRSplitPoincarePairing, routeRSplitPoincarePairing]
  simp only [routeRHyperbolicSourceGauge_apply]
  have hmul := routeR_exp_mul_exp_neg a
  have hmul' := routeR_exp_neg_mul_exp a
  calc
    ((Real.exp a : ℝ) : ℂ) * z.1 *
          (((Real.exp (-a) : ℝ) : ℂ) * w.2) +
        ((Real.exp (-a) : ℝ) : ℂ) * z.2 *
          (((Real.exp a : ℝ) : ℂ) * w.1) =
        ((((Real.exp a : ℝ) : ℂ) * ((Real.exp (-a) : ℝ) : ℂ)) *
          (z.1 * w.2)) +
        ((((Real.exp (-a) : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ)) *
          (z.2 * w.1)) := by ring
    _ = z.1 * w.2 + z.2 * w.1 := by rw [hmul, hmul']; simp

theorem routeRSplitAlternatingPairing_gauge (a : ℝ)
    (z w : RouteRHyperbolicSourcePlane) :
    routeRSplitAlternatingPairing (routeRHyperbolicSourceGauge a z)
        (routeRHyperbolicSourceGauge a w) =
      routeRSplitAlternatingPairing z w := by
  rw [routeRSplitAlternatingPairing, routeRSplitAlternatingPairing]
  simp only [routeRHyperbolicSourceGauge_apply]
  have hmul := routeR_exp_mul_exp_neg a
  have hmul' := routeR_exp_neg_mul_exp a
  calc
    ((Real.exp a : ℝ) : ℂ) * z.1 *
          (((Real.exp (-a) : ℝ) : ℂ) * w.2) -
        ((Real.exp (-a) : ℝ) : ℂ) * z.2 *
          (((Real.exp a : ℝ) : ℂ) * w.1) =
        ((((Real.exp a : ℝ) : ℂ) * ((Real.exp (-a) : ℝ) : ℂ)) *
          (z.1 * w.2)) -
        ((((Real.exp (-a) : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ)) *
          (z.2 * w.1)) := by ring
    _ = z.1 * w.2 - z.2 * w.1 := by rw [hmul, hmul']; simp

def routeRForwardSourceLeg : RouteRHyperbolicSourcePlane := (1, 0)
def routeRReciprocalSourceLeg : RouteRHyperbolicSourcePlane := (0, 1)

theorem routeRHyperbolicSourceGauge_forward (a : ℝ) :
    routeRHyperbolicSourceGauge a routeRForwardSourceLeg =
      (((Real.exp a : ℝ) : ℂ) • routeRForwardSourceLeg) := by
  ext <;> simp [routeRForwardSourceLeg]

theorem routeRHyperbolicSourceGauge_reciprocal (a : ℝ) :
    routeRHyperbolicSourceGauge a routeRReciprocalSourceLeg =
      (((Real.exp (-a) : ℝ) : ℂ) • routeRReciprocalSourceLeg) := by
  ext <;> simp [routeRReciprocalSourceLeg]

/-- Every linear landing natural for all horizontal gauges into one fixed,
trivially gauged physical fibre is zero. -/
theorem routeR_fixedTargetNaturalLanding_eq_zero
    (F : RouteRHyperbolicSourcePlane →ₗ[ℂ] RouteRHyperbolicSourcePlane)
    (hnatural : ∀ a z,
      F (routeRHyperbolicSourceGauge a z) = F z) :
    F = 0 := by
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  have hforward : F routeRForwardSourceLeg = 0 := by
    have h := hnatural (Real.log 2) routeRForwardSourceLeg
    rw [routeRHyperbolicSourceGauge_forward, LinearMap.map_smul, htwo] at h
    have hz : ((2 : ℂ) - 1) • F routeRForwardSourceLeg = 0 := by
      simpa [sub_smul] using sub_eq_zero.mpr h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hreciprocal : F routeRReciprocalSourceLeg = 0 := by
    have h := hnatural (-Real.log 2) routeRReciprocalSourceLeg
    rw [routeRHyperbolicSourceGauge_reciprocal] at h
    have harg : -(-Real.log 2) = Real.log 2 := by ring
    rw [harg, LinearMap.map_smul, htwo] at h
    have hz : ((2 : ℂ) - 1) • F routeRReciprocalSourceLeg = 0 := by
      simpa [sub_smul] using sub_eq_zero.mpr h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply LinearMap.ext
  intro z
  have hdecomp : z = z.1 • routeRForwardSourceLeg +
      z.2 • routeRReciprocalSourceLeg := by
    ext <;> simp [routeRForwardSourceLeg, routeRReciprocalSourceLeg]
  rw [hdecomp, map_add, map_smul, map_smul, hforward, hreciprocal]
  simp

/-- Fixed physical positive polarization on the two retained legs. -/
def routeRFixedPolarEnergy (z : RouteRHyperbolicSourcePlane) : ℝ :=
  Complex.normSq z.1 + Complex.normSq z.2

theorem routeRFixedPolarEnergy_pos {z : RouteRHyperbolicSourcePlane}
    (hz : z ≠ 0) : 0 < routeRFixedPolarEnergy z := by
  rw [routeRFixedPolarEnergy]
  have h : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    contrapose! hz
    exact Prod.ext hz.1 hz.2
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h)
      (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Complex.normSq_pos.mpr h)

/-- Pullback of the fixed physical metric along the inverse gauge. -/
def routeRTransportedPolarEnergy (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) : ℝ :=
  routeRFixedPolarEnergy (routeRHyperbolicSourceGauge (-a) z)

theorem routeRTransportedPolarEnergy_pos (a : ℝ)
    {z : RouteRHyperbolicSourcePlane} (hz : z ≠ 0) :
    0 < routeRTransportedPolarEnergy a z := by
  apply routeRFixedPolarEnergy_pos
  intro hzero
  apply hz
  apply (routeRHyperbolicSourceGauge (-a)).injective
  simpa using hzero

theorem routeRTransportedPolarEnergy_gauge (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    routeRTransportedPolarEnergy a (routeRHyperbolicSourceGauge a z) =
      routeRFixedPolarEnergy z := by
  rw [routeRTransportedPolarEnergy, ← routeRHyperbolicSourceGauge_add]
  simp

/-- A transported positive metric equals the fixed metric for every vector
exactly on the unitary (neutral real-boost) subgroup. -/
theorem routeRTransportedPolarEnergy_eq_fixed_iff (a : ℝ) :
    (∀ z, routeRTransportedPolarEnergy a z = routeRFixedPolarEnergy z) ↔
      a = 0 := by
  constructor
  · intro h
    have hf := h routeRForwardSourceLeg
    rw [routeRTransportedPolarEnergy, routeRFixedPolarEnergy,
      routeRFixedPolarEnergy] at hf
    simp only [routeRHyperbolicSourceGauge_apply, routeRForwardSourceLeg,
      mul_one, mul_zero, Complex.normSq_zero, add_zero,
      Complex.normSq_one] at hf
    rw [Complex.normSq_ofReal] at hf
    have hexp : Real.exp (-a) = 1 := by
      have hp : 0 < Real.exp (-a) := Real.exp_pos _
      nlinarith
    have hneg : -a = 0 := (Real.exp_eq_one_iff (-a)).mp hexp
    linarith
  · rintro rfl
    intro z
    simp [routeRTransportedPolarEnergy]

theorem routeRFixedPolarEnergy_not_gaugeInvariant :
    ¬ ∀ a z, routeRFixedPolarEnergy (routeRHyperbolicSourceGauge a z) =
      routeRFixedPolarEnergy z := by
  intro h
  have ht := h (Real.log 2) routeRForwardSourceLeg
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  simp [routeRFixedPolarEnergy, routeRForwardSourceLeg, htwo] at ht
  norm_num at ht

/-- Actual prime-character orbit in the hyperbolic chart. -/
def routeRPrimeCharacterOrbit (p : ℕ) (a : ℝ) :
    RouteRHyperbolicSourcePlane :=
  routeRHyperbolicSourceGauge (2 * a * Real.log p) routeRForwardSourceLeg

/-- A gauge-invariant predicate is constant on the actual prime-character
orbit and therefore cannot characterize neutral grade. -/
theorem routeR_gaugeInvariantPredicate_not_neutralSelector
    (p : ℕ) (_hp : 1 < p)
    (P : RouteRHyperbolicSourcePlane → Prop)
    (hinv : ∀ a z, P (routeRHyperbolicSourceGauge a z) ↔ P z) :
    ¬ (∀ a, P (routeRPrimeCharacterOrbit p a) ↔ a = 0) := by
  intro hselect
  have hzero : P routeRForwardSourceLeg := by
    have := (hselect 0).2 rfl
    simpa [routeRPrimeCharacterOrbit] using this
  have hone : P (routeRPrimeCharacterOrbit p 1) := by
    exact (hinv (2 * 1 * Real.log p) routeRForwardSourceLeg).2 hzero
  have : (1 : ℝ) = 0 := (hselect 1).1 hone
  norm_num at this

/-- Interface demanded by a fixed-fibre, coefficient-faithful polar landing.
Its target is fixed and carries the ordinary positive metric; horizontal
naturality is required before divisor specialization. -/
structure RouteRFixedNaturalCoefficientFaithfulPolarLanding where
  landing : RouteRHyperbolicSourcePlane →ₗ[ℂ] RouteRHyperbolicSourcePlane
  natural : ∀ a z, landing (routeRHyperbolicSourceGauge a z) = landing z
  forward_nonErased : landing routeRForwardSourceLeg ≠ 0
  reciprocal_nonErased : landing routeRReciprocalSourceLeg ≠ 0
  fixedTargetPositive : ∀ z ≠ 0, 0 < routeRFixedPolarEnergy z

/-- **C33 terminal theorem.** Fixed-target naturality and coefficient
faithfulness on the retained Route-R atom are incompatible. -/
theorem routeR_no_fixedNaturalCoefficientFaithfulPolarLanding :
    ¬ Nonempty RouteRFixedNaturalCoefficientFaithfulPolarLanding := by
  rintro ⟨P⟩
  have hzero := routeR_fixedTargetNaturalLanding_eq_zero P.landing P.natural
  exact P.forward_nonErased (by rw [hzero]; rfl)

/-- Existing fixed-metric Stokes excess is the positive modular square on
the actual labelled source edge.  This packages the analytic part of C33
without reproving it. -/
theorem routeR_actualFixedMetricExcess_eq_modularSquare
    (rho : XiDivisorSupport) :
    primeDepthBVWoldSourcePolarizationStokesExcess
        (primeDepthBVWoldXiCenteredRate rho)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) =
      (primeDepthBVWoldXiCenteredRate rho *
          primeDepthBVWoldConnection primeDepthBVWoldWitnessZero
            primeDepthBVWoldWitnessOne /
          (xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessZero *
            xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessOne)) ^ 2 *
        Complex.normSq
          (iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)) :=
  primeDepthBVWoldSourcePolarizationStokesExcess_eq _ _ _ _

end

end RHTower
