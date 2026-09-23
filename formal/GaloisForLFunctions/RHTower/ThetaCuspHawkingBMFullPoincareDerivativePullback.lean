import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMKIVectorChiralReconstruction
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Full denominator-cleared Poincare derivative pullback

The inverse-radius chart used previously leaves square roots and coordinate nonvanishing premises
in the inverse Jacobian.  Introduce the global rapidity variable

`rho = sech xi`, `sqrt(1-rho^(2 : ℕ)) = tanh xi`.

The Rindler--AdS/Poincare chart becomes

`T = sigma tanh(xi) sinh(tau)`,
`Y = sigma tanh(xi) cosh(tau)`,
`Z = sigma sech(xi)`, `X = x`.

Instead of dividing at the degenerate chart edge, use the exact scaled coordinate fields

`sigma tanh(xi) partial_T`, `sigma tanh(xi) partial_Y`,
`sigma sech(xi) partial_Z`.

Their BM coefficients are globally defined and this module proves, without hypotheses, that they
diagonalize the full chart Jacobian.  Algebraic inverse-scale variables then give the unscaled
Poincare `T,Y,Z,X` jets and the genuine light-cone `u,w` kinematic bracket on arbitrary BM first
jets.  This removes the incorrect fixed-Poincare-momentum shortcut for BM separated modes.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [FULL INVERSE JACOBIAN]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Algebraic `sech`, written using mathlib's everywhere-nonzero hyperbolic cosine. -/
def d4BMRindlerRapiditySech (xi : ℝ) : ℝ :=
  (Real.cosh xi)⁻¹

/-- Poincare time in the rapidity chart. -/
def d4BMRindlerRapidityToPoincareTime (tau xi sigma : ℝ) : ℝ :=
  sigma * Real.tanh xi * Real.sinh tau

/-- Poincare horizon-transverse coordinate in the rapidity chart. -/
def d4BMRindlerRapidityToPoincareHorizonY (tau xi sigma : ℝ) : ℝ :=
  sigma * Real.tanh xi * Real.cosh tau

/-- Poincare radial coordinate in the rapidity chart. -/
def d4BMRindlerRapidityToPoincareRadial (xi sigma : ℝ) : ℝ :=
  sigma * d4BMRindlerRapiditySech xi

/-- Global Pythagorean identity for the rapidity chart. -/
theorem d4BMRindlerRapidity_tanh_sq_add_sech_sq (xi : ℝ) :
    Real.tanh xi ^ (2 : ℕ) + d4BMRindlerRapiditySech xi ^ (2 : ℕ) = 1 := by
  rw [d4BMRindlerRapiditySech, inv_pow]
  have h := HTGeometry.one_sub_tanh_sq xi
  rw [one_div] at h
  nlinarith

/-- Value and four first BM-coordinate derivatives of a scalar leg. -/
structure D4BMFullFirstJet where
  value : ℂ
  tau : ℂ
  horizonX : ℂ
  sigma : ℂ
  xi : ℂ

/-- Denominator-cleared pullback of `partial_T`, scaled by `sigma*tanh(xi)`. -/
def d4ScaledPoincareTimeDerivativeOnBMFirstJet
    (tau xi sigma : ℝ) (J : D4BMFullFirstJet) : ℂ :=
  (Real.cosh tau : ℂ) * J.tau -
    (sigma * Real.tanh xi ^ (2 : ℕ) * Real.sinh tau : ℝ) * J.sigma -
    (Real.tanh xi * Real.sinh tau : ℝ) * J.xi

/-- Denominator-cleared pullback of `partial_Y`, scaled by `sigma*tanh(xi)`. -/
def d4ScaledPoincareHorizonYDerivativeOnBMFirstJet
    (tau xi sigma : ℝ) (J : D4BMFullFirstJet) : ℂ :=
  -(Real.sinh tau : ℂ) * J.tau +
    (sigma * Real.tanh xi ^ (2 : ℕ) * Real.cosh tau : ℝ) * J.sigma +
    (Real.tanh xi * Real.cosh tau : ℝ) * J.xi

/-- Denominator-cleared pullback of `partial_Z`, scaled by `sigma*sech(xi)`. -/
def d4ScaledPoincareRadialDerivativeOnBMFullFirstJet
    (xi sigma : ℝ) (J : D4BMFullFirstJet) : ℂ :=
  (sigma * d4BMRindlerRapiditySech xi ^ (2 : ℕ) : ℝ) * J.sigma -
    (Real.tanh xi : ℂ) * J.xi

/-- BM first jet of the chart coordinate `T`. -/
def d4BMRindlerRapidityPoincareTimeFirstJet
    (tau xi sigma : ℝ) : D4BMFullFirstJet where
  value := d4BMRindlerRapidityToPoincareTime tau xi sigma
  tau := sigma * Real.tanh xi * Real.cosh tau
  horizonX := 0
  sigma := Real.tanh xi * Real.sinh tau
  xi := sigma * d4BMRindlerRapiditySech xi ^ (2 : ℕ) * Real.sinh tau

/-- BM first jet of the chart coordinate `Y`. -/
def d4BMRindlerRapidityPoincareHorizonYFirstJet
    (tau xi sigma : ℝ) : D4BMFullFirstJet where
  value := d4BMRindlerRapidityToPoincareHorizonY tau xi sigma
  tau := sigma * Real.tanh xi * Real.sinh tau
  horizonX := 0
  sigma := Real.tanh xi * Real.cosh tau
  xi := sigma * d4BMRindlerRapiditySech xi ^ (2 : ℕ) * Real.cosh tau

/-- BM first jet of the chart coordinate `Z`. -/
def d4BMRindlerRapidityPoincareRadialFirstJet
    (xi sigma : ℝ) : D4BMFullFirstJet where
  value := d4BMRindlerRapidityToPoincareRadial xi sigma
  tau := 0
  horizonX := 0
  sigma := d4BMRindlerRapiditySech xi
  xi := -sigma * d4BMRindlerRapiditySech xi * Real.tanh xi

/-- The scaled `T` field acts diagonally on all three nontrivial Poincare chart coordinates. -/
theorem d4ScaledPoincareTimeDerivative_is_coordinateVector
    (tau xi sigma : ℝ) :
    d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareTimeFirstJet tau xi sigma) =
          (sigma * Real.tanh xi : ℝ) ∧
      d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareHorizonYFirstJet tau xi sigma) = 0 ∧
      d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareRadialFirstJet xi sigma) = 0 := by
  have hpyth := d4BMRindlerRapidity_tanh_sq_add_sech_sq xi
  have hlorentz := Real.cosh_sq_sub_sinh_sq tau
  constructor
  · simp only [d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareTimeFirstJet]
    norm_cast
    linear_combination
      (sigma * Real.tanh xi) * hlorentz -
        (sigma * Real.tanh xi * Real.sinh tau ^ (2 : ℕ)) * hpyth
  constructor
  · simp only [d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareHorizonYFirstJet]
    norm_cast
    linear_combination
      -(sigma * Real.tanh xi * Real.sinh tau * Real.cosh tau) * hpyth
  · simp only [d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareRadialFirstJet]
    norm_cast
    ring

/-- The scaled `Y` field acts diagonally on the full chart. -/
theorem d4ScaledPoincareHorizonYDerivative_is_coordinateVector
    (tau xi sigma : ℝ) :
    d4ScaledPoincareHorizonYDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareTimeFirstJet tau xi sigma) = 0 ∧
      d4ScaledPoincareHorizonYDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareHorizonYFirstJet tau xi sigma) =
          (sigma * Real.tanh xi : ℝ) ∧
      d4ScaledPoincareHorizonYDerivativeOnBMFirstJet tau xi sigma
        (d4BMRindlerRapidityPoincareRadialFirstJet xi sigma) = 0 := by
  have hpyth := d4BMRindlerRapidity_tanh_sq_add_sech_sq xi
  have hlorentz := Real.cosh_sq_sub_sinh_sq tau
  constructor
  · simp only [d4ScaledPoincareHorizonYDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareTimeFirstJet]
    norm_cast
    linear_combination
      (sigma * Real.tanh xi * Real.sinh tau * Real.cosh tau) * hpyth
  constructor
  · simp only [d4ScaledPoincareHorizonYDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareHorizonYFirstJet]
    norm_cast
    linear_combination
      (sigma * Real.tanh xi) * hlorentz +
        (sigma * Real.tanh xi * Real.cosh tau ^ (2 : ℕ)) * hpyth
  · simp only [d4ScaledPoincareHorizonYDerivativeOnBMFirstJet,
      d4BMRindlerRapidityPoincareRadialFirstJet]
    norm_cast
    ring

/-- The scaled `Z` field acts diagonally on the full chart. -/
theorem d4ScaledPoincareRadialDerivative_is_coordinateVector
    (tau xi sigma : ℝ) :
    d4ScaledPoincareRadialDerivativeOnBMFullFirstJet xi sigma
        (d4BMRindlerRapidityPoincareTimeFirstJet tau xi sigma) = 0 ∧
      d4ScaledPoincareRadialDerivativeOnBMFullFirstJet xi sigma
        (d4BMRindlerRapidityPoincareHorizonYFirstJet tau xi sigma) = 0 ∧
      d4ScaledPoincareRadialDerivativeOnBMFullFirstJet xi sigma
        (d4BMRindlerRapidityPoincareRadialFirstJet xi sigma) =
          (sigma * d4BMRindlerRapiditySech xi : ℝ) := by
  have hpyth := d4BMRindlerRapidity_tanh_sq_add_sech_sq xi
  constructor
  · simp only [d4ScaledPoincareRadialDerivativeOnBMFullFirstJet,
      d4BMRindlerRapidityPoincareTimeFirstJet]
    norm_cast
    ring
  constructor
  · simp only [d4ScaledPoincareRadialDerivativeOnBMFullFirstJet,
      d4BMRindlerRapidityPoincareHorizonYFirstJet]
    norm_cast
    ring
  · simp only [d4ScaledPoincareRadialDerivativeOnBMFullFirstJet,
      d4BMRindlerRapidityPoincareRadialFirstJet]
    norm_cast
    linear_combination
      (sigma * d4BMRindlerRapiditySech xi) * hpyth

/-- Poincare-coordinate first jet obtained from a BM first jet.  The two inverse-scale variables
are algebraic, so the definition is total at chart edges. -/
structure D4PoincareFullFirstJet where
  value : ℂ
  T : ℂ
  X : ℂ
  Y : ℂ
  Z : ℂ

/-- Full algebraic inverse-Jacobian action on a BM first jet. -/
def d4PoincareFullFirstJetOfBMInv
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (J : D4BMFullFirstJet) : D4PoincareFullFirstJet where
  value := J.value
  T := timeScaleInv * d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma J
  X := J.horizonX
  Y := timeScaleInv * d4ScaledPoincareHorizonYDerivativeOnBMFirstJet tau xi sigma J
  Z := radialScaleInv * d4ScaledPoincareRadialDerivativeOnBMFullFirstJet xi sigma J

/-- Poincare light-cone `partial_u = (partial_T+partial_Z)/2`. -/
def d4PoincareLightConeUDerivative (J : D4PoincareFullFirstJet) : ℂ :=
  (J.T + J.Z) / 2

/-- Complex transverse derivative `partial_w = (partial_X-i partial_Y)/2`. -/
def d4PoincareLightConeWDerivative (J : D4PoincareFullFirstJet) : ℂ :=
  (J.X - Complex.I * J.Y) / 2

/-- Coordinate-space self-dual kinematic bracket on two arbitrary BM first jets after the full
inverse-Jacobian pullback. -/
def ads4SelfDualKinematicBracketOnBMFullFirstJets
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (P Q : D4BMFullFirstJet) : ℂ :=
  let p := d4PoincareFullFirstJetOfBMInv timeScaleInv radialScaleInv tau xi sigma P
  let q := d4PoincareFullFirstJetOfBMInv timeScaleInv radialScaleInv tau xi sigma Q
  d4PoincareLightConeUDerivative p * d4PoincareLightConeWDerivative q -
    d4PoincareLightConeWDerivative p * d4PoincareLightConeUDerivative q

/-- The full chart-pulled coordinate bracket is alternating under leg exchange. -/
theorem ads4SelfDualKinematicBracketOnBMFullFirstJets_exchange
    (timeScaleInv radialScaleInv : ℂ) (tau xi sigma : ℝ)
    (P Q : D4BMFullFirstJet) :
    ads4SelfDualKinematicBracketOnBMFullFirstJets
        timeScaleInv radialScaleInv tau xi sigma Q P =
      -ads4SelfDualKinematicBracketOnBMFullFirstJets
        timeScaleInv radialScaleInv tau xi sigma P Q := by
  simp [ads4SelfDualKinematicBracketOnBMFullFirstJets]
  ring

/-- Compatibility with the existing momentum-space bracket: Poincare eigenjets factor the
coordinate-space bracket into `X(p,h;q,k)` times the product of leg values. -/
theorem ads4SelfDualKinematicBracketOnPoincareEigenjets
    (p h q k P Q : ℂ) :
    p * P * (k * Q) - h * P * (q * Q) =
      ads4SelfDualKinematicBracket p h q k * P * Q := by
  simp [ads4SelfDualKinematicBracket]
  ring

/-- Normalized pure BM time-eigenjet.  `frequency` is its logarithmic `tau` derivative. -/
def d4BMNormalizedPureTimeEigenFirstJet (frequency : ℂ) : D4BMFullFirstJet where
  value := 1
  tau := frequency
  horizonX := 0
  sigma := 0
  xi := 0

/-- Sharp fixed-momentum classification.  A normalized BM time eigenmode has one constant
Poincare-`T` eigencharge across the hyperbolic scale exactly when its BM frequency is zero. -/
theorem exists_fixedPoincareTimeCharge_for_BMTimeEigenJet_iff
    (frequency : ℂ) :
    (∃ qT : ℂ, ∀ tau xi sigma : ℝ,
      d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma
          (d4BMNormalizedPureTimeEigenFirstJet frequency) =
        (sigma * Real.tanh xi : ℝ) * qT) ↔ frequency = 0 := by
  constructor
  · rintro ⟨qT, hqT⟩
    have h1 := hqT 0 1 1
    have h2 := hqT 0 1 2
    norm_num [d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4BMNormalizedPureTimeEigenFirstJet] at h1 h2
    have hdouble : frequency = 2 * frequency := by
      calc
        frequency = 2 * Complex.tanh 1 * qT := h2
        _ = 2 * frequency := by rw [h1]; ring
    have hneg : -frequency = 0 := by
      calc
        -frequency = frequency - 2 * frequency := by ring
        _ = 0 := sub_eq_zero.mpr hdouble
    exact neg_eq_zero.mp hneg
  · intro hfrequency
    subst frequency
    refine ⟨0, ?_⟩
    intro tau xi sigma
    simp [d4ScaledPoincareTimeDerivativeOnBMFirstJet,
      d4BMNormalizedPureTimeEigenFirstJet]

/-- Every actual positive-branch Xi QNM has nonzero BM time frequency. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMPlus_xi_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q) ≠ 0 := by
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hstrip
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdamped :
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus
        n (xiSpectralPoint q)).im < 0 := by
    rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus_im,
      thetaCuspHawkingTopologicalBlackHoleConformalDecay]
    norm_num at hstrip ⊢
    linarith
  intro hzero
  have him := congrArg Complex.im hzero
  simp at him
  linarith

/-- Physical route killer: no actual Xi QNM can be treated as a single fixed-Poincare-momentum
leg throughout a BM hyperbolic fibre. -/
theorem not_exists_fixedPoincareTimeCharge_for_BMXiQNM
    (n : ℕ) (q : XiZeroCopy) :
    ¬ ∃ qT : ℂ, ∀ tau xi sigma : ℝ,
      d4ScaledPoincareTimeDerivativeOnBMFirstJet tau xi sigma
          (d4BMNormalizedPureTimeEigenFirstJet
            (-Complex.I *
              thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))) =
        (sigma * Real.tanh xi : ℝ) * qT := by
  intro hcharge
  have hzero :=
    (exists_fixedPoincareTimeCharge_for_BMTimeEigenJet_iff
      (-Complex.I *
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))).1 hcharge
  exact (thetaCuspHawkingTopologicalBlackHoleQNMPlus_xi_ne_zero n q)
    ((mul_eq_zero.mp hzero).resolve_left (by simp))

end

end RHTower
