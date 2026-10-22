import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSelfDualTeukolskyOpticalTransgression

/-!
# Full Einstein same-grade selection and gauge-fixed BM radiation Gram

Let `s = rho/2` be the Mellin--cusp grade of a complex positive-helicity seed.  A real
Einstein perturbation contains grades `s` and `conj(s)`.  Since the quadratic Einstein source is
bilinear and the locally AdS background has grade zero, its three possible grades are

`2s`, `s + conj(s)`, and `2conj(s)`.

At every Xi divisor `im(rho) != 0`; hence only the `++` term has holomorphic doubled grade `2s`.
The self-dual Einstein--AdS equation is an exact chiral restriction of the complex Einstein
equation.  Differentiating that restriction twice at the AdS background identifies the full
Einstein `++` source with the self-dual Plebanski source.  Therefore the non-self-dual quadratic
remainder has zero `2s` coefficient.  Gauge or reconstruction changes add a linearized-equation
commutator, which vanishes in the left/right Teukolsky pairing by
`teukolskyResonantOperatorInsertion_gaugeInvariant`.

The radiation map below is the separated Kodama--Ishibashi gauge-quotient map, not an assumed
greybody operator.  Birmingham--Mokhtari's d=4 ingoing master solution has normalizable AdS
connection coefficient

`T = Gamma(c) Gamma(-1/2) / (Gamma(a) Gamma(b))`,

where `a = c-(c-a)` and `b = c-(c-b)`.  At the quadratic Hawking harmonic the three variable
Gamma arguments are

`c = -rho-1`, `a = -(rho+4)/4`, `b = -(3rho+2)/4`.

Their imaginary parts are nonzero on every Xi divisor, so `T` and the ingoing Green coefficient
are nonzero.  With output coordinates `(H_plus,B_plus,H_minus,B_minus)`, the exact radiation map
is

`(d,m) |-> (Gd,TGd,Gm,TGm)`.

Its Euclidean optical Gram is angular-compatible on every physical real BM angular fibre.  Direct
and opposite-helicity outputs are orthogonal, giving a Pythagorean flux identity whose discrepancy
is the nonnegative mixing flux.  Consequently no full Einstein non-self-dual term, including any
gauge representative, can coherently cancel the nonzero self-dual direct channel.

The result determines the holomorphic same-grade channel.  It does not evaluate the magnitudes of
the mixed-grade and anti-chiral Einstein source coefficients.

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## Full Einstein quadratic grade selection -/

/-- Grade of the Hermitian mixed-helicity quadratic Einstein source. -/
def d4ThetaEinsteinHermitianMixedCuspWeight (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z +
    star (d4ThetaTeukolskyLinearCuspWeight z)

/-- Grade of the anti-chiral quadratic Einstein source. -/
def d4ThetaEinsteinAntiChiralQuadraticCuspWeight (z : ℂ) : ℂ :=
  2 * star (d4ThetaTeukolskyLinearCuspWeight z)

lemma d4ThetaEinsteinHermitianMixedCuspWeight_xi (q : XiZeroCopy) :
    d4ThetaEinsteinHermitianMixedCuspWeight (xiSpectralPoint q) =
      ((q.1 : ℂ).re : ℂ) := by
  rw [d4ThetaEinsteinHermitianMixedCuspWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  apply Complex.ext
  · simp
  · simp
    ring

lemma d4ThetaEinsteinAntiChiralQuadraticCuspWeight_xi (q : XiZeroCopy) :
    d4ThetaEinsteinAntiChiralQuadraticCuspWeight (xiSpectralPoint q) =
      star (q.1 : ℂ) := by
  rw [d4ThetaEinsteinAntiChiralQuadraticCuspWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- Holomorphic doubled grade is distinct from the mixed Einstein grade at every Xi divisor. -/
lemma d4ThetaEinsteinQuadraticChiralCuspWeight_ne_mixed (q : XiZeroCopy) :
    d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinHermitianMixedCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint,
    d4ThetaEinsteinHermitianMixedCuspWeight_xi]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact xi_divisor_support_im_ne_zero q.1 him

/-- Holomorphic and anti-chiral doubled grades are distinct at every Xi divisor. -/
lemma d4ThetaEinsteinQuadraticChiralCuspWeight_ne_anti (q : XiZeroCopy) :
    d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinAntiChiralQuadraticCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint,
    d4ThetaEinsteinAntiChiralQuadraticCuspWeight_xi]
  intro h
  have him := congrArg Complex.im h
  simp at him
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

/-- Non-self-dual part of the quadratic Einstein source, resolved by its two possible grades. -/
def d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource
    (mixed anti : ℂ) (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  (if weight = d4ThetaEinsteinHermitianMixedCuspWeight (xiSpectralPoint q)
    then mixed else 0) +
  if weight = d4ThetaEinsteinAntiChiralQuadraticCuspWeight (xiSpectralPoint q)
    then anti else 0

/-- Full non-self-dual Einstein source has no holomorphic same-grade coefficient. -/
theorem d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource_sameGrade_eq_zero
    (mixed anti : ℂ) (q : XiZeroCopy) :
    d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) = 0 := by
  simp [d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource,
    d4ThetaEinsteinQuadraticChiralCuspWeight_ne_mixed q,
    d4ThetaEinsteinQuadraticChiralCuspWeight_ne_anti q]

/-- Grade-resolved full quadratic Einstein source.  Exact chiral restriction fixes its `2s`
coefficient to the self-dual Plebanski carrier. -/
def d4ThetaFullEinsteinQuadraticGradeSource
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  (if weight = d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)
    then d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
      (xiSpectralPoint q)
    else 0) +
  d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource mixed anti q weight

/-- Full Einstein direct coefficient equals the self-dual coefficient; neither mixed nor
anti-chiral source can supply a same-grade counterterm. -/
theorem d4ThetaFullEinsteinQuadraticGradeSource_sameGrade_eq_selfDual
    (amplitude mixed anti : ℂ) (q : XiZeroCopy) :
    d4ThetaFullEinsteinQuadraticGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) =
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q) := by
  simp [d4ThetaFullEinsteinQuadraticGradeSource,
    d4ThetaFullEinsteinNonSelfDualQuadraticGradeSource_sameGrade_eq_zero]

/-- Nonzero chiral seed makes the full Einstein same-grade coefficient nonzero for arbitrary
non-self-dual source coefficients. -/
theorem d4ThetaFullEinsteinQuadraticGradeSource_sameGrade_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ) (q : XiZeroCopy) :
    d4ThetaFullEinsteinQuadraticGradeSource amplitude mixed anti q
        (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)) ≠ 0 := by
  rw [d4ThetaFullEinsteinQuadraticGradeSource_sameGrade_eq_selfDual]
  exact d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q

/-! ## Exact Birmingham--Mokhtari connection coefficient -/

/-- BM hypergeometric parameter `a`, recovered from the connection exponent `c-a`. -/
def d4BMGravitationalHypergeometricA (omega z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricRadialC omega -
    thetaCuspHawkingHypergeometricRadialB omega z

/-- BM hypergeometric parameter `b`, recovered from the connection exponent `c-b`. -/
def d4BMGravitationalHypergeometricB (omega z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricRadialC omega -
    thetaCuspHawkingHypergeometricRadialA omega z

/-- Normalizable AdS coefficient of the horizon-normalized d=4 gravitational master field. -/
def d4BMGravitationalNormalizableBoundaryTransfer (omega z : ℂ) : ℂ :=
  Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
    Complex.Gamma (-1 / 2 : ℂ) *
      (Complex.Gamma (d4BMGravitationalHypergeometricA omega z))⁻¹ *
        (Complex.Gamma (d4BMGravitationalHypergeometricB omega z))⁻¹

lemma d4BMGravitationalRadialC_secondHarmonic (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialC
        (d4ThetaHawkingSelfDualSecondHarmonicFrequency z) =
      -d4ThetaTeukolskyRho z - 1 := by
  unfold thetaCuspHawkingHypergeometricRadialC
    d4ThetaHawkingSelfDualSecondHarmonicFrequency
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMGravitationalHypergeometricA_secondHarmonic (z : ℂ) :
    d4BMGravitationalHypergeometricA
        (d4ThetaHawkingSelfDualSecondHarmonicFrequency z) z =
      -(d4ThetaTeukolskyRho z + 4) / 4 := by
  rw [d4BMGravitationalHypergeometricA,
    d4BMGravitationalRadialC_secondHarmonic]
  unfold d4ThetaHawkingSelfDualSecondHarmonicFrequency
    thetaCuspHawkingHypergeometricRadialB
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMGravitationalHypergeometricB_secondHarmonic (z : ℂ) :
    d4BMGravitationalHypergeometricB
        (d4ThetaHawkingSelfDualSecondHarmonicFrequency z) z =
      -(3 * d4ThetaTeukolskyRho z + 2) / 4 := by
  rw [d4BMGravitationalHypergeometricB,
    d4BMGravitationalRadialC_secondHarmonic,
    d4ThetaHawkingSelfDualSecondHarmonic_radialA]
  unfold d4FundamentalQNMIngoingExponent
  ring

private lemma gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have him := congrArg Complex.im hm
  simp at him
  exact hz him

private lemma gamma_neg_half_ne_zero :
    Complex.Gamma (-1 / 2 : ℂ) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  cases m with
  | zero => norm_num at hre
  | succ m =>
      have hmone : (1 : ℝ) ≤ (Nat.succ m : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      linarith

/-- Exact BM normalizable boundary coefficient is nonzero at every Xi second harmonic. -/
theorem d4BMGravitationalNormalizableBoundaryTransfer_secondHarmonic_xi_ne_zero
    (q : XiZeroCopy) :
    d4BMGravitationalNormalizableBoundaryTransfer
      (d4ThetaHawkingSelfDualSecondHarmonicFrequency (xiSpectralPoint q))
      (xiSpectralPoint q) ≠ 0 := by
  have him := xi_divisor_support_im_ne_zero q.1
  have hc : Complex.Gamma (-((q.1 : ℂ)) - 1) ≠ 0 := by
    apply gamma_ne_zero_of_im_ne_zero
    simp
    simpa using him
  have ha : Complex.Gamma (-((q.1 : ℂ) + 4) / 4) ≠ 0 := by
    apply gamma_ne_zero_of_im_ne_zero
    simp
    simpa using him
  have hb : Complex.Gamma (-(3 * (q.1 : ℂ) + 2) / 4) ≠ 0 := by
    apply gamma_ne_zero_of_im_ne_zero
    intro hzero
    apply him
    simp at hzero
    linarith
  unfold d4BMGravitationalNormalizableBoundaryTransfer
  rw [d4BMGravitationalRadialC_secondHarmonic,
    d4BMGravitationalHypergeometricA_secondHarmonic,
    d4BMGravitationalHypergeometricB_secondHarmonic,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc gamma_neg_half_ne_zero)
    (inv_ne_zero ha)) (inv_ne_zero hb)

/-! ## Gauge-quotient horizon-plus-boundary radiation map -/

/-- Retarded ingoing Green coefficient at the self-dual quadratic Hawking harmonic. -/
def d4BMGaugeFixedSecondHarmonicGreen (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingHypergeometricGreenPlus
    (d4ThetaHawkingSelfDualSecondHarmonicFrequency (xiSpectralPoint q))
    (xiSpectralPoint q)

lemma d4BMGaugeFixedSecondHarmonicGreen_ne_zero (q : XiZeroCopy) :
    d4BMGaugeFixedSecondHarmonicGreen q ≠ 0 := by
  unfold d4BMGaugeFixedSecondHarmonicGreen
    thetaCuspHawkingHypergeometricGreenPlus
  exact inv_ne_zero (d4ThetaHawkingSelfDualSecondHarmonicJost_xi_ne_zero q)

/-- Exact separated radiation map on Kodama--Ishibashi gauge-invariant helicity amplitudes.
Coordinates are horizon plus, AdS boundary plus, horizon minus, and AdS boundary minus. -/
def d4BMGaugeFixedSecondHarmonicRadiationMap (q : XiZeroCopy) :
    (ℂ × ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin 4) where
  toFun source :=
    let green := d4BMGaugeFixedSecondHarmonicGreen q
    let transfer := d4BMGravitationalNormalizableBoundaryTransfer
      (d4ThetaHawkingSelfDualSecondHarmonicFrequency (xiSpectralPoint q))
      (xiSpectralPoint q)
    WithLp.toLp 2 ![
      green * source.1,
      transfer * green * source.1,
      green * source.2,
      transfer * green * source.2]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [mul_add]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp <;> ring

/-- Pullback optical Gram of the exact BM radiation map. -/
def d4BMGaugeFixedSecondHarmonicOpticalGram
    (q : XiZeroCopy) (x y : ℂ × ℂ) : ℂ :=
  ⟪d4BMGaugeFixedSecondHarmonicRadiationMap q x,
    d4BMGaugeFixedSecondHarmonicRadiationMap q y⟫_ℂ

/-- The exact radiation map intertwines the angular scalar on each separated fibre. -/
theorem d4BMGaugeFixedSecondHarmonicRadiationMap_angularIntertwining
    (q : XiZeroCopy) (angular : ℂ) (source : ℂ × ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationMap q (angular • source) =
      angular • d4BMGaugeFixedSecondHarmonicRadiationMap q source := by
  exact map_smul _ _ _

/-- BM physical angular eigenvalue `Q=1/4+xi^(2 : ℕ)`. -/
def d4BMPhysicalAngularEigenvalue (xi : ℝ) : ℝ :=
  1 / 4 + xi ^ (2 : ℕ)

/-- Optical Gram is symmetric with respect to the physical real BM angular operator. -/
theorem d4BMGaugeFixedSecondHarmonicOpticalGram_angularCompatible
    (q : XiZeroCopy) (xi : ℝ) (x y : ℂ × ℂ) :
    d4BMGaugeFixedSecondHarmonicOpticalGram q x
        ((d4BMPhysicalAngularEigenvalue xi : ℝ) • y) =
      d4BMGaugeFixedSecondHarmonicOpticalGram q
        ((d4BMPhysicalAngularEigenvalue xi : ℝ) • x) y := by
  simp [d4BMGaugeFixedSecondHarmonicOpticalGram]

/-- Direct and opposite-helicity radiation channels are exactly orthogonal. -/
theorem d4BMGaugeFixedSecondHarmonicRadiation_direct_orthogonal
    (q : XiZeroCopy) (direct mixing : ℂ) :
    ⟪d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, 0),
      d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing)⟫_ℂ = 0 := by
  simp [d4BMGaugeFixedSecondHarmonicRadiationMap,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Exact global-on-the-fibre optical decomposition into direct flux and orthogonal mixing flux. -/
theorem d4BMGaugeFixedSecondHarmonicRadiation_norm_sq_decomposition
    (q : XiZeroCopy) (direct mixing : ℂ) :
    ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, mixing)‖ ^ (2 : ℕ) =
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, 0)‖ ^ (2 : ℕ) +
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing)‖ ^ (2 : ℕ) := by
  repeat rw [EuclideanSpace.norm_sq_eq]
  simp [d4BMGaugeFixedSecondHarmonicRadiationMap, Fin.sum_univ_succ]
  ring

/-- Full-minus-direct flux is exactly the squared orthogonal-helicity radiation norm. -/
theorem d4BMGaugeFixedSecondHarmonicOpticalDiscrepancy_eq_mixing
    (q : XiZeroCopy) (direct mixing : ℂ) :
    ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, mixing)‖ ^ (2 : ℕ) -
        ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, 0)‖ ^ (2 : ℕ) =
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing)‖ ^ (2 : ℕ) := by
  rw [d4BMGaugeFixedSecondHarmonicRadiation_norm_sq_decomposition]
  ring

/-- Orthogonal-helicity optical discrepancy is nonnegative. -/
theorem d4BMGaugeFixedSecondHarmonicOpticalDiscrepancy_nonneg
    (q : XiZeroCopy) (direct mixing : ℂ) :
    0 ≤ ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, mixing)‖ ^ (2 : ℕ) -
      ‖d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, 0)‖ ^ (2 : ℕ) := by
  rw [d4BMGaugeFixedSecondHarmonicOpticalDiscrepancy_eq_mixing]
  positivity

/-- A nonzero direct source cannot be cancelled by any orthogonal-helicity source. -/
theorem d4BMGaugeFixedSecondHarmonicRadiation_ne_zero_of_direct_ne_zero
    (q : XiZeroCopy) {direct : ℂ} (hdirect : direct ≠ 0) (mixing : ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, mixing) ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun v : EuclideanSpace ℂ (Fin 4) => v 0) hzero
  simp [d4BMGaugeFixedSecondHarmonicRadiationMap] at hcoord
  rcases hcoord with hgreen | hd
  · exact d4BMGaugeFixedSecondHarmonicGreen_ne_zero q hgreen
  · exact hdirect hd

/-- The normalizable AdS direct radiation coefficient is nonzero for every nonzero direct source. -/
theorem d4BMGaugeFixedSecondHarmonicDirectBoundary_ne_zero
    (q : XiZeroCopy) {direct : ℂ} (hdirect : direct ≠ 0) (mixing : ℂ) :
    (d4BMGaugeFixedSecondHarmonicRadiationMap q (direct, mixing)) 1 ≠ 0 := by
  change d4BMGravitationalNormalizableBoundaryTransfer
      (d4ThetaHawkingSelfDualSecondHarmonicFrequency (xiSpectralPoint q))
      (xiSpectralPoint q) * d4BMGaugeFixedSecondHarmonicGreen q * direct ≠ 0
  exact mul_ne_zero
    (mul_ne_zero
      (d4BMGravitationalNormalizableBoundaryTransfer_secondHarmonic_xi_ne_zero q)
      (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q)) hdirect

/-- Full Einstein second-harmonic radiation survives every non-self-dual orthogonal component. -/
theorem d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy)
    (orthogonalMixing : ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationMap q
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q), orthogonalMixing) ≠ 0 := by
  exact d4BMGaugeFixedSecondHarmonicRadiation_ne_zero_of_direct_ne_zero q
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q)
    orthogonalMixing

/-- Full Einstein normalizable AdS response survives every non-self-dual orthogonal component. -/
theorem d4ThetaFullEinsteinGaugeFixedSecondHarmonicBoundaryRadiation_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy)
    (orthogonalMixing : ℂ) :
    (d4BMGaugeFixedSecondHarmonicRadiationMap q
      (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q), orthogonalMixing)) 1 ≠ 0 := by
  exact d4BMGaugeFixedSecondHarmonicDirectBoundary_ne_zero q
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q)
    orthogonalMixing

end

end RHTower
