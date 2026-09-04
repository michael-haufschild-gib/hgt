import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import Mathlib.Tactic

/-!
# The modulus-one Jacobi endpoint of arXiv:2607.21750

The local hyperbolic soliton profiles give a concrete construction of the degenerate Jacobi
functions at parameter `m = 1`: `sn = tanh` and `cn = dn = sech`.  This module certifies their
first-order system, quadratic identities, first integral, Lamé equation, and the identification
of the paper's limiting elastica curvature with its optical NLS soliton density.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def jacobiSnOne (x : ℝ) : ℝ := solitonT x

noncomputable def jacobiCnOne (x : ℝ) : ℝ := solitonA x

noncomputable def jacobiDnOne (x : ℝ) : ℝ := solitonA x

noncomputable def jacobiDnOne1 (x : ℝ) : ℝ :=
  -(jacobiSnOne x * jacobiDnOne x)

/-- The Jacobi identity `sn² + cn² = 1` at `m = 1`. -/
theorem jacobiSnOne_sq_add_jacobiCnOne_sq (x : ℝ) :
    jacobiSnOne x ^ 2 + jacobiCnOne x ^ 2 = 1 := by
  rw [jacobiSnOne, jacobiCnOne, solitonA_sq]
  simp [solitonQ]

/-- The Jacobi identity `dn² + m sn² = 1` at `m = 1`. -/
theorem jacobiDnOne_sq_add_jacobiSnOne_sq (x : ℝ) :
    jacobiDnOne x ^ 2 + jacobiSnOne x ^ 2 = 1 := by
  rw [jacobiDnOne, jacobiSnOne, solitonA_sq]
  simp [solitonQ]

/-- First equation in the Jacobi differential system at `m = 1`. -/
theorem hasDerivAt_jacobiSnOne (x : ℝ) :
    HasDerivAt jacobiSnOne (jacobiCnOne x * jacobiDnOne x) x := by
  change HasDerivAt solitonT (solitonA x * solitonA x) x
  rw [show solitonA x * solitonA x = solitonA x ^ 2 by ring, solitonA_sq]
  exact hasDerivAt_solitonT x

/-- Second equation in the Jacobi differential system at `m = 1`. -/
theorem hasDerivAt_jacobiCnOne (x : ℝ) :
    HasDerivAt jacobiCnOne (-(jacobiSnOne x * jacobiDnOne x)) x := by
  change HasDerivAt solitonA (-(solitonT x * solitonA x)) x
  simpa [solitonA1] using hasDerivAt_solitonA x

/-- Third equation in the Jacobi differential system at `m = 1`. -/
theorem hasDerivAt_jacobiDnOne (x : ℝ) :
    HasDerivAt jacobiDnOne (jacobiDnOne1 x) x := by
  change HasDerivAt solitonA (-(solitonT x * solitonA x)) x
  simpa [solitonA1] using hasDerivAt_solitonA x

/-- The paper's Lamé equation `dn'' = (2m sn² - m)dn` at `m = 1`. -/
theorem hasDerivAt_jacobiDnOne1 (x : ℝ) :
    HasDerivAt jacobiDnOne1
      ((2 * jacobiSnOne x ^ 2 - 1) * jacobiDnOne x) x := by
  have h := hasDerivAt_solitonA1 x
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [jacobiDnOne1, jacobiSnOne, jacobiDnOne, solitonA1]
  · have hid := jacobiDnOne_sq_add_jacobiSnOne_sq x
    simp only [jacobiDnOne, jacobiSnOne, solitonA2] at hid ⊢
    linear_combination -2 * solitonA x * hid

/-- The Jacobi first integral `(sn')² = (1-sn²)(1-m sn²)` at `m = 1`. -/
theorem jacobiSnOne_firstIntegral (x : ℝ) :
    (jacobiCnOne x * jacobiDnOne x) ^ 2 =
      (1 - jacobiSnOne x ^ 2) * (1 - jacobiSnOne x ^ 2) := by
  have hcn := jacobiSnOne_sq_add_jacobiCnOne_sq x
  have hdn := jacobiDnOne_sq_add_jacobiSnOne_sq x
  nlinarith [sq_nonneg (jacobiCnOne x * jacobiDnOne x)]

/-- Standard initial data select the modulus-one Jacobi solution. -/
theorem jacobiOne_initial :
    jacobiSnOne 0 = 0 ∧ jacobiCnOne 0 = 1 ∧ jacobiDnOne 0 = 1 := by
  simp [jacobiSnOne, jacobiCnOne, jacobiDnOne, solitonT, solitonA]

/-- Paper equation (61) specialized to the soliton boundary `m = q₀ = 1`. -/
noncomputable def degenerateJacobiCurvatureSq (k₀ s : ℝ) : ℝ :=
  k₀ ^ 2 * (1 - jacobiSnOne (k₀ * s / 2) ^ 2)

theorem degenerateJacobiCurvatureSq_eq_sech (k₀ s : ℝ) :
    degenerateJacobiCurvatureSq k₀ s =
      (k₀ * jacobiDnOne (k₀ * s / 2)) ^ 2 := by
  rw [degenerateJacobiCurvatureSq]
  have h := jacobiDnOne_sq_add_jacobiSnOne_sq (k₀ * s / 2)
  nlinarith

/-- The optical envelope is exactly the modulus-one Jacobi curvature profile. -/
theorem opticalEnvelope_eq_degenerateJacobiCurvature (D k t x : ℝ) :
    envelope D k 0 t x = 2 * k * jacobiDnOne (k * x) := by
  simp [envelope, envelopeCoordinate, jacobiDnOne]

/-- Optical NLS mass density equals the squared limiting elastica curvature. -/
theorem opticalSoliton_normSq_eq_degenerateJacobiCurvatureSq (D k t x : ℝ) :
    ‖opticalSoliton D k t x‖ ^ 2 = degenerateJacobiCurvatureSq (2 * k) x := by
  rw [opticalSoliton, norm_envelopeSoliton_sq,
    opticalEnvelope_eq_degenerateJacobiCurvature]
  rw [degenerateJacobiCurvatureSq_eq_sech]
  congr 1
  ring_nf

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
