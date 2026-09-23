import GaloisForLFunctions.HTGeometry.GaussianCramerRaoOrderLaws

/-!
# Squeezed-bath diffusion and Gaussian estimation

The bath coefficients in arXiv:2606.25061, Eqs. (4), (7), and (17), have
an exact positive quadratic-form decomposition. The same diffusion weights
appear in the corpus's Gaussian displacement-estimation formulas.
-/

noncomputable section
namespace HTGeometry

/-- Local thermal occupation induced by two-mode squeezing. -/
def coppoBathOccupation (r : ℝ) : ℝ := Real.sinh r ^ (2 : ℕ)

/-- Correlated bath amplitude for real squeezing. -/
def coppoBathCorrelation (r : ℝ) : ℝ := Real.sinh r * Real.cosh r

/-- Diffusion of the enhanced collective coordinate. -/
def coppoDiffusionPlus (gamma r : ℝ) : ℝ := gamma * Real.exp (2 * r)

/-- Diffusion of the suppressed collective coordinate. -/
def coppoDiffusionMinus (gamma r : ℝ) : ℝ := gamma * Real.exp (-2 * r)

/-- Squeezed vacuum saturates the occupation-correlation identity. -/
theorem coppoBathCorrelation_sq (r : ℝ) :
    coppoBathCorrelation r ^ (2 : ℕ) = coppoBathOccupation r * (coppoBathOccupation r + 1) := by
  have h := Real.cosh_sq_sub_sinh_sq r
  dsimp [coppoBathCorrelation, coppoBathOccupation]
  nlinarith [sq_nonneg (Real.sinh r ^ (2 : ℕ))]

/-- The bath covariance determinant is independent of squeezing. -/
theorem coppoBathCovariance_det (r : ℝ) :
    (coppoBathOccupation r + 1 / 2) ^ (2 : ℕ) - coppoBathCorrelation r ^ (2 : ℕ) = 1 / 4 := by
  rw [coppoBathCorrelation_sq]; ring

/-- The positive collective diffusion is the sum of thermal and correlation contributions. -/
theorem coppoDiffusionPlus_eq_bath (gamma r : ℝ) :
    coppoDiffusionPlus gamma r = gamma * (1 + 2 * coppoBathOccupation r + 2 * coppoBathCorrelation r) := by
  dsimp [coppoDiffusionPlus, coppoBathOccupation, coppoBathCorrelation]
  rw [show 2 * r = r + r by ring, Real.exp_add, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp
  ring

/-- The negative collective diffusion is the thermal contribution minus the correlation. -/
theorem coppoDiffusionMinus_eq_bath (gamma r : ℝ) :
    coppoDiffusionMinus gamma r = gamma * (1 + 2 * coppoBathOccupation r - 2 * coppoBathCorrelation r) := by
  dsimp [coppoDiffusionMinus, coppoBathOccupation, coppoBathCorrelation]
  rw [show -2 * r = -(r + r) by ring, Real.exp_neg, Real.exp_add, Real.cosh_eq,
    Real.sinh_eq, Real.exp_neg]
  field_simp
  ring

/-- Squeezing redistributes diffusion but preserves its product. -/
theorem coppoDiffusion_product (gamma r : ℝ) :
    coppoDiffusionPlus gamma r * coppoDiffusionMinus gamma r = gamma ^ (2 : ℕ) := by
  dsimp [coppoDiffusionPlus, coppoDiffusionMinus]
  rw [show -2 * r = -(2 * r) by ring, Real.exp_neg]
  field_simp

/-- The ratio of collective timescales is the fourth-power squeezing exponential. -/
theorem coppoDiffusion_ratio (g r : ℝ) :
    coppoDiffusionPlus (Real.exp g) r / coppoDiffusionMinus (Real.exp g) r = Real.exp (4 * r) := by
  dsimp [coppoDiffusionPlus, coppoDiffusionMinus]
  rw [show 4 * r = 2 * r - (-2 * r) by ring, Real.exp_sub]
  field_simp

/-- The real covariance quadratic form in the two local coordinates. -/
def coppoBathQuadratic (r x y : ℝ) : ℝ :=
  (coppoBathOccupation r + 1 / 2) * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) - 2 * coppoBathCorrelation r * x * y

/-- Orthogonal collective coordinates diagonalize the bath exactly. -/
theorem coppoBathQuadratic_squares (r x y : ℝ) :
    coppoBathQuadratic r x y =
      (coppoDiffusionPlus 1 r * (x - y) ^ (2 : ℕ) + coppoDiffusionMinus 1 r * (x + y) ^ (2 : ℕ)) / 4 := by
  rw [coppoDiffusionPlus_eq_bath, coppoDiffusionMinus_eq_bath]
  dsimp [coppoBathQuadratic]; ring

/-- The bath covariance is positive for every squeezing strength. -/
theorem coppoBathQuadratic_nonneg (r x y : ℝ) : 0 ≤ coppoBathQuadratic r x y := by
  rw [coppoBathQuadratic_squares]
  dsimp [coppoDiffusionPlus, coppoDiffusionMinus]
  positivity

/-- The covariance has no nontrivial null direction at finite squeezing. -/
theorem coppoBathQuadratic_zero_iff (r x y : ℝ) :
    coppoBathQuadratic r x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    rw [coppoBathQuadratic_squares] at h
    dsimp [coppoDiffusionPlus, coppoDiffusionMinus] at h
    have hp := Real.exp_pos (2 * r)
    have hm := Real.exp_pos (-2 * r)
    have hx : (x - y) ^ (2 : ℕ) = 0 := by
      nlinarith [sq_nonneg (x - y), mul_nonneg hm.le (sq_nonneg (x + y))]
    have hy : (x + y) ^ (2 : ℕ) = 0 := by
      nlinarith [sq_nonneg (x + y), mul_nonneg hp.le (sq_nonneg (x - y))]
    constructor <;> nlinarith [sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy]
  · rintro ⟨rfl, rfl⟩; simp [coppoBathQuadratic]

/-- The corpus's displacement bound is thermal baseline plus collective-diffusion cost. -/
theorem displacedSqueezedSLDCRB_eq_coppoBath (r x y : ℝ) :
    displacedSqueezedSLDCRB r 0 x y = 1 + coppoBathOccupation r +
      (coppoDiffusionPlus 1 r * x ^ (2 : ℕ) + coppoDiffusionMinus 1 r * y ^ (2 : ℕ)) / 2 := by
  dsimp [displacedSqueezedSLDCRB, coppoBathOccupation, coppoDiffusionPlus, coppoDiffusionMinus]
  rw [add_zero]
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

/-- Displacement estimation always pays at least the local thermal baseline. -/
theorem coppoBath_thermal_floor_SLDCRB (r x y : ℝ) :
    1 + coppoBathOccupation r ≤ displacedSqueezedSLDCRB r 0 x y := by
  rw [displacedSqueezedSLDCRB_eq_coppoBath]
  have h : 0 ≤ (coppoDiffusionPlus 1 r * x ^ (2 : ℕ) + coppoDiffusionMinus 1 r * y ^ (2 : ℕ)) / 2 := by
    dsimp [coppoDiffusionPlus, coppoDiffusionMinus]; positivity
  linarith

/-- The alternate probe order adds squeezing before applying exactly the same bath cost. -/
theorem squeezedCoherentSLDCRB_eq_coppoBath (r xi x y : ℝ) :
    squeezedCoherentSLDCRB r xi x y = 1 + coppoBathOccupation (r + xi) +
      (coppoDiffusionPlus 1 (r + xi) * x ^ (2 : ℕ) + coppoDiffusionMinus 1 (r + xi) * y ^ (2 : ℕ)) / 2 := by
  have h := displacedSqueezedSLDCRB_eq_coppoBath (r + xi) x y
  simpa only [squeezedCoherentSLDCRB, displacedSqueezedSLDCRB, add_zero] using h

end HTGeometry
