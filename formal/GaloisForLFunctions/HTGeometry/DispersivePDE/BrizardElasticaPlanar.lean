import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Open planar elastica consequences

The paper's torsionless walls and midpoint-angle claims are audited.  The `q₀ = 1` wall has
negative squared speed throughout the classical modulus range.  The admissible `q₀ = m` wall has
nonnegative squared speed exactly through `m = 1/2`.  The printed one-argument arctangent formula
collapses to zero at that endpoint; a complex argument (the two-argument angle) restores `π/2`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Admissible classical moduli for the paper's planar traveling branch `q₀ = m`. -/
abbrev PlanarTravelingModulus := Set.Ioc (0 : ℝ) (1 / 2)

noncomputable def planarTorsionlessParameters (m : PlanarTravelingModulus) : Parameters where
  modulus := m
  q₀ := Units.mk0 (m : ℝ) (ne_of_gt m.property.1)

@[simp] theorem planarTorsionlessParameters_modulus (m : PlanarTravelingModulus) :
    (planarTorsionlessParameters m).modulus = (m : ℝ) := rfl

@[simp] theorem planarTorsionlessParameters_q₀ (m : PlanarTravelingModulus) :
    ((planarTorsionlessParameters m).q₀ : ℝ) = (m : ℝ) := rfl

theorem planarTorsionless_nuSq (m : PlanarTravelingModulus) :
    nuSq (planarTorsionlessParameters m) = 0 := by
  rw [nuSq]
  simp only [planarTorsionlessParameters_modulus, planarTorsionlessParameters_q₀, sub_self,
    mul_zero, zero_div]

/-- Squared-speed formula in the paper's admissible planar branch. -/
theorem planarTorsionless_gammaSq (m : PlanarTravelingModulus) :
    gammaSq (planarTorsionlessParameters m) = 1 / (m : ℝ) - 2 := by
  rw [gammaSq]
  simp only [planarTorsionlessParameters_modulus, planarTorsionlessParameters_q₀]
  field_simp [ne_of_gt m.property.1]
  ring

theorem planarTorsionless_gammaSq_nonneg (m : PlanarTravelingModulus) :
    0 ≤ gammaSq (planarTorsionlessParameters m) := by
  rw [planarTorsionless_gammaSq, sub_nonneg, le_div_iff₀ m.property.1]
  linarith [m.property.2]

theorem planarTorsionless_gammaSq_eq_zero_iff (m : PlanarTravelingModulus) :
    gammaSq (planarTorsionlessParameters m) = 0 ↔ (m : ℝ) = 1 / 2 := by
  rw [planarTorsionless_gammaSq]
  have hm : (m : ℝ) ≠ 0 := ne_of_gt m.property.1
  constructor
  · intro h
    field_simp [hm] at h
    linarith
  · intro h
    rw [h]
    norm_num

noncomputable def planarGamma (m : PlanarTravelingModulus) : ℝ :=
  Real.sqrt (gammaSq (planarTorsionlessParameters m))

theorem planarGamma_sq (m : PlanarTravelingModulus) :
    planarGamma m ^ 2 = gammaSq (planarTorsionlessParameters m) := by
  rw [planarGamma, Real.sq_sqrt (planarTorsionless_gammaSq_nonneg m)]

noncomputable def quarterPlanarModulus : PlanarTravelingModulus :=
  ⟨1 / 4, by norm_num⟩

noncomputable def halfPlanarModulus : PlanarTravelingModulus :=
  ⟨1 / 2, by norm_num⟩

theorem quarterPlanar_gammaSq :
    gammaSq (planarTorsionlessParameters quarterPlanarModulus) = 2 := by
  rw [planarTorsionless_gammaSq]
  norm_num [quarterPlanarModulus]

theorem halfPlanar_gammaSq :
    gammaSq (planarTorsionlessParameters halfPlanarModulus) = 0 := by
  rw [planarTorsionless_gammaSq]
  norm_num [halfPlanarModulus]

/-- The other torsionless wall `q₀ = 1`, defined across the classical modulus range. -/
noncomputable def unitTorsionlessParameters (m : ClassicalModulus) : Parameters where
  modulus := m
  q₀ := 1

@[simp] theorem unitTorsionlessParameters_modulus (m : ClassicalModulus) :
    (unitTorsionlessParameters m).modulus = (m : ℝ) := rfl

@[simp] theorem unitTorsionlessParameters_q₀ (m : ClassicalModulus) :
    ((unitTorsionlessParameters m).q₀ : ℝ) = 1 := rfl

theorem unitTorsionless_nuSq (m : ClassicalModulus) :
    nuSq (unitTorsionlessParameters m) = 0 := by
  simp only [nuSq, unitTorsionlessParameters_modulus, unitTorsionlessParameters_q₀,
    sub_self, zero_mul, zero_div]

/-- The paper's `q₀ = 1` branch has no real traveling speed for `0 < m < 1`. -/
theorem unitTorsionless_gammaSq_neg (m : ClassicalModulus) :
    gammaSq (unitTorsionlessParameters m) < 0 := by
  rw [gammaSq]
  simp only [unitTorsionlessParameters_modulus, unitTorsionlessParameters_q₀,
    div_one]
  linarith [m.property.2]

theorem unitTorsionless_no_real_speed (m : ClassicalModulus) :
    ¬ ∃ γ : ℝ, gammaSq (unitTorsionlessParameters m) = γ ^ 2 := by
  rintro ⟨γ, hγ⟩
  have hnonneg : 0 ≤ gammaSq (unitTorsionlessParameters m) := by
    rw [hγ]
    exact sq_nonneg γ
  exact (not_le_of_gt (unitTorsionless_gammaSq_neg m)) hnonneg

/-- Literal one-argument arctangent printed in the planar appendix. -/
noncomputable def printedPlanarMidpointAngle (m : ℝ) : ℝ :=
  Real.arctan (2 * Real.sqrt (m * (1 - m)) / (1 - 2 * m))

/-- Two-argument angle encoded as a complex argument; defined at the vertical endpoint. -/
noncomputable def planarMidpointDirection (m : ℝ) : ℂ :=
  ((1 - 2 * m : ℝ) : ℂ) +
    Complex.I * ((2 * Real.sqrt (m * (1 - m)) : ℝ) : ℂ)

noncomputable def planarMidpointAngle (m : ℝ) : ℝ :=
  Complex.arg (planarMidpointDirection m)

theorem printedPlanarMidpointAngle_half : printedPlanarMidpointAngle (1 / 2) = 0 := by
  norm_num [printedPlanarMidpointAngle]

/-- At `m=1/2`, the literal printed formula disagrees with the paper's claimed `π/2`. -/
theorem printedPlanarMidpointAngle_half_ne_pi_div_two :
    printedPlanarMidpointAngle (1 / 2) ≠ Real.pi / 2 := by
  rw [printedPlanarMidpointAngle_half]
  positivity

theorem planarMidpointAngle_nonneg (m : PlanarTravelingModulus) :
    0 ≤ planarMidpointAngle m := by
  rw [planarMidpointAngle, Complex.arg_nonneg_iff]
  simp only [planarMidpointDirection, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul, Complex.ofReal_re,
    zero_add]
  positivity

theorem planarMidpointAngle_le_pi_div_two (m : PlanarTravelingModulus) :
    planarMidpointAngle m ≤ Real.pi / 2 := by
  rw [planarMidpointAngle, Complex.arg_le_pi_div_two_iff]
  left
  simp only [planarMidpointDirection, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im]
  linarith [m.property.2]

theorem planarMidpointAngle_half : planarMidpointAngle (1 / 2) = Real.pi / 2 := by
  rw [planarMidpointAngle, Complex.arg_eq_pi_div_two_iff]
  constructor <;> norm_num [planarMidpointDirection]

theorem printedPlanarMidpointAngle_quarter :
    printedPlanarMidpointAngle (1 / 4) = Real.pi / 3 := by
  rw [printedPlanarMidpointAngle]
  rw [show 2 * Real.sqrt ((1 / 4 : ℝ) * (1 - 1 / 4)) / (1 - 2 * (1 / 4 : ℝ)) =
      Real.sqrt 3 by
    have hs : Real.sqrt 3 ^ 2 = 3 := by norm_num
    have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    norm_num at hs ⊢
    nlinarith]
  exact Real.arctan_sqrt_three

theorem planarMidpointDirection_quarter : planarMidpointDirection (1 / 4) =
    (Real.cos (Real.pi / 3) : ℂ) + (Real.sin (Real.pi / 3) : ℂ) * Complex.I := by
  apply Complex.ext
  · norm_num [planarMidpointDirection, Real.cos_pi_div_three]
  · simp only [planarMidpointDirection, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, zero_mul, Complex.I_im, one_mul, Complex.ofReal_re,
      Real.sin_pi_div_three]
    have hs : Real.sqrt 3 ^ 2 = 3 := by norm_num
    have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    norm_num at hs ⊢
    nlinarith

theorem planarMidpointAngle_quarter : planarMidpointAngle (1 / 4) = Real.pi / 3 := by
  rw [planarMidpointAngle, planarMidpointDirection_quarter,
    Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I (θ := Real.pi / 3)
    ⟨by nlinarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
