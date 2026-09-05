import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSystem
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Concrete Jacobi endpoint systems

The general Jacobi interface is realized at `m=0` by `(sin,cos,1)` and at `m=1` by the hyperbolic
`(tanh,sech,sech)` triple already constructed in the corpus.  The latter endpoint also exposes a
parameter-reality obstruction: at `m=q₀=1`, the paper's reconstructed `γ²` is `-1`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Trigonometric Jacobi degeneration at modulus zero. -/
noncomputable def jacobiZeroSystem : JacobiEllipticSystem 0 where
  sn := Real.sin
  cn := Real.cos
  dn := fun _ => 1
  sn_deriv := fun x => by simpa using Real.hasDerivAt_sin x
  cn_deriv := fun x => by simpa using Real.hasDerivAt_cos x
  dn_deriv := fun x => by simpa using hasDerivAt_const x (1 : ℝ)
  sn_sq_add_cn_sq := Real.sin_sq_add_cos_sq
  dn_sq_add_m_sn_sq := fun x => by simp
  sn_zero := by simp
  cn_zero := by simp
  dn_zero := rfl

/-- Hyperbolic Jacobi degeneration at modulus one. -/
noncomputable def jacobiOneSystem : JacobiEllipticSystem 1 where
  sn := jacobiSnOne
  cn := jacobiCnOne
  dn := jacobiDnOne
  sn_deriv := hasDerivAt_jacobiSnOne
  cn_deriv := hasDerivAt_jacobiCnOne
  dn_deriv := fun x => by
    simpa [jacobiDnOne1, jacobiCnOne, jacobiDnOne] using hasDerivAt_jacobiDnOne x
  sn_sq_add_cn_sq := jacobiSnOne_sq_add_jacobiCnOne_sq
  dn_sq_add_m_sn_sq := fun x => by
    simpa [add_comm] using jacobiDnOne_sq_add_jacobiSnOne_sq x
  sn_zero := jacobiOne_initial.1
  cn_zero := jacobiOne_initial.2.1
  dn_zero := jacobiOne_initial.2.2

noncomputable def zeroModulusParameters (q₀ : ℝˣ) : Parameters :=
  ⟨0, q₀⟩

noncomputable def oneUnitParameters : Parameters :=
  ⟨1, 1⟩

theorem zeroJacobiSquaredCurvature_eq (q₀ : ℝˣ) (v : ℝ) :
    jacobiSquaredCurvature (zeroModulusParameters q₀) jacobiZeroSystem v =
      (q₀ : ℝ) := by
  simp [jacobiSquaredCurvature, zeroModulusParameters]

theorem zeroJacobiSquaredCurvatureVelocity_eq (q₀ : ℝˣ) (v : ℝ) :
    jacobiSquaredCurvatureVelocity (zeroModulusParameters q₀) jacobiZeroSystem v = 0 := by
  simp [jacobiSquaredCurvatureVelocity, zeroModulusParameters]

theorem zeroJacobiSquaredCurvature_equation (q₀ : ℝˣ) (v : ℝ) :
    jacobiSquaredCurvatureVelocity (zeroModulusParameters q₀) jacobiZeroSystem v ^ 2 =
      dimensionlessCurvatureRHSWithSquares (q₀ : ℝ)
        (gammaSq (zeroModulusParameters q₀)) (nuSq (zeroModulusParameters q₀))
        (jacobiSquaredCurvature (zeroModulusParameters q₀) jacobiZeroSystem v) := by
  exact jacobiSquaredCurvature_equation (zeroModulusParameters q₀) jacobiZeroSystem v

theorem oneJacobiSquaredCurvature_eq (v : ℝ) :
    jacobiSquaredCurvature oneUnitParameters jacobiOneSystem v = jacobiDnOne v ^ 2 := by
  rw [jacobiSquaredCurvature]
  simp only [oneUnitParameters, jacobiOneSystem, Units.val_one, one_mul]
  have h := jacobiDnOne_sq_add_jacobiSnOne_sq v
  nlinarith

theorem oneUnitParameters_gammaSq : gammaSq oneUnitParameters = -1 := by
  rw [gammaSq, oneUnitParameters]
  norm_num

theorem oneUnitParameters_nuSq : nuSq oneUnitParameters = 0 := by
  rw [nuSq, oneUnitParameters]
  norm_num

/-- The modulus-one, unit-scale endpoint has no real wave-speed parameter. -/
theorem oneUnitParameters_no_real_gamma :
    ¬ ∃ γ : ℝ, γ ^ 2 = gammaSq oneUnitParameters := by
  rw [oneUnitParameters_gammaSq]
  rintro ⟨γ, hγ⟩
  nlinarith [sq_nonneg γ]

theorem oneJacobiSquaredCurvature_equation (v : ℝ) :
    jacobiSquaredCurvatureVelocity oneUnitParameters jacobiOneSystem v ^ 2 =
      dimensionlessCurvatureRHSWithSquares 1 (-1) 0 (jacobiDnOne v ^ 2) := by
  have h := jacobiSquaredCurvature_equation oneUnitParameters jacobiOneSystem v
  rw [oneUnitParameters_gammaSq, oneUnitParameters_nuSq,
    oneJacobiSquaredCurvature_eq] at h
  exact h

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
