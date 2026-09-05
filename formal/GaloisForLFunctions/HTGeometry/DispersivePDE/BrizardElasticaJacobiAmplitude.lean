import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSystem
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Tactic

/-!
# Correct Jacobi amplitude in physical region I

The elastica amplitude is `sqrt(q/q₀)` with `q=q₀-m sn²`, not `dn`.  Region-I inequalities and
the Jacobi quadratic identities make this square root globally real and strictly positive.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem JacobiEllipticSystem.sn_sq_le_one
    {m : ℝ} (J : JacobiEllipticSystem m) (v : ℝ) :
    J.sn v ^ 2 ≤ 1 := by
  nlinarith [J.sn_sq_add_cn_sq v, sq_nonneg (J.cn v)]

theorem physicalRegionI_jacobiSquaredCurvature_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < jacobiSquaredCurvature P.val J v := by
  rw [jacobiSquaredCurvature]
  have hsn0 := sq_nonneg (J.sn v)
  have hsn1 := J.sn_sq_le_one v
  by_cases hm : 0 ≤ P.val.modulus
  · have hmq := P.property.2.1
    nlinarith
  · have hmneg : P.val.modulus < 0 := lt_of_not_ge hm
    nlinarith [P.property.1]

theorem physicalRegionI_jacobiCurvatureRatio_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < jacobiSquaredCurvature P.val J v / (P.val.q₀ : ℝ) :=
  div_pos (physicalRegionI_jacobiSquaredCurvature_pos P J v) P.property.1

/-- Correct normalized elastica amplitude. -/
noncomputable def correctedJacobiAmplitude
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  Real.sqrt (jacobiSquaredCurvature P.val J v / (P.val.q₀ : ℝ))

theorem correctedJacobiAmplitude_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < correctedJacobiAmplitude P J v := by
  rw [correctedJacobiAmplitude]
  exact Real.sqrt_pos.2 (physicalRegionI_jacobiCurvatureRatio_pos P J v)

theorem correctedJacobiAmplitude_sq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    correctedJacobiAmplitude P J v ^ 2 =
      1 - P.val.modulus / (P.val.q₀ : ℝ) * J.sn v ^ 2 := by
  rw [correctedJacobiAmplitude,
    Real.sq_sqrt (le_of_lt (physicalRegionI_jacobiCurvatureRatio_pos P J v)),
    jacobiSquaredCurvature]
  field_simp [P.val.q₀.ne_zero]

theorem correctedJacobiAmplitude_zero
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) :
    correctedJacobiAmplitude P J 0 = 1 := by
  have hsq := correctedJacobiAmplitude_sq P J 0
  rw [J.sn_zero] at hsq
  have hpos := correctedJacobiAmplitude_pos P J 0
  nlinarith

/-- Difference between correct squared amplitude and printed `dn²`. -/
theorem correctedJacobiAmplitude_sq_sub_dnSq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    correctedJacobiAmplitude P J v ^ 2 - J.dn v ^ 2 =
      P.val.modulus * ((P.val.q₀ : ℝ) - 1) /
        (P.val.q₀ : ℝ) * J.sn v ^ 2 := by
  rw [correctedJacobiAmplitude_sq]
  have hdn := J.dn_sq_add_m_sn_sq v
  have hq : (P.val.q₀ : ℝ) ≠ 0 := P.val.q₀.ne_zero
  field_simp [hq]
  linear_combination (-(P.val.q₀ : ℝ)) * hdn

/-- Positive physical curvature scale, packaged without theorem-side hypotheses. -/
abbrev PositiveCurvatureScale := {k : ℝ // 0 < k}

noncomputable def correctedJacobiCurvature
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  (k₀ : ℝ) * correctedJacobiAmplitude P J v

theorem correctedJacobiCurvature_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < correctedJacobiCurvature k₀ P J v :=
  mul_pos k₀.property (correctedJacobiAmplitude_pos P J v)

/-- Paper equation (68), with the correct positive square-root branch. -/
theorem correctedJacobiCurvature_sq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    correctedJacobiCurvature k₀ P J v ^ 2 =
      (k₀ : ℝ) ^ 2 *
        (1 - P.val.modulus / (P.val.q₀ : ℝ) * J.sn v ^ 2) := by
  rw [correctedJacobiCurvature, mul_pow, correctedJacobiAmplitude_sq]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
