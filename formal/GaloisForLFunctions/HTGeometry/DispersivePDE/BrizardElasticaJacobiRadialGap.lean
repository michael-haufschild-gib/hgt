import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitudeDynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAngularCubic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Jacobi profile stays inside the cylindrical chart

For physical region I, the corrected Jacobi curvature amplitude lies strictly above the angular
floor `Ω²` at every point.  The proof exposes a new exact square factor in the minimum gap and
therefore certifies the square root used by the paper's radial solution globally.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def physicalRegionIAngularParameters
    (P : PhysicalRegionI) : AngularPhysicalParameters :=
  ⟨P.val, (physicalRegionI_gammaSq_pos P).le,
    (physicalRegionI_nuSq_pos P).le⟩

/-- Exact reserve between the minimum Jacobi amplitude and the angular floor. -/
theorem lowerJacobiAmplitudeSq_sub_angularOmegaSq
    (P : AngularPhysicalParameters) :
    (1 - P.val.modulus / (P.val.q₀ : ℝ)) - angularOmegaSq P =
      ((P.val.q₀ : ℝ) - P.val.modulus) *
          (1 - P.val.modulus - (P.val.q₀ : ℝ)) ^ (2 : ℕ) /
        ((P.val.q₀ : ℝ) ^ (3 : ℕ) *
          ((2 + gammaSq P.val) ^ (2 : ℕ) + 4 * nuSq P.val)) := by
  rw [angularOmegaSq]
  field_simp [ne_of_gt (angularOmegaSq_den_pos P)]
  rw [gammaSq, nuSq]
  field_simp [P.val.q₀.ne_zero]
  ring

theorem physicalRegionI_lowerJacobiAmplitude_gap_pos
    (P : PhysicalRegionI) :
    angularOmegaSq (physicalRegionIAngularParameters P) <
      1 - P.val.modulus / (P.val.q₀ : ℝ) := by
  have hb := physicalRegionI_bounds P
  have hsum : 0 < 1 - P.val.modulus - (P.val.q₀ : ℝ) := by
    linarith [hb.2.1, hb.2.2.2]
  have hden := angularOmegaSq_den_pos (physicalRegionIAngularParameters P)
  have hfactor := lowerJacobiAmplitudeSq_sub_angularOmegaSq
    (physicalRegionIAngularParameters P)
  rw [show (physicalRegionIAngularParameters P).val = P.val by rfl] at hfactor
  rw [← sub_pos] at ⊢
  rw [hfactor]
  exact div_pos
    (mul_pos (sub_pos.2 P.property.2.1) (sq_pos_of_pos hsum))
    (mul_pos (pow_pos P.property.1 3) hden)

/-- The paper's radial square-root radicand is strictly positive along every region-I profile. -/
theorem physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < correctedJacobiAmplitude P J v ^ (2 : ℕ) -
      angularOmegaSq (physicalRegionIAngularParameters P) := by
  have hlower := physicalRegionI_lowerJacobiAmplitude_gap_pos P
  have hA := correctedJacobiAmplitude_sq P J v
  by_cases hm : 0 ≤ P.val.modulus
  · have hterm :
        0 ≤ P.val.modulus / (P.val.q₀ : ℝ) * (1 - J.sn v ^ (2 : ℕ)) :=
      mul_nonneg (div_nonneg hm P.property.1.le)
        (sub_nonneg.2 (J.sn_sq_le_one v))
    nlinarith
  · have hmneg : P.val.modulus < 0 := lt_of_not_ge hm
    have hterm :
        P.val.modulus / (P.val.q₀ : ℝ) * J.sn v ^ (2 : ℕ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg hmneg.le P.property.1.le)
        (sq_nonneg (J.sn v))
    have hOmega := angularOmegaSq_lt_one (physicalRegionIAngularParameters P)
    nlinarith

noncomputable def jacobiRadialAmplitude
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  Real.sqrt (correctedJacobiAmplitude P J v ^ (2 : ℕ) -
    angularOmegaSq (physicalRegionIAngularParameters P))

theorem jacobiRadialAmplitude_pos
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    0 < jacobiRadialAmplitude P J v := by
  rw [jacobiRadialAmplitude]
  exact Real.sqrt_pos.2
    (physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos P J v)

theorem jacobiRadialAmplitude_sq
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    jacobiRadialAmplitude P J v ^ (2 : ℕ) =
      (1 - angularOmegaSq (physicalRegionIAngularParameters P)) -
        P.val.modulus / (P.val.q₀ : ℝ) * J.sn v ^ (2 : ℕ) := by
  rw [jacobiRadialAmplitude,
    Real.sq_sqrt
      (physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos P J v).le,
    correctedJacobiAmplitude_sq]
  ring

noncomputable def jacobiRadialAmplitudeVelocity
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) : ℝ :=
  correctedJacobiAmplitude P J v * correctedJacobiAmplitudeVelocity P J v /
    jacobiRadialAmplitude P J v

theorem jacobiRadialAmplitude_hasDerivAt
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus) (v : ℝ) :
    HasDerivAt (jacobiRadialAmplitude P J)
      (jacobiRadialAmplitudeVelocity P J v) v := by
  have hA := correctedJacobiAmplitude_hasDerivAt P J v
  have hsq := hA.fun_pow 2
  norm_num at hsq
  have hgap := hsq.sub_const
    (angularOmegaSq (physicalRegionIAngularParameters P))
  have hsqrt := HasDerivAt.sqrt hgap
    (ne_of_gt
      (physicalRegionI_correctedAmplitude_sq_sub_angularOmegaSq_pos P J v))
  have hderiv :
      (2 * correctedJacobiAmplitude P J v *
          correctedJacobiAmplitudeVelocity P J v) /
          (2 * Real.sqrt
            (correctedJacobiAmplitude P J v ^ (2 : ℕ) -
              angularOmegaSq (physicalRegionIAngularParameters P))) =
        jacobiRadialAmplitudeVelocity P J v := by
    rw [jacobiRadialAmplitudeVelocity, jacobiRadialAmplitude]
    field_simp [ne_of_gt (jacobiRadialAmplitude_pos P J v)]
  change HasDerivAt
    (fun y => Real.sqrt (correctedJacobiAmplitude P J y ^ (2 : ℕ) -
      angularOmegaSq (physicalRegionIAngularParameters P)))
    (jacobiRadialAmplitudeVelocity P J v) v
  exact hsqrt.congr_deriv hderiv

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
