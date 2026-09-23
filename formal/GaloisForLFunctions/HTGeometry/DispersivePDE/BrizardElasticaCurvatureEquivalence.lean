import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaLemniscaticClosure
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Curvature-functional equivalence

The paper's final appendix claims invariance of normalized total curvature under the
negative-to-classical Jacobi transformation.  The identity is proved first for every positive
classical scale and its forced negative-side partner, then specialized to the closure graph and to
the exact pair `m=-1 ↔ n=1/2`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Scale paired with `q` by maximum-curvature normalization. -/
noncomputable def transportedNegativeCurvatureScale
    (m : NegativeModulus) (q : ℝ) : ℝ :=
  (m : ℝ) + (1 - (m : ℝ)) * q

/-- Paper equation (B2) in the negative-modulus normalization. -/
noncomputable def normalizedNegativeCurvatureFunctional
    (m : NegativeModulus) (q : ℝ) : ℝ :=
  2 / Real.sqrt (q - (m : ℝ)) *
    (completeEllipticE m - (1 - q) * completeEllipticK m)

/-- Paper equation (B2) in the classical-modulus normalization. -/
noncomputable def normalizedClassicalCurvatureFunctional
    (n : ClassicalModulus) (q : ℝ) : ℝ :=
  2 / Real.sqrt q *
    (completeEllipticE n - (1 - q) * completeEllipticK n)

theorem transportedNegativeCurvatureScale_sub_modulus
    (m : NegativeModulus) (q : ℝ) :
    transportedNegativeCurvatureScale m q - (m : ℝ) = (1 - (m : ℝ)) * q := by
  rw [transportedNegativeCurvatureScale]
  ring

/-- Strong scale-parametric form of the appendix's curvature equivalence. -/
theorem normalizedCurvatureFunctional_transport
    (m : NegativeModulus) (q : PositiveCurvatureScale) :
    normalizedNegativeCurvatureFunctional m (transportedNegativeCurvatureScale m q) =
      normalizedClassicalCurvatureFunctional (extendedToClassical m) q := by
  have hm0 : (m : ℝ) < 0 := m.property
  have hm : 0 < 1 - (m : ℝ) := by linarith
  have hq : 0 < (q : ℝ) := q.property
  have hs : Real.sqrt (1 - (m : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  have hsq : Real.sqrt (q : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hs2 : Real.sqrt (1 - (m : ℝ)) ^ (2 : ℕ) = 1 - (m : ℝ) :=
    Real.sq_sqrt hm.le
  rw [normalizedNegativeCurvatureFunctional, normalizedClassicalCurvatureFunctional,
    transportedNegativeCurvatureScale_sub_modulus,
    completeEllipticE_negative_transform_raw, completeEllipticK_negative_transform_raw,
    Real.sqrt_mul hm.le]
  rw [transportedNegativeCurvatureScale]
  field_simp [hs, hsq]
  rw [hs2]
  ring

/-- Closure scales themselves obey the same affine pairing law. -/
theorem closureQ_curvatureScale_transport (m : NegativeModulus) :
    closureQ m = transportedNegativeCurvatureScale m (closureQ (extendedToClassical m)) := by
  have hm0 : (m : ℝ) < 0 := m.property
  have hm : 1 - (m : ℝ) ≠ 0 := by linarith
  have hK : completeEllipticK (extendedToClassical m) ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos (extendedToClassical m))
  rw [closureQ, closureQ, transportedNegativeCurvatureScale,
    completeEllipticE_negative_transform_raw, completeEllipticK_negative_transform_raw,
    extendedToClassical]
  have hs : Real.sqrt (1 - (m : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by linarith)
  have hs2 : Real.sqrt (1 - (m : ℝ)) ^ (2 : ℕ) = 1 - (m : ℝ) := by
    rw [Real.sq_sqrt]
    linarith
  field_simp [hm, hK, hs]
  rw [hs2]
  ring

noncomputable def normalizedClosureCurvatureNegative (m : NegativeModulus) : ℝ :=
  normalizedNegativeCurvatureFunctional m (closureQ m)

noncomputable def normalizedClosureCurvatureClassical (n : ClassicalModulus) : ℝ :=
  normalizedClassicalCurvatureFunctional n (closureQ n)

/-- Appendix modulus symmetry on the exact vertical-closure graph. -/
theorem normalizedClosureCurvature_transport (m : NegativeModulus) :
    normalizedClosureCurvatureNegative m =
      normalizedClosureCurvatureClassical (extendedToClassical m) := by
  let q : PositiveCurvatureScale :=
    ⟨closureQ (extendedToClassical m), closureQ_classical_pos (extendedToClassical m)⟩
  have h := normalizedCurvatureFunctional_transport m q
  rw [normalizedClosureCurvatureNegative, normalizedClosureCurvatureClassical,
    closureQ_curvatureScale_transport]
  exact h

/-- Exact, non-numerical version of the paper's `m=-1` and `m=1/2` example. -/
theorem normalizedClosureCurvature_negativeOne_eq_half :
    normalizedClosureCurvatureNegative negativeOneModulus =
      normalizedClosureCurvatureClassical halfClassicalModulus := by
  rw [← negativeOne_to_halfClassical]
  exact normalizedClosureCurvature_transport negativeOneModulus

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
