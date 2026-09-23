import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaEllipticIntegralPositivity
import Mathlib.Tactic

/-!
# Closed-knot elliptic closure function

Section VI and Appendix A of arXiv:2607.21750 use
`Q(m)=2 E(m)/K(m)-(1-m)` to impose zero vertical drift.  The integral infrastructure now makes
`Q` an actual defined function.  We prove its negative-to-classical transformation and the exact
equivalence between an extended zero of `Q` and the paper's classical torsionless equation.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Paper equations (91) and (A7), the vertical-period closure scale. -/
noncomputable def closureQ (m : ℝ) : ℝ :=
  2 * completeEllipticE m / completeEllipticK m - (1 - m)

/-- The transformed expression in paper equation (A8). -/
noncomputable def classicalClosureCore (n : ClassicalModulus) : ℝ :=
  2 * completeEllipticE n / completeEllipticK n - 1

theorem closureQ_zero : closureQ 0 = 1 := by
  rw [closureQ, completeEllipticK_zero, completeEllipticE_zero]
  field_simp [Real.pi_ne_zero]
  ring

/-- Paper equation (A8), now derived from the defining interval integrals. -/
theorem closureQ_negative_transform (m : NegativeModulus) :
    closureQ m =
      (1 - (extendedToClassical m : ℝ))⁻¹ *
        classicalClosureCore (extendedToClassical m) := by
  have hm0 : (m : ℝ) < 0 := m.property
  have hs : Real.sqrt (1 - (m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith [hm0]))
  have hK : completeEllipticK (extendedToClassical m) ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos (extendedToClassical m))
  rw [closureQ, classicalClosureCore, completeEllipticK_negative_transform_raw,
    completeEllipticE_negative_transform_raw, transformedComplement]
  have hs2 : Real.sqrt (1 - (m : ℝ)) ^ (2 : ℕ) = 1 - (m : ℝ) :=
    Real.sq_sqrt (by linarith [hm0])
  field_simp [hs, hK, ne_of_gt (show 0 < 1 - (m : ℝ) by linarith [hm0])]
  rw [hs2]
  ring

theorem classicalClosureCore_eq_zero_iff (n : ClassicalModulus) :
    classicalClosureCore n = 0 ↔
      2 * completeEllipticE n = completeEllipticK n := by
  have hK : completeEllipticK n ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos n)
  rw [classicalClosureCore]
  constructor
  · intro h
    field_simp [hK] at h
    linarith
  · intro h
    field_simp [hK]
    linarith

/-- An extended closure zero is exactly a classical `2E=K` point. -/
theorem closureQ_negative_eq_zero_iff (m : NegativeModulus) :
    closureQ m = 0 ↔
      2 * completeEllipticE (extendedToClassical m) =
        completeEllipticK (extendedToClassical m) := by
  rw [closureQ_negative_transform]
  have hn : 1 - (extendedToClassical m : ℝ) ≠ 0 := by
    linarith [(extendedToClassical m).property.2]
  rw [mul_eq_zero, inv_eq_zero, classicalClosureCore_eq_zero_iff]
  simp [hn]

/-- For a classical parameter, the same `2E=K` equation is exactly `Q(n)=n`. -/
theorem closureQ_classical_eq_modulus_iff (n : ClassicalModulus) :
    closureQ n = (n : ℝ) ↔
      2 * completeEllipticE n = completeEllipticK n := by
  have hK : completeEllipticK n ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos n)
  rw [closureQ]
  constructor
  · intro h
    field_simp [hK] at h
    linarith
  · intro h
    field_simp [hK]
    linarith

/-- Paper's extended knot-closure zero and classical torsionless point are the same orbit. -/
theorem closureQ_negative_zero_iff_classical_torsionless (m : NegativeModulus) :
    closureQ m = 0 ↔
      closureQ (extendedToClassical m) = (extendedToClassical m : ℝ) := by
  rw [closureQ_negative_eq_zero_iff, closureQ_classical_eq_modulus_iff]

theorem closureQ_negative_pos_iff (m : NegativeModulus) :
    0 < closureQ m ↔ 0 < classicalClosureCore (extendedToClassical m) := by
  rw [closureQ_negative_transform]
  exact mul_pos_iff_of_pos_left
    (inv_pos.mpr (sub_pos.mpr (extendedToClassical m).property.2))

theorem closureQ_negative_neg_iff (m : NegativeModulus) :
    closureQ m < 0 ↔ classicalClosureCore (extendedToClassical m) < 0 := by
  rw [closureQ_negative_transform]
  have hpos : 0 < (1 - (extendedToClassical m : ℝ))⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (extendedToClassical m).property.2)
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hgood | hbad
    · exact hgood.2
    · exact False.elim (not_lt_of_ge hpos.le hbad.1)
  · exact mul_neg_of_pos_of_neg hpos

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
