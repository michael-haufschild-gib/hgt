import GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow
import Mathlib.Analysis.SpecialFunctions.Sigmoid

set_option autoImplicit false

/-!
# Conservative–dissipative fermi laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

namespace RHTower
noncomputable section

/-- The reflected Fermi information potential in an unconstrained real coordinate. -/
def schafferExlFermiEnergy (u : ℝ) : ℝ :=
  fzzCigarParityReflectedFermiInformationWork (Real.sigmoid u)

/-- Actual gradient after the sigmoid coordinate change, including its Jacobian factor. -/
def schafferExlFermiForce (u : ℝ) : ℝ :=
  fzzCigarParityReflectedFermiInformationForce (Real.sigmoid u) *
    (Real.sigmoid u * (1 - Real.sigmoid u))


theorem hasDerivAt_schafferExlFermiEnergy (u : ℝ) :
    HasDerivAt schafferExlFermiEnergy (schafferExlFermiForce u) u := by
  have h := (hasDerivAt_fzzCigarParityReflectedFermiInformationWork
    (Real.sigmoid_pos u) (Real.sigmoid_lt_one u)).comp u (Real.hasDerivAt_sigmoid u)
  convert h using 1 <;> rfl

/-- The unique stationary point is the sigmoid image of the critical center. -/
theorem schafferExlFermiForce_eq_zero_iff (u : ℝ) : schafferExlFermiForce u = 0 ↔ u = 0 := by
  have hpos : 0 < Real.sigmoid u * (1 - Real.sigmoid u) :=
    mul_pos (Real.sigmoid_pos u) (sub_pos.mpr (Real.sigmoid_lt_one u))
  rw [schafferExlFermiForce, mul_eq_zero]
  simp only [ne_of_gt hpos, or_false]
  rw [fzzCigarParityReflectedFermiInformationForce_eq_zero_iff
    (Real.sigmoid_pos u) (Real.sigmoid_lt_one u)]
  have hz : Real.sigmoid 0 = (1 / 2 : ℝ) := by simp
  rw [← hz, Real.sigmoid_inj]

/-- Two Fermi sources coupled by conservative exchange and independent unit damping. -/
def schafferExlFermiPairField (w u v : ℝ) : ℝ × ℝ :=
  (-schafferExlFermiForce u - w * schafferExlFermiForce v,
    w * schafferExlFermiForce u - schafferExlFermiForce v)

/-- Conservative exchange does not change the exact sum-of-squares loss. -/
theorem schafferExlFermiPair_power (w u v : ℝ) :
    schafferExlFermiForce u * (schafferExlFermiPairField w u v).1 +
      schafferExlFermiForce v * (schafferExlFermiPairField w u v).2 =
      -(schafferExlFermiForce u) ^ 2 - (schafferExlFermiForce v) ^ 2 := by
  simp only [schafferExlFermiPairField]
  ring

/-- Actual directional derivative of the coupled information potential. -/
theorem hasDerivAt_schafferExlFermiPairEnergy (w u v : ℝ) :
    HasDerivAt
      (fun t => schafferExlFermiEnergy (u + t * (schafferExlFermiPairField w u v).1) +
        schafferExlFermiEnergy (v + t * (schafferExlFermiPairField w u v).2))
      (-(schafferExlFermiForce u) ^ 2 - (schafferExlFermiForce v) ^ 2) 0 := by
  have hu : HasDerivAt (fun t => u + t * (schafferExlFermiPairField w u v).1)
      (schafferExlFermiPairField w u v).1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (schafferExlFermiPairField w u v).1).const_add u
  have hv : HasDerivAt (fun t => v + t * (schafferExlFermiPairField w u v).2)
      (schafferExlFermiPairField w u v).2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (schafferExlFermiPairField w u v).2).const_add v
  have h := ((hasDerivAt_schafferExlFermiEnergy (u + 0 * (schafferExlFermiPairField w u v).1)).comp 0 hu).add
    ((hasDerivAt_schafferExlFermiEnergy (v + 0 * (schafferExlFermiPairField w u v).2)).comp 0 hv)
  simp only [zero_mul, add_zero, schafferExlFermiPair_power] at h
  convert h using 1 <;> rfl

/-- The coupled system has exactly one equilibrium for every conservative coupling strength. -/
theorem schafferExlFermiPair_equilibrium_iff (w u v : ℝ) :
    schafferExlFermiPairField w u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hp := schafferExlFermiPair_power w u v
    rw [h] at hp
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at hp
    have hu : schafferExlFermiForce u = 0 := by nlinarith [sq_nonneg (schafferExlFermiForce v)]
    have hv : schafferExlFermiForce v = 0 := by nlinarith [sq_nonneg (schafferExlFermiForce u)]
    exact ⟨(schafferExlFermiForce_eq_zero_iff u).mp hu, (schafferExlFermiForce_eq_zero_iff v).mp hv⟩
  · rintro ⟨rfl, rfl⟩
    simp [schafferExlFermiPairField, (schafferExlFermiForce_eq_zero_iff 0).mpr rfl]

end
end RHTower
