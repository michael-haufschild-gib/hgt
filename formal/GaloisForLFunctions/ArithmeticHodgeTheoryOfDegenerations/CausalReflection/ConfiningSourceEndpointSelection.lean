import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundEnergyCurvature
import GaloisForLFunctions.HTGeometry.Thermodynamics.EndpointSourceSwitch

/-!
# Endpoint selection for the arithmetic confinement energy

Subtracting a linear external control preserves the strict concavity of
the actual half-line ground energy. Thus comparison across a closed
positive confinement interval reduces to its endpoints, with no interior
minimizer. The source-response jump equals the interval width.

This is the endpoint-selection mechanism of arXiv:2611.16364, section 4,
applied to the arithmetic variational floor.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.HTGeometry.Thermodynamics

def confiningSourceEnergy (z t : ℝ) : ℝ := confiningHalfLineGroundEnergy t - z * t

/-- Every interval value lies above an endpoint; equality is possible only at an endpoint. -/
theorem confiningSourceEnergy_endpoint_bound (u v z : ℝ) :
    ∀ t ∈ Icc (Real.exp u) (Real.exp u + Real.exp v),
      min (confiningSourceEnergy z (Real.exp u))
        (confiningSourceEnergy z (Real.exp u + Real.exp v)) ≤ confiningSourceEnergy z t ∧
      (min (confiningSourceEnergy z (Real.exp u))
        (confiningSourceEnergy z (Real.exp u + Real.exp v)) = confiningSourceEnergy z t →
          t = Real.exp u ∨ t = Real.exp u + Real.exp v) := by
  intro t ht
  by_cases ha : t = Real.exp u
  · subst t
    exact ⟨min_le_left _ _, fun _ => Or.inl rfl⟩
  by_cases hb : t = Real.exp u + Real.exp v
  · subst t
    exact ⟨min_le_right _ _, fun _ => Or.inr rfl⟩
  have hta : Real.exp u < t := lt_of_le_of_ne ht.1 (Ne.symm ha)
  have htb : t < Real.exp u + Real.exp v := lt_of_le_of_ne ht.2 hb
  have hα : 0 < (Real.exp u + Real.exp v - t) / Real.exp v :=
    div_pos (sub_pos.mpr htb) (Real.exp_pos v)
  have hβ : 0 < (t - Real.exp u) / Real.exp v :=
    div_pos (sub_pos.mpr hta) (Real.exp_pos v)
  have hsum : (Real.exp u + Real.exp v - t) / Real.exp v +
      (t - Real.exp u) / Real.exp v = 1 := by field_simp; ring
  have hpoint : (Real.exp u + Real.exp v - t) / Real.exp v * Real.exp u +
      (t - Real.exp u) / Real.exp v * (Real.exp u + Real.exp v) = t := by
    field_simp
    <;> ring
  have hj := confiningHalfLineGroundEnergy_strict_jensen (Real.exp_pos u)
    (add_pos (Real.exp_pos u) (Real.exp_pos v))
    (ne_of_lt (lt_add_of_pos_right _ (Real.exp_pos v))) hα hβ hsum
  rw [hpoint] at hj
  have hs : (Real.exp u + Real.exp v - t) / Real.exp v *
        confiningSourceEnergy z (Real.exp u) +
      (t - Real.exp u) / Real.exp v *
        confiningSourceEnergy z (Real.exp u + Real.exp v) < confiningSourceEnergy z t := by
    unfold confiningSourceEnergy
    have hcontrol := congrArg (fun x : ℝ => z * x) hpoint
    nlinarith only [hj, hcontrol]
  have hm := add_le_add
    (mul_le_mul_of_nonneg_left
      (min_le_left (confiningSourceEnergy z (Real.exp u))
        (confiningSourceEnergy z (Real.exp u + Real.exp v))) hα.le)
    (mul_le_mul_of_nonneg_left
      (min_le_right (confiningSourceEnergy z (Real.exp u))
        (confiningSourceEnergy z (Real.exp u + Real.exp v))) hβ.le)
  rw [← add_mul, hsum, one_mul] at hm
  have hstrict := hm.trans_lt hs
  exact ⟨hstrict.le, fun he => False.elim (hstrict.ne he)⟩

def confiningIntervalSourceFloor (u v z : ℝ) : ℝ :=
  sInf (confiningSourceEnergy z '' Icc (Real.exp u) (Real.exp u + Real.exp v))

/-- The infimum over all confinement strengths is exactly the two-endpoint envelope. -/
theorem confiningIntervalSourceFloor_eq (u v z : ℝ) :
    confiningIntervalSourceFloor u v z =
      endpointPotential (confiningHalfLineGroundEnergy (Real.exp u))
        (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v)) (Real.exp u) v z := by
  unfold confiningIntervalSourceFloor endpointPotential
  change sInf (confiningSourceEnergy z '' Icc (Real.exp u) (Real.exp u + Real.exp v)) =
    min (confiningSourceEnergy z (Real.exp u))
      (confiningSourceEnergy z (Real.exp u + Real.exp v))
  apply IsLeast.csInf_eq
  constructor
  · have hab : Real.exp u ≤ Real.exp u + Real.exp v := le_add_of_nonneg_right (Real.exp_pos v).le
    by_cases h : confiningSourceEnergy z (Real.exp u) ≤
        confiningSourceEnergy z (Real.exp u + Real.exp v)
    · rw [min_eq_left h]
      exact ⟨Real.exp u, ⟨le_rfl, hab⟩, rfl⟩
    · rw [min_eq_right (le_of_not_ge h)]
      exact ⟨Real.exp u + Real.exp v, ⟨hab, le_rfl⟩, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (confiningSourceEnergy_endpoint_bound u v z t ht).1

def confiningCoexistenceSource (u v : ℝ) : ℝ :=
  coexistenceSource (confiningHalfLineGroundEnergy (Real.exp u))
    (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v)) v

/-- The arithmetic variational problem has the same exact source-response jump. -/
theorem confiningIntervalSourceFloor_derivative_jump (u v s t : ℝ) :
    deriv (confiningIntervalSourceFloor u v) (confiningCoexistenceSource u v + Real.exp s) -
      deriv (confiningIntervalSourceFloor u v) (confiningCoexistenceSource u v - Real.exp t) =
        -Real.exp v := by
  have hf : confiningIntervalSourceFloor u v =
      endpointPotential (confiningHalfLineGroundEnergy (Real.exp u))
        (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v)) (Real.exp u) v := by
    funext z
    exact confiningIntervalSourceFloor_eq u v z
  rw [hf]
  exact endpointPotential_derivative_jump _ _ _ _ _ _

/-- The change of preferred confinement endpoint is a genuine first-order source transition. -/
theorem confiningIntervalSourceFloor_not_differentiable (u v : ℝ) :
    ¬ DifferentiableAt ℝ (confiningIntervalSourceFloor u v) (confiningCoexistenceSource u v) := by
  have hf : confiningIntervalSourceFloor u v =
      endpointPotential (confiningHalfLineGroundEnergy (Real.exp u))
        (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v)) (Real.exp u) v := by
    funext z
    exact confiningIntervalSourceFloor_eq u v z
  rw [hf]
  exact endpointPotential_not_differentiable _ _ _ _

#print axioms confiningSourceEnergy_endpoint_bound
#print axioms confiningIntervalSourceFloor_eq
#print axioms confiningIntervalSourceFloor_derivative_jump
#print axioms confiningIntervalSourceFloor_not_differentiable

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
