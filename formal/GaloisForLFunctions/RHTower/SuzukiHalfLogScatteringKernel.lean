import GaloisForLFunctions.HTGeometry.HighFrequencyTransportBound

/-!
# The kernel of the half-log scattering map

The two frequency channels `cp, cm` of a homogeneous solution enter the terminal endpoint trace
only through

`β(cp,cm) = (2√π)⁻¹ [e^{iπ/4} cp + e^{-iπ/4} cm]`,

the half-log scattering map.  Its kernel is not trivial: `β(cp,cm) = 0` exactly when
`cm = -i cp`.  Thus a single vanishing signed trace does not force the homogeneous component to
vanish; it moves that component off the critical `L^{-1/2}` corona, where the remainder is
`O(L^{-1})` and hence square integrable at infinity.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The half-log scattering map from the two frequency channels to the endpoint trace. -/
def halfLogScatter (cp cm : X) : X :=
  ((1 : ℂ) / (2 * (Real.sqrt Real.pi : ℂ))) •
    (Complex.exp ((Real.pi / 4 : ℝ) * I) • cp + Complex.exp (-(Real.pi / 4 : ℝ) * I) • cm)

theorem exp_quarter_mul_self : Complex.exp ((Real.pi / 4 : ℝ) * I)
    * Complex.exp ((Real.pi / 4 : ℝ) * I) = I := by
  rw [← Complex.exp_add]
  have h : ((Real.pi / 4 : ℝ) : ℂ) * I + ((Real.pi / 4 : ℝ) : ℂ) * I
      = ((Real.pi / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.exp_mul_I]
  have hcos : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [show (((Real.pi / 2 : ℝ)) : ℂ) = (Real.pi / 2 : ℂ) by push_cast; ring]
    exact Complex.cos_pi_div_two
  have hsin : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [show (((Real.pi / 2 : ℝ)) : ℂ) = (Real.pi / 2 : ℂ) by push_cast; ring]
    exact Complex.sin_pi_div_two
  rw [hcos, hsin, one_mul, zero_add]

theorem exp_quarter_mul_neg : Complex.exp ((Real.pi / 4 : ℝ) * I)
    * Complex.exp (-(Real.pi / 4 : ℝ) * I) = 1 := by
  rw [← Complex.exp_add]
  have h : ((Real.pi / 4 : ℝ) : ℂ) * I + -((Real.pi / 4 : ℝ) : ℂ) * I = 0 := by
    push_cast; ring
  rw [h, Complex.exp_zero]

/-- **The kernel of the half-log scattering map.**  The two channels cancel exactly when the
negative channel is the `-i` rotation of the positive one. -/
theorem halfLogScatter_eq_zero_iff (cp cm : X) :
    halfLogScatter cp cm = 0 ↔ cm = (-I) • cp := by
  have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hne : ((1 : ℂ) / (2 * (Real.sqrt Real.pi : ℂ))) ≠ 0 := by
    refine div_ne_zero one_ne_zero ?_
    refine mul_ne_zero two_ne_zero ?_
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hπ
  constructor
  · intro h
    rw [halfLogScatter, smul_eq_zero] at h
    rcases h with h | h
    · exact absurd h hne
    · have h2 : Complex.exp ((Real.pi / 4 : ℝ) * I) •
          (Complex.exp ((Real.pi / 4 : ℝ) * I) • cp
            + Complex.exp (-(Real.pi / 4 : ℝ) * I) • cm) = 0 := by
        rw [h, smul_zero]
      rw [smul_add, smul_smul, smul_smul, exp_quarter_mul_self, exp_quarter_mul_neg,
        one_smul] at h2
      have h3 : cm = -(I • cp) := by
        have hx := add_eq_zero_iff_eq_neg.mp h2
        rw [hx, neg_neg]
      rw [h3, neg_smul]
  · intro h
    rw [halfLogScatter, h]
    have h4 : Complex.exp ((Real.pi / 4 : ℝ) * I) • cp
        + Complex.exp (-(Real.pi / 4 : ℝ) * I) • ((-I) • cp) = 0 := by
      rw [smul_smul]
      have hcoeff : Complex.exp (-(Real.pi / 4 : ℝ) * I) * (-I)
          = -Complex.exp ((Real.pi / 4 : ℝ) * I) := by
        have hmul : Complex.exp ((Real.pi / 4 : ℝ) * I)
            * (Complex.exp (-(Real.pi / 4 : ℝ) * I) * (-I))
            = Complex.exp ((Real.pi / 4 : ℝ) * I) * (-Complex.exp ((Real.pi / 4 : ℝ) * I)) := by
          rw [← mul_assoc, exp_quarter_mul_neg, one_mul, mul_neg, exp_quarter_mul_self]
        have hexpne : Complex.exp ((Real.pi / 4 : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
        exact mul_left_cancel₀ hexpne hmul
      rw [hcoeff, neg_smul, add_neg_cancel]
    rw [h4, smul_zero]

/-- The two-channel data lies in the kernel exactly when the endpoint trace loses its critical
`L^{-1/2}` term; the classification is a rotation condition, not a vanishing condition. -/
theorem halfLogScatter_ne_zero_of_ne (cp cm : X) (h : cm ≠ (-I) • cp) :
    halfLogScatter cp cm ≠ 0 := fun hz => h ((halfLogScatter_eq_zero_iff cp cm).mp hz)

end

end GaloisForLFunctions.RHTower
