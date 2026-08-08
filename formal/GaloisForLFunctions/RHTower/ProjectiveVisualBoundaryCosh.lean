import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The visual-boundary Jacobian and the Tate `cosh` character

Moving the base vertex of the Bruhat–Tits tree of `PGL₂(Q_p)` by one edge multiplies the visual
measure by `p` inside the first shadow pointing that way and by `p⁻¹` outside it.  The two first
shadows of that decomposition carry visual mass `1/(p+1)` and `p/(p+1)`, so the spherical moment of
the weighted boundary transport is

`m_p(s) = ∫ J_g^s dν_o = (p^s + p^{1-s})/(p+1)`.

This file builds that two-atom visual model, evaluates the moment, and proves the two laws the card
attaches to it: the Riemann reflection `m_p(s) = m_p(1-s)`, and the normalized Tate character

`m_p(s)/m_p(1/2) = cosh((s - 1/2) log p)`.

It also records the half-density norm law: the multiplier `J_g^{c}` has supremum `p^{|c|}` over the
two visual atoms, so the weighted transport is contractive in the fixed source norm exactly on the
critical line `c = 0`.
-/

open MeasureTheory Complex

namespace RHTower

noncomputable section

variable (p : ℕ)

/-! ## The two-atom visual shadow model -/

/-- The visual probability measure at the base vertex, restricted to the first-shadow
decomposition: `true` is the shadow pointing at the moved vertex, `false` its complement. -/
def visualShadowMeasure : Measure Bool :=
  ENNReal.ofReal (1 / ((p : ℝ) + 1)) • Measure.dirac true +
    ENNReal.ofReal ((p : ℝ) / ((p : ℝ) + 1)) • Measure.dirac false

/-- **Equation (39).**  The visual Radon–Nikodym Jacobian of a one-edge base change. -/
def visualJacobian : Bool → ℝ := fun b => if b then (p : ℝ) else ((p : ℝ))⁻¹

theorem visualJacobian_pos (hp : 0 < p) (b : Bool) : 0 < visualJacobian p b := by
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  cases b <;> simp [visualJacobian] <;> positivity

/-- The singleton masses of the two visual atoms. -/
theorem visualShadowMeasure_true :
    visualShadowMeasure p {true} = ENNReal.ofReal (1 / ((p : ℝ) + 1)) := by
  rw [visualShadowMeasure]
  simp

theorem visualShadowMeasure_false :
    visualShadowMeasure p {false} = ENNReal.ofReal ((p : ℝ) / ((p : ℝ) + 1)) := by
  rw [visualShadowMeasure]
  simp

/-- The visual model is a probability measure: the two first shadows exhaust the boundary. -/
theorem visualShadowMeasure_univ (hp : 0 < p) :
    visualShadowMeasure p Set.univ = 1 := by
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  rw [visualShadowMeasure]
  simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    show (1 : ℝ) / ((p : ℝ) + 1) + (p : ℝ) / ((p : ℝ) + 1) = 1 from by field_simp; ring]
  simp

theorem visualShadowMeasure_isFinite (hp : 0 < p) :
    IsFiniteMeasure (visualShadowMeasure p) :=
  ⟨by rw [visualShadowMeasure_univ p hp]; exact ENNReal.one_lt_top⟩

/-! ## The spherical moment -/

/-- The constant-vector coefficient of the weighted boundary transport. -/
def visualSphericalMoment (s : ℂ) : ℂ :=
  (((p : ℂ)) ^ s + ((p : ℂ)) ^ (1 - s)) / ((p : ℂ) + 1)

/-- **Equation (43).**  The spherical moment is the visual integral of the Jacobian power. -/
theorem integral_visualJacobian_cpow (hp : 0 < p) (s : ℂ) :
    (∫ b, ((visualJacobian p b : ℝ) : ℂ) ^ s ∂(visualShadowMeasure p)) =
      visualSphericalMoment p s := by
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hpr)
  have harg : (((p : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [show (((p : ℕ) : ℂ)) = ((((p : ℕ) : ℝ)) : ℂ) from by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact fun h => Real.pi_ne_zero h.symm
  haveI := visualShadowMeasure_isFinite p hp
  have hint : Integrable (fun b : Bool => ((visualJacobian p b : ℝ) : ℂ) ^ s)
      (visualShadowMeasure p) := Integrable.of_finite
  rw [integral_fintype hint, Fintype.sum_bool]
  have hcast : ((((p : ℕ) : ℝ)) : ℂ) = ((p : ℕ) : ℂ) := by push_cast; ring
  have hinv : (((visualJacobian p false : ℝ)) : ℂ) ^ s = ((p : ℂ)) ^ (-s) := by
    rw [visualJacobian]
    simp only [if_neg (by simp : ¬ (false = true))]
    rw [Complex.ofReal_inv, hcast, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  have htrue : (((visualJacobian p true : ℝ)) : ℂ) ^ s = ((p : ℂ)) ^ s := by
    rw [visualJacobian]
    simp
  rw [hinv, htrue, Measure.real, Measure.real, visualShadowMeasure_true,
    visualShadowMeasure_false, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), visualSphericalMoment]
  have hpow : ((p : ℂ)) ^ (1 - s) = (p : ℂ) * ((p : ℂ)) ^ (-s) := by
    rw [Complex.cpow_sub _ _ hpC, Complex.cpow_one, Complex.cpow_neg]
    ring
  rw [hpow, Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp

/-- **Equation (44), reflection.**  The spherical moment obeys the Riemann reflection. -/
theorem visualSphericalMoment_reflection (s : ℂ) :
    visualSphericalMoment p (1 - s) = visualSphericalMoment p s := by
  rw [visualSphericalMoment, visualSphericalMoment]
  congr 1
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  ring

theorem visualSphericalMoment_half :
    visualSphericalMoment p (1 / 2) =
      2 * ((p : ℂ)) ^ ((1 : ℂ) / 2) / ((p : ℂ) + 1) := by
  rw [visualSphericalMoment]
  congr 1
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 from by ring]
  ring

theorem cpow_eq_exp_mul_log (hp : 0 < p) (w : ℂ) :
    ((p : ℂ)) ^ w = Complex.exp (w * (Real.log p : ℂ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hppos)
  rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log, mul_comm]

/-- The half-density normalization is nonzero. -/
theorem cpow_half_ne_zero (hp : 0 < p) : ((p : ℂ)) ^ ((1 : ℂ) / 2) ≠ 0 := by
  rw [cpow_eq_exp_mul_log p hp]
  exact Complex.exp_ne_zero _

theorem visualSphericalMoment_numerator (hp : 0 < p) (s : ℂ) :
    ((p : ℂ)) ^ s + ((p : ℂ)) ^ (1 - s) =
      Complex.cosh ((s - 1 / 2) * (Real.log p : ℂ)) * (2 * ((p : ℂ)) ^ ((1 : ℂ) / 2)) := by
  rw [cpow_eq_exp_mul_log p hp s, cpow_eq_exp_mul_log p hp (1 - s),
    cpow_eq_exp_mul_log p hp ((1 : ℂ) / 2), Complex.cosh]
  have e1 : Complex.exp ((s - 1 / 2) * (Real.log p : ℂ)) *
      Complex.exp ((1 / 2 : ℂ) * (Real.log p : ℂ)) =
      Complex.exp (s * (Real.log p : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-((s - 1 / 2) * (Real.log p : ℂ))) *
      Complex.exp ((1 / 2 : ℂ) * (Real.log p : ℂ)) =
      Complex.exp ((1 - s) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← e1, ← e2]
  ring

/-- **Equation (44), Tate character.**  Normalizing the spherical moment at the critical point
produces exactly the Tate `cosh` character of the prime dilation. -/
theorem visualSphericalMoment_div_half (hp : 0 < p) (s : ℂ) :
    visualSphericalMoment p s / visualSphericalMoment p (1 / 2) =
      Complex.cosh ((s - 1 / 2) * (Real.log p : ℂ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hden : ((p : ℂ)) + 1 ≠ 0 := by
    have hd : (0 : ℝ) < (p : ℝ) + 1 := by linarith
    have hcast : ((p : ℂ)) + 1 = ((((p : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
  have hhalf := cpow_half_ne_zero p hp
  rw [visualSphericalMoment, visualSphericalMoment_half p,
    visualSphericalMoment_numerator p hp s]
  field_simp

/-! ## The half-density norm law -/

/-- **Equations (41)–(42).**  The multiplier of the weighted transport takes exactly the two
values `p^{c}` and `p^{-c}` on the visual atoms; its supremum is `p^{|c|}`. -/
theorem visualJacobian_rpow_sup (hp : 1 < p) (c : ℝ) :
    max (((p : ℝ)) ^ c) (((p : ℝ)) ^ (-c)) = ((p : ℝ)) ^ |c| := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc, max_eq_left]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  · rw [abs_of_neg hc, max_eq_right]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)

/-- The transport is contractive in the fixed source norm exactly on the critical line. -/
theorem visualJacobian_rpow_sup_eq_one_iff (hp : 1 < p) (c : ℝ) :
    max (((p : ℝ)) ^ c) (((p : ℝ)) ^ (-c)) = 1 ↔ c = 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [visualJacobian_rpow_sup p hp c]
  constructor
  · intro h
    by_contra hc
    have habs : 0 < |c| := abs_pos.mpr hc
    have hgt : (1 : ℝ) < ((p : ℝ)) ^ |c| :=
      Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr (Or.inl ⟨hp1, habs⟩)
    linarith
  · intro h
    rw [h]
    simp

/-- The multiplier value at each visual atom. -/
theorem visualJacobian_rpow_values (hp : 0 < p) (c : ℝ) :
    (visualJacobian p true) ^ c = ((p : ℝ)) ^ c ∧
      (visualJacobian p false) ^ c = ((p : ℝ)) ^ (-c) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  refine ⟨by simp [visualJacobian], ?_⟩
  rw [visualJacobian]
  simp only [if_neg (by simp : ¬ (false = true))]
  rw [← Real.rpow_neg_one ((p : ℝ)), ← Real.rpow_mul hppos.le]
  congr 1
  ring

end

end RHTower
