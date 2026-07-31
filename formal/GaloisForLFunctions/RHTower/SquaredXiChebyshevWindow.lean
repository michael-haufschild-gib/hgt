import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceAlignment
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The reverse-Bessel radial kernel: Lebesgue side and Gamma-mixture scale

Fix a real base point `s > 1` and put `w = s - 1/2`, `a = s - 1`.  The radial kernel

`f_{n,s} x = x^(-s) * B_n (w log x)`,   `B_n z = sum_j b_{n,j} z^j`,

has an exact Lebesgue integral over the ray `x >= 1`,

`∫_1^∞ f_{n,s} = sum_j b_{n,j} j! w^j / a^(j+1)`,

obtained from the substitution `x = exp t`, which turns the kernel into the finite Gamma mixture
`sum_j b_{n,j} w^j t^j exp (-a t)`.

The mixture weights `c_{n,j} = b_{n,j} j! (w/a)^j` obey the exact adjacent ratio

`c_{n,j+1} / c_{n,j} = 2 (n - j) w / ((2n - j) a)`,

so the mixture index increases exactly while `j s < n`: the Gamma-mixture shape is unimodal at the
integers adjacent to `n / s`.  This is the modal scale of the polar window.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-! ### Exponential substitution on the ray `x >= 1` -/

theorem exp_image_Ioi_zero : Real.exp '' (Ioi (0:ℝ)) = Ioi (1:ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : (0:ℝ) < x := hx
    have h : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hx0
    rw [Real.exp_zero] at h
    exact h
  · intro hy
    have hy1 : (1:ℝ) < y := hy
    exact ⟨Real.log y, Real.log_pos hy1, Real.exp_log (by linarith)⟩

private theorem abs_exp_smul_eq (g : ℝ → ℝ) :
    (fun x : ℝ => |Real.exp x| • g (Real.exp x))
      = fun t : ℝ => Real.exp t * g (Real.exp t) := by
  funext x
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul]

theorem integral_Ioi_one_comp_exp (g : ℝ → ℝ) :
    ∫ x in Ioi (1:ℝ), g x = ∫ t in Ioi (0:ℝ), Real.exp t * g (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn (s := Ioi (0:ℝ))) g
  rw [exp_image_Ioi_zero, abs_exp_smul_eq] at h
  exact h

/-! ### The scaled Gamma integral -/

theorem integrableOn_pow_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-(r * t))) (Ioi (0:ℝ)) := by
  have hG : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) (Ioi (0:ℝ)) :=
    Real.GammaIntegral_convergent (by positivity)
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) 0 hr).mpr (by simpa using hG)
  have hc : IntegrableOn
      (fun x : ℝ => (r ^ j)⁻¹ * (Real.exp (-(r * x)) * (r * x) ^ (((j : ℝ) + 1) - 1)))
      (Ioi (0:ℝ)) := hscale.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hrj : (r : ℝ) ^ j ≠ 0 := by positivity
  have hexp : ((r * x) : ℝ) ^ (((j : ℝ) + 1) - 1) = r ^ j * x ^ j := by
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring, Real.rpow_natCast, mul_pow]
  simp only [hexp]
  field_simp

theorem integral_pow_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-(r * t)) = (j.factorial : ℝ) / r ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := r)
    (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have hcongr : ∫ t in Ioi (0:ℝ), t ^ (((j : ℝ) + 1) - 1) * Real.exp (-(r * t))
      = ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring, Real.rpow_natCast]
  rw [hcongr] at h
  rw [h, one_div, Real.inv_rpow hr.le, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  field_simp

/-! ### The radial kernel and its Lebesgue integral -/

/-- The reverse-Bessel radial kernel `f_{n,s} x = x^(-s) B_n ((s - 1/2) log x)`. -/
def radialBesselKernel (n : ℕ) (s x : ℝ) : ℝ :=
  x ^ (-s) * ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℝ) * ((s - 1 / 2) * Real.log x) ^ j

private theorem radialBesselKernel_exp {n : ℕ} {s : ℝ} (t : ℝ) :
    Real.exp t * radialBesselKernel n s (Real.exp t)
      = ∑ j ∈ Finset.range (n + 1),
          ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
            (t ^ j * Real.exp (-((s - 1) * t))) := by
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hrpow : (Real.exp t) ^ (-s) = Real.exp (-(s * t)) := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp]
    congr 1
    ring
  rw [radialBesselKernel, hrpow, Real.log_exp, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_pow]
  rw [show Real.exp t * (Real.exp (-(s * t)) *
      ((squaredRadialJetWeight n j : ℝ) * ((s - 1 / 2) ^ j * t ^ j)))
      = ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        (t ^ j * (Real.exp t * Real.exp (-(s * t)))) from by ring]
  congr 2
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Equation (2).**  The Lebesgue integral of the radial kernel over `x >= 1` is the exact
reverse-Bessel Gamma sum. -/
theorem integral_radialBesselKernel {n : ℕ} {s : ℝ} (hs : 1 < s) :
    ∫ x in Ioi (1:ℝ), radialBesselKernel n s x
      = ∑ j ∈ Finset.range (n + 1),
          (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) *
            (s - 1 / 2) ^ j / (s - 1) ^ (j + 1) := by
  have ha : (0:ℝ) < s - 1 := by linarith
  rw [integral_Ioi_one_comp_exp]
  have hcongr : ∫ t in Ioi (0:ℝ), Real.exp t * radialBesselKernel n s (Real.exp t)
      = ∫ t in Ioi (0:ℝ), ∑ j ∈ Finset.range (n + 1),
          ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
            (t ^ j * Real.exp (-((s - 1) * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    exact radialBesselKernel_exp t
  rw [hcongr]
  rw [MeasureTheory.integral_finsetSum _ (fun j _ =>
    ((integrableOn_pow_mul_exp_neg_mul_Ioi ha j).const_mul _))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi ha j]
  ring

/-! ### The Gamma-mixture weights and their exact adjacent ratio -/

/-- **Equation (8).**  The unnormalized Gamma-mixture weight `c_{n,j} = b_{n,j} j! (w/a)^j`. -/
def radialMixtureWeight (n : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ) * ((s - 1 / 2) / (s - 1)) ^ j

theorem radialMixtureWeight_pos {n j : ℕ} (hj : j ≤ n) {s : ℝ} (hs : 1 < s) :
    0 < radialMixtureWeight n s j := by
  have hb : (0:ℝ) < (squaredRadialJetWeight n j : ℝ) := by
    exact_mod_cast squaredRadialJetWeight_pos n j hj
  have hf : (0:ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hw : (0:ℝ) < (s - 1 / 2) / (s - 1) := by
    apply div_pos <;> linarith
  rw [radialMixtureWeight]
  positivity

/-- The exact factorial recurrence behind the mixture ratio:
`(j+1) b_{n,j+1} (2n - j) = 2 (n - j) b_{n,j}`. -/
theorem squaredRadialJetWeight_adjacent {n j : ℕ} (hj : j < n) :
    ((j : ℚ) + 1) * (squaredRadialJetWeight n (j + 1) : ℚ) * (2 * (n : ℚ) - (j : ℚ))
      = 2 * ((n : ℚ) - (j : ℚ)) * (squaredRadialJetWeight n j : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - j - 1, by omega⟩
  rw [squaredRadialJetWeight_eq_closedForm _ _ (by omega),
    squaredRadialJetWeight_eq_closedForm _ _ (by omega)]
  unfold squaredRadialJetWeightClosedForm
  rw [show 2 * (j + 1 + m) - (j + 1) = j + 2 * m + 1 by omega,
    show (j + 1 + m) - (j + 1) = m by omega,
    show 2 * (j + 1 + m) - j = j + 2 * m + 2 by omega,
    show (j + 1 + m) - j = m + 1 by omega,
    show (j + 2 * m + 2).factorial = (j + 2 * m + 2) * (j + 2 * m + 1).factorial from by
      rw [show j + 2 * m + 2 = (j + 2 * m + 1) + 1 from rfl, Nat.factorial_succ],
    show (m + 1).factorial = (m + 1) * m.factorial from Nat.factorial_succ m,
    show (j + 1).factorial = (j + 1) * j.factorial from Nat.factorial_succ j]
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hjf : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hf : ((j + 2 * m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- **Equation (9).**  The exact adjacent mixture ratio, in cleared form:
`c_{n,j+1} (2n - j) a = c_{n,j} 2 (n - j) w`. -/
theorem radialMixtureWeight_adjacent {n j : ℕ} (hj : j < n) {s : ℝ} (hs : 1 < s) :
    radialMixtureWeight n s (j + 1) * (2 * (n : ℝ) - (j : ℝ)) * (s - 1)
      = radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2) := by
  have hrat : ((j : ℝ) + 1) * (squaredRadialJetWeight n (j + 1) : ℝ) *
      (2 * (n : ℝ) - (j : ℝ))
      = 2 * ((n : ℝ) - (j : ℝ)) * (squaredRadialJetWeight n j : ℝ) := by
    exact_mod_cast squaredRadialJetWeight_adjacent (n := n) (j := j) hj
  have hane : (s : ℝ) - 1 ≠ 0 := by intro h; linarith [hs]
  have hq : ((s - 1 / 2) / (s - 1)) * (s - 1) = s - 1 / 2 := by field_simp
  calc radialMixtureWeight n s (j + 1) * (2 * (n : ℝ) - (j : ℝ)) * (s - 1)
      = (((j : ℝ) + 1) * (squaredRadialJetWeight n (j + 1) : ℝ) *
            (2 * (n : ℝ) - (j : ℝ))) *
          ((j.factorial : ℝ) * ((s - 1 / 2) / (s - 1)) ^ j) *
          (((s - 1 / 2) / (s - 1)) * (s - 1)) := by
        rw [radialMixtureWeight, Nat.factorial_succ, pow_succ]
        push_cast
        ring
    _ = (2 * ((n : ℝ) - (j : ℝ)) * (squaredRadialJetWeight n j : ℝ)) *
          ((j.factorial : ℝ) * ((s - 1 / 2) / (s - 1)) ^ j) * (s - 1 / 2) := by
        rw [hrat, hq]
    _ = radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2) := by
        rw [radialMixtureWeight]
        ring

/-- **Equation (10).**  The mixture weights increase exactly while `j s < n`, so the Gamma-mixture
index is unimodal at the integers adjacent to `n / s`. -/
theorem radialMixtureWeight_lt_succ_iff {n j : ℕ} (hj : j < n) {s : ℝ} (hs : 1 < s) :
    radialMixtureWeight n s j < radialMixtureWeight n s (j + 1) ↔ (j : ℝ) * s < (n : ℝ) := by
  have ha : (0:ℝ) < s - 1 := by linarith
  have hcj : 0 < radialMixtureWeight n s j :=
    radialMixtureWeight_pos (le_of_lt hj) hs
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hden : (0:ℝ) < 2 * (n : ℝ) - (j : ℝ) := by linarith
  have hDa : (0:ℝ) < (2 * (n : ℝ) - (j : ℝ)) * (s - 1) := mul_pos hden ha
  have hkey := radialMixtureWeight_adjacent hj hs
  have hrw : radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
      = radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ)) * (s - 1 / 2)) := by
    rw [← mul_assoc, hkey]
    ring
  constructor
  · intro hlt
    have h1 : radialMixtureWeight n s j * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
        < radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1)) :=
      mul_lt_mul_of_pos_right hlt hDa
    rw [hrw] at h1
    have h2 := lt_of_mul_lt_mul_left h1 hcj.le
    nlinarith [h2]
  · intro hlt
    have h2 : (2 * (n : ℝ) - (j : ℝ)) * (s - 1)
        < 2 * ((n : ℝ) - (j : ℝ)) * (s - 1 / 2) := by nlinarith [hlt]
    have h1 : radialMixtureWeight n s j * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
        < radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ)) * (s - 1 / 2)) :=
      mul_lt_mul_of_pos_left h2 hcj
    rw [← hrw] at h1
    exact lt_of_mul_lt_mul_right h1 hDa.le

end

end RHTower
