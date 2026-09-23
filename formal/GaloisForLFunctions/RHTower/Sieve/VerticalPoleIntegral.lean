import GaloisForLFunctions.RHTower.Sieve.PoleTermSplit

/-!
# The vertical integral of the pole term

The residue of the Chebyshev integrand is carried by `(s-1)⁻¹`, whose real part on the line
`re s = 1 + α` is `α/(α² + y²)`.  Its integral over `[-T, T]` is `2·arctan(T/α)`, which tends to `π`
as `T → ∞`; the imaginary part `-y/(α² + y²)` is odd and integrates to zero.

The difference between the two vertical edges — one with `α = d - 1 > 0`, one with `α = c - 1 < 0` —
therefore tends to `2π`, and that is the residue.
-/

namespace RHTower.Sieve

/-- **The real part of the vertical pole integral.** -/
theorem integral_re_pole_line {α T : ℝ} (hα : α ≠ 0) :
    (∫ y : ℝ in (-T)..T, α / (α ^ (2 : ℕ) + y ^ (2 : ℕ))) = 2 * Real.arctan (T / α) := by
  have hα0 : α ≠ 0 := hα
  have hpt : ∀ y : ℝ, α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) = α⁻¹ * (1 + (y / α) ^ (2 : ℕ))⁻¹ := by
    intro y
    have hsq : (0 : ℝ) < α ^ (2 : ℕ) + y ^ (2 : ℕ) := by positivity
    field_simp
  rw [intervalIntegral.integral_congr (g := fun y => α⁻¹ * (1 + (y / α) ^ (2 : ℕ))⁻¹)
    (fun y _ => hpt y)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x : ℝ => (1 + x ^ (2 : ℕ))⁻¹) hα0,
    integral_inv_one_add_sq, smul_eq_mul,
    show (-T) / α = -(T / α) by ring, Real.arctan_neg]
  field_simp
  ring

/-- **The imaginary part of the vertical pole integral vanishes.**  The integrand is odd. -/
theorem integral_im_pole_line {α T : ℝ} :
    (∫ y : ℝ in (-T)..T, -y / (α ^ (2 : ℕ) + y ^ (2 : ℕ))) = 0 := by
  have hodd : ∀ y : ℝ, -(-y) / (α ^ (2 : ℕ) + (-y) ^ (2 : ℕ)) = -(-y / (α ^ (2 : ℕ) + y ^ (2 : ℕ))) := by
    intro y
    rw [neg_neg, neg_sq, neg_div, neg_neg]
  have hcomp := intervalIntegral.integral_comp_neg
    (a := -T) (b := T) (f := fun y : ℝ => -y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))
  have hcongr : (∫ y : ℝ in (-T)..T, -(-y) / (α ^ (2 : ℕ) + (-y) ^ (2 : ℕ)))
      = -∫ y : ℝ in (-T)..T, -y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    rw [intervalIntegral.integral_congr
      (g := fun y => -(-y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))) (fun y _ => hodd y)]
    exact intervalIntegral.integral_neg
  rw [hcongr] at hcomp
  simp only [neg_neg] at hcomp
  linarith [hcomp]

/-- **The limit of the vertical pole integral.**  Half the residue, from each side. -/
theorem tendsto_integral_re_pole_line {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))
      Filter.atTop (nhds Real.pi) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hdiv : Filter.Tendsto (fun T : ℝ => T / α) Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < α⁻¹)
      (Filter.tendsto_id (α := ℝ))
    refine h.congr fun T => ?_
    simp only [id_eq]
    field_simp
  have harc : Filter.Tendsto (fun T : ℝ => Real.arctan (T / α)) Filter.atTop
      (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv
  have hmul : Filter.Tendsto (fun T : ℝ => 2 * Real.arctan (T / α)) Filter.atTop
      (nhds (2 * (Real.pi / 2))) := harc.const_mul 2
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at hmul
  exact hmul.congr fun T => (integral_re_pole_line hαne).symm

/-- **The pole term on a vertical line, in closed form.**  Real and imaginary parts separated. -/
theorem inv_add_mul_I_eq {α y : ℝ} (hα : α ≠ 0) :
    ((α : ℂ) + (y : ℝ) * Complex.I)⁻¹
      = ((α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) - ((y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) * Complex.I := by
  have hsq : (α ^ (2 : ℕ) + y ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
  refine inv_eq_of_mul_eq_one_right ?_
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_im]
    field_simp
    ring

/-- **The complex vertical pole integral.**  On the line at distance `α > 0` from the pole it is the
real number `2·arctan(T/α)`. -/
theorem integral_vertical_pole {α T : ℝ} (hα : α ≠ 0) :
    (∫ y : ℝ in (-T)..T, ((α : ℂ) + (y : ℝ) * Complex.I)⁻¹)
      = ((2 * Real.arctan (T / α) : ℝ) : ℂ) := by
  have hcontA : Continuous fun y : ℝ => ((α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Continuous.div continuous_const ?_ ?_)
    · fun_prop
    · intro y
      positivity
  have hcontB : Continuous fun y : ℝ => ((y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) * Complex.I := by
    refine Continuous.mul (Complex.continuous_ofReal.comp (Continuous.div continuous_id ?_ ?_))
      continuous_const
    · fun_prop
    · intro y
      positivity
  rw [intervalIntegral.integral_congr
    (g := fun y => ((α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) - ((y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) : ℂ) * Complex.I)
    (fun y _ => inv_add_mul_I_eq hα)]
  rw [intervalIntegral.integral_sub (hcontA.intervalIntegrable _ _)
    (hcontB.intervalIntegrable _ _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hzero : (∫ y : ℝ in (-T)..T, y / (α ^ (2 : ℕ) + y ^ (2 : ℕ))) = 0 := by
    have h := integral_im_pole_line (α := α) (T := T)
    have hcongr : (∫ y : ℝ in (-T)..T, -y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))
        = -∫ y : ℝ in (-T)..T, y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
      rw [intervalIntegral.integral_congr
        (g := fun y => -(y / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))) (fun y _ => neg_div _ _)]
      exact intervalIntegral.integral_neg
    rw [hcongr] at h
    linarith
  rw [hzero, integral_re_pole_line hα]
  simp

/-- **The residue, in real form.**  The two vertical edges together contribute `2π`: `π` from the
line to the right of the pole and `π` from the line to its left. -/
theorem tendsto_pole_difference {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Filter.Tendsto (fun T : ℝ =>
        (∫ y : ℝ in (-T)..T, α / (α ^ (2 : ℕ) + y ^ (2 : ℕ)))
          + (∫ y : ℝ in (-T)..T, β / (β ^ (2 : ℕ) + y ^ (2 : ℕ))))
      Filter.atTop (nhds (2 * Real.pi)) := by
  have h := (tendsto_integral_re_pole_line hα).add (tendsto_integral_re_pole_line hβ)
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring] at h
  exact h

/-- **The two vertical edges of the pole term.**  Their difference, in the orientation of the
four-edge identity, is `2·arctan(T/(d-1)) + 2·arctan(T/(1-c))`. -/
theorem integral_vertical_pole_pair {c d T : ℝ} (hc : c < 1) (hd : 1 < d) :
    (∫ y : ℝ in (-T)..T, ((d : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
        - (∫ y : ℝ in (-T)..T, ((c : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
      = ((2 * Real.arctan (T / (d - 1)) + 2 * Real.arctan (T / (1 - c)) : ℝ) : ℂ) := by
  have hd0 : (d - 1 : ℝ) ≠ 0 := by intro h; apply absurd hd; simp; linarith
  have hc0 : (c - 1 : ℝ) ≠ 0 := by intro h; apply absurd hc; simp; linarith
  have hrwd : ∀ y : ℝ, ((d : ℂ) + (y : ℝ) * Complex.I - 1)
      = ((d - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
    intro y; push_cast; ring
  have hrwc : ∀ y : ℝ, ((c : ℂ) + (y : ℝ) * Complex.I - 1)
      = ((c - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
    intro y; push_cast; ring
  have hd_eq : (∫ y : ℝ in (-T)..T, ((d : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T, (((d - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => by rw [hrwd y])
  have hc_eq : (∫ y : ℝ in (-T)..T, ((c : ℂ) + (y : ℝ) * Complex.I - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T, (((c - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => by rw [hrwc y])
  rw [hd_eq, hc_eq, integral_vertical_pole hd0, integral_vertical_pole hc0]
  have h1c : (1 - c : ℝ) ≠ 0 := by intro h; apply absurd hc; simp; linarith
  have harc : Real.arctan (T / (c - 1)) = -Real.arctan (T / (1 - c)) := by
    rw [show T / (c - 1) = -(T / (1 - c)) by
      rw [show (c - 1 : ℝ) = -(1 - c) by ring, div_neg], Real.arctan_neg]
  rw [harc]
  push_cast
  ring

end RHTower.Sieve
