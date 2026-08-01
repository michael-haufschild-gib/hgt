import GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform

/-!
# The normalized phase lift

The last link of the Suzuki rigidity chain is `Theta -> phi`, recovering the phase from the inner
function.  On the real boundary the Cayley transform of a real Herglotz value lies on the unit
circle, and its argument is the explicit lift

`m |-> pi + 2 arctan m`.

Indeed `(m - i)/(m + i) = exp (i (pi + 2 arctan m))` for real `m`: writing `m = tan u`, the real
part is `-cos 2u` and the imaginary part is `-sin 2u`.

The lift is strictly increasing and injective, because `arctan` is; and equal boundary Cayley values
already force equal Herglotz boundary values, by a single cross-multiplication.  So the phase-lift
link is an injection, which is exactly what the rigidity chain needs of it.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- The normalized phase lift: the boundary argument of the Cayley transform. -/
noncomputable def cayleyPhaseLift (m : ℝ) : ℝ := Real.pi + 2 * Real.arctan m

theorem cos_arctan_sq (m : ℝ) : Real.cos (Real.arctan m) ^ 2 = 1 / (1 + m ^ 2) := by
  rw [Real.cos_arctan, div_pow, one_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + m ^ 2)]

theorem sin_arctan_mul_cos_arctan (m : ℝ) :
    Real.sin (Real.arctan m) * Real.cos (Real.arctan m) = m / (1 + m ^ 2) := by
  have hs : Real.sqrt (1 + m ^ 2) * Real.sqrt (1 + m ^ 2) = 1 + m ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, hs]

theorem cos_cayleyPhaseLift (m : ℝ) :
    Real.cos (cayleyPhaseLift m) = (m ^ 2 - 1) / (m ^ 2 + 1) := by
  have hpos : (0:ℝ) < 1 + m ^ 2 := by positivity
  rw [cayleyPhaseLift, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_two_mul, cos_arctan_sq]
  field_simp
  ring

theorem sin_cayleyPhaseLift (m : ℝ) :
    Real.sin (cayleyPhaseLift m) = -(2 * m) / (m ^ 2 + 1) := by
  have hpos : (0:ℝ) < 1 + m ^ 2 := by positivity
  have hprod := sin_arctan_mul_cos_arctan m
  rw [cayleyPhaseLift, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_two_mul, mul_assoc,
    hprod]
  field_simp
  ring

theorem ofReal_add_I_ne_zero (m : ℝ) : (m : ℂ) + Complex.I ≠ 0 := by
  intro hc
  have him : ((m : ℂ) + Complex.I).im = 0 := by rw [hc]; simp
  simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add] at him
  exact one_ne_zero him

theorem ofReal_sq_add_one_ne_zero (m : ℝ) : ((m : ℂ) ^ 2 + 1) ≠ 0 := by
  intro hc
  have hre : (((m : ℂ) ^ 2 + 1)).re = 0 := by rw [hc]; simp
  rw [← Complex.ofReal_pow] at hre
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
  nlinarith [sq_nonneg m]

/-- **The Cayley transform of a real Herglotz value is the exponential of the phase lift.** -/
theorem cayleyOfHerglotz_ofReal (m : ℝ) :
    cayleyOfHerglotz (m : ℂ) = Complex.exp ((cayleyPhaseLift m : ℝ) * Complex.I) := by
  have hden := ofReal_add_I_ne_zero m
  have hsq := ofReal_sq_add_one_ne_zero m
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    cos_cayleyPhaseLift, sin_cayleyPhaseLift, cayleyOfHerglotz]
  push_cast
  rw [div_mul_eq_mul_div, ← add_div, div_eq_div_iff hden hsq]
  linear_combination (2 * (m : ℂ)) * Complex.I_sq

/-- The boundary Cayley values lie on the unit circle. -/
theorem normSq_cayleyOfHerglotz_ofReal (m : ℝ) :
    Complex.normSq (cayleyOfHerglotz (m : ℂ)) = 1 := by
  rw [cayleyOfHerglotz_ofReal, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq (cayleyPhaseLift m)]

/-- **The phase lift is strictly increasing.** -/
theorem strictMono_cayleyPhaseLift : StrictMono cayleyPhaseLift := by
  intro a b hab
  have h := Real.arctan_strictMono hab
  rw [cayleyPhaseLift, cayleyPhaseLift]
  linarith

theorem cayleyPhaseLift_injective : Function.Injective cayleyPhaseLift :=
  strictMono_cayleyPhaseLift.injective

/-- The phase lift takes values in one full turn, which is the normalization. -/
theorem cayleyPhaseLift_mem_Ioo (m : ℝ) :
    cayleyPhaseLift m ∈ Set.Ioo 0 (2 * Real.pi) := by
  have h1 := Real.neg_pi_div_two_lt_arctan m
  have h2 := Real.arctan_lt_pi_div_two m
  constructor
  · rw [cayleyPhaseLift]; linarith
  · rw [cayleyPhaseLift]; linarith

/-- **The phase-lift link `Theta -> phi` is injective.**  Equal boundary Cayley values force equal
Herglotz boundary values: cross-multiplying, the two sides differ by `2 i (m₁ - m₂)`. -/
theorem eq_of_cayleyOfHerglotz_ofReal_eq {m1 m2 : ℝ}
    (h : cayleyOfHerglotz (m1 : ℂ) = cayleyOfHerglotz (m2 : ℂ)) : m1 = m2 := by
  have hden1 := ofReal_add_I_ne_zero m1
  have hden2 := ofReal_add_I_ne_zero m2
  rw [cayleyOfHerglotz, cayleyOfHerglotz, div_eq_div_iff hden1 hden2] at h
  have hI : (2 * Complex.I) * ((m1 : ℂ) - m2) = 0 := by linear_combination h
  have h2 : ((m1 : ℂ) - m2) = 0 := by
    rcases mul_eq_zero.mp hI with hc | hc
    · exact absurd hc (by simp)
    · exact hc
  exact_mod_cast sub_eq_zero.mp h2

/-- The phase lift determines and is determined by the Herglotz boundary value. -/
theorem cayleyPhaseLift_eq_iff {m1 m2 : ℝ} :
    cayleyPhaseLift m1 = cayleyPhaseLift m2 ↔ m1 = m2 :=
  ⟨fun h => cayleyPhaseLift_injective h, fun h => by rw [h]⟩

/-- **The composed link `m -> Theta -> phi`.**  The boundary phase determines the Herglotz boundary
value, so the last two links of the rigidity chain compose to an injection. -/
theorem eq_of_exp_cayleyPhaseLift_eq {m1 m2 : ℝ}
    (h : Complex.exp ((cayleyPhaseLift m1 : ℝ) * Complex.I)
      = Complex.exp ((cayleyPhaseLift m2 : ℝ) * Complex.I)) : m1 = m2 := by
  refine eq_of_cayleyOfHerglotz_ofReal_eq ?_
  rw [cayleyOfHerglotz_ofReal, cayleyOfHerglotz_ofReal, h]

end GaloisForLFunctions.RHTower
