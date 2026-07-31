import Mathlib

/-!
# The first trivial zero of `ζ` and its exact first derivative

The functional equation

`ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(π s / 2) ζ(s)`

carries a simple cosine zero at `s = 3`.  Differentiating the identity there, every term in
which the cosine is *not* differentiated vanishes, so the derivative of the left-hand side is
the derivative of the cosine times the remaining archimedean factor.  This yields the closed
form

`ζ'(-2) = -ζ(3) / (4π²)`,

which is nonzero because `ζ(3) ≠ 0`.  Hence `-2` is a *simple* zero of `ζ`.

The same functional equation shows that `ζ` has no zero on the real segment `[-1, 0)`: there
the reflected argument `1 - x` lies in `(1, 2]`, a range on which the exponential factor, the
Gamma factor, the cosine factor, and `ζ` itself are all nonzero.
-/

open Complex Filter Topology

namespace RHTower

/-- A point of the open right half-plane is not a nonpositive integer. -/
theorem ne_neg_natCast_of_zero_lt_re {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro hn
  rw [hn] at hs
  simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at hs
  exact absurd hs (not_lt.mpr (Nat.cast_nonneg n))

/-- The archimedean factor of the reflection formula with its cosine removed. -/
noncomputable def reflectionArchFactor (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * riemannZeta s

theorem ofReal_pi_ne_zero : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

theorem two_mul_ofReal_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero ofReal_pi_ne_zero

/-- The reflection formula splits as cosine times the archimedean factor. -/
theorem riemannZeta_one_sub_eq_cos_mul {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = Complex.cos ((Real.pi : ℂ) * s / 2) * reflectionArchFactor s := by
  rw [riemannZeta_one_sub hs hs', reflectionArchFactor]
  ring

/-- Away from the nonpositive integers and from `1`, the archimedean factor is holomorphic. -/
theorem differentiableAt_reflectionArchFactor {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ))
    (hs' : s ≠ 1) : DifferentiableAt ℂ reflectionArchFactor s := by
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    DifferentiableAt.const_cpow (differentiableAt_id.neg) (Or.inl two_mul_ofReal_pi_ne_zero)
  have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hs
  have hZ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs'
  exact (((differentiableAt_const (2 : ℂ)).mul hcpow).mul hG).mul hZ

theorem cos_three_pi_div_two : Complex.cos ((Real.pi : ℂ) * 3 / 2) = 0 := by
  have hcast : ((Real.pi : ℂ) * 3 / 2) = ((Real.pi * 3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hreal : Real.cos (Real.pi * 3 / 2) = 0 := by
    have h : Real.pi * 3 / 2 = Real.pi / 2 + Real.pi := by ring
    rw [h, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  rw [hcast, ← Complex.ofReal_cos, hreal, Complex.ofReal_zero]

theorem sin_three_pi_div_two : Complex.sin ((Real.pi : ℂ) * 3 / 2) = -1 := by
  have hcast : ((Real.pi : ℂ) * 3 / 2) = ((Real.pi * 3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hreal : Real.sin (Real.pi * 3 / 2) = -1 := by
    have h : Real.pi * 3 / 2 = Real.pi / 2 + Real.pi := by ring
    rw [h, Real.sin_add_pi, Real.sin_pi_div_two]
  rw [hcast, ← Complex.ofReal_sin, hreal]
  norm_num

theorem two_mul_pi_cpow_neg_three :
    ((2 * (Real.pi : ℂ)) ^ (-(3 : ℂ))) = 1 / (8 * (Real.pi : ℂ) ^ 3) := by
  rw [show (-(3 : ℂ)) = ((-3 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  field_simp
  ring

theorem Gamma_three : Complex.Gamma 3 = 2 := by
  have h : (3 : ℂ) = ((2 : ℕ) : ℂ) + 1 := by norm_num
  rw [h, Complex.Gamma_nat_eq_factorial]
  norm_num

theorem reflectionArchFactor_three :
    reflectionArchFactor 3 = riemannZeta 3 / (2 * (Real.pi : ℂ) ^ 3) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  rw [reflectionArchFactor, two_mul_pi_cpow_neg_three, Gamma_three]
  field_simp
  ring

/-- `-2` is a zero of `ζ`. -/
theorem riemannZeta_neg_two : riemannZeta (-2) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

/-- **Exact first derivative at the first trivial zero.**  Differentiating the reflection
formula at `s = 3`, where its cosine factor vanishes simply. -/
theorem deriv_riemannZeta_neg_two :
    deriv riemannZeta (-2) = -riemannZeta 3 / (4 * (Real.pi : ℂ) ^ 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have hzeta : DifferentiableAt ℂ riemannZeta (-2) := differentiableAt_riemannZeta (by norm_num)
  have hL : HasDerivAt (fun s : ℂ => riemannZeta (1 - s)) (-deriv riemannZeta (-2)) 3 := by
    refine HasDerivAt.comp_const_sub 1 3 ?_
    rw [show (1 : ℂ) - 3 = -2 by norm_num]
    exact hzeta.hasDerivAt
  have h3re : (0 : ℝ) < (3 : ℂ).re := by norm_num
  have hs3 : ∀ n : ℕ, (3 : ℂ) ≠ -(n : ℂ) := ne_neg_natCast_of_zero_lt_re h3re
  have harch : DifferentiableAt ℂ reflectionArchFactor 3 :=
    differentiableAt_reflectionArchFactor hs3 (by norm_num)
  have hcos : HasDerivAt (fun s : ℂ => Complex.cos ((Real.pi : ℂ) * s / 2))
      ((Real.pi : ℂ) / 2) 3 := by
    have h1 : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) * s / 2) ((Real.pi : ℂ) / 2) 3 := by
      simpa using ((hasDerivAt_id (3 : ℂ)).const_mul (Real.pi : ℂ)).div_const 2
    have h2 := h1.ccos
    rw [sin_three_pi_div_two] at h2
    simpa using h2
  have hR : HasDerivAt (fun s : ℂ => Complex.cos ((Real.pi : ℂ) * s / 2) * reflectionArchFactor s)
      ((Real.pi : ℂ) / 2 * reflectionArchFactor 3) 3 := by
    have h := hcos.mul harch.hasDerivAt
    rw [cos_three_pi_div_two, zero_mul, add_zero] at h
    exact h
  have heq : (fun s : ℂ => riemannZeta (1 - s)) =ᶠ[𝓝 3] fun s : ℂ =>
      Complex.cos ((Real.pi : ℂ) * s / 2) * reflectionArchFactor s := by
    have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | 2 < s.re} ∈ 𝓝 (3 : ℂ) := hopen.mem_nhds (by norm_num)
    filter_upwards [hmem] with s hs
    have hs' : (2 : ℝ) < s.re := hs
    have hs0 : ∀ n : ℕ, s ≠ -(n : ℂ) :=
      ne_neg_natCast_of_zero_lt_re (by linarith)
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hs'
      linarith
    exact riemannZeta_one_sub_eq_cos_mul hs0 hs1
  have huniq := (heq.hasDerivAt_iff.mp hL).unique hR
  rw [reflectionArchFactor_three] at huniq
  field_simp at huniq ⊢
  linear_combination -huniq

/-- The first trivial zero of `ζ` is simple. -/
theorem deriv_riemannZeta_neg_two_ne_zero : deriv riemannZeta (-2) ≠ 0 := by
  rw [deriv_riemannZeta_neg_two]
  have h3 : riemannZeta 3 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  exact div_ne_zero (neg_ne_zero.mpr h3)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))

/-- `ζ` does not vanish on the real segment `[-1, 0)`. -/
theorem riemannZeta_ne_zero_of_neg_one_le_of_lt_zero {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x < 0) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have ht1 : 1 < 1 - x := by linarith
  have ht2 : 1 - x ≤ 2 := by linarith
  set s : ℂ := ((1 - x : ℝ) : ℂ) with hsdef
  have hsre : s.re = 1 - x := by rw [hsdef]; simp
  have hone : 1 < s.re := by rw [hsre]; linarith
  have hs0 : ∀ n : ℕ, s ≠ -(n : ℂ) := ne_neg_natCast_of_zero_lt_re (by linarith)
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hone
    linarith
  have h1s : (1 : ℂ) - s = (x : ℂ) := by rw [hsdef]; push_cast; ring
  have hzz := riemannZeta_one_sub hs0 hs1
  rw [h1s] at hzz
  rw [hzz]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => two_mul_ofReal_pi_ne_zero h.1
  · exact Complex.Gamma_ne_zero hs0
  · have hcast : ((Real.pi : ℂ) * s / 2) = ((Real.pi * (1 - x) / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    have hlow : Real.pi / 2 < Real.pi * (1 - x) / 2 := by
      have hp := Real.pi_pos
      nlinarith
    have hhigh : Real.pi * (1 - x) / 2 < Real.pi + Real.pi / 2 := by
      have hp := Real.pi_pos
      nlinarith
    have hneg : Real.cos (Real.pi * (1 - x) / 2) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt hlow hhigh
    rw [hcast, ← Complex.ofReal_cos]
    exact_mod_cast hneg.ne
  · exact riemannZeta_ne_zero_of_one_lt_re hone

end RHTower
