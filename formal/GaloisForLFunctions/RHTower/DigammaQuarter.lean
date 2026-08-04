import GaloisForLFunctions.RHTower.DigammaBounds
import GaloisForLFunctions.HTGeometry.GammaLogDeriv

/-!
# The digamma value at a quarter

Gauss's value

```text
psi(1/4) = -gamma - pi/2 - 3 log 2
```

follows from three facts the corpus and mathlib already own: Legendre duplication at `s = 1/4`,
reflection at `z = 1/4`, and `psi(1/2) = -2 log 2 - gamma`.  Adding the duplication and reflection
identities eliminates `psi(3/4)`:

```text
psi(1/4) + psi(3/4) = 2 psi(1/2) - 2 log 2,
psi(1/4) - psi(3/4) = -pi,
```

because `cot(pi/4) = 1`.

The consequence used downstream is `archRatioCharge > 0`, where
`archRatioCharge = log pi - psi(1/4)` is the first-jet magnitude of the archimedean local ratio on the
critical line.  Positivity needs no monotonicity of `psi`: every term of the closed value is
positive, and `gamma > 1/2` is in mathlib.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-! ## The two functional equations at a quarter -/

theorem quarter_ne_intCast : ∀ m : ℤ, (1 / 4 : ℂ) ≠ (m : ℂ) := by
  intro m hm
  have hcast : (((1 / 4 : ℝ)) : ℂ) = (((m : ℝ)) : ℂ) := by
    push_cast at hm ⊢
    exact hm
  have hr : (1 / 4 : ℝ) = (m : ℝ) := Complex.ofReal_injective hcast
  have h0 : (0 : ℝ) < (m : ℝ) := by rw [← hr]; norm_num
  have h1 : (m : ℝ) < 1 := by rw [← hr]; norm_num
  have hm0 : 0 < m := by exact_mod_cast h0
  have hm1 : m < 1 := by exact_mod_cast h1
  omega

theorem half_ne_negNatCast : ∀ n : ℕ, 2 * (1 / 4 : ℂ) ≠ -(n : ℂ) := by
  intro n hn
  have hre : (2 * (1 / 4 : ℂ)).re = (-(n : ℂ)).re := by rw [hn]
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have h2 : (2 * (1 / 4 : ℂ)).re = 1 / 2 := by norm_num
  rw [h2] at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [hre]

theorem digamma_quarter_add_three_quarter :
    digamma (1 / 4 : ℂ) + digamma (3 / 4 : ℂ)
      = 2 * digamma (1 / 2 : ℂ) - 2 * Complex.log 2 := by
  have h := HTGeometry.digamma_duplication (1 / 4 : ℂ) half_ne_negNatCast
  rw [show (2 : ℂ) * (1 / 4 : ℂ) = 1 / 2 from by norm_num,
    show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 from by norm_num] at h
  linear_combination -h

theorem digamma_quarter_sub_three_quarter :
    digamma (1 / 4 : ℂ) - digamma (3 / 4 : ℂ) = -(Real.pi : ℂ) := by
  have h := RHTower.digamma_reflection (z := (1 / 4 : ℂ)) quarter_ne_intCast
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 from by norm_num] at h
  have harg : (Real.pi : ℂ) * (1 / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four] at h
  have hs2 : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  rw [mul_div_assoc, div_self hs2, mul_one] at h
  exact h

/-- **Gauss's digamma value at a quarter.** -/
theorem digamma_quarter :
    digamma (1 / 4 : ℂ)
      = -(((3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2 : ℝ)) : ℂ) := by
  have hsum := digamma_quarter_add_three_quarter
  have hdiff := digamma_quarter_sub_three_quarter
  have hhalf : digamma (1 / 2 : ℂ)
      = -2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) := Complex.digamma_one_half
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hhalf, hlog] at hsum
  push_cast
  linear_combination (hsum + hdiff) / 2

/-! ## The archimedean first-jet magnitude -/

/-- The first-jet magnitude of the archimedean local ratio, `b_infinity = log pi - psi(1/4)`. -/
def archRatioCharge : ℝ :=
  Real.log Real.pi + 3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2

theorem ofReal_archRatioCharge :
    ((archRatioCharge : ℝ) : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) - digamma (1 / 4 : ℂ) := by
  rw [digamma_quarter, archRatioCharge]
  push_cast
  ring

/-- **Equation (4), positivity.**  Every term of the closed value is positive, so no monotonicity of
`psi` is needed. -/
theorem archRatioCharge_pos : 0 < archRatioCharge := by
  have hpi : 1 < Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos hpi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgamma : 0 < Real.eulerMascheroniConstant := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hpipos : 0 < Real.pi := Real.pi_pos
  rw [archRatioCharge]
  linarith

end GaloisForLFunctions.RHTower

end
