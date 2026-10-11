import GaloisForLFunctions.RHTower.LiSignSmallAngle

/-!
# Li's criterion along arithmetic progressions, and the reach of the zero-free band

**Progressions** (`riemannHypothesis_iff_eventually_re_xiLiPaired_progression`). For `1 ≤ a ≤ 22`
and every `b`, the Riemann hypothesis holds iff `Re 2λ_{an+b} ≥ 0` for all large `n`. The progression
has a term of absolute value `≤ a/2 ≤ 11` at some integer argument, so the small-angle theorem of
`LiSignSmallAngle` applies.

**Sharpness** (`smallAnglePair_re_liTerm_progression_pos`). The small-angle mechanism, driven only by
the bound `|arg v| ≤ 7/100` from the zero-free band, cannot reach modulus `100`. The Cayley pair
`Re^{±2πi/100}` has argument `2π/100 < 7/100`, yet its paired Li sum along `100k + 50` equals
`2(2 + Rⁿ + R⁻ⁿ) > 0`, because `e^{2πi(100k+50)/100} = −1`. Reaching larger moduli needs a higher
zero-free band (smaller off-line Cayley angles).
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-- Every progression `an + b` with `1 ≤ a` has a value of absolute value `≤ a/2` at an integer. -/
theorem exists_abs_progression_le (a b : ℕ) (ha : 1 ≤ a) :
    ∃ x₀ : ℤ, |(a : ℤ) * x₀ + b| ≤ (a / 2 : ℕ) := by
  set q : ℕ := (b + a / 2) / a with hq
  set r : ℕ := (b + a / 2) % a with hr
  have hdm : b + a / 2 = a * q + r := (Nat.div_add_mod (b + a / 2) a).symm
  have hra : r < a := Nat.mod_lt _ (by omega)
  refine ⟨-(q : ℤ), ?_⟩
  have hdmz : (b : ℤ) + ((a / 2 : ℕ) : ℤ) = (a : ℤ) * q + r := by exact_mod_cast hdm
  have hraz : (r : ℤ) < a := by exact_mod_cast hra
  have hhalf : (a : ℤ) ≤ 2 * ((a / 2 : ℕ) : ℤ) + 1 := by
    have : a ≤ 2 * (a / 2) + 1 := by omega
    exact_mod_cast this
  have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg r
  rw [abs_le]
  constructor <;> nlinarith

/-- **Li's criterion along short-modulus progressions.** For `1 ≤ a ≤ 22` and any `b`, RH holds iff
`Re 2λ_{an+b} ≥ 0` for all large `n`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_progression {a b : ℕ} (ha : 1 ≤ a)
    (ha22 : a ≤ 22) :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, 0 ≤ (xiLiPaired (a * n + b)).re := by
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hlc : 0 < (C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).leadingCoeff := by
    rw [leadingCoeff_linear haz]; exact_mod_cast (show 0 < a by omega)
  have hdeg : 1 ≤ (C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).natDegree := by
    rw [natDegree_linear haz]
  obtain ⟨x₀, hx₀⟩ := exists_abs_progression_le a b ha
  have hsmall : |(C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).eval x₀| ≤ 11 := by
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have : ((a / 2 : ℕ) : ℤ) ≤ 11 := by exact_mod_cast (show a / 2 ≤ 11 by omega)
    linarith
  have h := riemannHypothesis_iff_eventually_re_xiLiPaired_of_small_value hlc hdeg hsmall
  have e : ∀ n : ℕ, ((C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).eval (n : ℤ)).toNat = a * n + b := by
    intro n
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have : (a : ℤ) * n + b = ((a * n + b : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [e] at h
  exact h

/-! ## Sharpness: the band does not reach modulus `100` -/

/-- The unit root `e^{2πi/100}`. -/
def hundredthRoot : ℂ := Complex.exp (((2 * Real.pi / 100 : ℝ) : ℂ) * I)

theorem norm_hundredthRoot : ‖hundredthRoot‖ = 1 := by
  unfold hundredthRoot; exact Complex.norm_exp_ofReal_mul_I _

theorem arg_hundredthRoot : Complex.arg hundredthRoot = 2 * Real.pi / 100 := by
  unfold hundredthRoot
  rw [Complex.arg_exp_mul_I]
  have hπ := Real.pi_pos
  rw [toIocMod_eq_self]
  constructor <;> linarith

theorem abs_arg_hundredthRoot_le : |Complex.arg hundredthRoot| ≤ 7 / 100 := by
  rw [arg_hundredthRoot, abs_of_pos (by positivity)]
  have := Real.pi_lt_d2
  linarith

theorem re_hundredthRoot_pow_progression (k : ℕ) :
    (hundredthRoot ^ (100 * k + 50)).re = -1 := by
  unfold hundredthRoot
  rw [← Complex.exp_nat_mul, ← mul_assoc]
  have : ((100 * k + 50 : ℕ) : ℂ) * ((2 * Real.pi / 100 : ℝ) : ℂ) =
      ((Real.pi + 2 * Real.pi * k : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_add, show 2 * Real.pi * (k : ℝ) =
    (k : ℕ) * (2 * Real.pi) by ring, Real.cos_nat_mul_two_pi, Real.sin_pi]
  simp

theorem re_conj_hundredthRoot_pow_progression (k : ℕ) :
    (((starRingEnd ℂ) hundredthRoot) ^ (100 * k + 50)).re = -1 := by
  rw [← map_pow, Complex.conj_re, re_hundredthRoot_pow_progression]

/-- **The small-angle pair evading `100k + 50`.** For `R > 0` the Cayley pair `Re^{±2πi/100}` has
paired Li sum `2(2 + Rⁿ + R⁻ⁿ) > 0` at every index `n = 100k + 50`, although its argument is below
the band bound `7/100`. -/
theorem smallAnglePair_re_liTerm_progression_pos {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 < (liTerm ((R : ℂ) * hundredthRoot) (100 * k + 50)).re +
      (liTerm ((R : ℂ) * (starRingEnd ℂ) hundredthRoot) (100 * k + 50)).re := by
  have hc : ‖(starRingEnd ℂ) hundredthRoot‖ = 1 := by rw [Complex.norm_conj, norm_hundredthRoot]
  rw [re_liTerm_ofReal_mul_unit norm_hundredthRoot hR, re_liTerm_ofReal_mul_unit hc hR,
    re_hundredthRoot_pow_progression, re_conj_hundredthRoot_pow_progression]
  have h1 : 0 < R ^ (100 * k + 50) := pow_pos hR _
  have h2 : 0 < (R⁻¹) ^ (100 * k + 50) := pow_pos (inv_pos.mpr hR) _
  linarith

end RHTower

end
