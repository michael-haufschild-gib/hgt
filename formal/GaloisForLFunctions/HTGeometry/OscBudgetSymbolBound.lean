import GaloisForLFunctions.HTGeometry.TwoPhaseOscillatoryProduct

/-!
# The oscillatory budget of a symbol

The budget

```text
oscBudget a b m g g' Θ'' = (|g a| + |g b|)/m + ∫_a^b (|g'|/m + |g||Θ''|/m²)
```

is finite and *bounded uniformly in the right endpoint* as soon as the weight and its derivative
obey symbol bounds `|g| ≤ M/x`, `|g'| ≤ M'/x²` and the phase curvature obeys `|Θ''| ≤ N/x³` on a ray
starting at `1`.  Then

```text
oscBudget ≤ 2M/m + M'/m + M N/(3 m²) ,
```

because `∫_1^∞ x^{-2} = 1` and `∫_1^∞ x^{-4} = 1/3`.

This is what converts the first-derivative test into a genuine `O(1/(c·m))` estimate on an unbounded
exterior ray: the bound does not grow with the interval, so it survives the passage to the improper
integral.  For a product of two dilated radial amplitudes the constants carry the factor `1/(jk)`,
and `m` carries the index gap, giving the `1/(c j k |j−k|)` shape.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-! ## Two elementary tail integrals -/

theorem integral_one_div_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ 2) ≤ 1 / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun y : ℝ => -(y ^ (-1 : ℤ))) (1 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    have h := (hasDerivAt_zpow (-1 : ℤ) x (Or.inl hx0)).neg
    refine h.congr_deriv ?_
    push_cast
    field_simp
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ 2) (Icc a b) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_pow 2) ?_
    intro x hx
    have : 0 < x := lt_of_lt_of_le ha hx.1
    positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc hab)
  rw [h]
  have hval : -(b ^ (-1 : ℤ)) - -(a ^ (-1 : ℤ)) = 1 / a - 1 / b := by
    field_simp
    ring
  rw [hval]
  have hpos : (0 : ℝ) < 1 / b := by positivity
  linarith

theorem integral_one_div_pow_four_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ 4) ≤ 1 / (3 * a ^ 3) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -(1 / 3 * y ^ (-3 : ℤ))) (1 / x ^ 4) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    have h := ((hasDerivAt_zpow (-3 : ℤ) x (Or.inl hx0)).const_mul (1 / 3 : ℝ)).neg
    refine h.congr_deriv ?_
    push_cast
    field_simp
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ 4) (Icc a b) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_pow 4) ?_
    intro x hx
    have : 0 < x := lt_of_lt_of_le ha hx.1
    positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc hab)
  rw [h]
  have hval : -(1 / 3 * b ^ (-3 : ℤ)) - -(1 / 3 * a ^ (-3 : ℤ))
      = 1 / (3 * a ^ 3) - 1 / (3 * b ^ 3) := by
    field_simp
    ring
  rw [hval]
  have hpos : (0 : ℝ) < 1 / (3 * b ^ 3) := by positivity
  linarith

/-! ## The budget of a symbol -/

/-- **The symbol bound for the oscillatory budget.**  On a ray starting at `1`, a weight with the
symbol decay `|g| ≤ M/x`, `|g'| ≤ M'/x²` against a phase with curvature `|Θ''| ≤ N/x³` has a budget
bounded independently of the right endpoint. -/
theorem oscBudget_le_of_symbolBounds {a b m M M' N : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hN : 0 ≤ N)
    {g g' Θ'' : ℝ → ℝ}
    (hgc : ContinuousOn g (Icc a b)) (hg'c : ContinuousOn g' (Icc a b))
    (hΘc : ContinuousOn Θ'' (Icc a b))
    (hg : ∀ x ∈ Icc a b, |g x| ≤ M / x)
    (hg' : ∀ x ∈ Icc a b, |g' x| ≤ M' / x ^ 2)
    (hΘ : ∀ x ∈ Icc a b, |Θ'' x| ≤ N / x ^ 3) :
    oscBudget a b m g g' Θ'' ≤ 2 * M / m + M' / m + M * N / (3 * m ^ 2) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb : (1 : ℝ) ≤ b := le_trans ha hab
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  -- endpoint terms
  have hea : |g a| / m ≤ M / m := by
    have h1 : |g a| ≤ M := by
      refine (hg a haI).trans ?_
      rw [div_le_iff₀ ha0]
      nlinarith
    gcongr
  have heb : |g b| / m ≤ M / m := by
    have h1 : |g b| ≤ M := by
      refine (hg b hbI).trans ?_
      rw [div_le_iff₀ hb0]
      nlinarith
    gcongr
  -- integral term
  have hptw : ∀ x ∈ Icc a b,
      |g' x| / m + |g x| * |Θ'' x| / m ^ 2
        ≤ (M' / m) * (1 / x ^ 2) + (M * N / m ^ 2) * (1 / x ^ 4) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha0 hx.1
    have h1 : |g' x| / m ≤ (M' / m) * (1 / x ^ 2) := by
      have hgx := hg' x hx
      have hval : (M' / m) * (1 / x ^ 2) = (M' / x ^ 2) / m := by ring
      rw [hval]
      gcongr
    have h2 : |g x| * |Θ'' x| / m ^ 2 ≤ (M * N / m ^ 2) * (1 / x ^ 4) := by
      have hgx := hg x hx
      have hΘx := hΘ x hx
      have hprod : |g x| * |Θ'' x| ≤ (M / x) * (N / x ^ 3) :=
        mul_le_mul hgx hΘx (abs_nonneg _) (by positivity)
      have hm2 : (0 : ℝ) < m ^ 2 := by positivity
      rw [div_le_iff₀ hm2]
      have hval : (M * N / m ^ 2) * (1 / x ^ 4) * m ^ 2 = (M / x) * (N / x ^ 3) := by
        field_simp
      rw [hval]
      exact hprod
    linarith
  have hmajc : ContinuousOn
      (fun x : ℝ => (M' / m) * (1 / x ^ 2) + (M * N / m ^ 2) * (1 / x ^ 4)) (Icc a b) := by
    have h2 : ContinuousOn (fun x : ℝ => (1 : ℝ) / x ^ 2) (Icc a b) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_pow 2) ?_
      intro x hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
    have h4 : ContinuousOn (fun x : ℝ => (1 : ℝ) / x ^ 4) (Icc a b) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_pow 4) ?_
      intro x hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
    exact (h2.const_smul (M' / m)).add (h4.const_smul (M * N / m ^ 2))
  have hintc : ContinuousOn
      (fun x : ℝ => |g' x| / m + |g x| * |Θ'' x| / m ^ 2) (Icc a b) :=
    ((hg'c.abs.div_const m).add ((hgc.abs.mul hΘc.abs).div_const (m ^ 2)))
  have hmono : (∫ x in a..b, (|g' x| / m + |g x| * |Θ'' x| / m ^ 2))
      ≤ ∫ x in a..b, ((M' / m) * (1 / x ^ 2) + (M * N / m ^ 2) * (1 / x ^ 4)) :=
    intervalIntegral.integral_mono_on hab (hintc.intervalIntegrable_of_Icc hab)
      (hmajc.intervalIntegrable_of_Icc hab) hptw
  have hsplit : (∫ x in a..b, ((M' / m) * (1 / x ^ 2) + (M * N / m ^ 2) * (1 / x ^ 4)))
      = (M' / m) * (∫ x in a..b, 1 / x ^ 2) + (M * N / m ^ 2) * ∫ x in a..b, 1 / x ^ 4 := by
    have hi2 : IntervalIntegrable (fun x : ℝ => (M' / m) * (1 / x ^ 2)) volume a b := by
      refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
      refine ContinuousOn.const_smul ?_ (M' / m)
      refine ContinuousOn.div continuousOn_const (continuousOn_pow 2) ?_
      intro x hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
    have hi4 : IntervalIntegrable (fun x : ℝ => (M * N / m ^ 2) * (1 / x ^ 4)) volume a b := by
      refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
      refine ContinuousOn.const_smul ?_ (M * N / m ^ 2)
      refine ContinuousOn.div continuousOn_const (continuousOn_pow 4) ?_
      intro x hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
    rw [intervalIntegral.integral_add hi2 hi4, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have h2 := integral_one_div_sq_le ha0 hab
  have h4 := integral_one_div_pow_four_le ha0 hab
  have hcoef2 : (M' / m) * (∫ x in a..b, 1 / x ^ 2) ≤ (M' / m) * (1 / a) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hcoef4 : (M * N / m ^ 2) * (∫ x in a..b, 1 / x ^ 4)
      ≤ (M * N / m ^ 2) * (1 / (3 * a ^ 3)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have hend2 : (M' / m) * (1 / a) ≤ M' / m := by
    have : (1 : ℝ) / a ≤ 1 := by
      rw [div_le_one ha0]
      exact ha
    nlinarith [this, div_nonneg hM' hm.le]
  have hend4 : (M * N / m ^ 2) * (1 / (3 * a ^ 3)) ≤ M * N / (3 * m ^ 2) := by
    have ha3 : (1 : ℝ) ≤ a ^ 3 := one_le_pow₀ ha
    have hnn : (0 : ℝ) ≤ M * N / m ^ 2 := by positivity
    have hle : (1 : ℝ) / (3 * a ^ 3) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    have := mul_le_mul_of_nonneg_left hle hnn
    calc (M * N / m ^ 2) * (1 / (3 * a ^ 3)) ≤ (M * N / m ^ 2) * (1 / 3) := this
      _ = M * N / (3 * m ^ 2) := by ring
  have h2M : 2 * M / m = M / m + M / m := by ring
  rw [oscBudget]
  linarith [hea, heb, hmono, hsplit.le, hsplit.ge, hcoef2, hcoef4, hend2, hend4, h2M]


/-! ## Symbol bounds for the four product weights -/

theorem abs_half_mul_add_le {x Mj Mk p q r t : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMk : 0 ≤ Mk)
    (hp : |p| ≤ Mj / x) (hq : |q| ≤ Mk / x) (hr : |r| ≤ Mj / x) (ht : |t| ≤ Mk / x)
    (ε : ℝ) (hε : |ε| = 1) :
    |1 / 2 * (p * q + ε * (r * t))| ≤ Mj * Mk / x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hpq : |p * q| ≤ Mj * Mk / x ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hp hq (abs_nonneg _) (by positivity)
    calc |p| * |q| ≤ (Mj / x) * (Mk / x) := this
      _ = Mj * Mk / x ^ 2 := by ring
  have hrt : |r * t| ≤ Mj * Mk / x ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hr ht (abs_nonneg _) (by positivity)
    calc |r| * |t| ≤ (Mj / x) * (Mk / x) := this
      _ = Mj * Mk / x ^ 2 := by ring
  have hεabs : |ε| = 1 := hε
  have hsum : |1 / 2 * (p * q + ε * (r * t))| ≤ Mj * Mk / x ^ 2 := by
    have hstep : |1 / 2 * (p * q + ε * (r * t))| ≤ 1 / 2 * (|p * q| + |ε * (r * t)|) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    have hεrt : |ε * (r * t)| = |r * t| := by rw [abs_mul, hεabs, one_mul]
    rw [hεrt] at hstep
    linarith [hstep, hpq, hrt]
  have hmono : Mj * Mk / x ^ 2 ≤ Mj * Mk / x := by
    apply div_le_div_of_nonneg_left (by positivity) hx0
    nlinarith
  linarith

theorem abs_half_mul_deriv_le {x Mj Mj' Mk Mk' p p' q q' r r' t t' : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk')
    (hp : |p| ≤ Mj / x) (hp' : |p'| ≤ Mj' / x ^ 2)
    (hq : |q| ≤ Mk / x) (hq' : |q'| ≤ Mk' / x ^ 2)
    (hr : |r| ≤ Mj / x) (hr' : |r'| ≤ Mj' / x ^ 2)
    (ht : |t| ≤ Mk / x) (ht' : |t'| ≤ Mk' / x ^ 2)
    (ε : ℝ) (hε : |ε| = 1) :
    |1 / 2 * (p' * q + p * q' + ε * (r' * t + r * t'))|
      ≤ (Mj' * Mk + Mj * Mk') / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  have hbound : ∀ {u' Mu' v Mv : ℝ}, 0 ≤ Mu' → 0 ≤ Mv →
      |u'| ≤ Mu' / x ^ 2 → |v| ≤ Mv / x → |u' * v| ≤ Mu' * Mv / x ^ 3 := by
    intro u' Mu' v Mv hMu' hMv hu' hv
    rw [abs_mul]
    have := mul_le_mul hu' hv (abs_nonneg _) (by positivity)
    calc |u'| * |v| ≤ (Mu' / x ^ 2) * (Mv / x) := this
      _ = Mu' * Mv / x ^ 3 := by ring
  have h1 : |p' * q| ≤ Mj' * Mk / x ^ 3 := hbound hMj' hMk hp' hq
  have h2 : |p * q'| ≤ Mk' * Mj / x ^ 3 := by
    rw [mul_comm p q']
    exact hbound hMk' hMj hq' hp
  have h3 : |r' * t| ≤ Mj' * Mk / x ^ 3 := hbound hMj' hMk hr' ht
  have h4 : |r * t'| ≤ Mk' * Mj / x ^ 3 := by
    rw [mul_comm r t']
    exact hbound hMk' hMj ht' hr
  have hεabs : |ε| = 1 := hε
  have hstep : |1 / 2 * (p' * q + p * q' + ε * (r' * t + r * t'))|
      ≤ 1 / 2 * (|p' * q| + |p * q'| + (|r' * t| + |r * t'|)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hA : |p' * q + p * q' + ε * (r' * t + r * t')|
        ≤ |p' * q + p * q'| + |ε * (r' * t + r * t')| := abs_add_le _ _
    have hB : |p' * q + p * q'| ≤ |p' * q| + |p * q'| := abs_add_le _ _
    have hC : |ε * (r' * t + r * t')| = |r' * t + r * t'| := by
      rw [abs_mul, hεabs, one_mul]
    have hD : |r' * t + r * t'| ≤ |r' * t| + |r * t'| := abs_add_le _ _
    rw [hC] at hA
    linarith
  have hsum : 1 / 2 * (|p' * q| + |p * q'| + (|r' * t| + |r * t'|))
      ≤ (Mj' * Mk + Mj * Mk') / x ^ 3 := by
    have : (Mj' * Mk / x ^ 3 + Mk' * Mj / x ^ 3 + (Mj' * Mk / x ^ 3 + Mk' * Mj / x ^ 3))
        = 2 * ((Mj' * Mk + Mj * Mk') / x ^ 3) := by ring
    linarith [h1, h2, h3, h4, this]
  have hmono : (Mj' * Mk + Mj * Mk') / x ^ 3 ≤ (Mj' * Mk + Mj * Mk') / x ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  linarith


theorem abs_half_mul_add_le' {x Mj Mk p q r t : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMk : 0 ≤ Mk)
    (hp : |p| ≤ Mj / x) (hq : |q| ≤ Mk / x) (hr : |r| ≤ Mj / x) (ht : |t| ≤ Mk / x) :
    |1 / 2 * (p * q + r * t)| ≤ Mj * Mk / x := by
  have h := abs_half_mul_add_le hx hMj hMk hp hq hr ht 1 (by norm_num)
  simpa using h

theorem abs_half_mul_sub_le' {x Mj Mk p q r t : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMk : 0 ≤ Mk)
    (hp : |p| ≤ Mj / x) (hq : |q| ≤ Mk / x) (hr : |r| ≤ Mj / x) (ht : |t| ≤ Mk / x) :
    |1 / 2 * (p * q - r * t)| ≤ Mj * Mk / x := by
  have h := abs_half_mul_add_le hx hMj hMk hp hq hr ht (-1) (by norm_num)
  have hrw : 1 / 2 * (p * q + (-1 : ℝ) * (r * t)) = 1 / 2 * (p * q - r * t) := by ring
  rwa [hrw] at h

theorem abs_half_mul_deriv_add_le' {x Mj Mj' Mk Mk' p p' q q' r r' t t' : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk')
    (hp : |p| ≤ Mj / x) (hp' : |p'| ≤ Mj' / x ^ 2)
    (hq : |q| ≤ Mk / x) (hq' : |q'| ≤ Mk' / x ^ 2)
    (hr : |r| ≤ Mj / x) (hr' : |r'| ≤ Mj' / x ^ 2)
    (ht : |t| ≤ Mk / x) (ht' : |t'| ≤ Mk' / x ^ 2) :
    |1 / 2 * (p' * q + p * q' + (r' * t + r * t'))|
      ≤ (Mj' * Mk + Mj * Mk') / x ^ 2 := by
  have h := abs_half_mul_deriv_le hx hMj hMj' hMk hMk' hp hp' hq hq' hr hr' ht ht' 1
    (by norm_num)
  simpa using h

theorem abs_half_mul_deriv_sub_le' {x Mj Mj' Mk Mk' p p' q q' r r' t t' : ℝ} (hx : 1 ≤ x)
    (hMj : 0 ≤ Mj) (hMj' : 0 ≤ Mj') (hMk : 0 ≤ Mk) (hMk' : 0 ≤ Mk')
    (hp : |p| ≤ Mj / x) (hp' : |p'| ≤ Mj' / x ^ 2)
    (hq : |q| ≤ Mk / x) (hq' : |q'| ≤ Mk' / x ^ 2)
    (hr : |r| ≤ Mj / x) (hr' : |r'| ≤ Mj' / x ^ 2)
    (ht : |t| ≤ Mk / x) (ht' : |t'| ≤ Mk' / x ^ 2) :
    |1 / 2 * (p' * q + p * q' - (r' * t + r * t'))|
      ≤ (Mj' * Mk + Mj * Mk') / x ^ 2 := by
  have h := abs_half_mul_deriv_le hx hMj hMj' hMk hMk' hp hp' hq hq' hr hr' ht ht' (-1)
    (by norm_num)
  have hrw : 1 / 2 * (p' * q + p * q' + (-1 : ℝ) * (r' * t + r * t'))
      = 1 / 2 * (p' * q + p * q' - (r' * t + r * t')) := by ring
  rwa [hrw] at h

end GaloisForLFunctions.HTGeometry
