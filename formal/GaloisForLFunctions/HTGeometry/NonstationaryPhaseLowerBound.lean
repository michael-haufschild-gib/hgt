import GaloisForLFunctions.HTGeometry.OscillatoryIntegralVanishing

/-!
# Nonstationary phase from a lower bound on the phase derivative

`abs_integral_mul_cos_comp_le` bounds an oscillatory integral whose weight already carries the
phase speed, `∫ g · (ξ' cos(cξ + φ))`.  An integral against a bare oscillation `∫ g cos(cξ + φ)` is
brought to that form by dividing the weight by `ξ'`, which is legitimate exactly when the phase is
nonstationary: `|ξ'| ≥ m > 0`.  The quotient's variation costs one power of `m` on the weight's own
derivative and two on the phase curvature, giving the first-derivative test

```text
|∫_a^b g cos(cξ + φ)| ≤ (1/c) [ (|g(a)| + |g(b)|)/m + ∫ (|g'|/m + |g||ξ''|/m²) ] .
```

This is the estimate a two-index oscillatory product consumes: the difference of two dilated phases
has derivative bounded below by a positive multiple of the index gap, and the product amplitude and
its derivative are integrable, so the whole entry is `O(1/(c·gap))`.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- **The first-derivative test.**  A nonstationary phase converts an oscillatory integral into
`1/c` times the weight's endpoint values and total variation, each divided by the phase speed. -/
theorem abs_integral_mul_cos_phase_le {a b c φ m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g g' ξ ξ' ξ'' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ')
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hξ''c : Continuous ξ'')
    (hlow : ∀ x, m ≤ |ξ' x|) :
    |∫ x in a..b, g x * Real.cos (c * ξ x + φ)|
      ≤ (|g a| / m + |g b| / m
          + ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c := by
  have hne : ∀ x : ℝ, ξ' x ≠ 0 := by
    intro x hx
    have := hlow x
    rw [hx, abs_zero] at this
    linarith
  set G : ℝ → ℝ := fun x => g x / ξ' x with hGdef
  set G' : ℝ → ℝ := fun x => (g' x * ξ' x - g x * ξ'' x) / (ξ' x) ^ 2 with hG'def
  have hGderiv : ∀ x, HasDerivAt G (G' x) x := fun x => (hg x).div (hξ' x) (hne x)
  have hG'c : Continuous G' := by
    have : Continuous fun x : ℝ => (ξ' x) ^ 2 := hξ'c.pow 2
    exact ((hg'c.mul hξ'c).sub (hgc.mul hξ''c)).div this fun x => pow_ne_zero 2 (hne x)
  have hGc : Continuous G := hgc.div hξ'c hne
  have hrw : ∀ x : ℝ, g x * Real.cos (c * ξ x + φ)
      = G x * (ξ' x * Real.cos (c * ξ x + φ)) := by
    intro x
    have h : g x / ξ' x * (ξ' x * Real.cos (c * ξ x + φ))
        = (g x / ξ' x * ξ' x) * Real.cos (c * ξ x + φ) := by ring
    show g x * Real.cos (c * ξ x + φ) = g x / ξ' x * (ξ' x * Real.cos (c * ξ x + φ))
    rw [h, div_mul_cancel₀ _ (hne x)]
  have hmain := abs_integral_mul_cos_comp_le (a := a) (b := b) (c := c) (φ := φ)
    hab hc hGderiv hG'c hξ hξ'c
  have heq : (∫ x in a..b, g x * Real.cos (c * ξ x + φ))
      = ∫ x in a..b, G x * (ξ' x * Real.cos (c * ξ x + φ)) :=
    intervalIntegral.integral_congr fun x _ => hrw x
  rw [heq]
  refine hmain.trans ?_
  have hGa : |G a| ≤ |g a| / m := by
    rw [hGdef]
    simp only [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow a)
  have hGb : |G b| ≤ |g b| / m := by
    rw [hGdef]
    simp only [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow b)
  have hG'le : ∀ x ∈ Icc a b, |G' x| ≤ |g' x| / m + |g x| * |ξ'' x| / m ^ 2 := by
    intro x _
    have habs : |ξ' x| ≠ 0 := by
      have := hlow x
      intro h
      rw [h] at this
      linarith
    have hsq : (0 : ℝ) < |ξ' x| ^ 2 := by positivity
    have h1 : |g' x * ξ' x| / |ξ' x| ^ 2 ≤ |g' x| / m := by
      rw [abs_mul]
      rw [show |g' x| * |ξ' x| / |ξ' x| ^ 2 = |g' x| / |ξ' x| from by
        field_simp]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow x)
    have h2 : |g x * ξ'' x| / |ξ' x| ^ 2 ≤ |g x| * |ξ'' x| / m ^ 2 := by
      rw [abs_mul]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact pow_le_pow_left₀ hm.le (hlow x) 2
    calc |G' x| = |g' x * ξ' x - g x * ξ'' x| / |ξ' x| ^ 2 := by
          rw [hG'def, abs_div, abs_pow]
      _ ≤ (|g' x * ξ' x| + |g x * ξ'' x|) / |ξ' x| ^ 2 := by
          gcongr
          exact abs_sub _ _
      _ = |g' x * ξ' x| / |ξ' x| ^ 2 + |g x * ξ'' x| / |ξ' x| ^ 2 := by ring
      _ ≤ |g' x| / m + |g x| * |ξ'' x| / m ^ 2 := add_le_add h1 h2
  have hintle : (∫ x in a..b, |G' x|)
      ≤ ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) := by
    refine intervalIntegral.integral_mono_on hab (hG'c.abs.intervalIntegrable a b) ?_ hG'le
    exact (((hg'c.abs.div_const m).add
      ((hgc.abs.mul hξ''c.abs).div_const (m ^ 2)))).intervalIntegrable a b
  have hnum : |G a| + |G b| + ∫ x in a..b, |G' x|
      ≤ |g a| / m + |g b| / m + ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) := by
    linarith
  gcongr


/-- **The first-derivative test, with every hypothesis local to the interval.**  The division by the
phase speed happens under the integral sign, so it only needs the phase to be twice differentiable
and nonstationary where the integral lives.  This is the form a dilated radial phase supplies: it is
smooth and fast only on the exterior ray. -/
theorem abs_integral_mul_cos_phase_le_on {a b c φ m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g g' ξ ξ' ξ'' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hgc : ContinuousOn g (Icc a b)) (hg'c : ContinuousOn g' (Icc a b))
    (hξ : ∀ x ∈ Icc a b, HasDerivAt ξ (ξ' x) x) (hξ'c : ContinuousOn ξ' (Icc a b))
    (hξ'd : ∀ x ∈ Icc a b, HasDerivAt ξ' (ξ'' x) x) (hξ''c : ContinuousOn ξ'' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, m ≤ |ξ' x|) :
    |∫ x in a..b, g x * Real.cos (c * ξ x + φ)|
      ≤ (|g a| / m + |g b| / m
          + ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hne : ∀ x ∈ Icc a b, ξ' x ≠ 0 := by
    intro x hx hx0
    have := hlow x hx
    rw [hx0, abs_zero] at this
    linarith
  have hξcOn : ContinuousOn ξ (Icc a b) := fun x hx => (hξ x hx).continuousAt.continuousWithinAt
  set G : ℝ → ℝ := fun x => g x / ξ' x with hGdef
  set G' : ℝ → ℝ := fun x => (g' x * ξ' x - g x * ξ'' x) / (ξ' x) ^ 2 with hG'def
  set v : ℝ → ℝ := fun x => Real.sin (c * ξ x + φ) / c with hvdef
  set v' : ℝ → ℝ := fun x => ξ' x * Real.cos (c * ξ x + φ) with hv'def
  have hGderiv : ∀ x ∈ uIcc a b, HasDerivAt G (G' x) x := by
    intro x hx
    rw [huIcc] at hx
    exact (hg x hx).div (hξ'd x hx) (hne x hx)
  have hvderiv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x := by
    intro x hx
    rw [huIcc] at hx
    have hphase : HasDerivAt (fun y : ℝ => c * ξ y + φ) (c * ξ' x) x := by
      simpa using ((hξ x hx).const_mul c).add_const φ
    have h := (hphase.sin).div_const c
    refine h.congr_deriv ?_
    rw [hv'def]
    field_simp
  have hG'contIcc : ContinuousOn G' (Icc a b) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (hg'c.mul hξ'c).sub (hgc.mul hξ''c)
    · exact hξ'c.pow 2
    · intro x hx
      exact pow_ne_zero 2 (hne x hx)
  have hvcontIcc : ContinuousOn v (Icc a b) :=
    ((Real.continuous_sin.comp_continuousOn
      ((hξcOn.const_smul c).add continuousOn_const)).div_const c)
  have hv'contIcc : ContinuousOn v' (Icc a b) :=
    hξ'c.mul (Real.continuous_cos.comp_continuousOn ((hξcOn.const_smul c).add continuousOn_const))
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hGderiv hvderiv
    (hG'contIcc.intervalIntegrable_of_Icc hab) (hv'contIcc.intervalIntegrable_of_Icc hab)
  have hprod : EqOn (fun x => g x * Real.cos (c * ξ x + φ)) (fun x => G x * v' x) (uIcc a b) := by
    intro x hx
    rw [huIcc] at hx
    have hx0 := hne x hx
    show g x * Real.cos (c * ξ x + φ) = g x / ξ' x * (ξ' x * Real.cos (c * ξ x + φ))
    have h : g x / ξ' x * (ξ' x * Real.cos (c * ξ x + φ))
        = (g x / ξ' x * ξ' x) * Real.cos (c * ξ x + φ) := by ring
    rw [h, div_mul_cancel₀ _ hx0]
  rw [intervalIntegral.integral_congr hprod, hIBP]
  have hvb : ∀ y : ℝ, |v y| ≤ 1 / c := by
    intro y
    show |Real.sin (c * ξ y + φ) / c| ≤ 1 / c
    rw [abs_div, abs_of_pos hc]
    gcongr
    exact Real.abs_sin_le_one _
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbIcc : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hGa : |G a| ≤ |g a| / m := by
    rw [hGdef]
    simp only [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow a haIcc)
  have hGb : |G b| ≤ |g b| / m := by
    rw [hGdef]
    simp only [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow b hbIcc)
  have hend : |G b * v b - G a * v a| ≤ (|g b| / m + |g a| / m) / c := by
    have h1 : |G b * v b| ≤ (|g b| / m) * (1 / c) := by
      rw [abs_mul]
      exact mul_le_mul hGb (hvb b) (abs_nonneg _) (by positivity)
    have h2 : |G a * v a| ≤ (|g a| / m) * (1 / c) := by
      rw [abs_mul]
      exact mul_le_mul hGa (hvb a) (abs_nonneg _) (by positivity)
    calc |G b * v b - G a * v a| ≤ |G b * v b| + |G a * v a| := abs_sub _ _
      _ ≤ (|g b| / m) * (1 / c) + (|g a| / m) * (1 / c) := add_le_add h1 h2
      _ = (|g b| / m + |g a| / m) / c := by ring
  have hG'le : ∀ x ∈ Icc a b, |G' x| ≤ |g' x| / m + |g x| * |ξ'' x| / m ^ 2 := by
    intro x hx
    have hpos : (0 : ℝ) < |ξ' x| := lt_of_lt_of_le hm (hlow x hx)
    have hsq : (0 : ℝ) < |ξ' x| ^ 2 := by positivity
    have h1 : |g' x * ξ' x| / |ξ' x| ^ 2 ≤ |g' x| / m := by
      rw [abs_mul]
      rw [show |g' x| * |ξ' x| / |ξ' x| ^ 2 = |g' x| / |ξ' x| from by
        field_simp]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hm (hlow x hx)
    have h2 : |g x * ξ'' x| / |ξ' x| ^ 2 ≤ |g x| * |ξ'' x| / m ^ 2 := by
      rw [abs_mul]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact pow_le_pow_left₀ hm.le (hlow x hx) 2
    calc |G' x| = |g' x * ξ' x - g x * ξ'' x| / |ξ' x| ^ 2 := by
          rw [hG'def, abs_div, abs_pow]
      _ ≤ (|g' x * ξ' x| + |g x * ξ'' x|) / |ξ' x| ^ 2 := by
          gcongr
          exact abs_sub _ _
      _ = |g' x * ξ' x| / |ξ' x| ^ 2 + |g x * ξ'' x| / |ξ' x| ^ 2 := by ring
      _ ≤ |g' x| / m + |g x| * |ξ'' x| / m ^ 2 := add_le_add h1 h2
  have hmid : |∫ x in a..b, G' x * v x|
      ≤ (∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c := by
    have hint : IntervalIntegrable (fun x => G' x * v x) volume a b := by
      refine IntervalIntegrable.mul_continuousOn (hG'contIcc.intervalIntegrable_of_Icc hab) ?_
      rw [huIcc]
      exact hvcontIcc
    have hstep : |∫ x in a..b, G' x * v x| ≤ ∫ x in a..b, |G' x * v x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have hpt : ∀ x ∈ Icc a b, |G' x * v x| ≤ (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) / c := by
      intro x hx
      rw [abs_mul]
      have hb1 := hG'le x hx
      have hb2 := hvb x
      calc |G' x| * |v x| ≤ (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) * (1 / c) :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
        _ = (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) / c := by ring
    have hmajc : ContinuousOn
        (fun x => (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) / c) (Icc a b) :=
      (((hg'c.abs.div_const m).add ((hgc.abs.mul hξ''c.abs).div_const (m ^ 2))).div_const c)
    have hmono : (∫ x in a..b, |G' x * v x|)
        ≤ ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) / c :=
      intervalIntegral.integral_mono_on hab hint.abs
        (hmajc.intervalIntegrable_of_Icc hab) hpt
    have hpull : (∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2) / c)
        = (∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c :=
      intervalIntegral.integral_div _ _
    linarith [hstep, hmono, hpull.le, hpull.ge]
  have hsplit : (|g a| / m + |g b| / m
      + ∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c
      = (|g b| / m + |g a| / m) / c
        + (∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c := by
    ring
  rw [hsplit]
  calc |G b * v b - G a * v a - ∫ x in a..b, G' x * v x|
      ≤ |G b * v b - G a * v a| + |∫ x in a..b, G' x * v x| := abs_sub _ _
    _ ≤ (|g b| / m + |g a| / m) / c
        + (∫ x in a..b, (|g' x| / m + |g x| * |ξ'' x| / m ^ 2)) / c := add_le_add hend hmid

end GaloisForLFunctions.HTGeometry
