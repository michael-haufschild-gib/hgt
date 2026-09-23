import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# The endpoint variation of a Bessel-modulated amplitude

Away from a turning point an oscillatory factor `cos(cξ)` costs one power of the bandwidth per
differentiation, and its total variation over a ray is `O(c)`.  At the turning point that count is
wrong: the Bessel comparison function `J₀(cξ)` is *flat* there, because `ξ` itself vanishes.  The
correct statement is the one the endpoint layer of a first-row Gram entry needs, and it comes from
a single elementary bound on the Bessel derivative,

```text
|J₀′(v)| ≤ 2|v|/π ,
```

read off from the integral representation `J₀′(v) = −(1/π)∫₀^π sin θ · sin(v sin θ) dθ` together
with `|sin y| ≤ |y|`.  Multiplying by the chain-rule factor `cξ′` turns the differentiated Bessel
term into `(c²/π)·(ξ²)′` — an exact derivative — so its total variation over `[a,b]` is
`(c²/π)(ξ(b)² − ξ(a)²)` and stays bounded exactly where `cξ` does.  No cancellation, no asymptotic
expansion, and no lower bound on `ξ′` is used.
-/

open MeasureTheory Set Filter intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The Bessel derivative near the turning point -/

theorem integral_sin_zero_pi : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ) = 2 := by
  rw [integral_sin]
  norm_num

/-- A pointwise majorant `M·sin θ` of the Bessel derivative integrand gives `|J₀′| ≤ 2M/π`. -/
theorem abs_besselJ0Deriv_le_of_bound {M u : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      |Real.sin θ * Real.sin (u * Real.sin θ)| ≤ M * Real.sin θ) :
    |besselJ0Deriv u| ≤ 2 * M / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi := hpi.le
  have hint : IntervalIntegrable
      (fun θ => Real.sin θ * Real.sin (u * Real.sin θ)) volume 0 Real.pi :=
    (continuous_sin_mul_sin u).intervalIntegrable _ _
  have hintM : IntervalIntegrable (fun θ : ℝ => M * Real.sin θ) volume 0 Real.pi :=
    ((Real.continuous_sin.const_mul M).intervalIntegrable _ _)
  have habs : |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ ∫ θ in (0 : ℝ)..Real.pi, |Real.sin θ * Real.sin (u * Real.sin θ)| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, |Real.sin θ * Real.sin (u * Real.sin θ)|)
      ≤ ∫ θ in (0 : ℝ)..Real.pi, M * Real.sin θ :=
    intervalIntegral.integral_mono_on hle hint.abs hintM hbound
  have hval : (∫ θ in (0 : ℝ)..Real.pi, M * Real.sin θ) = 2 * M := by
    rw [intervalIntegral.integral_const_mul, integral_sin_zero_pi]
    ring
  rw [hval] at hmono
  have hchain : |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)| ≤ 2 * M :=
    habs.trans hmono
  unfold besselJ0Deriv
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  calc 1 / Real.pi * |∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 1 / Real.pi * (2 * M) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = 2 * M / Real.pi := by ring

/-- **The Bessel derivative is globally bounded.** -/
theorem abs_besselJ0Deriv_le (u : ℝ) : |besselJ0Deriv u| ≤ 2 / Real.pi := by
  have h := abs_besselJ0Deriv_le_of_bound (M := 1) (u := u) zero_le_one ?_
  · simpa using h
  · intro θ hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    rw [abs_mul, abs_of_nonneg hsin, one_mul]
    exact mul_le_of_le_one_right hsin (Real.abs_sin_le_one _)

/-- **The Bessel derivative vanishes linearly at the origin.**  This is the flatness that makes the
turning-point layer contribute a bounded variation instead of one power of the bandwidth. -/
theorem abs_besselJ0Deriv_le_mul_abs (u : ℝ) : |besselJ0Deriv u| ≤ 2 * |u| / Real.pi := by
  refine abs_besselJ0Deriv_le_of_bound (M := |u|) (u := u) (abs_nonneg u) ?_
  intro θ hθ
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hstep : |Real.sin (u * Real.sin θ)| ≤ |u| * Real.sin θ := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_mul, abs_of_nonneg hsin]
  rw [abs_mul, abs_of_nonneg hsin]
  calc Real.sin θ * |Real.sin (u * Real.sin θ)|
      ≤ Real.sin θ * (|u| * Real.sin θ) := by gcongr
    _ = |u| * (Real.sin θ * Real.sin θ) := by ring
    _ ≤ |u| * (Real.sin θ * 1) := by gcongr
    _ = |u| * Real.sin θ := by ring

/-! ## The endpoint variation -/

/-- **The endpoint variation of a Bessel-modulated amplitude.**  For an amplitude bounded by `Q`
with derivative bounded by `Q′`, and a nonnegative increasing phase `Θ`, the total variation of
`A·J₀(cΘ)` over `[a,b]` is at most

```text
Q′·(b − a) + (Q c²/π)·(Θ(b)² − Θ(a)²) .
```

The differentiated Bessel term is an exact derivative: `|J₀′(cΘ)|·cΘ′ ≤ (2c²/π)·Θ Θ′`, and
`2ΘΘ′ = (Θ²)′`. -/
theorem integral_abs_deriv_besselModulated_le
    {a b c Q Q' : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (hQ0 : 0 ≤ Q)
    {A A' Θ Θ' : ℝ → ℝ}
    (hΘ : ∀ x ∈ Icc a b, HasDerivAt Θ (Θ' x) x)
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hΘc : ContinuousOn Θ (Icc a b)) (hΘ'c : ContinuousOn Θ' (Icc a b))
    (hQ : ∀ x ∈ Icc a b, |A x| ≤ Q) (hQ' : ∀ x ∈ Icc a b, |A' x| ≤ Q')
    (hΘ0 : ∀ x ∈ Icc a b, 0 ≤ Θ x) (hΘ'0 : ∀ x ∈ Icc a b, 0 ≤ Θ' x) :
    (∫ x in a..b, |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      ≤ Q' * (b - a) + Q * c ^ (2 : ℕ) * (Θ b ^ (2 : ℕ) - Θ a ^ (2 : ℕ)) / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  -- integrability of the two sides
  have hbesselCont : Continuous besselJ0 :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0 u).continuousAt
  have hbesselDCont : Continuous besselJ0Deriv :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0Deriv u).continuousAt
  have hcΘ : ContinuousOn (fun x => c * Θ x) (Icc a b) := continuousOn_const.mul hΘc
  have hL : ContinuousOn
      (fun x => |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      (Icc a b) :=
    ((hA'c.mul (hbesselCont.comp_continuousOn hcΘ)).add
      (hAc.mul ((hbesselDCont.comp_continuousOn hcΘ).mul (continuousOn_const.mul hΘ'c)))).abs
  have hR : ContinuousOn (fun x => Q' + Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x)) (Icc a b) :=
    continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_const.mul hΘc).mul hΘ'c))
  have hLint : IntervalIntegrable
      (fun x => |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hL
  have hRint : IntervalIntegrable
      (fun x => Q' + Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hR
  -- the pointwise estimate
  have hpt : ∀ x ∈ Icc a b,
      |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ Q' + Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x) := by
    intro x hx
    have h1 : |A' x * besselJ0 (c * Θ x)| ≤ Q' := by
      rw [abs_mul]
      calc |A' x| * |besselJ0 (c * Θ x)| ≤ |A' x| * 1 :=
            mul_le_mul_of_nonneg_left (abs_besselJ0_le_one _) (abs_nonneg _)
        _ = |A' x| := by ring
        _ ≤ Q' := hQ' x hx
    have hcΘ0 : 0 ≤ c * Θ x := mul_nonneg hc (hΘ0 x hx)
    have h2 : |A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x) := by
      have hb : |besselJ0Deriv (c * Θ x)| ≤ 2 * (c * Θ x) / Real.pi := by
        have h := abs_besselJ0Deriv_le_mul_abs (c * Θ x)
        rwa [abs_of_nonneg hcΘ0] at h
      have hcΘ' : |c * Θ' x| = c * Θ' x := abs_of_nonneg (mul_nonneg hc (hΘ'0 x hx))
      rw [abs_mul, abs_mul, hcΘ']
      have hstep : |A x| * (|besselJ0Deriv (c * Θ x)| * (c * Θ' x))
          ≤ Q * ((2 * (c * Θ x) / Real.pi) * (c * Θ' x)) := by
        refine mul_le_mul (hQ x hx) ?_
          (mul_nonneg (abs_nonneg _) (mul_nonneg hc (hΘ'0 x hx))) hQ0
        exact mul_le_mul_of_nonneg_right hb (mul_nonneg hc (hΘ'0 x hx))
      refine hstep.trans (le_of_eq ?_)
      field_simp
    calc |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ |A' x * besselJ0 (c * Θ x)| + |A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))| :=
          abs_add_le _ _
      _ ≤ Q' + Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x) := add_le_add h1 h2
  have hmono := intervalIntegral.integral_mono_on hab hLint hRint hpt
  refine hmono.trans (le_of_eq ?_)
  -- the majorant integrates exactly
  have hsq : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Θ y ^ (2 : ℕ)) (2 * Θ x * Θ' x) x := by
    intro x hx
    rw [huIcc] at hx
    have h := (hΘ x hx).pow 2
    refine h.congr_deriv ?_
    ring
  have hsqInt : IntervalIntegrable (fun x => 2 * Θ x * Θ' x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact (continuousOn_const.mul hΘc).mul hΘ'c
  have hFTC : (∫ x in a..b, 2 * Θ x * Θ' x) = Θ b ^ (2 : ℕ) - Θ a ^ (2 : ℕ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hsq hsqInt
  have hconstInt : IntervalIntegrable (fun _ : ℝ => Q') volume a b := intervalIntegrable_const
  have hsplit : (∫ x in a..b, (Q' + Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x)))
      = (∫ _ in a..b, Q') + ∫ x in a..b, Q * c ^ (2 : ℕ) / Real.pi * (2 * Θ x * Θ' x) :=
    intervalIntegral.integral_add hconstInt (hsqInt.const_mul _)
  rw [hsplit, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hFTC]
  simp only [smul_eq_mul]
  field_simp

/-- **The exterior variation of a Bessel-modulated amplitude.**  Using only the global bound
`|J₀′| ≤ 2/π`, the variation costs one power of the bandwidth and one factor of the total phase
increment — the `O(c)` budget the exterior part of a first-row weight needs. -/
theorem integral_abs_deriv_besselModulated_le_phase
    {a b c Q Q' : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (hQ0 : 0 ≤ Q)
    {A A' Θ Θ' : ℝ → ℝ}
    (hΘ : ∀ x ∈ Icc a b, HasDerivAt Θ (Θ' x) x)
    (hAc : ContinuousOn A (Icc a b)) (hA'c : ContinuousOn A' (Icc a b))
    (hΘc : ContinuousOn Θ (Icc a b)) (hΘ'c : ContinuousOn Θ' (Icc a b))
    (hQ : ∀ x ∈ Icc a b, |A x| ≤ Q) (hQ' : ∀ x ∈ Icc a b, |A' x| ≤ Q')
    (hΘ'0 : ∀ x ∈ Icc a b, 0 ≤ Θ' x) :
    (∫ x in a..b, |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      ≤ Q' * (b - a) + 2 * Q * c * (Θ b - Θ a) / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hbesselCont : Continuous besselJ0 :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0 u).continuousAt
  have hbesselDCont : Continuous besselJ0Deriv :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0Deriv u).continuousAt
  have hcΘ : ContinuousOn (fun x => c * Θ x) (Icc a b) := continuousOn_const.mul hΘc
  have hL : ContinuousOn
      (fun x => |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      (Icc a b) :=
    ((hA'c.mul (hbesselCont.comp_continuousOn hcΘ)).add
      (hAc.mul ((hbesselDCont.comp_continuousOn hcΘ).mul (continuousOn_const.mul hΘ'c)))).abs
  have hR : ContinuousOn (fun x => Q' + 2 * Q * c / Real.pi * Θ' x) (Icc a b) :=
    continuousOn_const.add (continuousOn_const.mul hΘ'c)
  have hLint : IntervalIntegrable
      (fun x => |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|)
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hL
  have hRint : IntervalIntegrable (fun x => Q' + 2 * Q * c / Real.pi * Θ' x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hR
  have hpt : ∀ x ∈ Icc a b,
      |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ Q' + 2 * Q * c / Real.pi * Θ' x := by
    intro x hx
    have h1 : |A' x * besselJ0 (c * Θ x)| ≤ Q' := by
      rw [abs_mul]
      calc |A' x| * |besselJ0 (c * Θ x)| ≤ |A' x| * 1 :=
            mul_le_mul_of_nonneg_left (abs_besselJ0_le_one _) (abs_nonneg _)
        _ = |A' x| := by ring
        _ ≤ Q' := hQ' x hx
    have h2 : |A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ 2 * Q * c / Real.pi * Θ' x := by
      have hcΘ' : |c * Θ' x| = c * Θ' x := abs_of_nonneg (mul_nonneg hc (hΘ'0 x hx))
      rw [abs_mul, abs_mul, hcΘ']
      have hstep : |A x| * (|besselJ0Deriv (c * Θ x)| * (c * Θ' x))
          ≤ Q * (2 / Real.pi * (c * Θ' x)) := by
        refine mul_le_mul (hQ x hx) ?_
          (mul_nonneg (abs_nonneg _) (mul_nonneg hc (hΘ'0 x hx))) hQ0
        exact mul_le_mul_of_nonneg_right (abs_besselJ0Deriv_le _)
          (mul_nonneg hc (hΘ'0 x hx))
      refine hstep.trans (le_of_eq ?_)
      field_simp
    calc |A' x * besselJ0 (c * Θ x) + A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))|
        ≤ |A' x * besselJ0 (c * Θ x)| + |A x * (besselJ0Deriv (c * Θ x) * (c * Θ' x))| :=
          abs_add_le _ _
      _ ≤ Q' + 2 * Q * c / Real.pi * Θ' x := add_le_add h1 h2
  have hmono := intervalIntegral.integral_mono_on hab hLint hRint hpt
  refine hmono.trans (le_of_eq ?_)
  have hΘuIcc : ∀ x ∈ uIcc a b, HasDerivAt Θ (Θ' x) x := by
    rw [huIcc]; exact hΘ
  have hΘ'Int : IntervalIntegrable Θ' volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hΘ'c
  have hFTC : (∫ x in a..b, Θ' x) = Θ b - Θ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hΘuIcc hΘ'Int
  have hconstInt : IntervalIntegrable (fun _ : ℝ => Q') volume a b := intervalIntegrable_const
  have hsplit : (∫ x in a..b, (Q' + 2 * Q * c / Real.pi * Θ' x))
      = (∫ _ in a..b, Q') + ∫ x in a..b, 2 * Q * c / Real.pi * Θ' x :=
    intervalIntegral.integral_add hconstInt (hΘ'Int.const_mul _)
  rw [hsplit, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hFTC]
  simp only [smul_eq_mul]
  field_simp

end GaloisForLFunctions.RHTower

end
