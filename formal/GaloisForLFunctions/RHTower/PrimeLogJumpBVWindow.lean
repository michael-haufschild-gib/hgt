import GaloisForLFunctions.RHTower.PrimeLogJumpMellinAsymptotic

/-!
# The two boundary channels are Mellin transforms of two compact BV windows

The desingularized channels are not abstract Bezout multipliers.  Each is the Mellin transform of a
literal compactly supported window of bounded variation on the shell:

```text
W_A(x) = (x − B) / (D x),      W_B(x) = −(x − A) / (D x),      D = B − A.
```

Integration by parts against the cumulative functions `C_A(x) = (x − B)/D` and
`C_B(x) = −(x − A)/D` — both of total mass zero on the shell — gives

```text
s ∫_A^B W_A(x) x^{-s} dx = F_A(s),      s ∫_A^B W_B(x) x^{-s} dx = F_B(s),
```

with no division by `s` anywhere, so the identity holds at every complex point.  Both windows are
strictly negative on the open shell, so both transforms are nonzero at `s = 0`; combined with the
classification of the common zeros of `F_A, F_B`, the pair `(G_A, G_B)` has **no common zero in the
whole plane**.
-/

namespace GaloisForLFunctions.RHTower

open Complex intervalIntegral

variable {A B : ℝ}

/-- The first compact BV window on the shell. -/
noncomputable def bvWindowA (A B : ℝ) : ℝ → ℝ := fun x => (x - B) / ((B - A) * x)

/-- The second compact BV window on the shell. -/
noncomputable def bvWindowB (A B : ℝ) : ℝ → ℝ := fun x => -((x - A) / ((B - A) * x))

/-- The Mellin transform of the first window: the desingularized first channel. -/
noncomputable def windowMellinA (A B : ℝ) (s : ℂ) : ℂ :=
  ∫ x in A..B, ((bvWindowA A B x : ℝ) : ℂ) * (x : ℂ) ^ (-s)

/-- The Mellin transform of the second window: the desingularized second channel. -/
noncomputable def windowMellinB (A B : ℝ) (s : ℂ) : ℂ :=
  ∫ x in A..B, ((bvWindowB A B x : ℝ) : ℂ) * (x : ℂ) ^ (-s)

/-- The Mellin kernel drops one power along the positive ray. -/
theorem cpow_neg_sub_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) / (x : ℂ) := by
  have hx0 : ((x : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]

/-- The affine cumulative function of the first window has constant derivative. -/
theorem hasDerivAt_cumulA (hAB : A < B) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (((t - B) / (B - A) : ℝ) : ℂ))
      ((((B - A)⁻¹ : ℝ) : ℂ)) x := by
  have hD : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  have h1 : HasDerivAt (fun t : ℝ => (t - B) / (B - A)) ((B - A)⁻¹) x := by
    have h0 : HasDerivAt (fun t : ℝ => t - B) 1 x := (hasDerivAt_id x).sub_const B
    simpa [div_eq_mul_inv] using h0.div_const (B - A)
  exact h1.ofReal_comp

/-- The affine cumulative function of the second window has constant derivative. -/
theorem hasDerivAt_cumulB (hAB : A < B) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((-((t - A) / (B - A)) : ℝ) : ℂ))
      (((-(B - A)⁻¹ : ℝ) : ℂ)) x := by
  have h0 : HasDerivAt (fun t : ℝ => (t - A) / (B - A)) ((B - A)⁻¹) x := by
    have h := (hasDerivAt_id x).sub_const A
    simpa [div_eq_mul_inv] using h.div_const (B - A)
  exact h0.neg.ofReal_comp

/-- Rewriting the window transform as the cumulative transform one power down. -/
theorem windowMellinA_eq (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    windowMellinA A B s
      = ∫ x in A..B, (((x - B) / (B - A) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  refine intervalIntegral.integral_congr ?_
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hxc : ((x : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
  show ((bvWindowA A B x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
      = (((x - B) / (B - A) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
  rw [cpow_neg_sub_one hx0, bvWindowA]
  push_cast
  field_simp
  ring

/-- Rewriting the second window transform as the cumulative transform one power down. -/
theorem windowMellinB_eq (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    windowMellinB A B s
      = ∫ x in A..B, ((-((x - A) / (B - A)) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
  refine intervalIntegral.integral_congr ?_
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hxc : ((x : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
  show ((bvWindowB A B x : ℝ) : ℂ) * (x : ℂ) ^ (-s)
      = ((-((x - A) / (B - A)) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
  rw [cpow_neg_sub_one hx0, bvWindowB]
  push_cast
  field_simp
  ring

/-- **`(26e)` for the first window.**  Stieltjes integration by parts against a total-mass-zero
cumulative function, with no division by `s`. -/
theorem mul_windowMellinA (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    s * windowMellinA A B s = channelA A B s := by
  have hD : ((B : ℂ) - (A : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (Complex.ofReal_inj.mp h) (by linarith)
  have hDr : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => (((t - B) / (B - A) : ℝ) : ℂ)) ((((B - A)⁻¹ : ℝ) : ℂ)) x :=
    fun x _ => hasDerivAt_cumulA hAB x
  have hv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
    fun x hx => hasDerivAt_cpow_ofReal (w := -s) (hpos x hx)
  have hu' : IntervalIntegrable (fun _ : ℝ => (((B - A)⁻¹ : ℝ) : ℂ)) MeasureTheory.volume A B :=
    intervalIntegrable_const
  have hv' : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) MeasureTheory.volume A B :=
    (intervalIntegrable_cpow hA hAB (-s - 1)).const_mul _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft : (∫ x in A..B, (((x - B) / (B - A) : ℝ) : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = -s * ∫ x in A..B, (((x - B) / (B - A) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    ring
  have hright : (∫ x in A..B, (((B - A)⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (-s))
      = (((B : ℂ) - (A : ℂ))⁻¹) * ∫ x in A..B, (x : ℂ) ^ (-s) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    push_cast
    ring
  rw [hleft, hright] at hIBP
  have hBval : (((B - B) / (B - A) : ℝ) : ℂ) = 0 := by norm_num
  have hAval : (((A - B) / (B - A) : ℝ) : ℂ) = -1 := by
    have : (A - B) / (B - A) = -1 := by rw [div_eq_iff hDr]; ring
    rw [this]
    norm_num
  rw [hBval, hAval] at hIBP
  rw [windowMellinA_eq hA hAB s, channelA, shellAverage]
  linear_combination -hIBP

/-- **`(26e)` for the second window.** -/
theorem mul_windowMellinB (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    s * windowMellinB A B s = channelB A B s := by
  have hD : ((B : ℂ) - (A : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (Complex.ofReal_inj.mp h) (by linarith)
  have hDr : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  have hpos : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hu : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((-((t - A) / (B - A)) : ℝ) : ℂ)) (((-(B - A)⁻¹ : ℝ) : ℂ)) x :=
    fun x _ => hasDerivAt_cumulB hAB x
  have hv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
    fun x hx => hasDerivAt_cpow_ofReal (w := -s) (hpos x hx)
  have hu' : IntervalIntegrable (fun _ : ℝ => ((-(B - A)⁻¹ : ℝ) : ℂ)) MeasureTheory.volume A B :=
    intervalIntegrable_const
  have hv' : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) MeasureTheory.volume A B :=
    (intervalIntegrable_cpow hA hAB (-s - 1)).const_mul _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft : (∫ x in A..B, ((-((x - A) / (B - A)) : ℝ) : ℂ) * (-s * (x : ℂ) ^ (-s - 1)))
      = -s * ∫ x in A..B, ((-((x - A) / (B - A)) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    ring
  have hright : (∫ x in A..B, ((-(B - A)⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (-s))
      = (-((B : ℂ) - (A : ℂ))⁻¹) * ∫ x in A..B, (x : ℂ) ^ (-s) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    push_cast
    ring
  rw [hleft, hright] at hIBP
  have hBval : ((-((B - A) / (B - A)) : ℝ) : ℂ) = -1 := by
    have : -((B - A) / (B - A)) = -1 := by rw [div_self hDr]
    rw [this]
    norm_num
  have hAval : ((-((A - A) / (B - A)) : ℝ) : ℂ) = 0 := by norm_num
  rw [hBval, hAval] at hIBP
  rw [windowMellinB_eq hA hAB s, channelB, shellAverage]
  linear_combination -hIBP

/-! ## The windows are strictly negative on the shell -/

theorem bvWindowA_neg (hA : 0 < A) (hAB : A < B) {x : ℝ} (hx : x ∈ Set.Ioo A B) :
    bvWindowA A B x < 0 := by
  have hx0 : 0 < x := hA.trans hx.1
  have hD : 0 < B - A := by linarith
  rw [bvWindowA, div_neg_iff]
  exact Or.inr ⟨by linarith [hx.2], by positivity⟩

theorem bvWindowB_neg (hA : 0 < A) (hAB : A < B) {x : ℝ} (hx : x ∈ Set.Ioo A B) :
    bvWindowB A B x < 0 := by
  have hx0 : 0 < x := hA.trans hx.1
  have hD : 0 < B - A := by linarith
  rw [bvWindowB, neg_neg_iff_pos, div_pos_iff]
  exact Or.inl ⟨by linarith [hx.1], by positivity⟩

theorem intervalIntegrable_bvWindowA (hA : 0 < A) (hAB : A < B) :
    IntervalIntegrable (bvWindowA A B) MeasureTheory.volume A B := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hD : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  refine ContinuousAt.continuousWithinAt ?_
  exact ((continuousAt_id.sub continuousAt_const).div
    (continuousAt_const.mul continuousAt_id) (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨hD, ne_of_gt hx0⟩))

theorem intervalIntegrable_bvWindowB (hA : 0 < A) (hAB : A < B) :
    IntervalIntegrable (bvWindowB A B) MeasureTheory.volume A B := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le (le_of_lt hAB)] at hx
    linarith [hx.1]
  have hD : (B - A) ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : A = B) (ne_of_lt hAB)
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.neg ?_
  exact ((continuousAt_id.sub continuousAt_const).div
    (continuousAt_const.mul continuousAt_id) (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨hD, ne_of_gt hx0⟩))

/-- The window transform at the origin is the total window mass. -/
theorem windowMellinA_zero (A B : ℝ) :
    windowMellinA A B 0 = ((∫ x in A..B, bvWindowA A B x : ℝ) : ℂ) := by
  rw [windowMellinA, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr ?_
  intro x _
  simp

theorem windowMellinB_zero (A B : ℝ) :
    windowMellinB A B 0 = ((∫ x in A..B, bvWindowB A B x : ℝ) : ℂ) := by
  rw [windowMellinB, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr ?_
  intro x _
  simp

/-- **`(24)`, first channel.**  The desingularized first channel is strictly negative at the
origin. -/
theorem windowMellinA_zero_ne (hA : 0 < A) (hAB : A < B) : windowMellinA A B 0 ≠ 0 := by
  have hneg : (∫ x in A..B, bvWindowA A B x) < 0 := by
    have hpos : 0 < ∫ x in A..B, -bvWindowA A B x := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        (intervalIntegrable_bvWindowA hA hAB).neg (fun x hx => ?_) hAB
      exact neg_pos.mpr (bvWindowA_neg hA hAB hx)
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  rw [windowMellinA_zero A B]
  exact fun h => absurd (Complex.ofReal_eq_zero.mp h) (ne_of_lt hneg)

/-- **`(24)`, second channel.** -/
theorem windowMellinB_zero_ne (hA : 0 < A) (hAB : A < B) : windowMellinB A B 0 ≠ 0 := by
  have hneg : (∫ x in A..B, bvWindowB A B x) < 0 := by
    have hpos : 0 < ∫ x in A..B, -bvWindowB A B x := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on
        (intervalIntegrable_bvWindowB hA hAB).neg (fun x hx => ?_) hAB
      exact neg_pos.mpr (bvWindowB_neg hA hAB hx)
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  rw [windowMellinB_zero A B]
  exact fun h => absurd (Complex.ofReal_eq_zero.mp h) (ne_of_lt hneg)

/-- **`(25)`–`(26)`, coprimality.**  The two desingularized channels have no common zero anywhere
in the complex plane. -/
theorem no_common_zero_windowMellin (hA : 0 < A) (hAB : A < B) (s : ℂ) :
    windowMellinA A B s ≠ 0 ∨ windowMellinB A B s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hcA : channelA A B s = 0 := by rw [← mul_windowMellinA hA hAB s, h1, mul_zero]
  have hcB : channelB A B s = 0 := by rw [← mul_windowMellinB hA hAB s, h2, mul_zero]
  have hs : s = 0 := eq_zero_of_channel_common_zero hA hAB hcA hcB
  subst hs
  exact windowMellinA_zero_ne hA hAB h1

end GaloisForLFunctions.RHTower
