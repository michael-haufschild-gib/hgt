import GaloisForLFunctions.RHTower.BesselIZeroODE

/-!
# `I₀` from below at the exponential rate

The modified Bessel function of order zero grows like `e^z/sqrt(2 pi z)`.  Only the lower bound is
needed here, and only up to an absolute constant:

```text
e^z / (2 pi sqrt z)  ≤  I₀(z)      for z ≥ 1 .
```

The proof is the integral representation restricted to the window `|theta - pi/2| ≤ 1/sqrt z`, where
`sin theta = cos(theta - pi/2) ≥ 1 - 1/(2z)`, so the integrand is at least `e^(z - 1/2)/2` on a window
of length `2/sqrt z`.  No asymptotics and no saddle point are involved: the window is chosen, not
found.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

theorem exp_div_two_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have := (Real.exp_pos (-x)).le
  linarith

/-- **`I₀` from below.**  The constant is not sharp; the exponential rate and the `z^(-1/2)` are. -/
theorem exp_div_le_besselI0 {z : ℝ} (hz : 1 ≤ z) :
    Real.exp z / (2 * Real.pi * Real.sqrt z) ≤ besselI0 z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hsz : (0 : ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hsz1 : 1 ≤ Real.sqrt z := by
    nlinarith [Real.sq_sqrt hz0.le, hsz]
  set δ : ℝ := 1 / Real.sqrt z with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hsz]
    exact hsz1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ2 : (3 : ℝ) / 2 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  set a : ℝ := Real.pi / 2 - δ with hadef
  set b : ℝ := Real.pi / 2 + δ with hbdef
  have ha0 : (0 : ℝ) ≤ a := by
    rw [hadef]; linarith
  have hbπ : b ≤ Real.pi := by
    rw [hbdef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  set f : ℝ → ℝ := fun θ => Real.cosh (z * Real.sin θ) with hf
  have hfc : Continuous f := continuous_cosh_mul_sin z
  have hfnn : ∀ θ : ℝ, 0 ≤ f θ := fun θ => (Real.cosh_pos _).le
  -- the window carries at least its share of the whole integral
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := a) (c := b)
    (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (f := f) (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := b) (c := Real.pi)
    (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)
  have hleft : (0 : ℝ) ≤ ∫ θ in (0:ℝ)..a, f θ :=
    intervalIntegral.integral_nonneg ha0 fun t _ => hfnn t
  have hright : (0 : ℝ) ≤ ∫ θ in b..Real.pi, f θ :=
    intervalIntegral.integral_nonneg hbπ fun t _ => hfnn t
  have hwindow : (∫ θ in a..b, f θ) ≤ ∫ θ in (0:ℝ)..Real.pi, f θ := by
    linarith [hsplit1, hsplit2, hleft, hright]
  -- the integrand on the window
  have hbd : ∀ θ ∈ Icc a b, Real.exp (z - 1 / 2) / 2 ≤ f θ := by
    intro θ hθ
    have hsin : 1 - δ ^ 2 / 2 ≤ Real.sin θ := by
      have hcos : Real.sin θ = Real.cos (Real.pi / 2 - θ) := by
        rw [Real.cos_pi_div_two_sub]
      have hlow : 1 - (Real.pi / 2 - θ) ^ 2 / 2 ≤ Real.cos (Real.pi / 2 - θ) :=
        Real.one_sub_sq_div_two_le_cos
      have hsq : (Real.pi / 2 - θ) ^ 2 ≤ δ ^ 2 := by
        have h1 : a ≤ θ := hθ.1
        have h2 : θ ≤ b := hθ.2
        rw [hadef] at h1
        rw [hbdef] at h2
        nlinarith [h1, h2, hδ0]
      rw [hcos]
      linarith [hlow, hsq]
    have hexp : Real.exp (z - 1 / 2) ≤ Real.exp (z * Real.sin θ) := by
      rw [Real.exp_le_exp]
      have hzδ : z * δ ^ 2 = 1 := by
        rw [hδdef, div_pow, one_pow]
        rw [Real.sq_sqrt hz0.le]
        field_simp
      nlinarith [hsin, hz0, hzδ]
    have := exp_div_two_le_cosh (z * Real.sin θ)
    rw [hf]
    linarith [hexp, this]
  have hconst : (Real.exp (z - 1 / 2) / 2) * (b - a) ≤ ∫ θ in a..b, f θ := by
    have hmono : (∫ _θ in a..b, Real.exp (z - 1 / 2) / 2) ≤ ∫ θ in a..b, f θ := by
      refine intervalIntegral.integral_mono_on hab
        ((continuous_const : Continuous fun _ : ℝ => Real.exp (z - 1 / 2) / 2).intervalIntegrable
          _ _) (hfc.intervalIntegrable _ _) hbd
    have hval : (∫ _θ in a..b, Real.exp (z - 1 / 2) / 2)
        = (Real.exp (z - 1 / 2) / 2) * (b - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    linarith [hmono, hval.le, hval.ge]
  have hba : b - a = 2 * δ := by rw [hadef, hbdef]; ring
  -- assemble
  have h1 : Real.exp (z - 1 / 2) * δ ≤ ∫ θ in (0:ℝ)..Real.pi, f θ := by
    rw [hba] at hconst
    linarith [hconst, hwindow]
  have hI : Real.exp (z - 1 / 2) * δ ≤ Real.pi * besselI0 z := by
    have hval : besselI0 z = (1 / Real.pi) * ∫ θ in (0:ℝ)..Real.pi, Real.cosh (z * Real.sin θ) := by
      rw [besselI0]
    have hfeq : (∫ θ in (0:ℝ)..Real.pi, f θ)
        = ∫ θ in (0:ℝ)..Real.pi, Real.cosh (z * Real.sin θ) := by rw [hf]
    have hcancel : Real.pi * besselI0 z = ∫ θ in (0:ℝ)..Real.pi, f θ := by
      rw [hval, hfeq]
      field_simp
    rw [hcancel]
    exact h1
  have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have hlog : (1 : ℝ) / 2 < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have h2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
      have := Real.exp_lt_exp.2 hlog
      rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
      linarith
    have hpos : (0 : ℝ) < Real.exp ((1:ℝ) / 2) := Real.exp_pos _
    rw [Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith [h2]
  have hsplit : Real.exp (z - 1 / 2) = Real.exp z * Real.exp (-(1 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    ring_nf
  have hδz : δ * Real.sqrt z = 1 := by
    rw [hδdef]
    field_simp
  have hfinal : Real.exp z ≤ besselI0 z * (2 * Real.pi * Real.sqrt z) := by
    have hstep := mul_le_mul_of_nonneg_right hI (by positivity : (0:ℝ) ≤ 2 * Real.sqrt z)
    have hLHS : Real.exp (z - 1 / 2) * δ * (2 * Real.sqrt z) = 2 * Real.exp (z - 1 / 2) := by
      linear_combination (2 * Real.exp (z - 1 / 2)) * hδz
    have hRHS : Real.pi * besselI0 z * (2 * Real.sqrt z)
        = besselI0 z * (2 * Real.pi * Real.sqrt z) := by ring
    rw [hLHS, hRHS] at hstep
    have h2 : Real.exp z ≤ 2 * Real.exp (z - 1 / 2) := by
      rw [hsplit]
      nlinarith [hhalf, Real.exp_pos z]
    linarith [hstep, h2]
  rw [div_le_iff₀ (by positivity)]
  exact hfinal

end GaloisForLFunctions.RHTower

end
