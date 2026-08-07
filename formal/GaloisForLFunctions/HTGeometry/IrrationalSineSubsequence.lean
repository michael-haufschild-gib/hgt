import Mathlib

/-!
# An irrational rotation meets the far half of the circle infinitely often

For irrational `α` the set of natural `k` with `|sin (π α k)| ≥ 1/2` is infinite.

The proof needs neither equidistribution nor pigeonhole.  If the inequality failed for every large
`k`, then at every such `k` the cosine would be large, so the doubling identity
`|sin 2x| = 2 |sin x| |cos x|` would multiply the sine by at least `8/5` each time `k` is doubled.
Iterating from one large `k` forces `|sin (π α k)| = 0`, hence `α k ∈ ℤ`, contradicting
irrationality.

This is the sharpness input of the Gevrey-slope argument: it is the only place where irrationality
of the exponent enters, and it is what makes the exact Gevrey order irrational.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

/-- A small sine forces a large cosine. -/
theorem abs_cos_ge_of_abs_sin_lt {x : ℝ} (h : |Real.sin x| < 1 / 2) :
    4 / 5 ≤ |Real.cos x| := by
  have hpyth : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have hs : Real.sin x ^ 2 < 1 / 4 := by
    have h1 : |Real.sin x| ^ 2 = Real.sin x ^ 2 := sq_abs _
    nlinarith [abs_nonneg (Real.sin x)]
  have hc : 3 / 4 < Real.cos x ^ 2 := by nlinarith
  have habs : |Real.cos x| ^ 2 = Real.cos x ^ 2 := sq_abs _
  nlinarith [abs_nonneg (Real.cos x)]

/-- Doubling multiplies a small sine by at least `8/5`. -/
theorem abs_sin_two_mul_ge {x : ℝ} (h : |Real.sin x| < 1 / 2) :
    8 / 5 * |Real.sin x| ≤ |Real.sin (2 * x)| := by
  have hcos := abs_cos_ge_of_abs_sin_lt h
  rw [Real.sin_two_mul, abs_mul, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg (Real.sin x), abs_nonneg (Real.cos x)]

/-- If every dyadic multiple of `k` has small sine, the sine at `k` vanishes. -/
theorem sin_eq_zero_of_forall_dyadic_lt {α : ℝ} {k : ℕ}
    (h : ∀ j : ℕ, |Real.sin (Real.pi * α * ((2 ^ j * k : ℕ) : ℝ))| < 1 / 2) :
    Real.sin (Real.pi * α * (k : ℝ)) = 0 := by
  set f : ℕ → ℝ := fun j => |Real.sin (Real.pi * α * ((2 ^ j * k : ℕ) : ℝ))| with hf
  have hstep : ∀ j : ℕ, 8 / 5 * f j ≤ f (j + 1) := by
    intro j
    have hx : Real.pi * α * ((2 ^ (j + 1) * k : ℕ) : ℝ)
        = 2 * (Real.pi * α * ((2 ^ j * k : ℕ) : ℝ)) := by
      push_cast
      ring
    show 8 / 5 * f j ≤ |Real.sin (Real.pi * α * ((2 ^ (j + 1) * k : ℕ) : ℝ))|
    rw [hx]
    exact abs_sin_two_mul_ge (h j)
  have hgrow : ∀ j : ℕ, (8 / 5 : ℝ) ^ j * f 0 ≤ f j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h1 := hstep j
        have h2 : (0 : ℝ) ≤ f j := abs_nonneg _
        calc (8 / 5 : ℝ) ^ (j + 1) * f 0 = 8 / 5 * ((8 / 5 : ℝ) ^ j * f 0) := by ring
          _ ≤ 8 / 5 * f j := by linarith
          _ ≤ f (j + 1) := h1
  have hzero : f 0 = 0 := by
    by_contra hne
    have hpos : 0 < f 0 := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2) / f 0 < (8 / 5 : ℝ) ^ j :=
      pow_unbounded_of_one_lt _ (by norm_num)
    have h1 : (1 / 2 : ℝ) < (8 / 5 : ℝ) ^ j * f 0 := by
      rw [div_lt_iff₀ hpos] at hj
      linarith
    have h2 := hgrow j
    have h3 := h j
    linarith
  have h0 : f 0 = |Real.sin (Real.pi * α * (k : ℝ))| := by
    show |Real.sin (Real.pi * α * ((2 ^ 0 * k : ℕ) : ℝ))| = _
    norm_num
  rw [h0] at hzero
  exact abs_eq_zero.mp hzero

/-- **An irrational rotation is far from the integers infinitely often.** -/
theorem infinite_setOf_half_le_abs_sin {α : ℝ} (hα : Irrational α) :
    {k : ℕ | 1 / 2 ≤ |Real.sin (Real.pi * α * k)|}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hsmall : ∀ m : ℕ, N + 1 ≤ m → |Real.sin (Real.pi * α * m)| < 1 / 2 := by
    intro m hm
    by_contra hcon
    have hmem : m ∈ {k : ℕ | 1 / 2 ≤ |Real.sin (Real.pi * α * k)|} := not_lt.mp hcon
    have := hN hmem
    omega
  have hdy : ∀ j : ℕ, |Real.sin (Real.pi * α * ((2 ^ j * (N + 1) : ℕ) : ℝ))| < 1 / 2 := by
    intro j
    refine hsmall _ ?_
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    calc N + 1 = 1 * (N + 1) := (one_mul _).symm
      _ ≤ 2 ^ j * (N + 1) := Nat.mul_le_mul_right _ h1
  have hsin : Real.sin (Real.pi * α * ((N + 1 : ℕ) : ℝ)) = 0 :=
    sin_eq_zero_of_forall_dyadic_lt hdy
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin
  have hkne : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hαk : α * ((N + 1 : ℕ) : ℝ) = (m : ℝ) := by
    have h1 : Real.pi * (α * ((N + 1 : ℕ) : ℝ)) = Real.pi * (m : ℝ) := by
      rw [← mul_assoc, ← hm]; ring
    exact mul_left_cancel₀ hpine h1
  have hαval : α = (m : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    field_simp
    exact hαk
  exact hα ⟨(m : ℚ) / ((N + 1 : ℕ) : ℚ), by rw [hαval]; push_cast; ring⟩

/-- The form used by the Gevrey-slope argument: the exponent enters as `s k / 2`. -/
theorem infinite_setOf_half_le_abs_sin_half {s : ℝ} (hs : Irrational s) :
    {k : ℕ | 1 / 2 ≤ |Real.sin (Real.pi * s * k / 2)|}.Infinite := by
  have hhalf : Irrational (s / 2) := by
    simpa using hs.div_natCast (m := 2) (by norm_num)
  have := infinite_setOf_half_le_abs_sin hhalf
  refine this.mono ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  have hx : Real.pi * (s / 2) * (k : ℝ) = Real.pi * s * (k : ℝ) / 2 := by ring
  rwa [hx] at hk

end GaloisForLFunctions.HTGeometry
