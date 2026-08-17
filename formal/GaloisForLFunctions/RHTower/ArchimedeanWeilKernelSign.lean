import Mathlib

/-!
# The sign of the archimedean Weil kernel

Write the aperture-restricted archimedean Weil functional, together with the pole contribution, in
the autocorrelation variable.  For an even test correlation `g` supported in `[-S, S]` the two
contributions combine into

```
  C(S)·g 0  +  ∫_0^S (g 0 - g u) · K u  du,
```

where the weight is the elementary function

```
  K u  =  2 e^{-u/2} / (1 - e^{-2u})  -  4 cosh (u/2).
```

Since `g 0 - g u = ‖f - T_u f‖² / 2 ≥ 0` for `g = f ⋆ f̃`, the second term is a weighted Dirichlet
energy, and it is nonnegative exactly where `K` is.  This module determines the sign of `K` exactly.

**Main results.**

* `weilKernel_mul_pos_eq` — the exact identity
  `K u · (e^{-u/2}(1 - e^{-2u})) / 2 = e^{-3u} + e^{-2u} - 1`.
  The left factor is positive for `u > 0`, so the sign of the kernel is decided by the elementary
  quantity `e^{-3u} + e^{-2u} - 1`.
* `exists_unique_weilKernelThreshold` — there is a unique `u₀ > 0` with `e^{-3u₀} + e^{-2u₀} = 1`.
* `weilKernel_pos_of_lt_threshold`, `weilKernel_neg_of_threshold_lt` — the kernel is strictly
  positive below `u₀` and strictly negative above it.

So the archimedean Weil weight changes sign exactly once on `(0, ∞)`, at the root of
`e^{-3u} + e^{-2u} = 1`, and the Dirichlet-energy term is unconditionally nonnegative on every
aperture `S ≤ u₀`.  Everything here is elementary real analysis; no explicit formula and no
prolate analysis enters.
-/

namespace RHTower.ArchimedeanKernel

/-- The archimedean Weil weight in the autocorrelation variable. -/
noncomputable def weilKernel (u : ℝ) : ℝ :=
  2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) - 4 * Real.cosh (u / 2)

/-- The elementary quantity whose comparison with `1` decides the sign of the kernel. -/
noncomputable def kernelSign (u : ℝ) : ℝ := Real.exp (-3 * u) + Real.exp (-2 * u)

/-! ## Elementary exponential identities -/

theorem exp_neg_two_mul (u : ℝ) :
    Real.exp (-2 * u) =
      Real.exp (-u / 2) * Real.exp (-u / 2) * Real.exp (-u / 2) * Real.exp (-u / 2) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem exp_neg_three_mul (u : ℝ) :
    Real.exp (-3 * u) =
      Real.exp (-2 * u) * Real.exp (-u / 2) * Real.exp (-u / 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem exp_half_mul_exp_neg_half (u : ℝ) :
    Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
  rw [← Real.exp_add, show u / 2 + -u / 2 = 0 from by ring, Real.exp_zero]

theorem one_sub_exp_neg_two_mul_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-2 * u) := by
  have h : Real.exp (-2 * u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-! ## The sign identity -/

/-- **The kernel's sign is decided by `e^{-3u} + e^{-2u} - 1`.**  Multiplying the kernel by the
positive quantity `e^{-u/2}(1 - e^{-2u})/2` clears both denominators and leaves exactly that
elementary expression. -/
theorem weilKernel_mul_pos_eq {u : ℝ} (hu : 0 < u) :
    weilKernel u * (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) =
      Real.exp (-3 * u) + Real.exp (-2 * u) - 1 := by
  have hden : (1 : ℝ) - Real.exp (-2 * u) ≠ 0 := ne_of_gt (one_sub_exp_neg_two_mul_pos hu)
  have hEF := exp_half_mul_exp_neg_half u
  have hcosh : 4 * Real.cosh (u / 2) = 2 * (Real.exp (u / 2) + Real.exp (-u / 2)) := by
    rw [Real.cosh_eq, show -(u / 2) = -u / 2 from by ring]
    ring
  have hT : Real.exp (-3 * u) =
      Real.exp (-u / 2) * Real.exp (-u / 2) * Real.exp (-2 * u) := by
    rw [exp_neg_three_mul u]
    ring
  have h1 : 2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
      (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) =
      Real.exp (-u / 2) * Real.exp (-u / 2) := by
    have hself : (1 - Real.exp (-2 * u)) / (1 - Real.exp (-2 * u)) = 1 := div_self hden
    calc 2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
        (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2)
        = Real.exp (-u / 2) * Real.exp (-u / 2) *
          ((1 - Real.exp (-2 * u)) / (1 - Real.exp (-2 * u))) := by ring
      _ = Real.exp (-u / 2) * Real.exp (-u / 2) := by rw [hself]; ring
  rw [weilKernel, hcosh, hT]
  calc (2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) -
          2 * (Real.exp (u / 2) + Real.exp (-u / 2))) *
        (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2)
      = 2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
          (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) -
        2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
          (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) := by ring
    _ = Real.exp (-u / 2) * Real.exp (-u / 2) -
          (Real.exp (u / 2) * Real.exp (-u / 2) +
            Real.exp (-u / 2) * Real.exp (-u / 2)) * (1 - Real.exp (-2 * u)) := by
        rw [h1]; ring
    _ = Real.exp (-u / 2) * Real.exp (-u / 2) * Real.exp (-2 * u) +
          Real.exp (-2 * u) - 1 := by
        rw [hEF]; ring

/-- The kernel is positive exactly when `e^{-3u} + e^{-2u}` exceeds `1`. -/
theorem weilKernel_pos_iff {u : ℝ} (hu : 0 < u) :
    0 < weilKernel u ↔ 1 < kernelSign u := by
  have hE : (0 : ℝ) < Real.exp (-u / 2) := Real.exp_pos _
  have hden := one_sub_exp_neg_two_mul_pos hu
  have hfac : (0 : ℝ) < Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2 := by positivity
  have hid := weilKernel_mul_pos_eq hu
  constructor
  · intro hpos
    have : 0 < Real.exp (-3 * u) + Real.exp (-2 * u) - 1 := by
      rw [← hid]
      exact mul_pos hpos hfac
    rw [kernelSign]
    linarith
  · intro hgt
    rw [kernelSign] at hgt
    by_contra hcon
    push Not at hcon
    have hle : weilKernel u * (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon hfac.le
    rw [hid] at hle
    linarith

/-! ## The threshold -/

theorem kernelSign_strictAnti : StrictAntiOn kernelSign (Set.Ici (0 : ℝ)) := by
  intro a _ b _ hab
  rw [kernelSign, kernelSign]
  have h1 : Real.exp (-3 * b) < Real.exp (-3 * a) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have h2 : Real.exp (-2 * b) < Real.exp (-2 * a) := by
    apply Real.exp_lt_exp.mpr
    linarith
  linarith

theorem kernelSign_zero : kernelSign 0 = 2 := by
  rw [kernelSign]
  norm_num

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem kernelSign_one_lt_one : kernelSign 1 < 1 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  have h3 : (8 : ℝ) ≤ Real.exp 3 := by
    have : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    nlinarith
  have e2 : Real.exp (-2 * (1 : ℝ)) = (Real.exp 2)⁻¹ := by
    rw [show (-2 : ℝ) * 1 = -2 by ring, Real.exp_neg]
  have e3 : Real.exp (-3 * (1 : ℝ)) = (Real.exp 3)⁻¹ := by
    rw [show (-3 : ℝ) * 1 = -3 by ring, Real.exp_neg]
  rw [kernelSign, e2, e3]
  have p2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
  have p3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have i2 : (Real.exp 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ p2 (by norm_num)]
    linarith
  have i3 : (Real.exp 3)⁻¹ ≤ 1 / 8 := by
    rw [inv_le_comm₀ p3 (by norm_num)]
    linarith
  linarith

theorem continuous_kernelSign : Continuous kernelSign := by
  unfold kernelSign
  fun_prop

/-- **The threshold exists and is unique.**  There is exactly one `u₀ > 0` at which
`e^{-3u} + e^{-2u} = 1`. -/
theorem exists_unique_weilKernelThreshold :
    ∃! u₀ : ℝ, 0 < u₀ ∧ kernelSign u₀ = 1 := by
  have hcont : ContinuousOn kernelSign (Set.Icc 0 1) := continuous_kernelSign.continuousOn
  have h0 : kernelSign 0 = 2 := kernelSign_zero
  have h1 : kernelSign 1 < 1 := kernelSign_one_lt_one
  have hmem : (1 : ℝ) ∈ Set.Icc (kernelSign 1) (kernelSign 0) := by
    rw [h0]
    exact ⟨h1.le, by norm_num⟩
  obtain ⟨u₀, hu₀mem, hu₀⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  have hu₀pos : 0 < u₀ := by
    rcases lt_or_eq_of_le hu₀mem.1 with h | h
    · exact h
    · exfalso
      rw [← h, h0] at hu₀
      norm_num at hu₀
  refine ⟨u₀, ⟨hu₀pos, hu₀⟩, ?_⟩
  rintro v ⟨hvpos, hv⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := kernelSign_strictAnti (Set.mem_Ici.mpr hvpos.le) (Set.mem_Ici.mpr hu₀pos.le) hlt
    rw [hv, hu₀] at this
    exact absurd this (lt_irrefl 1)
  · have := kernelSign_strictAnti (Set.mem_Ici.mpr hu₀pos.le) (Set.mem_Ici.mpr hvpos.le) hgt
    rw [hv, hu₀] at this
    exact absurd this (lt_irrefl 1)

/-! ## The two-sided sign law -/

/-- Below the threshold the archimedean Weil weight is strictly positive. -/
theorem weilKernel_pos_of_lt_threshold {u u₀ : ℝ} (hu : 0 < u) (hu₀ : kernelSign u₀ = 1)
    (hlt : u < u₀) : 0 < weilKernel u := by
  rw [weilKernel_pos_iff hu]
  have := kernelSign_strictAnti (Set.mem_Ici.mpr hu.le)
    (Set.mem_Ici.mpr (le_of_lt (lt_trans hu hlt))) hlt
  rw [hu₀] at this
  exact this

/-- Above the threshold the archimedean Weil weight is strictly negative. -/
theorem weilKernel_neg_of_threshold_lt {u u₀ : ℝ} (hu₀pos : 0 < u₀) (hu₀ : kernelSign u₀ = 1)
    (hgt : u₀ < u) : weilKernel u < 0 := by
  have hu : 0 < u := lt_trans hu₀pos hgt
  have hlt : kernelSign u < 1 := by
    have := kernelSign_strictAnti (Set.mem_Ici.mpr hu₀pos.le) (Set.mem_Ici.mpr hu.le) hgt
    rw [hu₀] at this
    exact this
  by_contra hcon
  push Not at hcon
  rcases lt_or_eq_of_le hcon with h | h
  · have := (weilKernel_pos_iff hu).mp h
    linarith
  · have hE : (0 : ℝ) < Real.exp (-u / 2) := Real.exp_pos _
    have hden := one_sub_exp_neg_two_mul_pos hu
    have hid := weilKernel_mul_pos_eq hu
    rw [← h, zero_mul] at hid
    rw [kernelSign] at hlt
    linarith

end RHTower.ArchimedeanKernel
