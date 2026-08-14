import GaloisForLFunctions.RHTower.PrimeLogJumpBVWindow
import Mathlib.Analysis.MellinTransform

/-!
# The critical line is the zero-grade locus of the dilation

With the Sonin unitary dilation `(U_{1/r} f)(x) = r^{-1/2} f (x / r)`, the positive-ray Mellin
evaluation transforms by the exact multiplier

```text
M (U_{1/r} f)(s) = r^{1/2 - s} M f (s),
```

so the two sides of a dilation transition have Mellin normal grades differing by `1/2 - Re s`.  A
transition that preserves the size of a **nonzero** Mellin normal therefore forces `Re s = 1/2`.

This is a theorem about the constructed packets, not about Xi root modes: it is the exact falsifier
attached to the missing source-defined dagger.
-/

namespace GaloisForLFunctions.RHTower

open Complex MeasureTheory

variable {A B r : ℝ}

/-- The positive-ray Mellin evaluation, in the corpus normalization `∫_0^∞ f(x) x^{-s} dx`. -/
noncomputable def rayMellin (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f (1 - s)

theorem rayMellin_eq (f : ℝ → ℂ) (s : ℂ) :
    rayMellin f s = ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (-s) * f x := by
  rw [rayMellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [smul_eq_mul, show (1 - s - 1 : ℂ) = -s by ring]

/-- **`(14)`.**  The Mellin evaluation of the jump packet is the shell integral. -/
theorem rayMellin_jumpPacket (hA : 0 < A) (hAB : A < B) (κ : ℝ) (s : ℂ) :
    rayMellin (fun x => ((jumpPacket A B κ x : ℝ) : ℂ)) s = jumpMellin A B κ s := by
  rw [rayMellin_eq, jumpMellin, intervalIntegral.integral_of_le (le_of_lt hAB)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
  · intro x hx
    exact lt_trans hA hx.1
  · rintro x ⟨hx0, hxn⟩
    have hzero : jumpPacket A B κ x = 0 := by
      have hnot : x ∉ jumpShellSet A B := by
        rintro (h | h)
        · exact absurd (lt_trans h.2 (neg_lt_zero.mpr hA)) (not_lt.mpr (le_of_lt hx0))
        · exact hxn ⟨h.1, le_of_lt h.2⟩
      simp [jumpPacket, jumpShell, Set.indicator_of_notMem hnot]
    simp [hzero]

/-- The Sonin unitary dilation `(U_{1/r} f)(x) = r^{-1/2} f (x / r)`. -/
noncomputable def unitaryDilation (r : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * f (x / r)

/-- The half-power of a positive real, read complex. -/
theorem ofReal_sqrt_inv_eq (hr : 0 < r) :
    (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = (r : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have h1 : Real.sqrt r = r ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow r
  rw [h1, Complex.ofReal_inv, Complex.ofReal_cpow hr.le, Complex.cpow_neg]
  norm_num

/-- **`(28)`.**  The exact dilation grade of the positive-ray Mellin evaluation. -/
theorem rayMellin_unitaryDilation (hr : 0 < r) (f : ℝ → ℂ) (s : ℂ) :
    rayMellin (unitaryDilation r f) s = (r : ℂ) ^ ((1 / 2 : ℂ) - s) * rayMellin f s := by
  have hr0 : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have harg : ((r : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact fun h => absurd h.symm (ne_of_gt Real.pi_pos)
  have hfun : unitaryDilation r f = fun x : ℝ => (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * f (r⁻¹ * x) := by
    funext x
    rw [unitaryDilation, div_eq_inv_mul]
  have hmel : mellin (fun x : ℝ => (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * f (r⁻¹ * x)) (1 - s)
      = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * ((((r⁻¹ : ℝ)) : ℂ) ^ (-(1 - s)) * mellin f (1 - s)) := by
    have h1 : mellin (fun x : ℝ => (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • f (r⁻¹ * x)) (1 - s)
        = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) • mellin (fun x : ℝ => f (r⁻¹ * x)) (1 - s) :=
      mellin_const_smul _ _ _
    have h2 : mellin (fun x : ℝ => f (r⁻¹ * x)) (1 - s)
        = (((r⁻¹ : ℝ)) : ℂ) ^ (-(1 - s)) • mellin f (1 - s) :=
      mellin_comp_mul_left f (1 - s) (inv_pos.mpr hr)
    simpa [smul_eq_mul] using h1.trans (by rw [h2]; simp [smul_eq_mul])
  have hinv : (((r⁻¹ : ℝ)) : ℂ) ^ (-(1 - s)) = (r : ℂ) ^ (1 - s) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  rw [rayMellin, rayMellin, hfun, hmel, hinv, ofReal_sqrt_inv_eq hr]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hr0]
  congr 2
  ring

/-- **`(29)`.**  The grade of the dilation multiplier. -/
theorem norm_dilation_multiplier (hr : 0 < r) (s : ℂ) :
    ‖(r : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = r ^ (1 / 2 - s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  norm_num

/-- A positive base other than one has no nonzero exponent giving one. -/
theorem eq_zero_of_rpow_eq_one (hr : 0 < r) (hr1 : r ≠ 1) {y : ℝ} (h : r ^ y = 1) : y = 0 := by
  rw [Real.rpow_def_of_pos hr] at h
  have h2 : Real.exp (Real.log r * y) = Real.exp 0 := by simpa using h
  have hlog : Real.log r * y = 0 := Real.exp_eq_exp.mp h2
  rcases mul_eq_zero.mp hlog with h1 | h1
  · exfalso
    have hone : r = 1 := by
      have hexp := Real.exp_log hr
      rw [h1] at hexp
      simpa using hexp.symm
    exact hr1 hone
  · exact h1

/-- **`(30)`.**  Grade preservation of a nonzero Mellin normal forces the critical line. -/
theorem re_eq_half_of_norm_multiplier_eq_one (hr : 0 < r) (hr1 : r ≠ 1) {s : ℂ}
    (h : ‖(r : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = 1) : s.re = 1 / 2 := by
  rw [norm_dilation_multiplier hr] at h
  have := eq_zero_of_rpow_eq_one hr hr1 h
  linarith

/-- **The grade falsifier.**  If the Mellin normal of a packet is nonzero at `s` and a nontrivial
unitary dilation preserves its size there, then `s` lies on the critical line. -/
theorem re_eq_half_of_rayMellin_dilation_norm_eq (hr : 0 < r) (hr1 : r ≠ 1) {f : ℝ → ℂ} {s : ℂ}
    (hne : rayMellin f s ≠ 0)
    (h : ‖rayMellin (unitaryDilation r f) s‖ = ‖rayMellin f s‖) : s.re = 1 / 2 := by
  rw [rayMellin_unitaryDilation hr f s, norm_mul] at h
  have hpos : 0 < ‖rayMellin f s‖ := norm_pos_iff.mpr hne
  have hone : ‖(r : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = 1 := by
    refine mul_right_cancel₀ (ne_of_gt hpos) ?_
    rw [one_mul]
    exact h
  exact re_eq_half_of_norm_multiplier_eq_one hr hr1 hone

end GaloisForLFunctions.RHTower
