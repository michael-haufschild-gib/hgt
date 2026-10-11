import GaloisForLFunctions.RHTower.XiCosineShiftPoissonFlow

/-!
# Native Poisson ports indexed by nonnegative depth and gap

These are the actual cosine-producer transfer symbols. Nonnegative parameters supply the
contraction bounds intrinsically. A zero gap is identity; every positive gap decays at infinity.
-/

namespace RHTower
noncomputable section
open Filter Classical
open scoped Topology NNReal

/-- The native transfer from depth `h+d` to depth `h`. -/
def paperPoissonSymbol (h d : ℝ≥0) (u : ℝ) : ℝ :=
  poissonMultiplier (h : ℝ) ((h + d : ℝ≥0) : ℝ) u

theorem paperPoissonSymbol_pos (h d : ℝ≥0) (u : ℝ) :
    0 < paperPoissonSymbol h d u := poissonMultiplier_pos _ _ _

theorem continuous_paperPoissonSymbol (h d : ℝ≥0) : Continuous (paperPoissonSymbol h d) :=
  continuous_poissonMultiplier _ _

@[simp] theorem paperPoissonSymbol_zero_frequency (h d : ℝ≥0) :
    paperPoissonSymbol h d 0 = 1 := by simp [paperPoissonSymbol, poissonMultiplier]

@[simp] theorem paperPoissonSymbol_zero_gap (h : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h 0 u = 1 := by
  simp [paperPoissonSymbol, poissonMultiplier, (Real.cosh_pos _).ne']

@[simp] theorem paperPoissonSymbol_neg (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d (-u) = paperPoissonSymbol h d u := by
  simp only [paperPoissonSymbol, poissonMultiplier, mul_neg, Real.cosh_neg]

theorem paperPoissonSymbol_abs (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d |u| = paperPoissonSymbol h d u := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, paperPoissonSymbol_neg]

theorem paperPoissonSymbol_le_sech (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u ≤ 1 / Real.cosh ((d : ℝ) * u) := by
  have hle : (h : ℝ) ≤ ((h + d : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    exact le_add_of_nonneg_right d.coe_nonneg
  simpa only [paperPoissonSymbol, NNReal.coe_add, add_sub_cancel_left] using
    poissonMultiplier_le h.coe_nonneg hle u

theorem paperPoissonSymbol_le_one (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u ≤ 1 := by
  refine (paperPoissonSymbol_le_sech h d u).trans ?_
  exact (div_le_one (Real.cosh_pos _)).2 (Real.one_le_cosh _)

theorem norm_paperPoissonSymbol_complex_le (h d : ℝ≥0) (u : ℝ) :
    ‖(paperPoissonSymbol h d u : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (paperPoissonSymbol_pos h d u)] using paperPoissonSymbol_le_one h d u

/-- A positive gap damps every nonzero frequency strictly. -/
theorem paperPoissonSymbol_lt_one_iff (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u < 1 ↔ d ≠ 0 ∧ u ≠ 0 := by
  constructor
  · intro hs
    constructor
    · intro hd
      rw [hd, paperPoissonSymbol_zero_gap] at hs
      exact (lt_irrefl (1 : ℝ)) hs
    · intro hu
      rw [hu, paperPoissonSymbol_zero_frequency] at hs
      exact (lt_irrefl (1 : ℝ)) hs
  · rintro ⟨hd, hu⟩
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (pos_iff_ne_zero.mpr hd)
    apply (div_lt_one (Real.cosh_pos _)).2
    apply Real.cosh_lt_cosh.2
    rw [abs_mul, abs_mul, abs_of_nonneg h.coe_nonneg,
      abs_of_nonneg (h + d).coe_nonneg, NNReal.coe_add]
    exact mul_lt_mul_of_pos_right (by linarith) (abs_pos.mpr hu)

/-- The only undamped frequency at positive gap is the single zero frequency. -/
theorem paperPoissonSymbol_eq_one_iff (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u = 1 ↔ d = 0 ∨ u = 0 := by
  constructor
  · intro hs
    by_contra hn
    have ht := (paperPoissonSymbol_lt_one_iff h d u).2 (not_or.mp hn)
    rw [hs] at ht
    exact (lt_irrefl (1 : ℝ)) ht
  · rintro (rfl | rfl)
    · exact paperPoissonSymbol_zero_gap h u
    · exact paperPoissonSymbol_zero_frequency h d

/-- Intermediate producer depths cancel exactly. -/
theorem paperPoissonSymbol_compose (h d e : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u * paperPoissonSymbol (h + d) e u =
      paperPoissonSymbol h (d + e) u := by
  simp only [paperPoissonSymbol, poissonMultiplier, NNReal.coe_add, ← add_assoc]
  field_simp [(Real.cosh_pos (((h : ℝ) + d) * u)).ne',
    (Real.cosh_pos ((((h : ℝ) + d) + e) * u)).ne']

/-- Literal source density is transported without changing its arithmetic kernel. -/
theorem paperPoissonSymbol_source_transfer (h d : ℝ≥0) (u : ℝ) :
    paperPoissonSymbol h d u *
      (riemannKernelReal u * Real.cosh (((h + d : ℝ≥0) : ℝ) * u)) =
      riemannKernelReal u * Real.cosh ((h : ℝ) * u) := by
  unfold paperPoissonSymbol poissonMultiplier
  field_simp [(Real.cosh_pos (((h + d : ℝ≥0) : ℝ) * u)).ne']

/-- The exact cofinal character: identity only at zero gap. -/
theorem tendsto_paperPoissonSymbol_atTop (h d : ℝ≥0) :
    Tendsto (paperPoissonSymbol h d) atTop (𝓝 (if d = 0 then 1 else 0)) := by
  by_cases hd : d = 0
  · rw [if_pos hd]
    subst d
    change Tendsto (fun u : ℝ => paperPoissonSymbol h 0 u) atTop (𝓝 (1 : ℝ))
    simpa only [paperPoissonSymbol_zero_gap] using
      (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ)))
  · rw [if_neg hd]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (pos_iff_ne_zero.mpr hd)
    have hexp : Tendsto (fun u : ℝ => Real.exp ((d : ℝ) * u) / 2) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hdpos tendsto_id)).atTop_div_const
        (by norm_num : (0 : ℝ) < 2)
    have hcosh : Tendsto (fun u : ℝ => Real.cosh ((d : ℝ) * u)) atTop atTop := by
      refine tendsto_atTop_mono (fun u => ?_) hexp
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-((d : ℝ) * u))]
    exact squeeze_zero (fun u => (paperPoissonSymbol_pos h d u).le)
      (paperPoissonSymbol_le_sech h d)
      (by simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcosh)

theorem norm_paperPoissonSymbol_sub_one_le (h d : ℝ≥0) (u : ℝ) :
    ‖(paperPoissonSymbol h d u : ℂ) - 1‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (paperPoissonSymbol_le_one h d u))]
  linarith [paperPoissonSymbol_pos h d u]

/-- Integer samples retain the same scalar cofinal character. -/
theorem tendsto_paperPoissonSymbol_nat (h d : ℝ≥0) :
    Tendsto (fun n : ℕ => (paperPoissonSymbol h d n : ℂ)) atTop
      (𝓝 (Complex.ofReal (if d = 0 then 1 else 0))) :=
  Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_paperPoissonSymbol_atTop h d).comp tendsto_natCast_atTop_atTop)

end
end RHTower
