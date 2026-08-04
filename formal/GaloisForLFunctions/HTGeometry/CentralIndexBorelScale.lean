import GaloisForLFunctions.HTGeometry.MaximumModulusLocalGrowth
import GaloisForLFunctions.HTGeometry.BorelGrowthExponent

/-!
# Local growth at a Borel-good radius

The central index is nondecreasing and can jump arbitrarily, so the growth factor
`(r'/r)^{ν(r')}` across the Wiman scale `r' = r · e^{1/ν}` is not bounded at every radius.  The
Borel growth lemma supplies radii at which it is: beyond every bound there is one where the central
index does not double across the step `1/(ν+1)` in the logarithmic variable.

At such a radius the maximum modulus at `r · e^{1/(2ν)}` is at most a fixed multiple of `ν` times the
maximum term at `r`.  This is the local growth statement the composition disc needs, with the two
unbounded factors — the growth factor and the majorant-to-maximum-term ratio — both closed.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.Nevanlinna
open scoped ENNReal

variable {a : ℕ → ℂ}

/-- The central index in the logarithmic variable, shifted to be at least one. -/
noncomputable def logCentralIndex (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  (centralIndex a (Real.exp x) : ℝ) + 1

theorem one_le_logCentralIndex (a : ℕ → ℂ) (x : ℝ) : 1 ≤ logCentralIndex a x := by
  have : (0 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := Nat.cast_nonneg _
  rw [logCentralIndex]
  linarith

theorem logCentralIndex_pos (a : ℕ → ℂ) (x : ℝ) : 0 < logCentralIndex a x :=
  lt_of_lt_of_le one_pos (one_le_logCentralIndex a x)

theorem monotone_logCentralIndex (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Monotone (logCentralIndex a) := by
  intro x y hxy
  have h := centralIndex_mono ha (Real.exp_pos x) (Real.exp_le_exp.mpr hxy) hn₀
  rw [logCentralIndex, logCentralIndex]
  have hc : ((centralIndex a (Real.exp x) : ℝ)) ≤ ((centralIndex a (Real.exp y) : ℝ)) :=
    Nat.cast_le.mpr h
  linarith

/-- **A Borel-good logarithmic radius.**  Beyond every bound there is an `x` at which the central
index does not double across the step `1/(ν+1)`. -/
theorem exists_good_logRadius (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) (R : ℝ) :
    ∃ x, R ≤ x ∧
      logCentralIndex a (x + (logCentralIndex a x)⁻¹) < 2 * logCentralIndex a x := by
  obtain ⟨x, hx, hlt⟩ := exists_ge_lt_two_mul_rpow (T := logCentralIndex a)
    (monotone_logCentralIndex ha hn₀) (one_le_logCentralIndex a) one_pos R
  refine ⟨x, hx, ?_⟩
  rwa [Real.rpow_neg_one] at hlt

/-- The geometric tail ratio across a step `t` is at most `1/t`. -/
theorem exp_neg_ratio_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) / (1 - Real.exp (-t)) ≤ 1 / t := by
  have het : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hpos : 0 < Real.exp t - 1 := by linarith
  have hep : 0 < Real.exp t := Real.exp_pos t
  have hrw : Real.exp (-t) / (1 - Real.exp (-t)) = 1 / (Real.exp t - 1) := by
    rw [Real.exp_neg]
    field_simp
  rw [hrw]
  exact one_div_le_one_div_of_le ht (by linarith)

/-- **Local growth of the maximum modulus at a Borel-good radius.**  Beyond every bound there is a
radius `r = e^x` such that on the disc of radius `r · e^{1/(2ν₁)}`, with `ν₁ = ν(r) + 1`,

  `‖f w‖ ≤ 4e · ν₁ · μ(r)`.

Both losses are closed at once: the growth factor `(r'/r)^{ν(r')}` is below `e` because the central
index does not double across the step, and the majorant costs only `4ν₁` maximum terms because the
comparison radius may be taken inside the same step. -/
theorem norm_coeffFun_le_of_good (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x : ℝ}
    (hborel : logCentralIndex a (x + (logCentralIndex a x)⁻¹) < 2 * logCentralIndex a x) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ Real.exp (x + (2 * logCentralIndex a x)⁻¹) →
      ‖coeffFun a w‖
        ≤ 4 * Real.exp 1 * logCentralIndex a x * maxTerm a (Real.exp x) := by
  set ν₁ : ℝ := logCentralIndex a x with hν₁
  have hν₁pos : 0 < ν₁ := logCentralIndex_pos a x
  set t : ℝ := (2 * ν₁)⁻¹ with ht
  have htpos : 0 < t := by
    rw [ht]
    positivity
  set r : ℝ := Real.exp x with hr
  set r' : ℝ := Real.exp (x + t) with hr'
  set s : ℝ := Real.exp (x + ν₁⁻¹) with hs
  have hrpos : 0 < r := Real.exp_pos _
  have hr'pos : 0 < r' := Real.exp_pos _
  have hrr' : r ≤ r' := by
    rw [hr, hr']
    exact Real.exp_le_exp.mpr (by linarith)
  have htν : t < ν₁⁻¹ := by
    rw [ht]
    have h2 : 0 < 2 * ν₁ := by linarith
    rw [inv_lt_inv₀ h2 hν₁pos]
    linarith
  have hr's : r' < s := by
    rw [hr', hs]
    exact Real.exp_lt_exp.mpr (by linarith)
  -- the central index at the far end of the step
  have hνs : ((centralIndex a s : ℝ)) + 1 < 2 * ν₁ := by
    rw [hs, hν₁]
    exact hborel
  -- the majorant, compared inside the step
  have hmaj := coeffSum_le_maxTerm_mul_centralIndex ha hr'pos hr's hn₀
  have hratio : r' / s = Real.exp (-(ν₁⁻¹ - t)) := by
    rw [hr', hs, ← Real.exp_sub]
    congr 1
    ring
  have hgap : 0 < ν₁⁻¹ - t := by linarith
  have htail : (r' / s) / (1 - r' / s) ≤ 1 / (ν₁⁻¹ - t) := by
    rw [hratio]
    exact exp_neg_ratio_le hgap
  have hgapval : ν₁⁻¹ - t = t := by
    rw [ht]
    field_simp
    ring
  have htailval : (r' / s) / (1 - r' / s) ≤ 2 * ν₁ := by
    rw [hgapval] at htail
    have : (1 : ℝ) / t = 2 * ν₁ := by
      rw [ht, one_div, inv_inv]
    linarith [htail, this.le, this.ge]
  have hmaj' : coeffSum a r' ≤ maxTerm a r' * (4 * ν₁) := by
    refine le_trans hmaj ?_
    have hμ : (0 : ℝ) ≤ maxTerm a r' :=
      le_trans (term_nonneg a hr'pos 0) (term_le_maxTerm ha hr'pos 0)
    refine mul_le_mul_of_nonneg_left ?_ hμ
    linarith [hνs, htailval]
  -- the growth factor across the step
  have hνr' : (centralIndex a r' : ℝ) < 2 * ν₁ := by
    have hmono : centralIndex a r' ≤ centralIndex a s :=
      centralIndex_mono ha hr'pos (le_of_lt hr's) hn₀
    have : ((centralIndex a r' : ℝ)) ≤ ((centralIndex a s : ℝ)) := Nat.cast_le.mpr hmono
    linarith
  have hgrow : maxTerm a r' ≤ maxTerm a r * (r' / r) ^ (centralIndex a r') :=
    maxTerm_le_mul_pow ha hrpos hrr' hn₀
  have hquot : r' / r = Real.exp t := by
    rw [hr, hr', ← Real.exp_sub]
    congr 1
    ring
  have hfactor : (r' / r) ^ (centralIndex a r') ≤ Real.exp 1 := by
    rw [hquot, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    rw [ht]
    have h2 : 0 < 2 * ν₁ := by linarith
    rw [mul_inv_le_iff₀ h2]
    linarith [hνr']
  -- assemble
  intro w hw0 hw
  have hstep₁ : ‖coeffFun a w‖ ≤ coeffSum a ‖w‖ := norm_coeffFun_le ha hw0
  have hstep₂ : coeffSum a ‖w‖ ≤ coeffSum a r' := coeffSum_mono ha hw0 hw
  have hμr : (0 : ℝ) ≤ maxTerm a r :=
    le_trans (term_nonneg a hrpos 0) (term_le_maxTerm ha hrpos 0)
  have hchain : maxTerm a r' ≤ Real.exp 1 * maxTerm a r := by
    refine le_trans hgrow ?_
    rw [mul_comm (Real.exp 1) (maxTerm a r)]
    exact mul_le_mul_of_nonneg_left hfactor hμr
  have hν₁nn : (0 : ℝ) ≤ 4 * ν₁ := by linarith
  calc ‖coeffFun a w‖ ≤ coeffSum a r' := le_trans hstep₁ hstep₂
    _ ≤ maxTerm a r' * (4 * ν₁) := hmaj'
    _ ≤ (Real.exp 1 * maxTerm a r) * (4 * ν₁) := mul_le_mul_of_nonneg_right hchain hν₁nn
    _ = 4 * Real.exp 1 * ν₁ * maxTerm a r := by ring

/-- **Local growth at a cofinal set of radii.** -/
theorem exists_logRadius_norm_coeffFun_le (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) (R : ℝ) :
    ∃ x, R ≤ x ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ Real.exp (x + (2 * logCentralIndex a x)⁻¹) →
        ‖coeffFun a w‖
          ≤ 4 * Real.exp 1 * logCentralIndex a x * maxTerm a (Real.exp x) := by
  obtain ⟨x, hx, hborel⟩ := exists_good_logRadius ha hn₀ R
  exact ⟨x, hx, norm_coeffFun_le_of_good ha hn₀ hborel⟩

/-! ## Good radii in a prescribed window

The Borel lemma bounds the measure of the bad set, so a good radius is found not merely beyond every
bound but inside *every* interval longer than that bound.  This is what allows the Borel selection to
be intersected with a window prescribed by another selection. -/

/-- **A good radius inside every long enough interval.** -/
theorem exists_mem_Icc_lt_two_mul_rpow {T : ℝ → ℝ} {α : ℝ}
    (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (hα : 0 < α) {A B : ℝ}
    (hAB : (1 - ENNReal.ofReal (((2 : ℝ) ^ α)⁻¹))⁻¹ < ENNReal.ofReal (B - A)) :
    ∃ x ∈ Set.Icc A B, T (x + (T x) ^ (-α)) < 2 * T x := by
  by_contra hcon
  have hbad : Set.Icc A B ⊆ {r : ℝ | A ≤ r ∧ 2 * T r ≤ T (r + (T r) ^ (-α))} := by
    intro r hr
    refine ⟨hr.1, ?_⟩
    by_contra h
    exact hcon ⟨r, hr, not_le.mp h⟩
  have hvol := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hbad
  rw [Real.volume_Icc] at hvol
  exact absurd (le_trans hvol (borel_growth_monotone_rpow hmono hT1 hα A)) (not_le.mpr hAB)

/-- **A Borel-good logarithmic radius inside a prescribed window.** -/
theorem exists_good_logRadius_mem_Icc (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {A B : ℝ}
    (hAB : (1 - ENNReal.ofReal (((2 : ℝ) ^ (1 : ℝ))⁻¹))⁻¹ < ENNReal.ofReal (B - A)) :
    ∃ x ∈ Set.Icc A B,
      logCentralIndex a (x + (logCentralIndex a x)⁻¹) < 2 * logCentralIndex a x := by
  obtain ⟨x, hx, hlt⟩ := exists_mem_Icc_lt_two_mul_rpow (T := logCentralIndex a)
    (monotone_logCentralIndex ha hn₀) (one_le_logCentralIndex a) one_pos hAB
  refine ⟨x, hx, ?_⟩
  rwa [Real.rpow_neg_one] at hlt

/-- **Local growth at a radius inside a prescribed window.** -/
theorem exists_mem_Icc_norm_coeffFun_le (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {A B : ℝ}
    (hAB : (1 - ENNReal.ofReal (((2 : ℝ) ^ (1 : ℝ))⁻¹))⁻¹ < ENNReal.ofReal (B - A)) :
    ∃ x ∈ Set.Icc A B,
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ Real.exp (x + (2 * logCentralIndex a x)⁻¹) →
        ‖coeffFun a w‖
          ≤ 4 * Real.exp 1 * logCentralIndex a x * maxTerm a (Real.exp x) := by
  obtain ⟨x, hx, hborel⟩ := exists_good_logRadius_mem_Icc ha hn₀ hAB
  exact ⟨x, hx, norm_coeffFun_le_of_good ha hn₀ hborel⟩

/-- The measure bound at exponent one is exactly `2`. -/
theorem borel_bound_one : (1 - ENNReal.ofReal (((2 : ℝ) ^ (1 : ℝ))⁻¹))⁻¹ = 2 := by
  rw [Real.rpow_one]
  have h : ENNReal.ofReal ((2 : ℝ)⁻¹) = 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [h, ENNReal.one_sub_inv_two, inv_inv]

/-- **A window longer than `2` contains a Borel-good logarithmic radius.** -/
theorem exists_good_logRadius_of_two_lt (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {A B : ℝ} (hAB : 2 < B - A) :
    ∃ x ∈ Set.Icc A B,
      logCentralIndex a (x + (logCentralIndex a x)⁻¹) < 2 * logCentralIndex a x := by
  refine exists_good_logRadius_mem_Icc ha hn₀ ?_
  rw [borel_bound_one]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
    rw [ENNReal.ofReal_ofNat]
  rw [h2]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr hAB

/-- **Local growth at a radius inside any window longer than `2`.** -/
theorem exists_norm_coeffFun_le_of_two_lt (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {A B : ℝ} (hAB : 2 < B - A) :
    ∃ x ∈ Set.Icc A B,
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ Real.exp (x + (2 * logCentralIndex a x)⁻¹) →
        ‖coeffFun a w‖
          ≤ 4 * Real.exp 1 * logCentralIndex a x * maxTerm a (Real.exp x) := by
  obtain ⟨x, hx, hborel⟩ := exists_good_logRadius_of_two_lt ha hn₀ hAB
  exact ⟨x, hx, norm_coeffFun_le_of_good ha hn₀ hborel⟩

/-! ## The Wiman window already carries the Borel condition

The parameter selection of `WimanValironSelection.exists_good_parameters` delivers, alongside the
window, the non-doubling statement `ν(e^{d+2H}) + 1 < 2(ν(e^x) + 1)` across the *whole* window.  A
point selected later inside that window therefore inherits the Borel condition, and no second
selection has to be intersected with the first. -/

/-- **Window non-doubling gives the Borel condition at any interior point.**  If the central index
does not double across `[x, d + 2H]` and the step `1/ν₁` fits inside `H`, then every selected point
`x'` of the window is Borel-good. -/
theorem good_of_window_no_double (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x x' d H : ℝ} (hxx' : x ≤ x') (hx'd : x' ≤ d + H)
    (hstep : (logCentralIndex a x')⁻¹ ≤ H)
    (hnd : logCentralIndex a (d + 2 * H) < 2 * logCentralIndex a x) :
    logCentralIndex a (x' + (logCentralIndex a x')⁻¹) < 2 * logCentralIndex a x' := by
  have hmono := monotone_logCentralIndex ha hn₀
  have h1 : x' + (logCentralIndex a x')⁻¹ ≤ d + 2 * H := by linarith
  have h2 : logCentralIndex a (x' + (logCentralIndex a x')⁻¹) ≤ logCentralIndex a (d + 2 * H) :=
    hmono h1
  have h3 : logCentralIndex a x ≤ logCentralIndex a x' := hmono hxx'
  linarith

/-- **Local growth at a point of a Wiman window.**  The bound of `norm_coeffFun_le_of_good`, with the
Borel hypothesis replaced by the window non-doubling that the parameter selection already provides. -/
theorem norm_coeffFun_le_of_window (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x x' d H : ℝ} (hxx' : x ≤ x') (hx'd : x' ≤ d + H)
    (hstep : (logCentralIndex a x')⁻¹ ≤ H)
    (hnd : logCentralIndex a (d + 2 * H) < 2 * logCentralIndex a x) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ Real.exp (x' + (2 * logCentralIndex a x')⁻¹) →
      ‖coeffFun a w‖
        ≤ 4 * Real.exp 1 * logCentralIndex a x' * maxTerm a (Real.exp x') :=
  norm_coeffFun_le_of_good ha hn₀ (good_of_window_no_double ha hn₀ hxx' hx'd hstep hnd)

/-- The non-doubling conclusion of the parameter selection, in `logCentralIndex` form. -/
theorem logCentralIndex_no_double_iff (a : ℕ → ℂ) (x y : ℝ) :
    (logCentralIndex a y < 2 * logCentralIndex a x)
      ↔ ((centralIndex a (Real.exp y) : ℝ)) + 1
          < 2 * (((centralIndex a (Real.exp x) : ℝ)) + 1) := by
  rw [logCentralIndex, logCentralIndex]

end GaloisForLFunctions.HTGeometry
