import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideSeesEveryZero

/-!
# A real zero masks the shallower zeros

`TheStepanovSideIsBlindToRealZeros`: the Stepanov side `2 Re S(u) ≥ −K` decides the line for
configurations without real zeros, and the real pair `{¼, ¾}` passes it. The exact extent of the
blindness:

* `re_le_of_two_re_lagStructure_ge_of_realDepth`: if every real zero has depth `≤ x`, a lower bound
  `2 Re S(u) ≥ −K` puts every zero at depth `≤ x`. The Stepanov side sees every zero deeper than the
  deepest real zero.
* `stepanov_side_masked_by_real_zero`: this is sharp. The configuration `{¾, ¼, 5/8 + i, 3/8 + i}`
  passes the Stepanov side although `5/8 + i` is off the line and not real: the real zero of depth `¼`
  contributes `P e^{u/4}`, `P > 0`, which dominates `−N e^{u/8}` from the zeros of depth `1/8`.

The other side (`TheOtherSideSeesEveryZero`) has no mask. For the `L`-function of a real character a
real zero `β > ½` would hide from the Stepanov side every zero of depth `< β − ½`; for `ζ` there is no
real zero, and the Stepanov side sees everything.
-/

open Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### The Stepanov side sees beyond the real zeros -/

/-- **The deepest real zero bounds the blindness.** -/
theorem re_le_of_two_re_lagStructure_ge_of_realDepth (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {x : ℝ} (hx0 : 0 ≤ x) (hreal : ∀ ρ ∈ Z.carrier, ρ.im = 0 → ρ.re ≤ 1 / 2 + x) {K : ℝ}
    (hK : ∀ u : ℝ, 0 ≤ u → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + x := by
  intro ρ hρ
  rcases le_or_gt (1 / 2) x with hx | hx
  · linarith [(Z.strip ρ hρ).2]
  by_contra hre
  push Not at hre
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hbc := hasCompactSupport_of_support_subset_abs hbs
  have hreal' : ∀ y : ℂ, evenCoeff Z (boxSpline 1 3) y ≠ 0 → y.im = 0 → y.re ≤ x := by
    intro y hy him
    rcases mem_of_evenCoeff_ne_zero hy with h | h
    · have := hreal _ h (by simp [him])
      simp at this; linarith
    · have := hreal _ h (by simp [him])
      simp at this; linarith
  have hall : ∀ u : ℝ, 0 ≤ u → -(|K| * Real.exp (x * u)) ≤
      2 * (lagStructure Z (boxSpline 1 3) u).re := by
    intro u hu
    have he : 1 ≤ Real.exp (x * u) := Real.one_le_exp (mul_nonneg hx0 hu)
    have := mul_le_mul_of_nonneg_left he (abs_nonneg K)
    linarith [hK u hu, le_abs_self K]
  have hzero := evenCoeff_eq_zero_of_two_re_lagStructure_ge Z hZ hb hbs hx0 hx hreal' hall
    (z := ρ - 1 / 2) (by simp; linarith)
  exact evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc
    (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
    (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith))) hzero

/-! ### The mask -/

/-- A real pair of depth `¼` and a pair of depth `1/8` at height `1`. -/
def maskedConfig : ZeroConfig where
  carrier := {⟨3 / 4, 0⟩, ⟨1 / 4, 0⟩, ⟨5 / 8, 1⟩, ⟨3 / 8, 1⟩}
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ (rfl | rfl | rfl | rfl) <;> constructor <;> norm_num
  reflect_mem := by
    rintro ρ (rfl | rfl | rfl | rfl)
    · right; left; apply Complex.ext <;> norm_num [reflect]
    · left; apply Complex.ext <;> norm_num [reflect]
    · right; right; right; apply Complex.ext <;> norm_num [reflect]
    · right; right; left; apply Complex.ext <;> norm_num [reflect]
  mult_reflect := fun _ _ => rfl
  finite_window := fun _ _ => (Set.toFinite _).subset Set.inter_subset_left

theorem temperedConfig_maskedConfig : TemperedConfig maskedConfig := by
  have hfin : maskedConfig.carrier.Finite :=
    (((Set.finite_singleton _).insert _).insert _).insert _
  haveI := hfin.to_subtype
  exact Summable.of_finite

theorem mem_maskedConfig_iff (ρ : ℂ) : ρ ∈ maskedConfig.carrier ↔
    ρ = ⟨3 / 4, 0⟩ ∨ ρ = ⟨1 / 4, 0⟩ ∨ ρ = ⟨5 / 8, 1⟩ ∨ ρ = ⟨3 / 8, 1⟩ := Iff.rfl

/-- The exponents of `2 Re S`: `Re z = ¼` only at `z = ¼`, otherwise `Re z ≤ 1/8`. -/
theorem re_le_of_evenCoeff_maskedConfig_ne_zero {z : ℂ}
    (hz : evenCoeff maskedConfig (boxSpline 1 3) z ≠ 0) (hz4 : z ≠ 1 / 4) : z.re ≤ 1 / 8 := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · rw [mem_maskedConfig_iff] at h
    rcases h with h | h | h | h
    · exfalso; apply hz4
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      apply Complex.ext <;> simp <;> linarith
    all_goals have := congrArg Complex.re h; simp at this; linarith
  · rw [mem_maskedConfig_iff] at h
    rcases h with h | h | h | h
    · exfalso; apply hz4
      have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
      simp at h1 h2
      apply Complex.ext <;> simp <;> linarith
    all_goals have := congrArg Complex.re h; simp at this; linarith

/-- **A real zero masks a shallower off-line zero.** The configuration `{¾, ¼, 5/8 + i, 3/8 + i}` has
a non-real zero off the line, and its spline lag structure is bounded below. -/
theorem stepanov_side_masked_by_real_zero :
    (∃ ρ ∈ maskedConfig.carrier, ρ.im ≠ 0 ∧ ρ.re ≠ 1 / 2) ∧
      ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → -K ≤ 2 * (lagStructure maskedConfig (boxSpline 1 3) u).re := by
  classical
  refine ⟨⟨⟨5 / 8, 1⟩, (mem_maskedConfig_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))),
    by norm_num, by norm_num⟩, ?_⟩
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := temperedConfig_maskedConfig
  set e := evenCoeff maskedConfig (boxSpline 1 3) with he
  -- the dominant real exponent `¼`
  have h4mem : (1 / 2 + (1 / 4 : ℂ)) ∈ maskedConfig.carrier := by
    rw [mem_maskedConfig_iff]; left; apply Complex.ext <;> norm_num
  have hP : 0 < (e (1 / 4)).re :=
    evenCoeff_spline_pos_of_real maskedConfig h4mem (by norm_num) (by norm_num)
  set P := (e (1 / 4)).re with hPdef
  have hsum : Summable fun z => e z * cexp (z * (0 : ℝ)) :=
    (two_re_lagStructure_eq maskedConfig hZ hb hbs 0).1
  have hE : Summable fun z => ‖e z‖ := by
    have h0 := hsum.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  set N := ∑' z : ℂ, ‖e z‖ with hNdef
  have hN0 : 0 ≤ N := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨N ^ 2 / (4 * P), fun u hu => ?_⟩
  obtain ⟨hs, heq⟩ := two_re_lagStructure_eq maskedConfig hZ hb hbs u
  -- split off the term `z = ¼`
  have hsplit := hs.tsum_eq_add_tsum_ite (1 / 4 : ℂ)
  rw [← heq] at hsplit
  have hrest : ‖∑' z, (if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))‖ ≤
      N * Real.exp (u / 8) := by
    have hterm : ∀ z, ‖(if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))‖ ≤
        ‖e z‖ * Real.exp (u / 8) := by
      intro z
      split_ifs with hz4
      · simp only [norm_zero]; positivity
      · by_cases hz : e z = 0
        · simp [hz]
        rw [norm_mul, Complex.norm_exp]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        have := re_le_of_evenCoeff_maskedConfig_ne_zero hz hz4
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        nlinarith
    have hs' : Summable fun z => ‖(if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hE.mul_right _)
    calc ‖∑' z, (if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))‖
        ≤ ∑' z, ‖(if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' z, ‖e z‖ * Real.exp (u / 8) := Summable.tsum_le_tsum hterm hs' (hE.mul_right _)
      _ = N * Real.exp (u / 8) := tsum_mul_right
  -- the real part of the dominant term
  have hdom : (e (1 / 4) * cexp ((1 / 4 : ℂ) * u)).re = P * Real.exp (u / 4) := by
    have : cexp ((1 / 4 : ℂ) * u) = (Real.exp (u / 4) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre := congrArg Complex.re hsplit
  rw [Complex.ofReal_re, Complex.add_re, hdom] at hre
  have hlow : -(N * Real.exp (u / 8)) ≤
      (∑' z, (if z = (1 / 4 : ℂ) then 0 else e z * cexp (z * u))).re :=
    (neg_le_neg ((Complex.abs_re_le_norm _).trans hrest)).trans (neg_abs_le _)
  -- `P y² − N y ≥ −N²/(4P)` at `y = e^{u/8}`
  set y := Real.exp (u / 8) with hy
  have hy2 : Real.exp (u / 4) = y ^ 2 := by
    rw [hy, sq, ← Real.exp_add]; ring_nf
  rw [hy2] at hre
  have hsq : -(N ^ 2 / (4 * P)) ≤ P * y ^ 2 - N * y := by
    have hid : P * y ^ 2 - N * y + N ^ 2 / (4 * P) = (2 * P * y - N) ^ 2 / (4 * P) := by
      field_simp; ring
    have : 0 ≤ (2 * P * y - N) ^ 2 / (4 * P) := by positivity
    linarith
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
