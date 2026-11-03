import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCenterPartOfTheBulkEntries
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossMatrixIsCloseToItsCenterKernel
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# The cross error of the bulk entries

At overlap `0 < c < 1` the complete Weil matrix carries the cross error
`Cr(n, j) = X(s)/∫g² − ((∫g)²/∫g²) ω(|log(j/n)|)`, the exact archimedean pairing `X` of two atoms
`g = φ(·N/c)` at distance `s = |log(j/n)|` minus its center-density value (RAPT).

* **The entry** (`atomCrossErrorKernel_atomDilate_eq`): `Cr = (w/I) ∫ A(τ)(ω(s + wτ) − ω(s)) dτ`,
  `w = c/N`, `I = ∫φ²`, `A` the autocorrelation of `φ`.
* **The singular part** (`abs_crossError_sub_profile_le`): `ω(y) = 1/(2y) + O(1)`
  (`abs_archLevyDensity_sub_inv_le`), and the `1/(2y)` part is the exact function
  `σ(w/s)`, `σ(r) = (1/(2I))∫A(τ)(r/(1 + rτ) − r)`, of `w/s ≈ cn/(Nd)`; so
  `Cr(n, n + d) = (n/N) G_d(n/N) + O(1/N)` with `G_d(u) = (1/(2I))∫A(τ)(c/d)(1/(1 + cuτ/d) − 1)dτ`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence

/-! ### The archimedean density near its pole -/

theorem one_div_one_sub_exp_neg_sub_one_div {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / (1 - Real.exp (-x)) - 1 / x ∧ 1 / (1 - Real.exp (-x)) - 1 / x ≤ 1 := by
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-x) := by linarith
  have h1 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have h3 : (1 + x) * Real.exp (-x) ≤ 1 := by
    have hx1 := Real.add_one_le_exp x
    have hexp : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-x)]
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hd h1)
  · have e : 1 + 1 / x = (1 + x) / x := by field_simp; ring
    rw [sub_le_iff_le_add, e, div_le_div_iff₀ hd hx]
    nlinarith

/-- `|ω(y) − 1/(2y)| ≤ 5/4` for `y > 0`. -/
theorem abs_archLevyDensity_sub_inv_le {y : ℝ} (hy : 0 < y) :
    |_root_.RHTower.archLevyDensity y - 1 / (2 * y)| ≤ 5 / 4 := by
  obtain ⟨h0, h1⟩ := one_div_one_sub_exp_neg_sub_one_div (by linarith : 0 < 2 * y)
  have hE : 0 < Real.exp (-y / 2) := Real.exp_pos _
  have hE1 : Real.exp (-y / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE2 : 1 - y / 2 ≤ Real.exp (-y / 2) := by linarith [Real.add_one_le_exp (-y / 2)]
  have hd : 1 - Real.exp (-(2 * y)) ≠ 0 := by
    have : Real.exp (-(2 * y)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hy0 : y ≠ 0 := hy.ne'
  have e : _root_.RHTower.archLevyDensity y - 1 / (2 * y) =
      Real.exp (-y / 2) * (1 / (1 - Real.exp (-(2 * y))) - 1 / (2 * y)) +
        (Real.exp (-y / 2) - 1) / (2 * y) := by
    unfold _root_.RHTower.archLevyDensity
    rw [show -2 * y = -(2 * y) by ring]
    field_simp
    ring
  rw [e]
  have hb1 : |Real.exp (-y / 2) * (1 / (1 - Real.exp (-(2 * y))) - 1 / (2 * y))| ≤ 1 := by
    rw [abs_mul, abs_of_pos hE, abs_of_nonneg h0]
    nlinarith
  have hb2 : |(Real.exp (-y / 2) - 1) / (2 * y)| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * y), abs_of_nonpos (by linarith),
      div_le_iff₀ (by linarith)]
    linarith
  calc _ ≤ 1 + 1 / 4 := (abs_add_le _ _).trans (add_le_add hb1 hb2)
    _ = 5 / 4 := by norm_num

/-! ### The autocorrelation of the profile -/

section Autocorrelation

variable {φ : ℝ → ℝ}

theorem bumpAutocorr_atomDilate (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) (z : ℝ) :
    bumpAutocorr (atomDilate φ w) z = w * bumpAutocorr φ (z / w) := by
  unfold bumpAutocorr atomDilate
  have h := MeasureTheory.Measure.integral_comp_div (fun v => φ v * φ (v + z / w)) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  rw [← h]
  congr 1
  funext u
  rw [add_div]

theorem bumpAutocorr_profile_eq_zero (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {τ : ℝ}
    (hτ : 1 < |τ|) : bumpAutocorr φ τ = 0 :=
  bumpAutocorr_eq_zero hφsupp hτ

theorem stronglyMeasurable_bumpAutocorr (hg : Continuous φ) :
    StronglyMeasurable (bumpAutocorr φ) := by
  have hc : Continuous fun p : ℝ × ℝ => φ p.2 * φ (p.2 + p.1) := by fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

theorem exists_abs_bumpAutocorr_le (hg : Continuous φ) (hgc : HasCompactSupport φ) :
    ∃ B, ∀ τ, |bumpAutocorr φ τ| ≤ B := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hg1 : Integrable fun u => |φ u| := (hg.integrable_of_hasCompactSupport hgc).abs
  refine ⟨B * ∫ u, |φ u|, fun z => ?_⟩
  unfold bumpAutocorr
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
    (hg1.const_mul B) (Filter.Eventually.of_forall fun u => ?_)
  show |φ u * φ (u + z)| ≤ B * |φ u|
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (by have := hB (u + z); rwa [Real.norm_eq_abs] at this)
    (abs_nonneg _)

/-- `A·F` is integrable when `F` is measurable and bounded on `[−1, 1]`. -/
theorem integrable_bumpAutocorr_mul (hg : Continuous φ) (hgc : HasCompactSupport φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {F : ℝ → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ τ ∈ Set.Icc (-1 : ℝ) 1, |F τ| ≤ M) :
    Integrable fun τ => bumpAutocorr φ τ * F τ := by
  obtain ⟨B, hB⟩ := exists_abs_bumpAutocorr_le hg hgc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩)
  have hvan : ∀ τ, τ ∉ Set.Icc (-1 : ℝ) 1 → bumpAutocorr φ τ = 0 := fun τ hτ =>
    bumpAutocorr_profile_eq_zero hφsupp (by
      by_contra h
      exact hτ (abs_le.mp (not_lt.mp h)))
  refine integrable_of_bounded_of_vanish (a := -1) (b := 1) (C := B * M)
    ((stronglyMeasurable_bumpAutocorr hg).aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (fun τ hτ => by rw [hvan τ hτ, zero_mul]) fun τ => ?_
  by_cases hτ : τ ∈ Set.Icc (-1 : ℝ) 1
  · rw [abs_mul]; exact mul_le_mul (hB τ) (hM τ hτ) (abs_nonneg _) ((abs_nonneg _).trans (hB τ))
  · rw [hvan τ hτ, zero_mul, abs_zero]
    exact mul_nonneg ((abs_nonneg _).trans (hB 0)) hM0

theorem integrable_bumpAutocorr (hg : Continuous φ) (hgc : HasCompactSupport φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) : Integrable (bumpAutocorr φ) := by
  have := integrable_bumpAutocorr_mul hg hgc hφsupp (F := fun _ => 1) measurable_const
    (M := 1) (fun _ _ => by simp)
  simpa using this

/-- `|∫ A F| ≤ M ∫ |A|` when `|F| ≤ M` on `[−1, 1]`. -/
theorem abs_integral_bumpAutocorr_mul_le (hg : Continuous φ) (hgc : HasCompactSupport φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {F : ℝ → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ τ ∈ Set.Icc (-1 : ℝ) 1, |F τ| ≤ M) :
    |∫ τ, bumpAutocorr φ τ * F τ| ≤ M * ∫ τ, |bumpAutocorr φ τ| := by
  have hint := integrable_bumpAutocorr_mul hg hgc hφsupp hF hM
  have hA := (integrable_bumpAutocorr hg hgc hφsupp).abs
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hint.abs (hA.const_mul M) fun τ => ?_)
  show |bumpAutocorr φ τ * F τ| ≤ M * |bumpAutocorr φ τ|
  by_cases hτ : τ ∈ Set.Icc (-1 : ℝ) 1
  · rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hM τ hτ) (abs_nonneg _)
  · have : bumpAutocorr φ τ = 0 := bumpAutocorr_profile_eq_zero hφsupp (by
      by_contra h; exact hτ (abs_le.mp (not_lt.mp h)))
    rw [this]; simp

end Autocorrelation

/-! ### The cross term as an integral of the autocorrelation -/

/-- `X(s) − ω(s)(∫g)² = ∫ (ω(s + z) − ω(s)) G(z) dz` for an atom on `[0, w]`, `w < s`. -/
theorem atomCrossTerm_sub_eq {g : ℝ → ℝ} {w s : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (hws : w < s) :
    atomCrossTerm g s - _root_.RHTower.archLevyDensity s * (∫ u, g u) ^ 2 =
      ∫ z, (_root_.RHTower.archLevyDensity (s + z) - _root_.RHTower.archLevyDensity s) *
        bumpAutocorr g z := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hGsupp : ∀ z, z ∉ Set.Icc (-w) w → bumpAutocorr g z = 0 := fun z hz =>
    bumpAutocorr_eq_zero hgsupp (by
      by_contra h
      exact hz ⟨by linarith [neg_abs_le z, not_lt.mp h], (le_abs_self z).trans (not_lt.mp h)⟩)
  have hGm : StronglyMeasurable (bumpAutocorr g) := stronglyMeasurable_bumpAutocorr hg
  have hg1 : Integrable fun u => |g u| := (hg.integrable_of_hasCompactSupport hgc).abs
  have hGb : ∀ z, |bumpAutocorr g z| ≤ B * ∫ u, |g u| := fun z => by
    unfold bumpAutocorr
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
      (hg1.const_mul B) (Filter.Eventually.of_forall fun u => ?_)
    show |g u * g (u + z)| ≤ B * |g u|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by have := hB (u + z); rwa [Real.norm_eq_abs] at this)
      (abs_nonneg _)
  have hGint : Integrable (bumpAutocorr g) :=
    integrable_of_bounded_of_vanish hGm.aestronglyMeasurable hGsupp hGb
  have hsw : 0 < s - w := by linarith
  have hωb : ∀ z ∈ Set.Icc (-w) w,
      |_root_.RHTower.archLevyDensity (s + z) - _root_.RHTower.archLevyDensity s| ≤
      _root_.RHTower.archLevyDensity (s - w) - _root_.RHTower.archLevyDensity (s + w) := by
    intro z hz
    have hmem : ∀ t ∈ Set.Icc (s - w) (s + w), t ∈ Set.Ioi (0 : ℝ) := fun t ht =>
      lt_of_lt_of_le hsw ht.1
    have h1 := archLevyDensity_antitoneOn (hmem (s - w) ⟨le_rfl, by linarith⟩)
      (hmem (s + z) ⟨by linarith [hz.1], by linarith [hz.2]⟩) (by linarith [hz.1])
    have h2 := archLevyDensity_antitoneOn (hmem (s + z) ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      (hmem (s + w) ⟨by linarith, le_rfl⟩) (by linarith [hz.2])
    have h3 := archLevyDensity_antitoneOn (hmem (s - w) ⟨le_rfl, by linarith⟩)
      (hmem s ⟨by linarith, by linarith⟩) (by linarith)
    have h4 := archLevyDensity_antitoneOn (hmem s ⟨by linarith, by linarith⟩)
      (hmem (s + w) ⟨by linarith, le_rfl⟩) (by linarith)
    rw [abs_le]; constructor <;> linarith
  have hX : atomCrossTerm g s = ∫ z, _root_.RHTower.archLevyDensity (s + z) * bumpAutocorr g z := by
    unfold atomCrossTerm
    rw [← integral_indicator measurableSet_Ioi]
    rw [← integral_add_right_eq_self
      (fun y => (Set.Ioi (0 : ℝ)).indicator
        (fun y => _root_.RHTower.archLevyDensity y * bumpAutocorr g (y - s)) y) s]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : z ∈ Set.Icc (-w) w
    · have hpos : z + s ∈ Set.Ioi (0 : ℝ) := by
        show 0 < z + s; linarith [hz.1]
      rw [Set.indicator_of_mem hpos, add_sub_cancel_right, add_comm z s]
    · rw [hGsupp z hz, mul_zero]
      by_cases hpos : z + s ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hpos, add_sub_cancel_right, hGsupp z hz, mul_zero]
      · rw [Set.indicator_of_notMem hpos]
  have hdiff_int : Integrable fun z => (_root_.RHTower.archLevyDensity (s + z) -
      _root_.RHTower.archLevyDensity s) * bumpAutocorr g z := by
    refine integrable_of_bounded_of_vanish (a := -w) (b := w)
      (C := (_root_.RHTower.archLevyDensity (s - w) - _root_.RHTower.archLevyDensity (s + w)) *
        (B * ∫ u, |g u|)) ?_ ?_ ?_
    · exact ((_root_.RHTower.measurable_archLevyDensity.comp
        (measurable_const.add measurable_id)).sub
        measurable_const).aestronglyMeasurable.mul hGm.aestronglyMeasurable
    · intro z hz; rw [hGsupp z hz, mul_zero]
    · intro z
      by_cases hz : z ∈ Set.Icc (-w) w
      · rw [abs_mul]
        exact mul_le_mul (hωb z hz) (hGb z) (abs_nonneg _)
          (by linarith [abs_nonneg (_root_.RHTower.archLevyDensity (s + z) -
            _root_.RHTower.archLevyDensity s), hωb z hz])
      · rw [hGsupp z hz, mul_zero, abs_zero]
        have h0 : 0 ≤ _root_.RHTower.archLevyDensity (s - w) -
            _root_.RHTower.archLevyDensity (s + w) :=
          sub_nonneg.mpr (archLevyDensity_antitoneOn (Set.mem_Ioi.mpr hsw)
            (Set.mem_Ioi.mpr (by linarith)) (by linarith))
        have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
        have hA0 : 0 ≤ ∫ u, |g u| := integral_nonneg fun _ => abs_nonneg _
        positivity
  have hsplit : ∫ z, _root_.RHTower.archLevyDensity (s + z) * bumpAutocorr g z =
      (∫ z, (_root_.RHTower.archLevyDensity (s + z) - _root_.RHTower.archLevyDensity s) *
        bumpAutocorr g z) + _root_.RHTower.archLevyDensity s * ∫ z, bumpAutocorr g z := by
    rw [← integral_const_mul, ← integral_add hdiff_int (hGint.const_mul _)]
    congr 1; funext z; ring
  rw [hX, hsplit, integral_bumpAutocorr hg hgc, add_sub_cancel_right]

/-- **The cross-error entry**: `Cr(n, j) = (w/I) ∫ A(τ)(ω(s + wτ) − ω(s)) dτ`, `s = |log j − log n|`. -/
theorem atomCrossErrorKernel_atomDilate_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {w : ℝ} (hw : 0 < w)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) (hnj : n ≠ j)
    (hws : w < |Real.log j - Real.log n|) :
    atomCrossErrorKernel (atomDilate φ w) n j = w / (∫ u, φ u ^ 2) *
      ∫ τ, bumpAutocorr φ τ * (_root_.RHTower.archLevyDensity (|Real.log j - Real.log n| + w * τ) -
        _root_.RHTower.archLevyDensity |Real.log j - Real.log n|) := by
  set s := |Real.log j - Real.log n| with hs
  obtain ⟨hgC, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw
  have h1 := atomCrossTerm_sub_eq hgC.continuous hgc hgsupp hw.le hws
  have hI : ∫ u, atomDilate φ w u ^ 2 = w * ∫ u, φ u ^ 2 := integral_atomDilate_sq φ hw
  have hcenter : archimedeanCenterKernel n j = _root_.RHTower.archLevyDensity s := by
    unfold archimedeanCenterKernel
    rw [if_neg (by omega)]
  have hsub : ∫ z, (_root_.RHTower.archLevyDensity (s + z) - _root_.RHTower.archLevyDensity s) *
      bumpAutocorr (atomDilate φ w) z = w * w * ∫ τ, bumpAutocorr φ τ *
        (_root_.RHTower.archLevyDensity (s + w * τ) - _root_.RHTower.archLevyDensity s) := by
    simp_rw [bumpAutocorr_atomDilate φ hw]
    have h := MeasureTheory.Measure.integral_comp_div (fun τ => bumpAutocorr φ τ *
      (_root_.RHTower.archLevyDensity (s + w * τ) - _root_.RHTower.archLevyDensity s)) w
    simp only [smul_eq_mul, abs_of_pos hw] at h
    have e : ∀ z, (_root_.RHTower.archLevyDensity (s + z) - _root_.RHTower.archLevyDensity s) *
        (w * bumpAutocorr φ (z / w)) = w * (bumpAutocorr φ (z / w) *
          (_root_.RHTower.archLevyDensity (s + w * (z / w)) - _root_.RHTower.archLevyDensity s)) :=
      fun z => by rw [mul_div_cancel₀ z hw.ne']; ring
    simp_rw [e]
    rw [integral_const_mul, h]
    ring
  rw [atomCrossErrorKernel, if_neg hnj, hcenter]
  have hG0 : (∫ u, atomDilate φ w u ^ 2) ≠ 0 := by rw [hI]; positivity
  have e2 : atomCrossTerm (atomDilate φ w) s / (∫ u, atomDilate φ w u ^ 2) -
      (∫ u, atomDilate φ w u) ^ 2 / (∫ u, atomDilate φ w u ^ 2) *
        _root_.RHTower.archLevyDensity s =
      (atomCrossTerm (atomDilate φ w) s - _root_.RHTower.archLevyDensity s *
        (∫ u, atomDilate φ w u) ^ 2) / (∫ u, atomDilate φ w u ^ 2) := by ring
  rw [e2, h1, hsub, hI]
  field_simp

/-! ### The singular profile -/

/-- The singular cross profile `σ(r) = (1/(2I)) ∫ A(τ)(r/(1 + rτ) − r) dτ`. -/
def crossSingular (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  1 / (2 * ∫ u, φ u ^ 2) * ∫ τ, bumpAutocorr φ τ * (r / (1 + r * τ) - r)

/-- The row profile `G_d(u) = (1/(2I)) ∫ A(τ)(c/d)(1/(1 + (cu/d)τ) − 1) dτ`. -/
def crossProfile (φ : ℝ → ℝ) (c : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  1 / (2 * ∫ u, φ u ^ 2) * ∫ τ, bumpAutocorr φ τ * (c / d * (1 / (1 + c * u / d * τ) - 1))

theorem crossSingular_eq (φ : ℝ → ℝ) (c : ℝ) (d : ℕ) (u : ℝ) :
    crossSingular φ (c * u / d) = u * crossProfile φ c d u := by
  unfold crossSingular crossProfile
  have hin : (∫ τ, bumpAutocorr φ τ * (c * u / d / (1 + c * u / d * τ) - c * u / d)) =
      u * ∫ τ, bumpAutocorr φ τ * (c / d * (1 / (1 + c * u / d * τ) - 1)) := by
    rw [← integral_const_mul]
    congr 1
    funext τ
    ring
  rw [hin]
  ring

theorem measurable_rational {a : ℝ} : Measurable fun τ : ℝ => a / (1 + a * τ) - a :=
  (measurable_const.div (measurable_const.add (measurable_const.mul measurable_id))).sub
    measurable_const

/-- `σ` is Lipschitz on `[0, ρ]`, `ρ < 1`. -/
theorem abs_crossSingular_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {ρ a b : ℝ}
    (hρ : ρ < 1) (ha : a ∈ Set.Icc 0 ρ) (hb : b ∈ Set.Icc 0 ρ) :
    |crossSingular φ a - crossSingular φ b| ≤
      1 / (2 * ∫ u, φ u ^ 2) * ((1 / (1 - ρ) ^ 2 + 1) * ∫ τ, |bumpAutocorr φ τ|) * |a - b| := by
  have hg := hφ.continuous
  have hgc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hρ0 : 0 < 1 - ρ := by linarith
  have hfac : ∀ x ∈ Set.Icc (0 : ℝ) ρ, ∀ τ ∈ Set.Icc (-1 : ℝ) 1, 1 - ρ ≤ 1 + x * τ := by
    intro x hx τ hτ
    have : -x ≤ x * τ := by nlinarith [hx.1, hτ.1]
    linarith [hx.2]
  have hbd : ∀ x ∈ Set.Icc (0 : ℝ) ρ, ∀ τ ∈ Set.Icc (-1 : ℝ) 1, |x / (1 + x * τ) - x| ≤
      ρ / (1 - ρ) + ρ := fun x hx τ hτ => by
    have h1 := hfac x hx τ hτ
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_nonneg hx.1, abs_of_pos (by linarith)]
      exact div_le_div₀ (by linarith [hx.1, hx.2]) hx.2 hρ0 h1
    · rw [abs_of_nonneg hx.1]; exact hx.2
  have hia := integrable_bumpAutocorr_mul hg hgc hφsupp (measurable_rational (a := a))
    (hbd a ha)
  have hib := integrable_bumpAutocorr_mul hg hgc hφsupp (measurable_rational (a := b))
    (hbd b hb)
  unfold crossSingular
  rw [← mul_sub, ← integral_sub hia hib, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ∫ u, φ u ^ 2)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e : ∀ τ, bumpAutocorr φ τ * (a / (1 + a * τ) - a) - bumpAutocorr φ τ * (b / (1 + b * τ) - b) =
      bumpAutocorr φ τ * ((a / (1 + a * τ) - a) - (b / (1 + b * τ) - b)) := fun τ => by ring
  simp_rw [e]
  have h := abs_integral_bumpAutocorr_mul_le hg hgc hφsupp
    (F := fun τ => (a / (1 + a * τ) - a) - (b / (1 + b * τ) - b))
    (measurable_rational.sub measurable_rational) (M := (1 / (1 - ρ) ^ 2 + 1) * |a - b|)
    (fun τ hτ => by
      have h1 := hfac a ha τ hτ
      have h2 := hfac b hb τ hτ
      have hpa : 0 < 1 + a * τ := by linarith
      have hpb : 0 < 1 + b * τ := by linarith
      have hD : 0 < (1 + a * τ) * (1 + b * τ) := mul_pos hpa hpb
      have e0 : a / (1 + a * τ) - b / (1 + b * τ) = (a - b) / ((1 + a * τ) * (1 + b * τ)) := by
        rw [div_sub_div _ _ hpa.ne' hpb.ne']
        congr 1
        ring
      have e1 : (a / (1 + a * τ) - a) - (b / (1 + b * τ) - b) =
          (a - b) / ((1 + a * τ) * (1 + b * τ)) - (a - b) := by
        linear_combination e0
      have hprod : (1 - ρ) ^ 2 ≤ (1 + a * τ) * (1 + b * τ) := by
        rw [sq]; exact mul_le_mul h1 h2 hρ0.le (by linarith)
      rw [e1]
      calc |(a - b) / ((1 + a * τ) * (1 + b * τ)) - (a - b)|
          ≤ |(a - b) / ((1 + a * τ) * (1 + b * τ))| + |a - b| := abs_sub _ _
        _ = |a - b| / ((1 + a * τ) * (1 + b * τ)) + |a - b| := by rw [abs_div, abs_of_pos hD]
        _ ≤ |a - b| / (1 - ρ) ^ 2 + |a - b| := by
            gcongr
        _ = (1 / (1 - ρ) ^ 2 + 1) * |a - b| := by ring)
  calc _ ≤ (1 / (1 - ρ) ^ 2 + 1) * |a - b| * ∫ τ, |bumpAutocorr φ τ| := h
    _ = _ := by ring

/-- `0 ≤ 1/log(1 + x) − 1/x ≤ 1` for `x > 0`. -/
theorem inv_log_one_add_sub_inv {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / Real.log (1 + x) - 1 / x ∧ 1 / Real.log (1 + x) - 1 / x ≤ 1 := by
  have hl : 0 < Real.log (1 + x) := Real.log_pos (by linarith)
  have h1 : Real.log (1 + x) ≤ x := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)]
  have h2 : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
    have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hl h1)
  · rw [sub_le_iff_le_add, div_le_iff₀ hl]
    have e : (1 + 1 / x) * (x / (1 + x)) = 1 := by field_simp; ring
    calc (1 : ℝ) = (1 + 1 / x) * (x / (1 + x)) := e.symm
      _ ≤ (1 + 1 / x) * Real.log (1 + x) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The entry constant `K(φ, c)`. -/
def crossLip (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  c * (5 / 2 * (∫ τ, |bumpAutocorr φ τ|) / (∫ u, φ u ^ 2) +
    1 / (2 * ∫ u, φ u ^ 2) * ((1 / (1 - c) ^ 2 + 1) * ∫ τ, |bumpAutocorr φ τ|))

/-- **The entry against its profile**: `|Cr(n, n + d) − (n/N) G_d(n/N)| ≤ K/N` for `n + d ≤ N`. -/
theorem abs_crossError_sub_profile_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {N n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (hnd : n + d ≤ N) :
    |atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d) -
      (n / N : ℝ) * crossProfile φ c d (n / N)| ≤ crossLip φ c / N := by
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hg := hφ.continuous
  have hgc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hAabs : 0 ≤ ∫ τ, |bumpAutocorr φ τ| := integral_nonneg fun _ => abs_nonneg _
  have hxd : (0 : ℝ) < d / n := by positivity
  have hs_eq : |Real.log ((n + d : ℕ) : ℝ) - Real.log n| = Real.log (1 + d / n) := by
    have hlt : Real.log n < Real.log ((n + d : ℕ) : ℝ) :=
      Real.log_lt_log hn0 (by push_cast; linarith)
    rw [abs_of_pos (by linarith), ← Real.log_div (by positivity) hn0.ne']
    congr 1
    push_cast
    field_simp
  have hs0 : 0 < Real.log (1 + d / n) := Real.log_pos (by linarith)
  obtain ⟨hb0, hb1⟩ := inv_log_one_add_sub_inv hxd
  rw [one_div_div] at hb0 hb1
  have hws : c / N < Real.log (1 + d / n) := by
    have h := HTGeometry.integer_log_gap_sub_window_pos (n := n) (j := n + d) (N := N) (c := c)
      (w := c / N) (Finset.mem_Icc.mpr ⟨hn, by omega⟩) (Finset.mem_Icc.mpr ⟨by omega, hnd⟩)
      (by omega) hc0.le hc1 le_rfl
    rw [abs_sub_comm, hs_eq] at h
    linarith
  rw [atomCrossErrorKernel_atomDilate_eq hφ hφsupp hφ0 hw0 hn (by omega) (by omega)
    (by rw [hs_eq]; exact hws), hs_eq]
  set w := c / N with hw
  set s := Real.log (1 + d / n) with hs
  have hsw : 0 < s - w := by linarith
  -- the singular and regular parts
  set S : ℝ → ℝ := fun τ => 1 / (2 * (s + w * τ)) - 1 / (2 * s) with hS
  set R : ℝ → ℝ := fun τ => (_root_.RHTower.archLevyDensity (s + w * τ) - 1 / (2 * (s + w * τ))) -
    (_root_.RHTower.archLevyDensity s - 1 / (2 * s)) with hR
  have hpos : ∀ τ ∈ Set.Icc (-1 : ℝ) 1, s - w ≤ s + w * τ := fun τ hτ => by
    nlinarith [hτ.1, hτ.2]
  have hSb : ∀ τ ∈ Set.Icc (-1 : ℝ) 1, |S τ| ≤ 1 / (2 * (s - w)) + 1 / (2 * s) := fun τ hτ => by
    have h1 := hpos τ hτ
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_of_pos (one_div_pos.mpr (by linarith))]
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · rw [abs_of_pos (one_div_pos.mpr (by linarith))]
  have hRb : ∀ τ ∈ Set.Icc (-1 : ℝ) 1, |R τ| ≤ 5 / 2 := fun τ hτ => by
    have h1 := hpos τ hτ
    have a1 := abs_archLevyDensity_sub_inv_le (y := s + w * τ) (by linarith)
    have a2 := abs_archLevyDensity_sub_inv_le hs0
    calc |R τ| ≤ 5 / 4 + 5 / 4 := (abs_sub _ _).trans (add_le_add a1 a2)
      _ = 5 / 2 := by norm_num
  have hSm : Measurable S :=
    (measurable_const.div (measurable_const.mul (measurable_const.add
      (measurable_const.mul measurable_id)))).sub measurable_const
  have hRm : Measurable R :=
    ((_root_.RHTower.measurable_archLevyDensity.comp (measurable_const.add
      (measurable_const.mul measurable_id))).sub (measurable_const.div (measurable_const.mul
        (measurable_const.add (measurable_const.mul measurable_id))))).sub measurable_const
  have hiS := integrable_bumpAutocorr_mul hg hgc hφsupp hSm hSb
  have hiR := integrable_bumpAutocorr_mul hg hgc hφsupp hRm hRb
  have hsplit : ∫ τ, bumpAutocorr φ τ * (_root_.RHTower.archLevyDensity (s + w * τ) -
      _root_.RHTower.archLevyDensity s) =
      (∫ τ, bumpAutocorr φ τ * S τ) + ∫ τ, bumpAutocorr φ τ * R τ := by
    rw [← integral_add hiS hiR]
    congr 1
    funext τ
    simp only [hS, hR]
    ring
  -- the singular part is `σ(w/s)`
  have hsing : w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * S τ) =
      crossSingular φ (w / s) := by
    unfold crossSingular
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    funext τ
    by_cases hτ : τ ∈ Set.Icc (-1 : ℝ) 1
    · have h1 := hpos τ hτ
      have h2 : 0 < s + w * τ := by linarith
      have hI0 : (∫ u, φ u ^ 2) ≠ 0 := hφ0.ne'
      simp only [hS]
      field_simp
    · have : bumpAutocorr φ τ = 0 := bumpAutocorr_profile_eq_zero hφsupp (by
        by_contra h; exact hτ (abs_le.mp (not_lt.mp h)))
      rw [this]; ring
  have hreg : |w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * R τ)| ≤
      w / (∫ u, φ u ^ 2) * (5 / 2 * ∫ τ, |bumpAutocorr φ τ|) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_integral_bumpAutocorr_mul_le hg hgc hφsupp hRm hRb)
      (by positivity)
  -- the Lipschitz step from `w/s` to `r₀ = cn/(Nd)`
  have hr0 : c * (n / N : ℝ) / d = w * (n / d) := by rw [hw]; ring
  have hws1 : w / s = w * (1 / s) := div_eq_mul_one_div w s
  have hws_le : w / s ≤ w * (n / d) + w := by
    rw [hws1]
    have := mul_le_mul_of_nonneg_left (show 1 / s ≤ n / d + 1 by linarith) hw0.le
    linarith
  have hws_ge : w * (n / d) ≤ w / s := by
    rw [hws1]
    exact mul_le_mul_of_nonneg_left (by linarith) hw0.le
  have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
  have hnd' : (n : ℝ) / d ≤ n := div_le_self hn0.le (by exact_mod_cast hd)
  have hbig : w * (n / d) + w ≤ c := by
    rw [hw]
    have : c / N * (n / d) + c / N ≤ c / N * n + c / N :=
      by gcongr
    calc c / N * (n / d) + c / N ≤ c / N * n + c / N := this
      _ = c * ((n + 1) / N) := by ring
      _ ≤ c * 1 := by gcongr; rw [div_le_one hN0]; exact hnN
      _ = c := mul_one c
  have hLip := abs_crossSingular_sub_le hφ hφsupp hφ0 (ρ := c) hc1
    (a := w / s) (b := w * (n / d)) ⟨by positivity, by linarith⟩
    ⟨by positivity, by linarith⟩
  have hprof : (n / N : ℝ) * crossProfile φ c d (n / N) = crossSingular φ (w * (n / d)) := by
    rw [← hr0, crossSingular_eq]
  rw [hsplit, mul_add, hsing, hprof]
  have hdist : |w / s - w * (n / d)| ≤ w := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc |crossSingular φ (w / s) + w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * R τ) -
        crossSingular φ (w * (n / d))|
      ≤ |crossSingular φ (w / s) - crossSingular φ (w * (n / d))| +
          |w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * R τ)| := by
        rw [show crossSingular φ (w / s) + w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * R τ) -
          crossSingular φ (w * (n / d)) = (crossSingular φ (w / s) - crossSingular φ (w * (n / d))) +
            w / (∫ u, φ u ^ 2) * (∫ τ, bumpAutocorr φ τ * R τ) by ring]
        exact abs_add_le _ _
    _ ≤ 1 / (2 * ∫ u, φ u ^ 2) * ((1 / (1 - c) ^ 2 + 1) * ∫ τ, |bumpAutocorr φ τ|) * w +
          w / (∫ u, φ u ^ 2) * (5 / 2 * ∫ τ, |bumpAutocorr φ τ|) := by
        refine add_le_add (hLip.trans (mul_le_mul_of_nonneg_left hdist (by positivity))) hreg
    _ = crossLip φ c / N := by
        rw [hw]; unfold crossLip; field_simp; ring

/-! ### The row profile on `[0, 1]` -/

/-- `G_d` is Lipschitz on `[0, 1]`. -/
theorem abs_crossProfile_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {d : ℕ} (hd : 1 ≤ d) {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |crossProfile φ c d u - crossProfile φ c d v| ≤
      1 / (2 * ∫ u, φ u ^ 2) * (c ^ 2 / (1 - c) ^ 2 * ∫ τ, |bumpAutocorr φ τ|) * |u - v| := by
  have hg := hφ.continuous
  have hgc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcd : c / d ≤ c := div_le_self hc0.le hd0
  have hcd0 : 0 ≤ c / d := by positivity
  have hfac : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ τ ∈ Set.Icc (-1 : ℝ) 1, 1 - c ≤ 1 + c * x / d * τ :=
    fun x hx τ hτ => by
      have h1 : c * x / d ≤ c := by
        rw [mul_div_right_comm]; exact (mul_le_of_le_one_right hcd0 hx.2).trans hcd
      have h0 : 0 ≤ c * x / d := by have := hx.1; positivity
      nlinarith [hτ.1, hτ.2]
  have hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ τ ∈ Set.Icc (-1 : ℝ) 1,
      |c / d * (1 / (1 + c * x / d * τ) - 1)| ≤ c * (1 / (1 - c) + 1) := fun x hx τ hτ => by
    have h1 := hfac x hx τ hτ
    rw [abs_mul, abs_of_nonneg hcd0]
    refine mul_le_mul hcd ((abs_sub _ _).trans (add_le_add ?_ (by simp))) (abs_nonneg _) hc0.le
    rw [abs_of_pos (one_div_pos.mpr (by linarith))]
    exact one_div_le_one_div_of_le (by linarith) h1
  have hmeas : ∀ x : ℝ, Measurable fun τ : ℝ => c / d * (1 / (1 + c * x / d * τ) - 1) := fun x =>
    measurable_const.mul ((measurable_const.div (measurable_const.add
      (measurable_const.mul measurable_id))).sub measurable_const)
  have hiu := integrable_bumpAutocorr_mul hg hgc hφsupp (hmeas u) (hbd u hu)
  have hiv := integrable_bumpAutocorr_mul hg hgc hφsupp (hmeas v) (hbd v hv)
  unfold crossProfile
  rw [← mul_sub, ← integral_sub hiu hiv, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ∫ u, φ u ^ 2)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e : ∀ τ, bumpAutocorr φ τ * (c / d * (1 / (1 + c * u / d * τ) - 1)) -
      bumpAutocorr φ τ * (c / d * (1 / (1 + c * v / d * τ) - 1)) =
      bumpAutocorr φ τ * (c / d * (1 / (1 + c * u / d * τ) - 1 / (1 + c * v / d * τ))) :=
    fun τ => by ring
  simp_rw [e]
  have h := abs_integral_bumpAutocorr_mul_le hg hgc hφsupp
    (F := fun τ => c / d * (1 / (1 + c * u / d * τ) - 1 / (1 + c * v / d * τ)))
    (measurable_const.mul ((measurable_const.div (measurable_const.add
      (measurable_const.mul measurable_id))).sub (measurable_const.div (measurable_const.add
        (measurable_const.mul measurable_id)))))
    (M := c ^ 2 / (1 - c) ^ 2 * |u - v|) (fun τ hτ => by
      have h1 := hfac u hu τ hτ
      have h2 := hfac v hv τ hτ
      have hc' : (0 : ℝ) < 1 - c := by linarith
      have hpa : 0 < 1 + c * u / d * τ := by linarith
      have hpb : 0 < 1 + c * v / d * τ := by linarith
      have e0 : 1 / (1 + c * u / d * τ) - 1 / (1 + c * v / d * τ) =
          (c / d * τ * (v - u)) / ((1 + c * u / d * τ) * (1 + c * v / d * τ)) := by
        rw [div_sub_div _ _ hpa.ne' hpb.ne']
        congr 1
        ring
      rw [e0, abs_mul, abs_of_nonneg hcd0, abs_div, abs_of_pos (mul_pos hpa hpb), abs_mul,
        abs_mul, abs_of_nonneg hcd0, abs_sub_comm v u]
      have hτ1 : |τ| ≤ 1 := abs_le.mpr ⟨hτ.1, hτ.2⟩
      have hprod : (1 - c) ^ 2 ≤ (1 + c * u / d * τ) * (1 + c * v / d * τ) := by
        rw [sq]; exact mul_le_mul h1 h2 hc'.le (by linarith)
      calc c / d * (c / d * |τ| * |u - v| / ((1 + c * u / d * τ) * (1 + c * v / d * τ)))
          ≤ c * (c * 1 * |u - v| / (1 - c) ^ 2) := by
            gcongr
      _ = c ^ 2 / (1 - c) ^ 2 * |u - v| := by ring)
  calc _ ≤ c ^ 2 / (1 - c) ^ 2 * |u - v| * ∫ τ, |bumpAutocorr φ τ| := h
    _ = _ := by ring

/-- `|G_d| ≤ (1/(2I)) c (1/(1 − c) + 1) ∫|A|` on `[0, 1]`. -/
theorem abs_crossProfile_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {d : ℕ} (hd : 1 ≤ d) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |crossProfile φ c d u| ≤
      1 / (2 * ∫ u, φ u ^ 2) * (c * (1 / (1 - c) + 1) * ∫ τ, |bumpAutocorr φ τ|) := by
  have hg := hφ.continuous
  have hgc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcd : c / d ≤ c := div_le_self hc0.le hd0
  have hcd0 : 0 ≤ c / d := by positivity
  have hbd : ∀ τ ∈ Set.Icc (-1 : ℝ) 1,
      |c / d * (1 / (1 + c * u / d * τ) - 1)| ≤ c * (1 / (1 - c) + 1) := fun τ hτ => by
    have h1 : 1 - c ≤ 1 + c * u / d * τ := by
      have hh1 : c * u / d ≤ c := by
        rw [mul_div_right_comm]; exact (mul_le_of_le_one_right hcd0 hu.2).trans hcd
      have h0 : 0 ≤ c * u / d := by have := hu.1; positivity
      nlinarith [hτ.1, hτ.2]
    rw [abs_mul, abs_of_nonneg hcd0]
    refine mul_le_mul hcd ((abs_sub _ _).trans (add_le_add ?_ (by simp))) (abs_nonneg _) hc0.le
    rw [abs_of_pos (one_div_pos.mpr (by linarith))]
    exact one_div_le_one_div_of_le (by linarith) h1
  unfold crossProfile
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ∫ u, φ u ^ 2))]
  exact mul_le_mul_of_nonneg_left (abs_integral_bumpAutocorr_mul_le hg hgc hφsupp
    (measurable_const.mul ((measurable_const.div (measurable_const.add
      (measurable_const.mul measurable_id))).sub measurable_const)) hbd) (by positivity)

/-! ### Weighted Riemann sums -/

theorem abs_sum_range_mul_le_real (f g : ℕ → ℝ) (M : ℕ) {B : ℝ}
    (hB : ∀ k ≤ M, |∑ i ∈ range (k + 1), g i| ≤ B) :
    |∑ i ∈ range (M + 1), f i * g i| ≤ B * (|f M| + ∑ i ∈ range M, |f (i + 1) - f i|) := by
  have h := Finset.sum_range_by_parts f g (M + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  refine (abs_sub _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB M le_rfl) (abs_nonneg _)
  · rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB i (by simp at hi; omega)) (abs_nonneg _)

theorem continuousOn_of_abs_sub_le {G : ℝ → ℝ} {L : ℝ} {s : Set ℝ}
    (hL : ∀ u ∈ s, ∀ v ∈ s, |G u - G v| ≤ L * |u - v|) : ContinuousOn G s := by
  intro u hu
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / (|L| + 1), by positivity, fun v hv hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have h1 : |G v - G u| ≤ |L| * |v - u| :=
    (hL v hv u hu).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _))
  have h2 : |L| * |v - u| ≤ |L| * (ε / (|L| + 1)) :=
    mul_le_mul_of_nonneg_left hdist.le (abs_nonneg _)
  have h3 : |L| * (ε / (|L| + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg L]
  linarith

/-- **Riemann sums of a Lipschitz function**: `|(1/N)Σ_{n ≤ N} G(n/N) − ∫_0^1 G| ≤ L/N`. -/
theorem abs_riemannSum_sub_integral_le {G : ℝ → ℝ} {L : ℝ}
    (hL : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, |G u - G v| ≤ L * |u - v|)
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N, G (n / N)) / N - ∫ u in (0 : ℝ)..1, G u| ≤ L / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont := continuousOn_of_abs_sub_le hL
  have hstep : ∀ i : ℕ, ((i : ℝ) / N) ≤ ((i + 1 : ℕ) : ℝ) / N := fun i => by
    gcongr; push_cast; linarith
  have hmem : ∀ i < N, Set.uIcc ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) ⊆ Set.Icc 0 1 :=
    fun i hi => by
      rw [Set.uIcc_of_le (hstep i)]
      intro u hu
      refine ⟨le_trans (by positivity) hu.1, hu.2.trans ?_⟩
      rw [div_le_one hN0]; exact_mod_cast hi
  have hint : ∀ i < N, IntervalIntegrable G MeasureTheory.volume ((i : ℝ) / N)
      (((i + 1 : ℕ) : ℝ) / N) := fun i hi => (hcont.mono (hmem i hi)).intervalIntegrable
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / N) (f := G) (μ := MeasureTheory.volume) (n := N)
    fun k hk => hint k hk
  simp only [Nat.cast_zero, zero_div, div_self hN0.ne'] at hsplit
  rw [← hsplit, ← sum_range_succ_eq_sum_Icc (fun n => G (n / N)), Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ range N, |G (((i + 1 : ℕ) : ℝ) / N) / N -
      ∫ u in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, G u| ≤ L / N / N := fun i hi => by
    have hi' : i < N := Finset.mem_range.mp hi
    have hlen : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by push_cast; field_simp; ring
    have e : G (((i + 1 : ℕ) : ℝ) / N) / N - ∫ u in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, G u =
        ∫ u in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, (G (((i + 1 : ℕ) : ℝ) / N) - G u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint i hi'),
        intervalIntegral.integral_const, smul_eq_mul, hlen]
      ring
    rw [e]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := L / N)
      (f := fun u => G (((i + 1 : ℕ) : ℝ) / N) - G u) (a := (i : ℝ) / N)
      (b := ((i + 1 : ℕ) : ℝ) / N) (fun u hu => by
        rw [Set.uIoc_of_le (hstep i), Set.mem_Ioc] at hu
        have hu' : u ∈ Set.Icc (0 : ℝ) 1 := hmem i hi' (by
          rw [Set.uIcc_of_le (hstep i)]; exact ⟨hu.1.le, hu.2⟩)
        have hb' : ((i + 1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := hmem i hi' (by
          rw [Set.uIcc_of_le (hstep i)]; exact ⟨hstep i, le_rfl⟩)
        rw [Real.norm_eq_abs]
        refine (hL _ hb' u hu').trans ?_
        have hL0 : 0 ≤ L := by
          have := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
          simp at this
          linarith [abs_nonneg (G 0 - G 1)]
        refine mul_le_mul_of_nonneg_left ?_ hL0 |>.trans (le_of_eq (by ring))
        rw [abs_of_nonneg (by linarith)]
        linarith)
    rw [Real.norm_eq_abs, hlen.symm ▸ (by
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / N)] : |(1 : ℝ) / N| = 1 / N)] at hb
    sorry
  sorry

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
