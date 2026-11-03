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
    gcongr; linarith
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
        have hle : |((i + 1 : ℕ) : ℝ) / N - u| ≤ 1 / N := by
          rw [abs_of_nonneg (by linarith)]
          linarith [hlen]
        calc L * |((i + 1 : ℕ) : ℝ) / N - u| ≤ L * (1 / N) := mul_le_mul_of_nonneg_left hle hL0
          _ = L / N := by ring)
    rw [Real.norm_eq_abs, hlen, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)] at hb
    calc _ ≤ L / N * (1 / N) := hb
      _ = L / N / N := by ring
  calc ∑ i ∈ range N, |G (((i + 1 : ℕ) : ℝ) / N) / N -
        ∫ u in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, G u|
      ≤ ∑ _i ∈ range N, L / N / N := Finset.sum_le_sum hterm
    _ = L / N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- **Weighted Riemann sums**: for a periodic weight `w` and `G` Lipschitz on `[0, 1]`,
`(1/N)Σ_{n ≤ N − d} w(n) G(n/N) → mean(w) ∫_0^1 G`. -/
theorem tendsto_weighted_riemannSum {w : ℕ → ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, w (n + M) = w n) {W : ℝ} (hW : ∀ n, |w n| ≤ W) {G : ℝ → ℝ} {L B : ℝ}
    (hL : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, |G u - G v| ≤ L * |u - v|)
    (hB : ∀ u ∈ Set.Icc (0 : ℝ) 1, |G u| ≤ B) (d : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 (N - d), w n * G (n / N)) / N) atTop
      (𝓝 ((∑ r ∈ range M, w r) / M * ∫ u in (0 : ℝ)..1, G u)) := by
  set μ := (∑ r ∈ range M, w r) / M with hμ
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hL0 : 0 ≤ L := by
    have := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this
    linarith [abs_nonneg (G 0 - G 1)]
  have hshift : ∑ i ∈ range M, w (i + 1) = ∑ i ∈ range M, w i := by
    have := sum_range_shift_of_periodic w hper 1
    simpa [add_comm] using this
  have hpart : ∀ k, |∑ i ∈ range k, (w (i + 1) - μ)| ≤ 2 * M * W := fun k => by
    have h := abs_sum_range_sub_mul_mean_le hM (fun i => w (i + 1))
      (fun i => by rw [show i + M + 1 = i + 1 + M by ring]; exact hper (i + 1))
      (fun i => hW (i + 1)) k
    rw [hshift] at h
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact h
  set C : ℝ := |μ| * L + 2 * M * W * (B + L) + d * (W * B)
  have hbound : ∀ N : ℕ, max d 1 ≤ N →
      |(∑ n ∈ Icc 1 (N - d), w n * G (n / N)) / N - μ * ∫ u in (0 : ℝ)..1, G u| ≤ C / N := by
    intro N hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hdN : d ≤ N := le_of_max_le_left hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hmemG : ∀ n ∈ Icc 1 N, (n : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := fun n hn => by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hN0]; exact_mod_cast (Finset.mem_Icc.mp hn).2
    have htail_eq : ∑ n ∈ Icc 1 N, w n * G (n / N) = ∑ n ∈ Icc 1 (N - d), w n * G (n / N) +
        ∑ n ∈ Ioc (N - d) N, w n * G (n / N) := by
      rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
        Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.sub_le N d)]
    have htail : |∑ n ∈ Ioc (N - d) N, w n * G (n / N)| ≤ d * (W * B) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hcard : ((Ioc (N - d) N).card : ℝ) = d := by
        rw [Nat.card_Ioc, Nat.sub_sub_self hdN]
      calc ∑ n ∈ Ioc (N - d) N, |w n * G (n / N)| ≤ ∑ _n ∈ Ioc (N - d) N, W * B :=
            Finset.sum_le_sum fun n hn => by
              rw [abs_mul]
              have hn' : n ∈ Icc 1 N := by
                simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
              exact mul_le_mul (hW n) (hB _ (hmemG n hn')) (abs_nonneg _) hW0
        _ = d * (W * B) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hcent : |∑ n ∈ Icc 1 N, (w n - μ) * G (n / N)| ≤ 2 * M * W * (B + L) := by
      obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
      rw [← sum_range_succ_eq_sum_Icc (fun n => (w n - μ) * G (n / ((K + 1 : ℕ) : ℝ)))]
      have e : ∑ i ∈ range (K + 1), (w (i + 1) - μ) * G (((i + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) =
          ∑ i ∈ range (K + 1), G (((i + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) * (w (i + 1) - μ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e]
      refine (abs_sum_range_mul_le_real _ _ K fun k _ => hpart (k + 1)).trans ?_
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
      · exact hB _ (hmemG (K + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
      · have hK0 : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
        calc ∑ i ∈ range K, |G (((i + 1 + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) -
              G (((i + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ))|
            ≤ ∑ _i ∈ range K, L * (1 / ((K + 1 : ℕ) : ℝ)) :=
              Finset.sum_le_sum fun i hi => by
                have hi' : i < K := Finset.mem_range.mp hi
                refine (hL _ (hmemG _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) _
                  (hmemG _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))).trans ?_
                refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hL0
                rw [← sub_div, abs_div, abs_of_pos hK0]
                push_cast
                rw [show (i : ℝ) + 1 + 1 - (i + 1) = 1 by ring, abs_one]
          _ = L * (K / ((K + 1 : ℕ) : ℝ)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          _ ≤ L * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hL0
              rw [div_le_one hK0]; push_cast; linarith
          _ = L := mul_one L
    have hriem := abs_riemannSum_sub_integral_le hL hN1
    have hsplit : ∑ n ∈ Icc 1 N, w n * G (n / N) =
        μ * ∑ n ∈ Icc 1 N, G (n / N) + ∑ n ∈ Icc 1 N, (w n - μ) * G (n / N) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    have h1 : ∑ n ∈ Icc 1 (N - d), w n * G (n / N) = μ * ∑ n ∈ Icc 1 N, G (n / N) +
        ∑ n ∈ Icc 1 N, (w n - μ) * G (n / N) - ∑ n ∈ Ioc (N - d) N, w n * G (n / N) := by
      rw [← hsplit, htail_eq]; ring
    have hkey : (∑ n ∈ Icc 1 (N - d), w n * G (n / N)) / N - μ * ∫ u in (0 : ℝ)..1, G u =
        μ * ((∑ n ∈ Icc 1 N, G (n / N)) / N - ∫ u in (0 : ℝ)..1, G u) +
          (∑ n ∈ Icc 1 N, (w n - μ) * G (n / N)) / N -
          (∑ n ∈ Ioc (N - d) N, w n * G (n / N)) / N := by
      rw [h1]
      field_simp
      ring
    rw [hkey]
    have hμL : |μ * ((∑ n ∈ Icc 1 N, G (n / N)) / N - ∫ u in (0 : ℝ)..1, G u)| ≤
        |μ| * (L / N) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hriem (abs_nonneg _)
    have h2 : |(∑ n ∈ Icc 1 N, (w n - μ) * G (n / N)) / N| ≤ 2 * M * W * (B + L) / N := by
      rw [abs_div, abs_of_pos hN0]; exact div_le_div_of_nonneg_right hcent hN0.le
    have h3 : |(∑ n ∈ Ioc (N - d) N, w n * G (n / N)) / N| ≤ d * (W * B) / N := by
      rw [abs_div, abs_of_pos hN0]; exact div_le_div_of_nonneg_right htail hN0.le
    have h4 := abs_sub (μ * ((∑ n ∈ Icc 1 N, G (n / N)) / N - ∫ u in (0 : ℝ)..1, G u) +
          (∑ n ∈ Icc 1 N, (w n - μ) * G (n / N)) / N)
      ((∑ n ∈ Ioc (N - d) N, w n * G (n / N)) / N)
    have h5 := abs_add_le (μ * ((∑ n ∈ Icc 1 N, G (n / N)) / N - ∫ u in (0 : ℝ)..1, G u))
      ((∑ n ∈ Icc 1 N, (w n - μ) * G (n / N)) / N)
    have h6 : |μ| * (L / N) + 2 * M * W * (B + L) / N + d * (W * B) / N = C / N := by ring
    linarith
  have hmaj := tendsto_const_div_atTop_nhds_zero_nat C
  have hsq : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 (N - d), w n * G (n / N)) / N -
      μ * ∫ u in (0 : ℝ)..1, G u) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (max d 1)] with N hN
    rw [Real.norm_eq_abs]; exact hbound N hN
  have := hsq.add_const (μ * ∫ u in (0 : ℝ)..1, G u)
  rw [zero_add] at this
  exact this.congr fun N => by ring

/-! ### The rows of the cross pairing -/

/-- The gap-`d` row of the cross pairing. -/
def crossRow (φ : ℝ → ℝ) (c : ℝ) (e e' N d : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 (N - d), (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + d) +
      ramanujanLagCoefficient e' (n + d) * ramanujanLagCoefficient e n) *
    atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d) /
      (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ))

/-- **The cross pairing by gaps**: `⟨Cr R_e, R_{e'}⟩ = Σ_{d ≤ N} row_d/√(φ(e)φ(e'))`. -/
theorem crossPairing_eq (φ : ℝ → ℝ) (c : ℝ) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (N : ℕ) :
    ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (ramanujanHorizonVector e N),
      ramanujanHorizonVector e' N⟫ =
      (∑ d ∈ Icc 1 N, crossRow φ c e e' N d) / (Real.sqrt e.totient * Real.sqrt e'.totient) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, atomCrossErrorKernel (atomDilate φ (c / N)) n j *
      ramanujanPoleProfile e j = _
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, atomCrossErrorKernel (atomDilate φ (c / N)) n j *
      ramanujanPoleProfile e j)]
  have hinner : ∀ n : ℕ, (∑ j : PrimeHorizonIndex N, atomCrossErrorKernel (atomDilate φ (c / N)) n j *
      ramanujanPoleProfile e j) = ∑ j ∈ Icc 1 N, atomCrossErrorKernel (atomDilate φ (c / N)) n j *
        ramanujanPoleProfile e j := fun n =>
    Finset.sum_coe_sort (Icc 1 N) (fun j => atomCrossErrorKernel (atomDilate φ (c / N)) n j *
      ramanujanPoleProfile e j)
  simp only [hinner, Finset.mul_sum]
  set F : ℕ → ℕ → ℝ := fun n j => ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
    atomCrossErrorKernel (atomDilate φ (c / N)) n j / (Real.sqrt n * Real.sqrt j) with hF
  have hpt : ∀ n j, ramanujanPoleProfile e' n * (atomCrossErrorKernel (atomDilate φ (c / N)) n j *
      ramanujanPoleProfile e j) = F n j / (Real.sqrt e.totient * Real.sqrt e'.totient) :=
    fun n j => by rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he']; simp only [hF]; ring
  simp only [hpt, ← Finset.sum_div]
  congr 1
  have hsplit : ∀ n j, F n j = (if n < j then F n j else 0) + (if j < n then F n j else 0) :=
    fun n j => by
      rcases lt_trichotomy n j with h | h | h
      · rw [if_pos h, if_neg (by omega)]; ring
      · subst h; simp [hF]
      · rw [if_neg (by omega), if_pos h]; ring
  calc ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, F n j
      = ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (if n < j then F n j else 0) +
          ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if j < n then F n j else 0) := by
        rw [Finset.sum_comm (s := Icc 1 N) (t := Icc 1 N)
          (f := fun j n => if j < n then F n j else 0), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ => by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => hsplit n j
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - d), F n (n + d) +
          ∑ d ∈ Icc 1 N, ∑ j ∈ Icc 1 (N - d), F (j + d) j := by
        rw [sum_sum_ite_lt F N, sum_sum_ite_lt (fun j n => F n j) N]
    _ = ∑ d ∈ Icc 1 N, crossRow φ c e e' N d := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [crossRow, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [hF]
        rw [atomCrossErrorKernel_comm (atomDilate φ (c / N)) (n + d) n]
        ring

/-- The weight of the gap-`d` row and its mean `2[e = e'] c_e(d)`. -/
theorem sum_range_gapWeight {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (d : ℕ) :
    (∑ r ∈ range (e' * e), (ramanujanLagCoefficient e' r * ramanujanLagCoefficient e (r + d) +
      ramanujanLagCoefficient e' (r + d) * ramanujanLagCoefficient e r)) / ((e' * e : ℕ) : ℝ) =
      2 * (if e = e' then ramanujanLagCoefficient e d else 0) := by
  rw [Finset.sum_add_distrib, sum_range_lag_mul_lag_add he he' d]
  have h2 := sum_range_lag_mul_lag_add he' he d
  rw [show ∑ i ∈ range (e' * e), ramanujanLagCoefficient e' (i + d) * ramanujanLagCoefficient e i =
    ∑ i ∈ range (e * e'), ramanujanLagCoefficient e i * ramanujanLagCoefficient e' (i + d) by
      rw [mul_comm e' e]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _, h2]
  have hM0 : ((e' * e : ℕ) : ℝ) ≠ 0 := by positivity
  by_cases hee : e = e'
  · subst hee
    simp only [if_true]
    field_simp
    ring
  · rw [if_neg (Ne.symm hee), if_neg hee, if_neg hee]; simp

theorem sqrt_mul_sqrt_bounds (n d : ℕ) :
    (n : ℝ) ≤ Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ) ∧
      Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ) ≤ ((n + d : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle : (n : ℝ) ≤ ((n + d : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h1 := Real.sqrt_le_sqrt hle
  constructor
  · calc (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0).symm
      _ ≤ Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  · calc Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ) ≤
          Real.sqrt ((n + d : ℕ) : ℝ) * Real.sqrt ((n + d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = ((n + d : ℕ) : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- **The gap-`d` row converges**: `row_d → 2[e = e'] c_e(d) ∫_0^1 G_d`. -/
theorem tendsto_crossRow {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun N : ℕ => crossRow φ c e e' N d) atTop
      (𝓝 (2 * (if e = e' then ramanujanLagCoefficient e d else 0) *
        ∫ u in (0 : ℝ)..1, crossProfile φ c d u)) := by
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have hσ : 0 ≤ σ := by positivity
  have hσ' : 0 ≤ σ' := by positivity
  set wd : ℕ → ℝ := fun n => ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + d) +
    ramanujanLagCoefficient e' (n + d) * ramanujanLagCoefficient e n with hwd
  have hW : ∀ n, |wd n| ≤ 2 * σ' * σ := fun n => by
    simp only [hwd]
    have a1 := abs_ramanujanLagCoefficient_le e' n
    have a2 := abs_ramanujanLagCoefficient_le e (n + d)
    have a3 := abs_ramanujanLagCoefficient_le e' (n + d)
    have a4 := abs_ramanujanLagCoefficient_le e n
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 := mul_le_mul a1 a2 (abs_nonneg _) hσ'
    have b2 := mul_le_mul a3 a4 (abs_nonneg _) hσ'
    linarith
  have hP1 : ∀ n, ramanujanLagCoefficient e' (n + e' * e) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hP2 : ∀ n, ramanujanLagCoefficient e (n + e' * e) = ramanujanLagCoefficient e n := fun n => by
    rw [mul_comm]; exact ramanujanLagCoefficient_add_mul e n e'
  have hper : ∀ n, wd (n + e' * e) = wd n := fun n => by
    simp only [hwd]
    rw [show n + e' * e + d = n + d + e' * e by ring]
    simp only [hP1, hP2]
  have hM1 : 1 ≤ e' * e := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmain := tendsto_weighted_riemannSum hM1 hper hW (G := crossProfile φ c d)
    (fun u hu v hv => abs_crossProfile_sub_le hφ hφsupp hφ0 hc0 hc1 hd hu hv)
    (fun u hu => abs_crossProfile_le hφ hφsupp hφ0 hc0 hc1 hd hu) d
  rw [sum_range_gapWeight he he' d] at hmain
  set BG : ℝ := 1 / (2 * ∫ u, φ u ^ 2) * (c * (1 / (1 - c) + 1) * ∫ τ, |bumpAutocorr φ τ|)
  have hAabs : 0 ≤ ∫ τ, |bumpAutocorr φ τ| := integral_nonneg fun _ => abs_nonneg _
  have hBG : 0 ≤ BG := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  have hLip0 : 0 ≤ crossLip φ c := by
    unfold crossLip
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  set K : ℝ := 2 * σ' * σ * (crossLip φ c + BG * d)
  have hdiff : Tendsto (fun N : ℕ => crossRow φ c e e' N d -
      (∑ n ∈ Icc 1 (N - d), wd n * crossProfile φ c d (n / N)) / N) atTop (𝓝 0) := by
    have hmaj := tendsto_harmonic_div_self.const_mul K
    rw [mul_zero] at hmaj
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [crossRow, Finset.sum_div, ← Finset.sum_sub_distrib, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ n ∈ Icc 1 (N - d), |wd n * atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d) /
        (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ)) - wd n * crossProfile φ c d (n / N) / N| ≤
        K / N * (1 / n) := fun n hn => by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnd : n + d ≤ N := by have := (Finset.mem_Icc.mp hn).2; omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      obtain ⟨hPl, hPu⟩ := sqrt_mul_sqrt_bounds n d
      set P := Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ)
      have hP0 : 0 < P := lt_of_lt_of_le hn0 hPl
      have hnd' : ((n + d : ℕ) : ℝ) = n + d := by push_cast; ring
      set Cr := atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d)
      set G := crossProfile φ c d (n / N)
      have hCr : |Cr - (n / N : ℝ) * G| ≤ crossLip φ c / N :=
        abs_crossError_sub_profile_le hφ hφsupp hφ0 hc0 hc1 hn1 hd hnd
      have hu : (n : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by
        rw [div_le_one hN0]; exact_mod_cast (show n ≤ N by omega)⟩
      have hG : |G| ≤ BG := abs_crossProfile_le hφ hφsupp hφ0 hc0 hc1 hd hu
      have hinv1 : 0 ≤ 1 / (n : ℝ) - 1 / P := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hn0 hPl
      have hinv2 : 1 / (n : ℝ) - 1 / P ≤ d / ((n : ℝ) * n) := by
        have h1 : 1 / ((n : ℝ) + d) ≤ 1 / P := one_div_le_one_div_of_le hP0 (hnd' ▸ hPu)
        have h2 : 1 / (n : ℝ) - 1 / ((n : ℝ) + d) ≤ d / ((n : ℝ) * n) := by
          rw [div_sub_div _ _ hn0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hd0.le hd0.le) hn0.le]
        linarith
      have e : wd n * Cr / P - wd n * G / N =
          wd n * ((Cr - (n / N : ℝ) * G) / P - (n / N : ℝ) * G * (1 / (n : ℝ) - 1 / P)) := by
        field_simp
        ring
      rw [e, abs_mul]
      have hA : |(Cr - (n / N : ℝ) * G) / P| ≤ crossLip φ c / N * (1 / n) := by
        rw [abs_div, abs_of_pos hP0]
        calc |Cr - (n / N : ℝ) * G| / P ≤ crossLip φ c / N / n :=
              div_le_div₀ (by positivity) hCr hn0 hPl
          _ = crossLip φ c / N * (1 / n) := by ring
      have hB : |(n / N : ℝ) * G * (1 / (n : ℝ) - 1 / P)| ≤ BG * d / N * (1 / n) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / N),
          abs_of_nonneg hinv1]
        calc (n / N : ℝ) * |G| * (1 / (n : ℝ) - 1 / P) ≤ (n / N : ℝ) * BG * (d / ((n : ℝ) * n)) := by
              gcongr
          _ = BG * d / N * (1 / n) := by field_simp
      calc |wd n| * |(Cr - (n / N : ℝ) * G) / P - (n / N : ℝ) * G * (1 / (n : ℝ) - 1 / P)|
          ≤ (2 * σ' * σ) * (crossLip φ c / N * (1 / n) + BG * d / N * (1 / n)) :=
            mul_le_mul (hW n) ((abs_sub _ _).trans (add_le_add hA hB)) (abs_nonneg _)
              (by positivity)
        _ = K / N * (1 / n) := by ring
    calc ∑ n ∈ Icc 1 (N - d), |wd n * atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d) /
          (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ)) - wd n * crossProfile φ c d (n / N) / N|
        ≤ ∑ n ∈ Icc 1 (N - d), K / N * (1 / (n : ℝ)) := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Icc 1 N, K / N * (1 / (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sub_le N d))
            fun n _ _ => by positivity
      _ = K * ((harmonic N : ℝ) / N) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc_real]
          simp only [one_div]
          ring
  have := hdiff.add hmain
  rw [zero_add] at this
  refine this.congr fun N => ?_
  ring

/-- **The rows are dominated**: `|row_d| ≤ D/d²` uniformly in `N`. -/
theorem abs_crossRow_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (e e' : ℕ) {N d : ℕ} (hd : 1 ≤ d) :
    |crossRow φ c e e' N d| ≤ 4 * ((∑ t ∈ e'.divisors, (t : ℝ)) * ∑ t ∈ e.divisors, (t : ℝ)) *
      (38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c) ^ 2)) * c ^ 2 / d ^ 2 := by
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have hσ : 0 ≤ σ := by positivity
  have hσ' : 0 ≤ σ' := by positivity
  set K₀ : ℝ := 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c) ^ 2)
  have hc' : (0 : ℝ) < 1 - c := by linarith
  have hK₀ : 0 ≤ K₀ := by
    have : 0 ≤ ∫ u, |φ u| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [crossRow]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ n ∈ Icc 1 (N - d), |(ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + d) +
      ramanujanLagCoefficient e' (n + d) * ramanujanLagCoefficient e n) *
      atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d) /
        (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ))| ≤
      2 * σ' * σ * K₀ * c ^ 2 / d ^ 2 * (1 / Real.sqrt N * (1 / Real.sqrt n)) := fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnd : n + d ≤ N := by have := (Finset.mem_Icc.mp hn).2; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hW : |ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + d) +
        ramanujanLagCoefficient e' (n + d) * ramanujanLagCoefficient e n| ≤ 2 * σ' * σ := by
      have a1 := abs_ramanujanLagCoefficient_le e' n
      have a2 := abs_ramanujanLagCoefficient_le e (n + d)
      have a3 := abs_ramanujanLagCoefficient_le e' (n + d)
      have a4 := abs_ramanujanLagCoefficient_le e n
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have b1 := mul_le_mul a1 a2 (abs_nonneg _) hσ'
      have b2 := mul_le_mul a3 a4 (abs_nonneg _) hσ'
      linarith
    have hRA := abs_atomCrossErrorKernel_atomDilate_le hφ hφsupp hφ0 (w := c / N) (N := N)
      (div_pos hc0 hN0) hc0.le hc1 le_rfl (Finset.mem_Icc.mpr ⟨hn1, by omega⟩)
      (Finset.mem_Icc.mpr ⟨by omega, hnd⟩)
    have hmax : max (n : ℝ) ((n + d : ℕ) : ℝ) = ((n + d : ℕ) : ℝ) :=
      max_eq_right (by push_cast; linarith)
    have hgap : |(n : ℝ) - ((n + d : ℕ) : ℝ)| = d := by
      push_cast; rw [show (n : ℝ) - (n + d) = -d by ring, abs_neg, abs_of_pos hd0]
    rw [hmax, hgap] at hRA
    obtain ⟨hPl, hPu⟩ := sqrt_mul_sqrt_bounds n d
    have hP0 : 0 < Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ) := lt_of_lt_of_le hn0 hPl
    -- the scaling `(c/N)² (n+d)² / √(n(n+d)) ≤ c²/(√N √n)`
    obtain ⟨a, ha0, ha⟩ : ∃ a, 0 < a ∧ Real.sqrt ((n + d : ℕ) : ℝ) = a :=
      ⟨_, Real.sqrt_pos.mpr (by positivity), rfl⟩
    obtain ⟨b, hb0, hb⟩ : ∃ b, 0 < b ∧ Real.sqrt N = b := ⟨_, Real.sqrt_pos.mpr hN0, rfl⟩
    obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt n = r := ⟨_, Real.sqrt_pos.mpr hn0, rfl⟩
    have hak : ((n + d : ℕ) : ℝ) = a ^ 2 := by rw [← ha, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hbk : (N : ℝ) = b ^ 2 := by rw [← hb, Real.sq_sqrt hN0.le]
    have hab : a ≤ b := by
      rw [← ha, ← hb]; exact Real.sqrt_le_sqrt (by exact_mod_cast hnd)
    have hscale : (c / N) ^ 2 * ((n + d : ℕ) : ℝ) ^ 2 / (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ)) ≤
        c ^ 2 * (1 / Real.sqrt N * (1 / Real.sqrt n)) := by
      rw [ha, hb, hr, hak, hbk]
      have h3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha0.le hab 3
      rw [div_le_iff₀ (by positivity)]
      have e1 : c ^ 2 * (1 / b * (1 / r)) * (r * a) = c ^ 2 * a / b := by field_simp
      rw [e1]
      have e2 : (c / b ^ 2) ^ 2 * (a ^ 2) ^ 2 = c ^ 2 * a ^ 4 / b ^ 4 := by field_simp
      rw [e2, div_le_div_iff₀ (by positivity) hb0]
      have h4 : a ^ 4 * b ≤ a * b ^ 4 := by
        have := mul_le_mul_of_nonneg_left h3 (mul_nonneg ha0.le hb0.le)
        nlinarith [this]
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg c)
      nlinarith [h5]
    rw [abs_div, abs_mul, abs_of_pos hP0]
    calc |ramanujanLagCoefficient e' n * ramanujanLagCoefficient e (n + d) +
          ramanujanLagCoefficient e' (n + d) * ramanujanLagCoefficient e n| *
          |atomCrossErrorKernel (atomDilate φ (c / N)) n (n + d)| /
          (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ))
        ≤ 2 * σ' * σ * (K₀ * (c / N) ^ 2 * ((n + d : ℕ) : ℝ) ^ 2 / (d : ℝ) ^ 2) /
          (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul hW hRA (abs_nonneg _) (by positivity)) hP0.le
      _ = 2 * σ' * σ * K₀ / d ^ 2 * ((c / N) ^ 2 * ((n + d : ℕ) : ℝ) ^ 2 /
          (Real.sqrt n * Real.sqrt ((n + d : ℕ) : ℝ))) := by ring
      _ ≤ 2 * σ' * σ * K₀ / d ^ 2 * (c ^ 2 * (1 / Real.sqrt N * (1 / Real.sqrt n))) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  unfold crossRow
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsq := RHTower.sum_one_div_sqrt_le N
  have hsub : ∑ n ∈ Icc 1 (N - d), 1 / Real.sqrt n ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / Real.sqrt n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sub_le N d))
      fun n _ _ => by positivity
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  calc 2 * σ' * σ * K₀ * c ^ 2 / d ^ 2 * (1 / Real.sqrt N * ∑ n ∈ Icc 1 (N - d), 1 / Real.sqrt n)
      ≤ 2 * σ' * σ * K₀ * c ^ 2 / d ^ 2 * (1 / Real.sqrt N * (2 * Real.sqrt N)) := by
        gcongr
        exact hsub.trans hsq
    _ = 4 * (σ' * σ) * K₀ * c ^ 2 / d ^ 2 := by
        have h2 : 1 / Real.sqrt N * (2 * Real.sqrt N) = 2 := by
          rw [one_div, ← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, inv_mul_cancel₀ hsN.ne',
            mul_one]
        rw [h2]
        ring

/-- The cross second order `Cr(e, e') = Σ_d 2[e = e'] c_e(d) ∫_0^1 G_d / √(φ(e)φ(e'))`. -/
def crossSecondOrder (φ : ℝ → ℝ) (c : ℝ) (e e' : ℕ) : ℝ :=
  (∑' d : ℕ, 2 * (if e = e' then ramanujanLagCoefficient e d else 0) *
    ∫ u in (0 : ℝ)..1, crossProfile φ c d u) / (Real.sqrt e.totient * Real.sqrt e'.totient)

/-- **The cross part of the bulk entries**: `⟨Cr R_e, R_{e'}⟩ → Cr(e, e')`. -/
theorem tendsto_crossPairing {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫) atTop (𝓝 (crossSecondOrder φ c e e')) := by
  simp only [crossPairing_eq φ c he he']
  unfold crossSecondOrder
  refine Tendsto.div_const ?_ _
  set τ : ℕ → ℝ := fun d => 2 * (if e = e' then ramanujanLagCoefficient e d else 0) *
    ∫ u in (0 : ℝ)..1, crossProfile φ c d u with hτ
  set D₀ : ℝ := 4 * ((∑ t ∈ e'.divisors, (t : ℝ)) * ∑ t ∈ e.divisors, (t : ℝ)) *
    (38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c) ^ 2)) * c ^ 2
  have hc' : (0 : ℝ) < 1 - c := by linarith
  have hD₀ : 0 ≤ D₀ := by
    have : 0 ≤ ∫ u, |φ u| := integral_nonneg fun _ => abs_nonneg _
    positivity
  set F : ℕ → ℕ → ℝ := fun N d => if d ∈ Icc 1 N then crossRow φ c e e' N d else 0 with hF
  have hsum : ∀ N, ∑ d ∈ Icc 1 N, crossRow φ c e e' N d = ∑' d, F N d := fun N => by
    rw [tsum_eq_sum (s := Icc 1 N) fun d hd => by simp only [hF, if_neg hd]]
    exact Finset.sum_congr rfl fun d hd => by simp only [hF, if_pos hd]
  simp only [hsum]
  have hτ0 : τ 0 = 0 := by simp [hτ, crossProfile]
  have hab : ∀ d, Tendsto (fun N => F N d) atTop (𝓝 (τ d)) := fun d => by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [hτ0]
      exact tendsto_const_nhds.congr fun N => by simp [hF]
    · refine (tendsto_crossRow hφ hφsupp hφ0 hc0 hc1 he he' hd).congr' ?_
      filter_upwards [eventually_ge_atTop d] with N hN
      simp only [hF, if_pos (Finset.mem_Icc.mpr ⟨hd, hN⟩)]
  have hbd : ∀ N d, ‖F N d‖ ≤ D₀ * (1 / (d : ℝ) ^ 2) := fun N d => by
    simp only [hF]
    split_ifs with hd
    · rw [Real.norm_eq_abs]
      refine (abs_crossRow_le hφ hφsupp hφ0 hc0 hc1 e e' (Finset.mem_Icc.mp hd).1).trans
        (le_of_eq ?_)
      simp only [D₀]
      ring
    · rw [norm_zero]; positivity
  have hsumm : Summable fun d : ℕ => D₀ * (1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left D₀
  exact tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hsumm hab (Eventually.of_forall hbd)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
