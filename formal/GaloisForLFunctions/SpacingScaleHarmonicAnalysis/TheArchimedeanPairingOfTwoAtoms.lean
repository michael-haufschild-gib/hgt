import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRobinConstantOfAnAtom

/-!
# The archimedean pairing of two atoms

Two atoms of width `w` at distance `s > w` interact through the archimedean place only: their
supports are disjoint, so the Lévy energy of the pair is the two self-energies minus a cross term,
and the cross term reads the Lévy density at the distance.

For a `C²` bump `g` supported in `[0, w]` and `s > w`:

* **The mixed integrand** (`levyMixed_atom_shift`): for `y > 0`,
  `levyMixed g g(· − s) y = −ω(y) G(y − s)`, `G(z) = ∫ g(u) g(u + z) du` — of the four products in the
  Lévy cross integrand only the forward one survives.
* **The pair energy** (`levyEnergy_atom_pair`): `levyEnergy(g + g(· − s)) = 2 levyEnergy g − 2X`,
  `X = ∫_0^∞ ω(y) G(y − s) dy`.
* **The cross term is `ω(s)(∫g)²`** (`abs_crossTerm_sub_le`): since `ω` decreases and `G` lives on
  `[−w, w]` with `∫ G = (∫ g)²`,
  `|X − ω(s)(∫g)²| ≤ (ω(s − w) − ω(s + w))(∫|g|)²`.

With `2ω(s) = e^{s/2}/sinh s` this is the archimedean cross pairing
`K(s) = (∫g)² e^{s/2}/sinh s + O(w)` of two atoms; together with the exact self-energy
(`TheRobinConstantOfAnAtom`) it gives the archimedean Gram of a separated atomic family to `O(w)`.
-/

noncomputable section

open MeasureTheory Set RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

variable {g : ℝ → ℝ} {w s : ℝ}

/-! ### The Lévy density decreases -/

theorem archLevyDensity_antitoneOn : AntitoneOn archLevyDensity (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  unfold archLevyDensity
  have hda : 0 < 1 - Real.exp (-2 * a) := by
    have : Real.exp (-2 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hdb : 0 < 1 - Real.exp (-2 * b) := by
    have : Real.exp (-2 * b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_le_div_iff₀ hdb hda]
  have h1 : Real.exp (-b / 2) ≤ Real.exp (-a / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * b) := by
    have : Real.exp (-2 * b) ≤ Real.exp (-2 * a) := Real.exp_le_exp.mpr (by linarith)
    linarith
  exact mul_le_mul h1 h2 hda.le (Real.exp_pos _).le

/-! ### The cross term -/

/-- The autocorrelation `G(z) = ∫ g(u) g(u + z) du`. -/
def bumpAutocorr (g : ℝ → ℝ) (z : ℝ) : ℝ := ∫ u, g u * g (u + z)

theorem bumpAutocorr_eq_zero (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) {z : ℝ} (hz : w < |z|) :
    bumpAutocorr g z = 0 := by
  unfold bumpAutocorr
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Icc 0 w
  · have : u + z ∉ Icc 0 w := by
      intro h
      rcases le_or_gt 0 z with hz0 | hz0
      · rw [abs_of_nonneg hz0] at hz; linarith [h.2, hu.1]
      · rw [abs_of_neg hz0] at hz; linarith [h.1, hu.2]
    simp [hgsupp _ this]
  · simp [hgsupp u hu]

/-- **The mixed integrand of two separated atoms**: `levyMixed g g(· − s) y = −ω(y) G(y − s)`. -/
theorem levyMixed_atom_shift (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hws : w < s) {y : ℝ}
    (hy : 0 < y) :
    levyMixed g (fun u => g (u - s)) y = -(archLevyDensity y * bumpAutocorr g (y - s)) := by
  unfold levyMixed bumpAutocorr
  rw [← mul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h1 : g u * g (u - s) = 0 := by
    by_cases hu : u ∈ Icc 0 w
    · rw [hgsupp (u - s) fun h => by linarith [h.2, hu.2, h.1, hu.1], mul_zero]
    · rw [hgsupp u hu, zero_mul]
  have h2 : g (u + y) * g (u + y - s) = 0 := by
    by_cases hu : u + y ∈ Icc 0 w
    · rw [hgsupp (u + y - s) fun h => by linarith [h.1, hu.2], mul_zero]
    · rw [hgsupp (u + y) hu, zero_mul]
  have h3 : g (u + y) * g (u - s) = 0 := by
    by_cases hu : u + y ∈ Icc 0 w
    · rw [hgsupp (u - s) fun h => by linarith [h.1, hu.2], mul_zero]
    · rw [hgsupp (u + y) hu, zero_mul]
  have e : (g u - g (u + y)) * (g (u - s) - g (u + y - s)) =
      g u * g (u - s) - g u * g (u + y - s) - g (u + y) * g (u - s) +
        g (u + y) * g (u + y - s) := by ring
  simp only
  rw [e, h1, h2, h3, show u + (y - s) = u + y - s by ring]
  ring

/-- The cross term `X = ∫_0^∞ ω(y) G(y − s) dy`. -/
def atomCrossTerm (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ y in Ioi 0, archLevyDensity y * bumpAutocorr g (y - s)

theorem levyEnergy_translate (s : ℝ) :
    levyEnergy (fun u => g (u - s)) = levyEnergy g := by
  unfold levyEnergy
  congr 1
  funext y
  congr 1
  exact integral_sub_right_eq_self (fun u => (g u - g (u + y)) ^ 2) s |>.symm.trans
    (by congr 1; funext u; ring_nf) |>.symm

/-- **The pair energy**: `levyEnergy(g + g(· − s)) = 2 levyEnergy g − 2X`. -/
theorem levyEnergy_atom_pair (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hws : w < s) :
    levyEnergy (fun u => g u + g (u - s)) = 2 * levyEnergy g - 2 * atomCrossTerm g s := by
  have hgs : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
  have hgsc : HasCompactSupport fun u => g (u - s) := hgc.comp_homeomorph (Homeomorph.subRight s)
  have h := levyEnergy_smul_add hg hgc hgs hgsc 1
  simp only [one_mul] at h
  rw [h, levyEnergy_translate s]
  have hmix : ∫ y in Ioi 0, levyMixed g (fun u => g (u - s)) y = -atomCrossTerm g s := by
    unfold atomCrossTerm
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy => levyMixed_atom_shift hgsupp hws hy
  rw [hmix]
  ring

/-- A measurable function, bounded and vanishing off an interval, is integrable. -/
theorem integrable_of_bounded_of_vanish {F : ℝ → ℝ} {a b C : ℝ} (hm : AEStronglyMeasurable F)
    (hsupp : ∀ z, z ∉ Icc a b → F z = 0) (hb : ∀ z, |F z| ≤ C) : Integrable F := by
  have hon : IntegrableOn F (Icc a b) :=
    Measure.integrableOn_of_bounded (M := C) measure_Icc_lt_top.ne hm
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)
  exact (integrableOn_iff_integrable_of_support_subset fun z hz => by
    by_contra h; exact hz (hsupp z h)).mp hon

/-- The product `g(u) g(u + z)` is integrable on the plane. -/
theorem integrable_mul_shift_prod (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (Function.uncurry fun z u => g u * g (u + z)) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ : ∃ R, ∀ u, R < |u| → g u = 0 := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun u hu => ?_⟩
    by_contra h
    have := hR (subset_tsupport g h)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have hcont : Continuous (Function.uncurry fun z u => g u * g (u + z)) := by
    unfold Function.uncurry; fun_prop
  have hcs : HasCompactSupport (Function.uncurry fun z u => g u * g (u + z)) := by
    refine HasCompactSupport.intro (K := Icc (-(2 * R)) (2 * R) ×ˢ Icc (-R) R)
      ((isCompact_Icc).prod isCompact_Icc) fun p hp => ?_
    simp only [Function.uncurry]
    by_cases hu : |p.2| ≤ R
    · have hz : 2 * R < |p.1| := not_le.mp fun hz => hp ⟨abs_le.mp hz, abs_le.mp hu⟩
      have : R < |p.2 + p.1| := by
        have := abs_sub_abs_le_abs_sub p.1 (-p.2)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [hR _ this, mul_zero]
    · rw [hR _ (not_le.mp hu), zero_mul]
  exact hcont.integrable_of_hasCompactSupport hcs

/-- `∫ G = (∫ g)²`. -/
theorem integral_bumpAutocorr (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ z, bumpAutocorr g z = (∫ u, g u) ^ 2 := by
  unfold bumpAutocorr
  rw [integral_integral_swap (integrable_mul_shift_prod hg hgc)]
  have : ∀ u, ∫ z, g u * g (u + z) = g u * ∫ u, g u := fun u => by
    rw [integral_const_mul, integral_add_left_eq_self (fun z => g z) u]
  simp_rw [this]
  rw [integral_mul_const, sq]

/-- `∫ |G| ≤ (∫ |g|)²`. -/
theorem integral_abs_bumpAutocorr_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hGint : Integrable (bumpAutocorr g)) :
    ∫ z, |bumpAutocorr g z| ≤ (∫ u, |g u|) ^ 2 := by
  have habs := integrable_mul_shift_prod hg.abs (hgc.norm)
  have hpt : ∀ z, |bumpAutocorr g z| ≤ ∫ u, |g u| * |g (u + z)| := fun z => by
    unfold bumpAutocorr
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; funext u; rw [abs_mul]
  have hint : Integrable fun z => ∫ u, |g u| * |g (u + z)| := habs.integral_prod_left
  calc ∫ z, |bumpAutocorr g z| ≤ ∫ z, ∫ u, |g u| * |g (u + z)| :=
        integral_mono hGint.abs hint hpt
    _ = (∫ u, |g u|) ^ 2 := by
        rw [integral_integral_swap habs]
        have : ∀ u, ∫ z, |g u| * |g (u + z)| = |g u| * ∫ u, |g u| := fun u => by
          rw [integral_const_mul, integral_add_left_eq_self (fun z => |g z|) u]
        simp_rw [this]
        rw [integral_mul_const, sq]

/-- **The cross term is `ω(s)(∫g)²`**: `|X − ω(s)(∫g)²| ≤ (ω(s − w) − ω(s + w))(∫|g|)²`. -/
theorem abs_crossTerm_sub_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (hws : w < s) :
    |atomCrossTerm g s - archLevyDensity s * (∫ u, g u) ^ 2| ≤
      (archLevyDensity (s - w) - archLevyDensity (s + w)) * (∫ u, |g u|) ^ 2 := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hGsupp : ∀ z, z ∉ Icc (-w) w → bumpAutocorr g z = 0 := fun z hz =>
    bumpAutocorr_eq_zero hgsupp (by
      by_contra h
      exact hz ⟨by linarith [neg_abs_le z, not_lt.mp h], (le_abs_self z).trans (not_lt.mp h)⟩)
  have hGm : StronglyMeasurable (bumpAutocorr g) := by
    have hc : Continuous fun p : ℝ × ℝ => g p.2 * g (p.2 + p.1) := by
      have := hg; fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
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
  -- the density on `[s − w, s + w]`
  have hsw : 0 < s - w := by linarith
  have hωb : ∀ z ∈ Icc (-w) w, |archLevyDensity (s + z) - archLevyDensity s| ≤
      archLevyDensity (s - w) - archLevyDensity (s + w) := by
    intro z hz
    have hmem : ∀ t ∈ Icc (s - w) (s + w), t ∈ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hsw ht.1
    have h1 := archLevyDensity_antitoneOn (hmem (s - w) ⟨le_rfl, by linarith⟩)
      (hmem (s + z) ⟨by linarith [hz.1], by linarith [hz.2]⟩) (by linarith [hz.1])
    have h2 := archLevyDensity_antitoneOn (hmem (s + z) ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      (hmem (s + w) ⟨by linarith, le_rfl⟩) (by linarith [hz.2])
    have h3 := archLevyDensity_antitoneOn (hmem (s - w) ⟨le_rfl, by linarith⟩)
      (hmem s ⟨by linarith, by linarith⟩) (by linarith)
    have h4 := archLevyDensity_antitoneOn (hmem s ⟨by linarith, by linarith⟩)
      (hmem (s + w) ⟨by linarith, le_rfl⟩) (by linarith)
    rw [abs_le]; constructor <;> linarith
  -- the cross term as a translate
  have hX : atomCrossTerm g s = ∫ z, archLevyDensity (s + z) * bumpAutocorr g z := by
    unfold atomCrossTerm
    rw [← integral_indicator measurableSet_Ioi]
    rw [← integral_add_right_eq_self
      (fun y => (Ioi (0 : ℝ)).indicator (fun y => archLevyDensity y * bumpAutocorr g (y - s)) y) s]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : z ∈ Icc (-w) w
    · have hpos : z + s ∈ Ioi (0 : ℝ) := by
        show 0 < z + s; linarith [hz.1]
      rw [Set.indicator_of_mem hpos, add_sub_cancel_right, add_comm z s]
    · rw [hGsupp z hz, mul_zero]
      by_cases hpos : z + s ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hpos, add_sub_cancel_right, hGsupp z hz, mul_zero]
      · rw [Set.indicator_of_notMem hpos]
  -- integrability of the weighted cross term
  have hωcont : ContinuousOn archLevyDensity (Ioi 0) := by
    intro y hy
    have hden : 1 - Real.exp (-2 * y) ≠ 0 := by
      have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith [mem_Ioi.mp hy])
      linarith
    unfold archLevyDensity
    exact ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousAt.div
      ((continuous_const.sub (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)))).continuousAt hden).continuousWithinAt
  have hdiff_int : Integrable fun z => (archLevyDensity (s + z) - archLevyDensity s) *
      bumpAutocorr g z := by
    refine integrable_of_bounded_of_vanish (a := -w) (b := w)
      (C := (archLevyDensity (s - w) - archLevyDensity (s + w)) * (B * ∫ u, |g u|)) ?_ ?_ ?_
    · exact ((RHTower.measurable_archLevyDensity.comp (measurable_const.add measurable_id)).sub
        measurable_const).aestronglyMeasurable.mul hGm.aestronglyMeasurable
    · intro z hz; rw [hGsupp z hz, mul_zero]
    · intro z
      by_cases hz : z ∈ Icc (-w) w
      · rw [abs_mul]
        exact mul_le_mul (hωb z hz) (hGb z) (abs_nonneg _)
          (by linarith [abs_nonneg (archLevyDensity (s + z) - archLevyDensity s), hωb z hz])
      · rw [hGsupp z hz, mul_zero, abs_zero]
        have h0 : 0 ≤ archLevyDensity (s - w) - archLevyDensity (s + w) :=
          sub_nonneg.mpr (archLevyDensity_antitoneOn (mem_Ioi.mpr hsw)
            (mem_Ioi.mpr (by linarith)) (by linarith))
        have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
        have hA0 : 0 ≤ ∫ u, |g u| := integral_nonneg fun _ => abs_nonneg _
        positivity
  have hsplit : ∫ z, archLevyDensity (s + z) * bumpAutocorr g z =
      (∫ z, (archLevyDensity (s + z) - archLevyDensity s) * bumpAutocorr g z) +
        archLevyDensity s * ∫ z, bumpAutocorr g z := by
    rw [← integral_const_mul, ← integral_add hdiff_int (hGint.const_mul _)]
    congr 1; funext z; ring
  rw [hX, hsplit, integral_bumpAutocorr hg hgc, add_sub_cancel_right]
  have h0 : 0 ≤ archLevyDensity (s - w) - archLevyDensity (s + w) :=
    sub_nonneg.mpr (archLevyDensity_antitoneOn (mem_Ioi.mpr hsw) (mem_Ioi.mpr (by linarith))
      (by linarith))
  calc |∫ z, (archLevyDensity (s + z) - archLevyDensity s) * bumpAutocorr g z|
      ≤ ∫ z, |(archLevyDensity (s + z) - archLevyDensity s) * bumpAutocorr g z| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, (archLevyDensity (s - w) - archLevyDensity (s + w)) * |bumpAutocorr g z| := by
        refine integral_mono hdiff_int.abs (hGint.abs.const_mul _) fun z => ?_
        rw [abs_mul]
        by_cases hz : z ∈ Icc (-w) w
        · exact mul_le_mul_of_nonneg_right (hωb z hz) (abs_nonneg _)
        · rw [hGsupp z hz, abs_zero, mul_zero, mul_zero]
    _ = (archLevyDensity (s - w) - archLevyDensity (s + w)) * ∫ z, |bumpAutocorr g z| :=
        integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_bumpAutocorr_le hg hgc hGint) h0

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
