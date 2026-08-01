import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation
import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace

/-!
# Strict successive-aperture curvature

The scalar curvature left after principal mass conservation is minus the Hilbert--Schmidt energy of
the successive-layer coupling.  The coupling is nonzero at every large clock, so that curvature is
strictly negative, not merely nonpositive.

The final statement is scale-free: for every strict aperture flag there is an actual dilation scale
at which the coupling does not vanish and the curvature is strictly negative.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **`(5)`.**  Strict negativity of the successive-aperture curvature along a large clock. -/
theorem eventually_re_opTrace_evenSoninApertureRestrictionCurvature_neg
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c < r n * a)
    (hr : Tendsto r atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      (opTrace (evenSoninApertureRestrictionCurvature a b c (r n) (hrgt n))).re < 0 := by
  have hne := eventually_soninApertureCoupling_ne_zero a b c ha hb hab hbc q haq hqb r
    hrpos hrgt (fun n => (hcr n).le) hr
  filter_upwards [hne] with n hn
  have hZhs := evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt
    ha hab hbc (hrgt n) (hcr n)
  have hpos : 0 < hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) := by
    rcases lt_or_eq_of_le (hsNormSq_nonneg
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))) with h | h
    · exact h
    · exact absurd ((hsNormSq_eq_zero_iff hZhs).mp h.symm) hn
  rw [re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
    ha hab hbc (hrgt n) (hcr n)]
  linarith

/-- A concrete clock exceeding the crossing threshold. -/
def soninCrossingClock (a c : ℝ) : ℕ → ℝ := fun n => max 2 (c / a + 1) + n

theorem one_lt_soninCrossingClock (a c : ℝ) (n : ℕ) : 1 < soninCrossingClock a c n := by
  have h2 : (2 : ℝ) ≤ max 2 (c / a + 1) := le_max_left _ _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold soninCrossingClock
  linarith

theorem soninCrossingClock_pos (a c : ℝ) (n : ℕ) : 0 < soninCrossingClock a c n :=
  zero_lt_one.trans (one_lt_soninCrossingClock a c n)

theorem lt_soninCrossingClock_mul (a c : ℝ) (ha : 0 < a) (n : ℕ) :
    c < soninCrossingClock a c n * a := by
  have hge : c / a + 1 ≤ max 2 (c / a + 1) := le_max_right _ _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hstep : c / a + 1 ≤ soninCrossingClock a c n := by
    unfold soninCrossingClock
    linarith
  have := mul_le_mul_of_nonneg_right hstep ha.le
  have hdiv : (c / a) * a = c := div_mul_cancel₀ c ha.ne'
  nlinarith [this, hdiv, ha]

theorem tendsto_soninCrossingClock (a c : ℝ) :
    Tendsto (soninCrossingClock a c) atTop atTop := by
  unfold soninCrossingClock
  exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop

/-- **The coupling is genuinely nonzero.**  For every strict aperture flag there is an actual
dilation scale beyond the crossing threshold at which the successive-layer coupling does not
vanish. -/
theorem exists_scale_soninApertureCoupling_ne_zero
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenSoninApertureSuccessiveLayerTransition a b c r hr ≠ 0 := by
  have hne := eventually_soninApertureCoupling_ne_zero a b c ha hb hab hbc q haq hqb
    (soninCrossingClock a c) (soninCrossingClock_pos a c) (one_lt_soninCrossingClock a c)
    (fun n => (lt_soninCrossingClock_mul a c ha n).le) (tendsto_soninCrossingClock a c)
  obtain ⟨n, hn⟩ := hne.exists
  exact ⟨soninCrossingClock a c n, one_lt_soninCrossingClock a c n,
    lt_soninCrossingClock_mul a c ha n, hn⟩

/-- **The successive-aperture curvature is strictly negative at an actual scale.** -/
theorem exists_scale_re_opTrace_evenSoninApertureRestrictionCurvature_neg
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      (opTrace (evenSoninApertureRestrictionCurvature a b c r hr)).re < 0 := by
  have hne := eventually_re_opTrace_evenSoninApertureRestrictionCurvature_neg a b c ha hb hab
    hbc q haq hqb (soninCrossingClock a c) (soninCrossingClock_pos a c)
    (one_lt_soninCrossingClock a c) (fun n => lt_soninCrossingClock_mul a c ha n)
    (tendsto_soninCrossingClock a c)
  obtain ⟨n, hn⟩ := hne.exists
  exact ⟨soninCrossingClock a c n, one_lt_soninCrossingClock a c n,
    lt_soninCrossingClock_mul a c ha n, hn⟩

end RHTower
