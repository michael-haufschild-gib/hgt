import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-!
# Detection of separated copies by the infinite logarithmic grid

The node `ceil (exp T)` lies within `exp (-T)` of `T` in logarithmic coordinates.
At this node a separated copy samples the original correlation near the origin.
Every fixed compact continuous source therefore has a universal rescaled negative
tail defect. Preserving this sample with changing sources forces a full translation
square defect at an exponentially shrinking displacement.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- The first logarithmic grid node at or to the right of a real center. -/
def logarithmicCeilNode (T : ℝ) : ℕ := ⌈Real.exp T⌉₊

/-- Displacement of the first grid node to the right of the center. -/
def logarithmicCeilLag (T : ℝ) : ℝ := Real.log (logarithmicCeilNode T : ℝ) - T

theorem logarithmicCeilNode_cast_pos (T : ℝ) : 0 < (logarithmicCeilNode T : ℝ) :=
  lt_of_lt_of_le (Real.exp_pos T) (Nat.le_ceil _)

theorem logarithmicCeilNode_ge_two {T : ℝ} (hT : 0 < T) : 2 ≤ logarithmicCeilNode T := by
  have h : 1 < logarithmicCeilNode T := Nat.lt_ceil.mpr (by simpa using Real.one_lt_exp_iff.mpr hT)
  omega

/-- Exact exponential mesh bound; valid even for negative centers. -/
theorem logarithmicCeilLag_bounds (T : ℝ) :
    0 ≤ logarithmicCeilLag T ∧ logarithmicCeilLag T ≤ Real.exp (-T) := by
  have hn := logarithmicCeilNode_cast_pos T
  have he := Real.exp_pos T
  have hlo : Real.exp T ≤ (logarithmicCeilNode T : ℝ) := Nat.le_ceil _
  have hhi : (logarithmicCeilNode T : ℝ) ≤ Real.exp T + 1 :=
    (Nat.ceil_lt_add_one he.le).le
  constructor
  · have h := Real.log_le_log he hlo
    rw [Real.log_exp] at h
    exact sub_nonneg.mpr h
  · have hid : logarithmicCeilLag T =
        Real.log ((logarithmicCeilNode T : ℝ) / Real.exp T) := by
      rw [Real.log_div hn.ne' he.ne', Real.log_exp]
      rfl
    rw [hid]
    calc
      _ ≤ (logarithmicCeilNode T : ℝ) / Real.exp T - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hn he)
      _ ≤ (Real.exp T + 1) / Real.exp T - 1 :=
        sub_le_sub_right (div_le_div_of_nonneg_right hhi he.le) 1
      _ = Real.exp (-T) := by
        rw [Real.exp_neg]
        field_simp
        ring

theorem tendsto_logarithmicCeilLag : Tendsto logarithmicCeilLag atTop (𝓝 0) := by
  exact squeeze_zero (fun T => (logarithmicCeilLag_bounds T).1)
    (fun T => (logarithmicCeilLag_bounds T).2)
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

/-- Once separated, the first tail grid sample is precisely a near-origin source sample. -/
theorem autocorr_subtractCopy_logarithmicCeilNode (f : C_c(ℝ, ℝ))
    {D T : ℝ} (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D < T) (a : ℝ) :
    autocorr (subtractCopy f a T) (Real.log (logarithmicCeilNode T : ℝ)) =
      -a * autocorr f (logarithmicCeilLag T) := by
  have hlag := (logarithmicCeilLag_bounds T).1
  unfold logarithmicCeilLag at hlag
  have hx : D < |Real.log (logarithmicCeilNode T : ℝ)| :=
    lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hxt : D < |Real.log (logarithmicCeilNode T : ℝ) + T| :=
    lt_of_lt_of_le (by linarith) (le_abs_self _)
  rw [autocorr_subtractCopy (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport,
    hsupp _ hx, hsupp _ hxt]
  simp only [logarithmicCeilLag, mul_zero, add_zero, zero_sub, neg_mul]

/-- The rescaled tail sample has a source-independent form after separation. -/
theorem eventually_rescaled_polarCopy_sample (f : C_c(ℝ, ℝ)) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (T / 2) * autocorr (polarCopy f T)
        (Real.log (logarithmicCeilNode T : ℝ)) = -autocorr f (logarithmicCeilLag T) := by
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius f.hasCompactSupport
  filter_upwards [eventually_gt_atTop D] with T hT
  rw [polarCopy, autocorr_subtractCopy_logarithmicCeilNode f hD.le hsupp hT]
  have he : Real.exp (T / 2) * Real.exp (-T / 2) = 1 := by
    rw [← Real.exp_add, show T / 2 + -T / 2 = 0 by ring, Real.exp_zero]
  calc
    _ = -(Real.exp (T / 2) * Real.exp (-T / 2)) * autocorr f (logarithmicCeilLag T) := by ring
    _ = _ := by rw [he]; ring

/-- Every compact continuous source has the same rescaled negative-tail law, including
the zero-energy case. No grid, regularity modulus, or tail assumption is imposed. -/
theorem tendsto_rescaled_polarCopy_sample (f : C_c(ℝ, ℝ)) :
    Tendsto (fun T : ℝ => Real.exp (T / 2) * autocorr (polarCopy f T)
      (Real.log (logarithmicCeilNode T : ℝ))) atTop (𝓝 (-autocorr f 0)) := by
  have h := ((continuous_autocorr_compact f).tendsto 0).comp tendsto_logarithmicCeilLag
  apply h.neg.congr'
  filter_upwards [eventually_rescaled_polarCopy_sample f] with T hT
  exact hT.symm

/-- Unconditional dichotomy: zero origin energy, or every sufficiently distant polar copy
has a strictly negative logarithmic sample of at least half the canonical tail amplitude. -/
theorem polarCopy_infinite_grid_dichotomy (f : C_c(ℝ, ℝ)) :
    autocorr f 0 = 0 ∨ ∃ T₀ : ℝ, ∀ T ≥ T₀,
      2 ≤ logarithmicCeilNode T ∧
      autocorr (polarCopy f T) (Real.log (logarithmicCeilNode T : ℝ)) <
        -(Real.exp (-T / 2) * autocorr f 0 / 2) := by
  rcases eq_or_lt_of_le (autocorr_zero_nonneg (f : ℝ → ℝ)) with hR | hR
  · exact Or.inl hR.symm
  · right
    have hlim := ((continuous_autocorr_compact f).tendsto 0).comp tendsto_logarithmicCeilLag
    have hnear : ∀ᶠ T : ℝ in atTop, autocorr f 0 / 2 < autocorr f (logarithmicCeilLag T) :=
      hlim.eventually_const_lt (by linarith)
    obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius f.hasCompactSupport
    apply eventually_atTop.mp
    filter_upwards [hnear, eventually_gt_atTop D] with T hnear hT
    refine ⟨logarithmicCeilNode_ge_two (lt_trans hD hT), ?_⟩
    rw [polarCopy, autocorr_subtractCopy_logarithmicCeilNode f hD.le hsupp hT]
    have hp := mul_lt_mul_of_pos_left hnear (Real.exp_pos (-T / 2))
    nlinarith

/-- Preserving the detecting sample with any nonzero coefficient forces an exact full
translation-square defect at the exponentially small mesh displacement. -/
theorem subtractCopy_zero_forces_translation_defect (f : C_c(ℝ, ℝ))
    {D T a : ℝ} (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hT : D < T) (ha : a ≠ 0)
    (hz : autocorr (subtractCopy f a T) (Real.log (logarithmicCeilNode T : ℝ)) = 0) :
    0 ≤ logarithmicCeilLag T ∧ logarithmicCeilLag T ≤ Real.exp (-T) ∧
      autocorr f (logarithmicCeilLag T) = 0 ∧
      (∫ u, (f (u + logarithmicCeilLag T) - f u) ^ 2) = 2 * autocorr f 0 := by
  rw [autocorr_subtractCopy_logarithmicCeilNode f hD hsupp hT] at hz
  have hzero : autocorr f (logarithmicCeilLag T) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr ha)
  refine ⟨(logarithmicCeilLag_bounds T).1, (logarithmicCeilLag_bounds T).2, hzero, ?_⟩
  have hid := integral_shift_sub_shift_sq f.hasCompactSupport f.continuous
    (logarithmicCeilLag T) 0
  simpa only [add_zero, sub_zero, hzero] using hid

end

end GaloisForLFunctions.BiScaleUncertainty
