import GaloisForLFunctions.MatomakiRadziwill.LadderRouteT

/-!
# The ladder covers every frequency

Given sets `small_0, …, small_{J−1}` (the frequencies where every block of scale `j` is small) and
approximations `D_j` of `F` (`j < J`) and `D*` (the top scale), every frequency lies in
`small_0`, or in `small_j ∖ small_{j−1}` for some `1 ≤ j < J` (take the least `j` with
`w ∈ small_j`), or outside `small_{J−1}`.  On each piece `|F|² ≤ 2|F − D|² + 2|D|²`, so
(`ladder_cover_pointwise`, `ladder_cover_integral`)

`∫ |F|² ≤ 2∫|F − D_0|² + 2∫_{small_0} |D_0|²
        + Σ_{1 ≤ j < J} (2∫|F − D_j|² + 2∫_{small_j ∖ small_{j−1}} |D_j|²)
        + 2∫|F − D*|² + 2∫_{small_{J−1}ᶜ} |D*|²`.
-/

open Finset MeasureTheory Set

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem normSq_le_two_mul_add (a b : ℂ) : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_le_norm_sub_add a b
  have hsq : ‖a‖ ^ 2 ≤ (‖a - b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg a) h 2
  have h3 := sq_nonneg (‖a - b‖ - ‖b‖)
  nlinarith [hsq, h3]

/-- The piece of the cover attached to one approximation and one set. -/
def coverPiece (F D : ℝ → ℂ) (s : Set ℝ) (w : ℝ) : ℝ :=
  2 * ‖F w - D w‖ ^ 2 + 2 * s.indicator (fun w => ‖D w‖ ^ 2) w

theorem coverPiece_nonneg (F D : ℝ → ℂ) (s : Set ℝ) (w : ℝ) : 0 ≤ coverPiece F D s w := by
  unfold coverPiece
  have : 0 ≤ s.indicator (fun w => ‖D w‖ ^ 2) w := indicator_nonneg (fun _ _ => by positivity) w
  positivity

theorem le_coverPiece_of_mem {F D : ℝ → ℂ} {s : Set ℝ} {w : ℝ} (hw : w ∈ s) :
    ‖F w‖ ^ 2 ≤ coverPiece F D s w := by
  unfold coverPiece
  rw [indicator_of_mem hw]
  exact normSq_le_two_mul_add (F w) (D w)

/-- **The pointwise cover.** -/
theorem ladder_cover_pointwise (F : ℝ → ℂ) (D : ℕ → ℝ → ℂ) (Dtop : ℝ → ℂ)
    (small : ℕ → Set ℝ) {J : ℕ} (hJ : 1 ≤ J) (w : ℝ) :
    ‖F w‖ ^ 2 ≤ coverPiece F (D 0) (small 0) w
      + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w
      + coverPiece F Dtop (small (J - 1))ᶜ w := by
  classical
  have h0 := coverPiece_nonneg F (D 0) (small 0) w
  have hs : 0 ≤ ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w :=
    sum_nonneg fun j _ => coverPiece_nonneg _ _ _ w
  have ht := coverPiece_nonneg F Dtop (small (J - 1))ᶜ w
  by_cases hw0 : w ∈ small 0
  · have := le_coverPiece_of_mem (F := F) (D := D 0) hw0
    linarith
  by_cases hwJ : w ∈ small (J - 1)
  · have hex : ∃ j, w ∈ small j := ⟨J - 1, hwJ⟩
    set j₀ := Nat.find hex with hj₀
    have hmem : w ∈ small j₀ := Nat.find_spec hex
    have hle : j₀ ≤ J - 1 := Nat.find_min' hex hwJ
    have hpos : 1 ≤ j₀ := by
      rcases Nat.eq_zero_or_pos j₀ with h | h
      · rw [h] at hmem; exact absurd hmem hw0
      · exact h
    have hprev : w ∉ small (j₀ - 1) := Nat.find_min hex (by omega)
    have hj : j₀ ∈ Finset.Ico 1 J := Finset.mem_Ico.mpr ⟨hpos, by omega⟩
    have h1 := le_coverPiece_of_mem (F := F) (D := D j₀) (s := small j₀ ∩ (small (j₀ - 1))ᶜ)
      ⟨hmem, hprev⟩
    have h2 : coverPiece F (D j₀) (small j₀ ∩ (small (j₀ - 1))ᶜ) w
        ≤ ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w :=
      single_le_sum (f := fun j => coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w)
        (fun j _ => coverPiece_nonneg _ _ _ w) hj
    linarith
  · have := le_coverPiece_of_mem (F := F) (D := Dtop) (s := (small (J - 1))ᶜ) hwJ
    linarith

theorem integrableOn_coverPiece {F D : ℝ → ℂ} (hF : Continuous F) (hD : Continuous D) {s : Set ℝ}
    (hs : MeasurableSet s) (W : ℝ) : IntegrableOn (coverPiece F D s) (Icc (-W) W) := by
  have h1 : IntegrableOn (fun w => ‖F w - D w‖ ^ 2) (Icc (-W) W) :=
    ((hF.sub hD).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun w => ‖D w‖ ^ 2) (Icc (-W) W) :=
    (hD.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact (h1.const_mul 2).add ((h2.indicator hs).const_mul 2)

theorem integral_coverPiece {F D : ℝ → ℂ} (hF : Continuous F) (hD : Continuous D) {s : Set ℝ}
    (hs : MeasurableSet s) (W : ℝ) :
    ∫ w in Icc (-W) W, coverPiece F D s w
      = 2 * (∫ w in Icc (-W) W, ‖F w - D w‖ ^ 2)
        + 2 * (∫ w in Icc (-W) W, s.indicator (fun w => ‖D w‖ ^ 2) w) := by
  have h1 : IntegrableOn (fun w => ‖F w - D w‖ ^ 2) (Icc (-W) W) :=
    ((hF.sub hD).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun w => ‖D w‖ ^ 2) (Icc (-W) W) :=
    (hD.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  unfold coverPiece
  rw [integral_add (h1.const_mul 2) ((h2.indicator hs).const_mul 2), integral_const_mul,
    integral_const_mul]

/-- **The integrated cover.** -/
theorem ladder_cover_integral {F : ℝ → ℂ} {D : ℕ → ℝ → ℂ} {Dtop : ℝ → ℂ} (hF : Continuous F)
    (hD : ∀ j, Continuous (D j)) (hDtop : Continuous Dtop) {small : ℕ → Set ℝ}
    (hsmall : ∀ j, MeasurableSet (small j)) {J : ℕ} (hJ : 1 ≤ J) (W : ℝ) :
    (∫ w in Icc (-W) W, ‖F w‖ ^ 2)
      ≤ (2 * (∫ w in Icc (-W) W, ‖F w - D 0 w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (small 0).indicator (fun w => ‖D 0 w‖ ^ 2) w))
        + ∑ j ∈ Finset.Ico 1 J, (2 * (∫ w in Icc (-W) W, ‖F w - D j w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (small j ∩ (small (j - 1))ᶜ).indicator
              (fun w => ‖D j w‖ ^ 2) w))
        + (2 * (∫ w in Icc (-W) W, ‖F w - Dtop w‖ ^ 2)
          + 2 * (∫ w in Icc (-W) W, (small (J - 1))ᶜ.indicator (fun w => ‖Dtop w‖ ^ 2) w)) := by
  have hmeas : ∀ j, MeasurableSet (small j ∩ (small (j - 1))ᶜ) := fun j =>
    (hsmall j).inter (hsmall (j - 1)).compl
  have hi0 := integrableOn_coverPiece hF (hD 0) (hsmall 0) W
  have hij : ∀ j, IntegrableOn (coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ)) (Icc (-W) W) :=
    fun j => integrableOn_coverPiece hF (hD j) (hmeas j) W
  have hit := integrableOn_coverPiece hF hDtop (hsmall (J - 1)).compl W
  have hsum : IntegrableOn (fun w => ∑ j ∈ Finset.Ico 1 J,
      coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w) (Icc (-W) W) :=
    integrable_finsetSum _ fun j _ => hij j
  calc (∫ w in Icc (-W) W, ‖F w‖ ^ 2)
      ≤ ∫ w in Icc (-W) W, (coverPiece F (D 0) (small 0) w
          + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w
          + coverPiece F Dtop (small (J - 1))ᶜ w) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => by positivity)
          ((hi0.add hsum).add hit)
          (Filter.Eventually.of_forall fun w => ladder_cover_pointwise F D Dtop small hJ w)
    _ = _ := by
        have hA : IntegrableOn (fun w => coverPiece F (D 0) (small 0) w
            + ∑ j ∈ Finset.Ico 1 J, coverPiece F (D j) (small j ∩ (small (j - 1))ᶜ) w)
            (Icc (-W) W) := hi0.add hsum
        rw [integral_add hA hit, integral_add hi0 hsum,
          integral_finsetSum _ fun j _ => hij j, integral_coverPiece hF (hD 0) (hsmall 0),
          integral_coverPiece hF hDtop (hsmall (J - 1)).compl]
        congr 2
        exact sum_congr rfl fun j _ => integral_coverPiece hF (hD j) (hmeas j) W

end

end GaloisForLFunctions.MatomakiRadziwill
