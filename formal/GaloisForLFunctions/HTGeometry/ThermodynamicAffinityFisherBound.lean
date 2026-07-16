import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fisher coercivity of thermodynamic affinity

For positive oriented populations `forward` and `reverse`, the entropy-production value controls
the quadratic current cost

`2 (forward - reverse)^2 / (forward + reverse)`.

This is the edge inequality behind the pseudo-entropy-production form of thermodynamic uncertainty
relations.  It strengthens the qualitative second-law statement in
`ThermodynamicAffinityHolonomy`: entropy production is not merely nonnegative, but coercively
detects the observable current in the symmetric population metric.

The finite KMS specialization turns the scalar inequality into a pointwise transition-intensity
bound.  Monotonicity of the Lehmann resolvent then gives exact order relations for both the
absorptive response and its diagonal Pick value.  These are static relations between observed
values; no time evolution is postulated.

Physics provenance: the quadratic current cost is the pseudo entropy production used in direct
and generalized thermodynamic uncertainty relations for Markov jump systems; see Shiraishi and
Saito, arXiv:1806.09389, and the later direct TUR literature.  The proof below is the sharp scalar
logarithm inequality `2x/(x+2) <= log(1+x)` applied to an oriented population ratio.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric quadratic current cost, also called an edgewise pseudo entropy production. -/
def pseudoEntropyProductionValue (forward reverse : ℝ) : ℝ :=
  2 * (forward - reverse) ^ 2 / (forward + reverse)

/-- The quadratic current cost is independent of edge orientation. -/
theorem pseudoEntropyProductionValue_reverse (forward reverse : ℝ) :
    pseudoEntropyProductionValue reverse forward =
      pseudoEntropyProductionValue forward reverse := by
  rw [pseudoEntropyProductionValue, pseudoEntropyProductionValue]
  ring

/-- Positive populations make the quadratic current cost nonnegative. -/
theorem pseudoEntropyProductionValue_nonneg {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    0 ≤ pseudoEntropyProductionValue forward reverse := by
  rw [pseudoEntropyProductionValue]
  exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (add_pos hf hr).le

/-- The quadratic current cost vanishes exactly at local detailed balance. -/
theorem pseudoEntropyProductionValue_eq_zero_iff_eq {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    pseudoEntropyProductionValue forward reverse = 0 ↔ forward = reverse := by
  rw [pseudoEntropyProductionValue]
  constructor
  · intro hzero
    have hnum : 2 * (forward - reverse) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hzero with hnum | hden
      · exact hnum
      · exact False.elim ((add_pos hf hr).ne' hden)
    nlinarith [sq_nonneg (forward - reverse)]
  · rintro rfl
    simp

/-- The quadratic current cost is strict exactly away from detailed balance. -/
theorem pseudoEntropyProductionValue_pos_iff_ne {forward reverse : ℝ}
    (hf : 0 < forward) (hr : 0 < reverse) :
    0 < pseudoEntropyProductionValue forward reverse ↔ forward ≠ reverse := by
  constructor
  · intro hpos heq
    exact (ne_of_gt hpos) ((pseudoEntropyProductionValue_eq_zero_iff_eq hf hr).2 heq)
  · intro hne
    have hnonneg := pseudoEntropyProductionValue_nonneg hf hr
    exact lt_of_le_of_ne hnonneg
      (Ne.symm (mt (pseudoEntropyProductionValue_eq_zero_iff_eq hf hr).mp hne))

private theorem pseudoEntropyProductionValue_le_entropyProductionValue_of_le
    {forward reverse : ℝ} (hf : 0 < forward) (hr : 0 < reverse)
    (hrf : reverse ≤ forward) :
    pseudoEntropyProductionValue forward reverse ≤
      entropyProductionValue forward reverse := by
  have hx : 0 ≤ (forward - reverse) / reverse :=
    div_nonneg (sub_nonneg.mpr hrf) hr.le
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hsum : 0 < forward + reverse := add_pos hf hr
  have hrewriteOne :
      1 + (forward - reverse) / reverse = forward / reverse := by
    field_simp [hr.ne']
    ring
  have hrewriteFraction :
      2 * ((forward - reverse) / reverse) /
          (((forward - reverse) / reverse) + 2) =
        2 * (forward - reverse) / (forward + reverse) := by
    have hden :
        (forward - reverse) / reverse + 2 =
          (forward + reverse) / reverse := by
      field_simp [hr.ne']
      ring
    rw [hden]
    field_simp [hr.ne', hsum.ne']
  rw [hrewriteOne, hrewriteFraction] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hrf)
  rw [pseudoEntropyProductionValue, entropyProductionValue, thermodynamicAffinity]
  calc
    2 * (forward - reverse) ^ 2 / (forward + reverse) =
        (forward - reverse) *
          (2 * (forward - reverse) / (forward + reverse)) := by ring
    _ ≤ (forward - reverse) * Real.log (forward / reverse) := hmul

/-- **Edgewise thermodynamic uncertainty bound.**  Entropy production controls twice the
triangular-discrimination current cost. -/
theorem pseudoEntropyProductionValue_le_entropyProductionValue
    {forward reverse : ℝ} (hf : 0 < forward) (hr : 0 < reverse) :
    pseudoEntropyProductionValue forward reverse ≤
      entropyProductionValue forward reverse := by
  rcases le_total reverse forward with hrf | hfr
  · exact pseudoEntropyProductionValue_le_entropyProductionValue_of_le hf hr hrf
  · rw [← entropyProductionValue_reverse hf hr,
      ← pseudoEntropyProductionValue_reverse forward reverse]
    exact pseudoEntropyProductionValue_le_entropyProductionValue_of_le hr hf hfr

/-- A nontrivial calibration holonomy exposes a strictly positive quadratic current cost on at
least one observed edge, not only a qualitative entropy-production witness. -/
theorem exists_adjacent_pseudoEntropyProductionValue_pos_of_nontrivial_holonomy
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u : V} (p : G.Walk u u)
    (hhol : clockWalkTransport
      (rateRatioCalibration rate (fun a b ↦ (hrate a b).ne')) p ≠ 1) :
    ∃ a b, s(a, b) ∈ p.edges ∧
      0 < pseudoEntropyProductionValue (rate a b) (rate b a) := by
  obtain ⟨a, b, hab, hentropy⟩ :=
    exists_adjacent_entropyProductionValue_pos_of_nontrivial_holonomy rate hrate p hhol
  have hne : rate a b ≠ rate b a :=
    (entropyProductionValue_pos_iff_ne (hrate a b) (hrate b a)).mp hentropy
  exact ⟨a, b, hab,
    (pseudoEntropyProductionValue_pos_iff_ne (hrate a b) (hrate b a)).2 hne⟩

/-- Quadratic KMS current intensity obtained by weighting the population cost with the transition
probability. -/
def finiteKMSPseudoEntropyProductionTransitionIntensity
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (a b : α) : ℝ :=
  pseudoEntropyProductionValue
      (_root_.HTGeometry.finiteGibbsStateWeight β energy b)
      (_root_.HTGeometry.finiteGibbsStateWeight β energy a) *
    Complex.normSq (amplitude a b)

/-- Quadratic KMS current intensities are automatically nonnegative. -/
theorem finiteKMSPseudoEntropyProductionTransitionIntensity_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (a b : α) :
    0 ≤ finiteKMSPseudoEntropyProductionTransitionIntensity
      β energy amplitude a b := by
  exact mul_nonneg
    (pseudoEntropyProductionValue_nonneg
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy b)
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy a))
    (Complex.normSq_nonneg _)

/-- **KMS Fisher coercivity.**  Every Hermitian entropy-production transition intensity dominates
its algebraic quadratic-current intensity. -/
theorem finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α) :
    finiteKMSPseudoEntropyProductionTransitionIntensity β energy amplitude a b ≤
      finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSPseudoEntropyProductionTransitionIntensity,
    finiteKMSEntropyProductionTransitionIntensity_eq_entropyProductionValue_mul_normSq
      β energy amplitude hHermitian]
  exact mul_le_mul_of_nonneg_right
    (pseudoEntropyProductionValue_le_entropyProductionValue
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy b)
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β energy a))
    (Complex.normSq_nonneg _)

/-- Total quadratic KMS current cost is bounded by total entropy production. -/
theorem sum_finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) :
    (∑ a, ∑ b, finiteKMSPseudoEntropyProductionTransitionIntensity
      β energy amplitude a b) ≤
      ∑ a, ∑ b, finiteKMSEntropyProductionTransitionIntensity
        β energy amplitude a b := by
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
    β energy amplitude hHermitian a b

end

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

noncomputable section

/-- Increasing nonnegative Lehmann weights makes the upper-half-plane absorptive value more
negative.  No sign assumption on either packet is needed for this order relation. -/
theorem finiteTransitionPassiveResponse_im_anti_mono_of_intensity_le
    {α : Type*} [Fintype α]
    {intensity lowerIntensity : α → α → ℝ}
    (energy : α → ℝ)
    (hle : ∀ a b, lowerIntensity a b ≤ intensity a b)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteTransitionPassiveResponse intensity energy z).im ≤
      (finiteTransitionPassiveResponse lowerIntensity energy z).im := by
  rw [finiteTransitionPassiveResponse_im, finiteTransitionPassiveResponse_im]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  apply (div_le_div_iff_of_pos_right
    (normSq_sub_ofReal_pos (t := energy a - energy b) hz)).2
  exact neg_le_neg (mul_le_mul_of_nonneg_right (hle a b) hz.le)

/-- Increasing transition weights increases the diagonal Pick/Cauchy value. -/
theorem finiteTransitionPassiveResponse_cauchyDiagonal_mono_of_intensity_le
    {α : Type*} [Fintype α]
    {intensity lowerIntensity : α → α → ℝ}
    (energy : α → ℝ)
    (hle : ∀ a b, lowerIntensity a b ≤ intensity a b)
    {z : ℂ} (hz : 0 < z.im) :
    (((finiteTransitionPassiveResponse lowerIntensity energy ((starRingEnd ℂ) z) -
        finiteTransitionPassiveResponse lowerIntensity energy z) /
          (z - (starRingEnd ℂ) z)).re) ≤
      (((finiteTransitionPassiveResponse intensity energy ((starRingEnd ℂ) z) -
        finiteTransitionPassiveResponse intensity energy z) /
          (z - (starRingEnd ℂ) z)).re) := by
  rw [finiteTransitionPassiveResponse_cauchyDiagonal_re lowerIntensity energy hz,
    finiteTransitionPassiveResponse_cauchyDiagonal_re intensity energy hz]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact div_le_div_of_nonneg_right (hle a b) (Complex.normSq_nonneg _)

end

end HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The entropy-production KMS response has at least the absorptive strength of the quadratic
current response. -/
theorem finiteKMSEntropyProductionResponse_im_le_pseudo
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    {z : ℂ} (hz : 0 < z.im) :
    (_root_.HTGeometry.finiteTransitionPassiveResponse
      (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
      energy z).im ≤
    (_root_.HTGeometry.finiteTransitionPassiveResponse
      (finiteKMSPseudoEntropyProductionTransitionIntensity β energy amplitude)
      energy z).im := by
  exact _root_.HTGeometry.finiteTransitionPassiveResponse_im_anti_mono_of_intensity_le
    energy
    (finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
      β energy amplitude hHermitian) hz

/-- The diagonal Pick value of the entropy-production response dominates the quadratic-current
Pick value. -/
theorem finiteKMSPseudoEntropyProductionResponse_cauchyDiagonal_le_entropyProduction
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    {z : ℂ} (hz : 0 < z.im) :
    (((_root_.HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSPseudoEntropyProductionTransitionIntensity β energy amplitude)
        energy ((starRingEnd ℂ) z) -
      _root_.HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSPseudoEntropyProductionTransitionIntensity β energy amplitude)
        energy z) / (z - (starRingEnd ℂ) z)).re) ≤
    (((_root_.HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
        energy ((starRingEnd ℂ) z) -
      _root_.HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
        energy z) / (z - (starRingEnd ℂ) z)).re) := by
  exact _root_.HTGeometry.finiteTransitionPassiveResponse_cauchyDiagonal_mono_of_intensity_le
    energy
    (finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
      β energy amplitude hHermitian) hz

end

end GaloisForLFunctions.HTGeometry
