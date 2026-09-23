import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryConstants

/-!
# A sharp positive recovery gap on the actual physical section

The physical first mode lies between two proved coordinate bounds. Realized
edge probes force the exact minimax error for every scalar slope; a polynomial
factorization gives the matching global upper bound. The optimal slope is unique.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

theorem cubicRecoveryPhysical_middle (g : cubicProbeSection) : g.val 2 ∈ Icc (0:ℝ) 1 := by
  refine ⟨g.property.1 2,?_⟩
  have hs := g.property.2.1
  linarith [g.property.1 0,g.property.1 1,g.property.1 3,g.property.1 4]

theorem cubicRecoveryPhysical_mode (g : cubicProbeSection) :
    cubicRecoveryLower (g.val 2) ≤ cubicDecayMode 0 g.val ∧
      cubicDecayMode 0 g.val ≤ g.val 2/4 := by
  have ha := g.property.1 0
  have hc := g.property.1 2
  have he := g.property.1 4
  have hs : g.val 0+g.val 4 ≤ 1-g.val 2 := by
    have hsum := g.property.2.1
    linarith [g.property.1 1,g.property.1 3]
  have hc1 := (cubicRecoveryPhysical_middle g).2
  have hsq : (g.val 0-g.val 4)^(2 : ℕ) ≤ (1-g.val 2)^(2 : ℕ) := by
    have h1 : (g.val 0-g.val 4)^(2 : ℕ) ≤ (g.val 0+g.val 4)^(2 : ℕ) := by nlinarith [mul_nonneg ha he]
    have h2 : (g.val 0+g.val 4)^(2 : ℕ) ≤ (1-g.val 2)^(2 : ℕ) := by nlinarith
    exact h1.trans h2
  change cubicRecoveryLower (g.val 2) ≤ g.val 2*(1-(g.val 0-g.val 4)^(2 : ℕ))/4 ∧ _
  constructor
  · unfold cubicRecoveryLower
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hsq)]
  · change g.val 2*(1-(g.val 0-g.val 4)^(2 : ℕ))/4 ≤ g.val 2/4
    nlinarith [mul_nonneg hc (sq_nonneg (g.val 0-g.val 4))]

def cubicRecoveryEdge (c : Icc (0:ℝ) 1) : cubicProbeSection :=
  ⟨![1-c.val,0,c.val,0,0],by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      fin_cases i
      · simp; exact c.property.2
      · simp
      · simp; exact c.property.1
      · simp
      · simp
    all_goals simp⟩

theorem cubicRecoveryEdge_middle (c : Icc (0:ℝ) 1) : (cubicRecoveryEdge c).val 2=c.val := rfl

theorem cubicRecoveryEdge_mode (c : Icc (0:ℝ) 1) :
    cubicDecayMode 0 (cubicRecoveryEdge c).val=cubicRecoveryLower c.val := by
  simp [cubicDecayMode,cubicRecoveryEdge,cubicRecoveryLower]
  ring

def cubicRecoveryContactProbe : cubicProbeSection :=
  cubicRecoveryEdge ⟨cubicRecoveryContact,⟨cubicRecoveryContact_bounds.1.le,
    by linarith [cubicRecoveryContact_bounds.2]⟩⟩

theorem cubicRecoveryContactProbe_middle : cubicRecoveryContactProbe.val 2=cubicRecoveryContact := rfl

theorem cubicRecoveryContactProbe_mode :
    cubicDecayMode 0 cubicRecoveryContactProbe.val=cubicRecoveryLower cubicRecoveryContact :=
  cubicRecoveryEdge_mode _

theorem cubicRecoveryPhysical_optimalBound (g : cubicProbeSection) :
    |g.val 2-cubicRecoverySlope*cubicDecayMode 0 g.val| ≤ cubicRecoveryGap := by
  have hm := cubicRecoveryPhysical_mode g
  have hc := cubicRecoveryPhysical_middle g
  have hu := cubicRecoveryLower_error (g.val 2) hc
  have hs := cubicRecoverySlope_gt_four
  have hd := cubicRecoveryGap_slope
  have hp := cubicRecoveryGap_pos
  rw [abs_le]
  constructor
  · have h := mul_nonneg hp.le (sub_nonneg.mpr hc.2)
    nlinarith [mul_nonneg (by linarith : 0 ≤ cubicRecoverySlope) (sub_nonneg.mpr hm.2)]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ cubicRecoverySlope) (sub_nonneg.mpr hm.1)]

theorem cubicRecoveryPhysical_lowerBound (α : ℝ) :
    ∃ g : cubicProbeSection, cubicRecoveryGap ≤ |g.val 2-α*cubicDecayMode 0 g.val| := by
  by_cases hα : α ≤ cubicRecoverySlope
  · refine ⟨cubicRecoveryContactProbe,?_⟩
    rw [cubicRecoveryContactProbe_middle,cubicRecoveryContactProbe_mode]
    apply le_trans _ (le_abs_self _)
    have h := cubicRecoveryGap_contact
    nlinarith [mul_nonneg (sub_nonneg.mpr hα) cubicRecoveryLower_contact_pos.le]
  · refine ⟨cubicRecoveryEdge ⟨1,⟨zero_le_one,le_rfl⟩⟩,?_⟩
    rw [cubicRecoveryEdge_middle,cubicRecoveryEdge_mode]
    change cubicRecoveryGap ≤ |1-α*cubicRecoveryLower 1|
    have hL : cubicRecoveryLower 1=1/4 := by unfold cubicRecoveryLower; ring
    rw [hL]
    apply le_trans _ (neg_le_abs _)
    rw [cubicRecoveryGap_slope]
    linarith

theorem cubicRecoveryPhysical_unique (α : ℝ) :
    (∀ g : cubicProbeSection, |g.val 2-α*cubicDecayMode 0 g.val| ≤ cubicRecoveryGap) ↔
      α=cubicRecoverySlope := by
  constructor
  · intro h
    have h1 := h (cubicRecoveryEdge ⟨1,⟨zero_le_one,le_rfl⟩⟩)
    rw [cubicRecoveryEdge_middle,cubicRecoveryEdge_mode] at h1
    change |1-α*cubicRecoveryLower 1| ≤ cubicRecoveryGap at h1
    have hL : cubicRecoveryLower 1=1/4 := by unfold cubicRecoveryLower; ring
    rw [hL,abs_le] at h1
    have h2 := h cubicRecoveryContactProbe
    rw [cubicRecoveryContactProbe_middle,cubicRecoveryContactProbe_mode,abs_le] at h2
    have hd := cubicRecoveryGap_slope
    have hc := cubicRecoveryGap_contact
    have hp := cubicRecoveryLower_contact_pos
    have hα : α ≤ cubicRecoverySlope := by linarith [h1.1]
    have hβ : cubicRecoverySlope ≤ α := by nlinarith [h2.2]
    exact le_antisymm hα hβ
  · rintro rfl
    exact cubicRecoveryPhysical_optimalBound

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
