import GaloisForLFunctions.RHTower.SoninShellCutScaleConditions

/-!
# One product serving every obligation of the first choice

Four requirements fall on the prescribed product: the two tail conditions the packets need, and the
two slack terms the tied scale leaves independent of the cut.  All four improve as the product
grows, so all four hold beyond some product, and a single product can be chosen to satisfy them
together.

Nothing here mentions the cut, which is what makes this the first of the schedule's two choices.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- **A product satisfying every first-choice obligation.** -/
theorem exists_kappa_full (a q b A C D : ℝ) (hA : 0 ≤ A) (haq : a < q) (hb : 0 < b) (hq : 0 < q)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {target : ℝ} (htarget : 0 < target) :
    ∃ κ : ℝ, 0 < κ ∧
      2 * soninRefTailSup (κ * q) ≤ ∫ y : ℝ, soninUnitBumpData y ∧
      soninRefSqTailSup (κ * q) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20 ∧
      D * (Real.sqrt (A * (κ * (q - a))) * soninRefTailSup (κ * (q - a))) +
        Real.sqrt (C * (κ * b) ^ (1 - (2 * N₀ : ℝ))) ≤ target := by
  have hJ₀ : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  have hcarrier : Tendsto (fun κ : ℝ => κ * q) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hq tendsto_id
  -- the mean's tail condition
  have h1 : ∀ᶠ κ : ℝ in atTop,
      2 * soninRefTailSup (κ * q) ≤ ∫ y : ℝ, soninUnitBumpData y := by
    have h := (tendsto_soninRefTailSup_atTop.comp hcarrier).eventually
      (gt_mem_nhds (show (0 : ℝ) < (∫ y : ℝ, soninUnitBumpData y) / 2 by positivity))
    filter_upwards [h] with κ hκ
    have : soninRefTailSup (κ * q) < (∫ y : ℝ, soninUnitBumpData y) / 2 := hκ
    linarith
  -- the energy floor's tail condition
  have h2 : ∀ᶠ κ : ℝ in atTop,
      soninRefSqTailSup (κ * q) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20 := by
    have h := (tendsto_soninRefSqTailSup_atTop.comp hcarrier).eventually
      (gt_mem_nhds (show (0 : ℝ) < (∫ y : ℝ, soninUnitBumpSq y) / 20 by positivity))
    filter_upwards [h] with κ hκ
    exact le_of_lt hκ
  -- the two slack terms
  have hmid := (tendsto_middleSlackConst_atTop a q A hA haq).const_mul D
  rw [mul_zero] at hmid
  have hhigh := tendsto_highSlackConst_atTop b C hb hN₀
  have hsum := hmid.add hhigh
  rw [add_zero] at hsum
  have h3 : ∀ᶠ κ : ℝ in atTop,
      D * (Real.sqrt (A * (κ * (q - a))) * soninRefTailSup (κ * (q - a))) +
        Real.sqrt (C * (κ * b) ^ (1 - (2 * N₀ : ℝ))) ≤ target := by
    have h := hsum.eventually (gt_mem_nhds htarget)
    filter_upwards [h] with κ hκ
    exact le_of_lt hκ
  have h4 : ∀ᶠ κ : ℝ in atTop, (0 : ℝ) < κ := eventually_gt_atTop 0
  obtain ⟨κ, hκ4, hκ1, hκ2, hκ3⟩ := (h4.and (h1.and (h2.and h3))).exists
  exact ⟨κ, hκ4, hκ1, hκ2, hκ3⟩

end RHTower
