import GaloisForLFunctions.RHTower.SoninCouplingEnergyLinear

/-!
# The schedule as a sequence of scales

The rate test consumes a sequence of scales with uniform admissibility, not a family indexed by
thresholds.  Since the schedule's conclusion holds for every fine enough cut, shifting the index past
that point turns it into a sequence: the `i`-th scale is the one belonging to the cut with
`Nstart + i` annuli.

Every scale of the sequence exceeds one and reaches the aperture strictly, and the energy along it
grows with the index.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- The scale reaches the aperture strictly, once the cut is fine enough. -/
theorem eventually_soninShellCutScale_gt (a b c : ℝ) (hbc : b < c) (ha : 0 < a) {κ : ℝ}
    (hκ : 0 < κ) : ∀ᶠ N : ℕ in atTop, c < soninShellCutScale b c N κ * a :=
  (Filter.Tendsto.atTop_mul_const ha (tendsto_soninShellCutScale_atTop b c hbc hκ)).eventually_gt_atTop c

/-- **The schedule as a sequence.**  A single product, a starting cut, and the scales of all finer
cuts, each admissible and carrying energy that grows with the index. -/
theorem exists_scale_sequence_of_schedule (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      0 < κ ∧ (∀ i : ℕ, c < soninShellCutScale b c (Nstart + i) κ * a) ∧
        ∀ i : ℕ, ((Nstart + i : ℕ) : ℝ) / 4 -
            36 * (2 * hsNormSq (evenSoninProjectionCorrection b) +
              hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b)) ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
            (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
  obtain ⟨K, hK0, hK⟩ := exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling N₀ hN₀
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  obtain ⟨κ, hκ, hev⟩ := hK a b c q hbc ha hab hb haq hqb (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Nstart, hNstart⟩ :=
    eventually_atTop.mp (hev.and (eventually_soninShellCutScale_gt a b c hbc ha hκ))
  have hall : ∀ i : ℕ, (∃ hr : 1 < soninShellCutScale b c (Nstart + i) κ, 0 < Nstart + i ∧
      (((Nstart + i : ℕ) : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b
          (soninShellCutScale b c (Nstart + i) κ)⁻¹
          (inv_pos.mpr (zero_lt_one.trans hr)) k) / ((1 : ℝ) / 2 / 6) ^ 2) *
        (1 - (1 : ℝ) / 2) ^ 2 ≤
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninShellCutScale b c (Nstart + i) κ) hr)) ∧
      c < soninShellCutScale b c (Nstart + i) κ * a := fun i =>
    hNstart (Nstart + i) (Nat.le_add_right Nstart i)
  refine ⟨κ, Nstart, fun i => ((hall i).1).choose, hκ, fun i => (hall i).2, fun i => ?_⟩
  obtain ⟨hr, hN, hbound⟩ := (hall i).1
  have hrpos : (0 : ℝ) < soninShellCutScale b c (Nstart + i) κ := zero_lt_one.trans hr
  have hinv : (0 : ℝ) < (soninShellCutScale b c (Nstart + i) κ)⁻¹ := inv_pos.mpr hrpos
  have hsum : ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b
      (soninShellCutScale b c (Nstart + i) κ)⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) k) /
      ((1 : ℝ) / 2 / 6) ^ 2 = Dis / ((1 : ℝ) / 2 / 6) ^ 2 := by
    rw [← Finset.sum_div, hDis,
      sum_hsNormSq_soninCouplingIdealErrors a b
        (soninShellCutScale b c (Nstart + i) κ)⁻¹ ha hb hinv]
  rw [hsum] at hbound
  have harith : (((Nstart + i : ℕ) : ℝ) - Dis / ((1 : ℝ) / 2 / 6) ^ 2) * (1 - (1 : ℝ) / 2) ^ 2 =
      ((Nstart + i : ℕ) : ℝ) / 4 - 36 * Dis := by
    norm_num
    ring
  rw [harith] at hbound
  exact hbound

end RHTower
