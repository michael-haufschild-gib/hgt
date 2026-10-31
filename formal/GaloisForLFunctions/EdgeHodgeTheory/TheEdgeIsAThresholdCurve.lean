import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.EdgeHodgeTheory.TheHorizonFlowAtFixedWidth
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneHorizonMakesEveryBoundedOverlapPositive
import GaloisForLFunctions.EdgeHodgeTheory.TheFunctionFieldFlowIsTrivial

/-!
# The edge is a threshold curve

The complete Weil matrix `W_{φ,c,N}` is the horizon family of the atom of width `w = c/N` at
horizon `N`. Since that family is nested in the horizon, the resolutions at which `W` is positive
form, on each line of fixed width, an initial segment of horizons.

* **The section** (`positiveAt_iff_lt_horizonThreshold`): `W_{φ,c,N}` is positive semidefinite iff
  `N` is below the threshold of the atom of width `c/N`. The edge `e_φ(N)` is the first overlap at
  which the section `w = c/N` meets the graph of the threshold.
* **Width positivity is seeing** (`forall_positiveAt_width_iff`): at a fixed width the family is
  positive at every horizon iff its atom sees no zero right of the line.
* **The detection horizon diverges as the atoms shrink** (`tendsto_horizonThreshold_tiltedUnitSpline`):
  for the tilted spline the threshold of the atom of width `w` tends to `∞` as `w → 0⁺`.
  Positivity at every bounded overlap beyond one horizon places each small width below threshold at
  the horizon `⌈1/w⌉`.

* **Bounded over curves, unbounded over `ℤ`** (`edge_bounded_over_curves_and_unbounded_over_integers`):
  every violation of Weil's bound for a curve is seen within `2g` windows, while the edge of the
  tilted spline tends to `∞` unconditionally.

So the edge is a curve in the plane of resolutions `(w, N)`: the graph of the threshold. Under RH it
is at infinity on every line; without RH it is finite exactly on the lines whose atom sees an
off-line zero, and it recedes to infinity as the width shrinks.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.EdgeHodgeTheory

open HTGeometry SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory
open ArithmeticCastelnuovoSeveri (realTests)
open ArithmeticOrientationGeometry (seenRightZeros)
open Zeta23


theorem atomDilate_mem_realTests' {φ : ℝ → ℝ} (hφ : Admissible φ) {w : ℝ} (hw : 0 < w) :
    atomDilate φ w ∈ realTests := by
  obtain ⟨hg, -, hgc⟩ := atomDilate_facts hφ.contDiff hφ.supp hw
  exact ⟨hg, hgc⟩

/-- **The complete Weil family is a section of the threshold.** `W_{φ,c,N}` is positive
semidefinite iff `N` is below the threshold of the atom of width `c/N`. -/
theorem positiveAt_iff_lt_horizonThreshold {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    PositiveAt φ c N ↔ (N : ℕ∞) < horizonThreshold (atomDilate φ (c / N)) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  rw [positiveAt_iff_twinPositiveAt hφ hc hN, ← horizonDefect_eq_zero_iff_lt_horizonThreshold,
    horizonDefect_eq_zero_iff (atomDilate_mem_realTests' hφ hw)]
  exact Iff.rfl

/-- **Width positivity is seeing.** At a fixed width the complete Weil family is positive at every
horizon iff its atom sees no zero right of the line. -/
theorem forall_positiveAt_width_iff {φ : ℝ → ℝ} (hφ : Admissible φ) {w : ℝ} (hw : 0 < w) :
    (∀ N : ℕ, 1 ≤ N → PositiveAt φ (w * N) N) ↔
      seenRightZeros zetaZeroConfig (atomDilate φ w) = ∅ := by
  constructor
  · intro H
    rw [← Set.encard_eq_zero, ← iSup_horizonDefect (atomDilate_mem_realTests' hφ hw),
      ENat.iSup_eq_zero]
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact_mod_cast ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun x => by
        simp [hermQuad, dotProduct]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN : w * N / N = w := by field_simp
    have h := (positiveAt_iff_lt_horizonThreshold hφ (mul_pos hw hN0) hN).mp (H N hN)
    rw [hcN] at h
    exact_mod_cast (horizonDefect_eq_zero_iff_lt_horizonThreshold _ N).mpr h
  · intro hseen N hN
    have htop := (horizonThreshold_eq_top_iff (atomDilate_mem_realTests' hφ hw)).mpr hseen
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN : w * N / N = w := by field_simp
    rw [positiveAt_iff_lt_horizonThreshold hφ (mul_pos hw hN0) hN, hcN, htop]
    exact ENat.coe_lt_top N

/-! ### The detection horizon diverges as the atoms shrink -/

/-- **The detection horizon diverges.** For the tilted spline the threshold of the atom of width
`w` tends to `∞` as `w → 0⁺`: positivity at every bounded overlap beyond one horizon puts each
small width below threshold at the horizon `⌈1/w⌉`. -/
theorem tendsto_horizonThreshold_tiltedUnitSpline :
    Tendsto (fun w => horizonThreshold (atomDilate tiltedUnitSpline w)) (𝓝[>] 0) (𝓝 ⊤) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap
      2)
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro M
  have hδ : (0 : ℝ) < 1 / ((max N₀ M : ℕ) + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with w ⟨hw0, hw1⟩
  set N : ℕ := ⌈1 / w⌉₊ with hNdef
  have hwinv : ((max N₀ M : ℕ) : ℝ) + 1 < 1 / w := by
    rw [lt_div_iff₀ hw0]
    rw [lt_div_iff₀ (by positivity)] at hw1
    linarith
  have hN1 : 1 / w ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < 1 / w + 1 := Nat.ceil_lt_add_one (by positivity)
  have h' : (((max N₀ M + 1 : ℕ)) : ℝ) < N := by push_cast; exact hwinv.trans_le hN1
  have hNmax : max N₀ M + 1 < N := by exact_mod_cast h'
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := w * N
  have hc0 : 0 < c := mul_pos hw0 hN0
  have hc2 : c ≤ 2 := by
    have : c < 1 + w := by
      have := mul_lt_mul_of_pos_left hNlt hw0
      rw [mul_add, mul_one_div_cancel hw0.ne', mul_one] at this
      exact this
    have hw1' : w ≤ 1 := by
      have : 1 / ((max N₀ M : ℕ) + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (max N₀ M) : (0 : ℝ) ≤ _)]
      linarith
    linarith
  have hpos : PositiveAt tiltedUnitSpline c N := fun x =>
    RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
      (hN₀ N (by omega) c hc0 hc2) x
  have h := (positiveAt_iff_lt_horizonThreshold admissible_tiltedUnitSpline hc0 hN).mp hpos
  have hcN : c / N = w := by simp only [c]; field_simp
  rw [hcN] at h
  exact lt_trans (by exact_mod_cast (show M < N by omega)) h

/-- **The contrast between `𝔽_q` and `ℤ`.** Over a curve, every violation of Weil's bound is seen at
a window bounded by `2g`; over `ℤ`, the edge of the tilted spline tends to `∞` with the horizon,
unconditionally. -/
theorem edge_bounded_over_curves_and_unbounded_over_integers :
    (∀ (ι : Type) [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι), ¬ (∀ i, ‖D.β i‖ = 1) →
      windowEdge D ≤ Fintype.card ι) ∧
    Tendsto (edge SpacingScaleHarmonicAnalysis.tiltedUnitSpline) atTop (𝓝 ⊤) :=
  ⟨fun _ _ D h => windowEdge_le_card D h, tendsto_edge_tiltedUnitSpline⟩

end GaloisForLFunctions.EdgeHodgeTheory
