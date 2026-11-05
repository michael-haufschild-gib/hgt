import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TypicalZetaBoxBounds

/-!
# Typical zeta boxes cover almost every unit window

A finite net of the unit interval transfers typical-height estimates to
every point of a unit window. Translation preserves the exceptional
measure, and the two discarded endpoint strips have bounded length.
-/

open Filter Topology Set MeasureTheory Metric
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

noncomputable section

/-- Every height in the unit window lies near a typical box at the same dyadic scale. -/
def zetaPolylogTypicalWindow (η T X : ℝ) : Prop :=
  ∀ Y : ℝ, |Y - X| ≤ 1 → ∃ t : ℝ,
    zetaTypicalHeight η (zetaPolylogLevel T) T t ∧ |Y - t| ≤ η

private theorem exists_unit_interval_net {η : ℝ} (hη : 0 < η) :
    ∃ s : Finset ℝ, (∀ v ∈ s, |v| ≤ 1) ∧
      ∀ w : ℝ, |w| ≤ 1 → ∃ v ∈ s, |w - v| ≤ η := by
  classical
  obtain ⟨s, hs, hf, hc⟩ := finite_cover_balls_of_compact
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hη
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro v hv
    exact abs_le.mpr (hs (by simpa only [hf.mem_toFinset] using hv))
  · intro w hw
    obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.mp (hc (abs_le.mp hw))
    refine ⟨v, by simpa only [hf.mem_toFinset] using hv, ?_⟩
    exact (show |w - v| < η by simpa only [mem_ball, Real.dist_eq] using hwv).le

/-- Uniformity over a unit window preserves density one. -/
theorem eventually_volume_not_zetaPolylogTypicalWindow_le {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow η T X} ≤
        ENNReal.ofReal (δ * T) := by
  classical
  obtain ⟨s, hs, hcover⟩ := exists_unit_interval_net hη
  let δ' := δ / (2 * (s.card + 1))
  have hδ' : 0 < δ' := by dsimp only [δ']; positivity
  filter_upwards [eventually_volume_not_zetaPolylogTypical_le hη hδ',
    eventually_ge_atTop (4 / δ), eventually_ge_atTop (8 : ℝ)] with T hbad hTδ hT
  let E : Set ℝ := {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t}
  have hsub : {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow η T X} ⊆
      (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) ∪
        ⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E := by
    rintro X ⟨hXT, hn⟩
    by_cases hl : X ≤ T + 1
    · exact Or.inl (Or.inl ⟨hXT.1, hl⟩)
    by_cases hu : 2 * T - 1 ≤ X
    · exact Or.inl (Or.inr ⟨hu, hXT.2⟩)
    right
    by_contra hnone
    apply hn
    intro Y hYX
    obtain ⟨v, hv, hYv⟩ := hcover (Y - X) hYX
    have hvabs := abs_le.mp (hs v hv)
    have hcenter : X + v ∈ Icc T (2 * T) := by
      constructor <;> linarith only [not_le.mp hl, not_le.mp hu, hvabs.1, hvabs.2]
    have htyp : zetaTypicalHeight η (zetaPolylogLevel T) T (X + v) := by
      by_contra ht
      exact hnone (Set.mem_iUnion₂.mpr ⟨v, hv, hcenter, ht⟩)
    refine ⟨X + v, htyp, ?_⟩
    simpa only [sub_add_eq_sub_sub] using hYv
  have htrans : ∀ v ∈ s, volume ((fun X : ℝ => X + v) ⁻¹' E) ≤ ENNReal.ofReal (δ' * T) := by
    intro v _
    rw [measure_preimage_add_right]
    exact hbad
  have hfinite : volume (⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E) ≤
      ENNReal.ofReal ((s.card : ℝ) * δ' * T) := by
    calc
      _ ≤ ∑ v ∈ s, volume ((fun X : ℝ => X + v) ⁻¹' E) := measure_biUnion_finset_le s _
      _ ≤ ∑ _v ∈ s, ENNReal.ofReal (δ' * T) := Finset.sum_le_sum htrans
      _ = s.card * ENNReal.ofReal (δ' * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
        rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg s.card), ENNReal.ofReal_natCast]
  have hends : volume (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) ≤ ENNReal.ofReal 2 := by
    refine (measure_union_le _ _).trans ?_
    rw [Real.volume_Icc, Real.volume_Icc]
    rw [show T + 1 - T = 1 by ring, show 2 * T - (2 * T - 1) = 1 by ring]
    norm_num
  have hcard : (s.card : ℝ) * δ' ≤ δ / 2 := by
    dsimp only [δ']
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith only [hδ]
  have hsmall : 2 + (s.card : ℝ) * δ' * T ≤ δ * T := by
    have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ T by linarith only [hT])
    have hlarge := (div_le_iff₀ hδ).mp hTδ
    nlinarith only [hh, hlarge]
  calc
    _ ≤ volume (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) +
        volume (⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal 2 + ENNReal.ofReal ((s.card : ℝ) * δ' * T) := add_le_add hends hfinite
    _ = ENNReal.ofReal (2 + (s.card : ℝ) * δ' * T) := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsmall

#print axioms eventually_volume_not_zetaPolylogTypicalWindow_le

end

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
