import Mathlib

/-!
# Quantile transport on the half-line

Let `F` be strictly increasing on `[0, ∞)` and let `0 < m` be such that every `v ∈ (0, m)` is a value
`F t` with `t > 0`.  The quantile `Q v` is the unique `t > 0` with `F t = v`; it is strictly
increasing on `(0, m)`, and Lebesgue measure on `(0, m)` is pushed forward by `Q` onto every finite
measure on `ℝ` whose distribution function is `T ↦ min (F T) m` for `T ≥ 0` and `0` for `T < 0`.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The half-line quantile of `F`: a positive preimage of `v` (or `0` when there is none). -/
def halfLineQuantile (F : ℝ → ℝ) (v : ℝ) : ℝ := by
  classical
  exact if h : ∃ t, 0 < t ∧ F t = v then h.choose else 0

variable {F : ℝ → ℝ} {m v : ℝ}

theorem halfLineQuantile_spec (h : ∃ t, 0 < t ∧ F t = v) :
    0 < halfLineQuantile F v ∧ F (halfLineQuantile F v) = v := by
  classical
  unfold halfLineQuantile
  rw [dif_pos h]
  exact h.choose_spec

theorem halfLineQuantile_le_iff (hmono : StrictMonoOn F (Ici 0)) (h : ∃ t, 0 < t ∧ F t = v)
    {T : ℝ} (hT : 0 ≤ T) : halfLineQuantile F v ≤ T ↔ v ≤ F T := by
  obtain ⟨hpos, hF⟩ := halfLineQuantile_spec h
  constructor
  · intro hle
    rw [← hF]
    exact hmono.monotoneOn (mem_Ici.2 hpos.le) (mem_Ici.2 hT) hle
  · intro hle
    by_contra hlt
    rw [not_le] at hlt
    have := hmono (mem_Ici.2 hT) (mem_Ici.2 hpos.le) hlt
    rw [hF] at this
    linarith

theorem halfLineQuantile_strictMonoOn (hmono : StrictMonoOn F (Ici 0))
    (hhit : ∀ v ∈ Ioo 0 m, ∃ t, 0 < t ∧ F t = v) :
    StrictMonoOn (halfLineQuantile F) (Ioo 0 m) := by
  intro v₁ hv₁ v₂ hv₂ hlt
  obtain ⟨h1, hF1⟩ := halfLineQuantile_spec (hhit v₁ hv₁)
  obtain ⟨h2, hF2⟩ := halfLineQuantile_spec (hhit v₂ hv₂)
  by_contra hle
  rw [not_lt] at hle
  have := hmono.monotoneOn (mem_Ici.2 h2.le) (mem_Ici.2 h1.le) hle
  rw [hF1, hF2] at this
  linarith

/-- **Quantile transport.**  The quantile pushes Lebesgue measure on `(0, m)` onto every finite
measure with distribution function `min (F ·) m` on `[0, ∞)` and `0` on `(-∞, 0)`. -/
theorem map_halfLineQuantile_eq (hmono : StrictMonoOn F (Ici 0))
    (hhit : ∀ v ∈ Ioo 0 m, ∃ t, 0 < t ∧ F t = v) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμneg : ∀ T, T < 0 → μ (Iic T) = 0)
    (hμ : ∀ T, 0 ≤ T → μ (Iic T) = ENNReal.ofReal (min (F T) m)) :
    Measure.map (halfLineQuantile F) (volume.restrict (Ioo 0 m)) = μ := by
  have hae : AEMeasurable (halfLineQuantile F) (volume.restrict (Ioo 0 m)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      (halfLineQuantile_strictMonoOn hmono hhit).monotoneOn
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) m)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  refine Measure.ext_of_Iic _ _ fun T => ?_
  rw [Measure.map_apply_of_aemeasurable hae measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  rcases lt_or_ge T 0 with hT | hT
  · rw [hμneg T hT]
    have : halfLineQuantile F ⁻¹' Iic T ∩ Ioo 0 m = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro hw hwm
      have := (halfLineQuantile_spec (hhit w hwm)).1
      linarith
    rw [this, measure_empty]
  · rw [hμ T hT]
    have hset : halfLineQuantile F ⁻¹' Iic T ∩ Ioo 0 m = Ioo 0 m ∩ Iic (F T) := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_Iic]
      constructor
      · rintro ⟨hw, hwm⟩
        exact ⟨hwm, (halfLineQuantile_le_iff hmono (hhit w hwm) hT).1 hw⟩
      · rintro ⟨hwm, hw⟩
        exact ⟨(halfLineQuantile_le_iff hmono (hhit w hwm) hT).2 hw, hwm⟩
    rw [hset]
    rcases lt_or_ge (F T) m with hlt | hge
    · have : Ioo 0 m ∩ Iic (F T) = Ioc 0 (F T) := by
        ext w
        simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_of_le_of_lt h2 hlt⟩, h2⟩
      rw [this, Real.volume_Ioc, sub_zero, min_eq_left hlt.le]
    · have : Ioo 0 m ∩ Iic (F T) = Ioo 0 m := by
        ext w
        simp only [mem_inter_iff, mem_Ioo, mem_Iic]
        exact ⟨fun h => h.1, fun h => ⟨h, h.2.le.trans hge⟩⟩
      rw [this, Real.volume_Ioo, sub_zero, min_eq_right hge]

end

end GaloisForLFunctions.HTGeometry
