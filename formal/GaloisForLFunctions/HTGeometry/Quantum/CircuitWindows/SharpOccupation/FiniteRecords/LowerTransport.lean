import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.TimeTranslation

/-! # Transporting lower occupation density to a finite observation interval -/
open Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- Each block of length T-G can be translated wholly into the observation
window. A lower long-time density at the smaller tolerance therefore gives
a lower bound with the same multiplicative time correction. -/
theorem lower_occupation_from_periods (E F : Set ℝ) (hF : MeasurableSet F) {G p : ℝ}
    (hperiod : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), ∀ t ∈ E, t+τ ∈ F)
    (hocc : ∀ᶠ R : ℝ in atTop, p*R ≤ volume.real (E ∩ Icc 0 R))
    (a T : ℝ) (hT : G < T) :
    p*(T-G) ≤ volume.real (F ∩ Icc a (a+T)) := by
  let L := T-G
  let B := F ∩ Icc a (a+T)
  have hL : 0 < L := sub_pos.mpr hT
  have hB : MeasurableSet B := hF.inter measurableSet_Icc
  have hfin : volume B ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hblock (u : ℝ) : volume.real (E ∩ Icc u (u+L)) ≤ volume.real B := by
    obtain ⟨τ,hτ,hrep⟩ := hperiod (a-u)
    let f (v : ℝ) := v+τ
    have hmp : MeasurePreserving f volume volume := measurePreserving_add_right volume τ
    have hsub : E ∩ Icc u (u+L) ⊆ f ⁻¹' B := by
      rintro t ⟨ht,hlo,hhi⟩
      refine ⟨hrep t ht,?_,?_⟩
      · change a ≤ t+τ
        linarith only [hlo,hτ.1]
      · change t+τ ≤ a+T
        dsimp only [L] at hhi
        linarith only [hhi,hτ.2]
    exact (measureReal_mono hsub (by rwa [hmp.measure_preimage hB.nullMeasurableSet])).trans_eq
      (hmp.measureReal_preimage hB.nullMeasurableSet)
  have hmany (k : ℕ) : volume.real (E ∩ Icc 0 ((k:ℝ)*L)) ≤ k*volume.real B := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero,zero_mul]
      exact (measureReal_mono inter_subset_right measure_Icc_lt_top.ne).trans_eq
        ((Real.volume_real_Icc_of_le (le_refl (0:ℝ))).trans (sub_self 0))
    | succ k ih =>
      let u := (k:ℝ)*L
      have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg _) hL.le
      have hset : E ∩ Icc 0 (u+L)=(E ∩ Icc 0 u) ∪ (E ∩ Icc u (u+L)) := by
        ext t
        constructor
        · rintro ⟨ht,ht₀,ht₁⟩
          exact (le_total t u).elim (fun h => Or.inl ⟨ht,ht₀,h⟩) (fun h => Or.inr ⟨ht,h,ht₁⟩)
        · rintro (⟨ht,ht₀,ht₁⟩ | ⟨ht,ht₀,ht₁⟩)
          · exact ⟨ht,ht₀,ht₁.trans (le_add_of_nonneg_right hL.le)⟩
          · exact ⟨ht,hu.trans ht₀,ht₁⟩
      rw [Nat.cast_succ,add_mul,one_mul,add_mul,one_mul]
      change volume.real (E ∩ Icc 0 (u+L)) ≤ _
      rw [hset]
      exact (measureReal_union_le ..).trans (add_le_add ih (hblock u))
  obtain ⟨b,hb⟩ := eventually_atTop.mp hocc
  obtain ⟨m,hm⟩ := exists_nat_gt (max 0 (b/L))
  have hmpos : 0 < (m:ℝ) := (le_max_left ..).trans_lt hm
  have h := (hb ((m:ℝ)*L) ((div_lt_iff₀ hL).mp ((le_max_right ..).trans_lt hm)).le).trans (hmany m)
  rw [mul_left_comm p] at h
  exact le_of_mul_le_mul_left h hmpos

#print axioms lower_occupation_from_periods
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
