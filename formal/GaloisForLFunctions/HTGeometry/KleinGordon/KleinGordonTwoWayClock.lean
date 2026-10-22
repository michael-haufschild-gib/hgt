import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeReversalSpectrum

/-!
# A clock that keeps time in both directions oscillates

The criterion of statement 310 decides stability forwards in time, and the trichotomy of 335 leaves
three possibilities. An instrument that measures time must survive both directions of it, and that
single extra demand removes two of the three.

Stability forwards puts every multiplier in the closed unit disc. Stability of the *reflected*
background does the same for its multipliers, and those are the reciprocals of the original ones
(statement 363) — equivalently, the backward powers are controlled by the reflected forward ones
(357). So every multiplier satisfies `|k| ≤ 1` and `|k|⁻¹ ≤ 1`:

**a two-way stable clock has all of its Floquet multipliers on the unit circle, and spectral radius
exactly one.**

Neither the decaying branch nor the unbounded branch of the trichotomy is available to it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TwoWay

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The reflection of a periodic background is periodic with the same period. -/
theorem periodic_neg_background (hper : ∀ r : ℝ, W (r + T) = W r) (r : ℝ) :
    (fun s : ℝ => W (-s)) (r + T) = (fun s : ℝ => W (-s)) r := by
  show W (-(r + T)) = W (-r)
  have h := hper (-r - T)
  have harg : (-r - T) + T = -r := by ring
  rw [harg] at h
  have harg2 : -(r + T) = -r - T := by ring
  rw [harg2]
  exact h.symm

/-- **A clock that keeps time in both directions is purely oscillatory.** -/
theorem norm_eq_one_of_mem_spectrum_of_two_way_stable (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hfwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT W g h t‖ ≤ C)
    (hbwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT (fun r : ℝ => W (-r)) g h t‖ ≤ C)
    {k : ℂ} (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) : ‖k‖ = 1 := by
  obtain ⟨C, hC⟩ := (kgFloquet_stable_iff hb0 hWb hWs hper hT).mpr hfwd
  obtain ⟨C', hC'⟩ := (kgFloquet_stable_iff hb0 (norm_neg_background_le hWb)
    (continuous_neg_background_apply hWs) (periodic_neg_background hper) hT).mpr hbwd
  have hbwd' : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs (-T) ^ n‖ ≤ C' := fun n =>
    (norm_kgMonodromy_neg_pow_le hb0 hWb hWs n).trans (hC' n)
  have hab : kgMonodromy W b hb0 hWb hWs T * kgMonodromy W b hb0 hWb hWs (-T) = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_right_inverse hb0 hWb hWs hper v
  have hba : kgMonodromy W b hb0 hWb hWs (-T) * kgMonodromy W b hb0 hWb hWs T = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_left_inverse hb0 hWb hWs hper v
  exact norm_eq_one_of_mem_spectrum_of_inverse (le_of_eq norm_one_kgEnergy) hab hba hC hbwd' hk

/-- **A two-way stable clock has spectral radius exactly one.** Neither branch of the trichotomy is
available to it: it neither decays nor breaks. -/
theorem spectralRadius_eq_one_of_two_way_stable (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hfwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT W g h t‖ ≤ C)
    (hbwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT (fun r : ℝ => W (-r)) g h t‖ ≤ C) :
    spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) = 1 := by
  have hall : ∀ k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T), ‖k‖ = 1 := fun _ hk =>
    norm_eq_one_of_mem_spectrum_of_two_way_stable hb0 hWb hWs hper hT hfwd hbwd hk
  have hle : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) ≤ 1 :=
    spectralRadius_le_one_of_forall fun k hk => le_of_eq (hall k hk)
  obtain ⟨k₀, hk₀⟩ := spectrum_kgMonodromy_nonempty (T := T) hb0 hWb hWs
  have hge : (1 : ℝ≥0∞) ≤ spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) := by
    have hmem : ((‖k₀‖₊ : ℝ≥0∞))
        ≤ ⨆ k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T), (‖k‖₊ : ℝ≥0∞) :=
      le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) =>
        ((‖k‖₊ : ℝ≥0∞))) k₀ hk₀
    have hone : ((‖k₀‖₊ : ℝ≥0∞)) = 1 := by
      have h1 : ‖k₀‖ = 1 := hall k₀ hk₀
      have h2 : ‖k₀‖₊ = 1 := by
        rw [← NNReal.coe_inj]
        simpa using h1
      rw [h2]
      exact ENNReal.coe_one
    rw [hone] at hmem
    exact hmem
  exact le_antisymm hle hge

end TwoWay

end GaloisForLFunctions.HTGeometry
