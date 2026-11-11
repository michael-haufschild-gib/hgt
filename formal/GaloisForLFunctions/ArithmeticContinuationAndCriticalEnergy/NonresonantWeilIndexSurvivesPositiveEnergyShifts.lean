import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheRightApertureIndexIncludesExactlyTheNullModes

/-!
# Nonresonant Weil index survives positive energy shifts

A fixed-aperture compactness argument bounds every sufficiently small
upward energy shift by the original nonpositive dimension. Away from a
null mode, this preserves the negative index while allowing a mass error.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil HTGeometry SignedArithmeticEnergyIncidence

/-- A positive energy shift can be chosen without creating more negative
directions than the original negative space plus kernel. -/
theorem exists_positive_energyShift_negativeRank_le (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ negativeRank a (E + δ) ≤ negativeRank a E + weilNullity a E := by
  classical
  let W : Submodule ℂ (Space a) := negativeSpace a E ⊔ (operator a E).toLinearMap.ker
  have hdim : Module.finrank ℂ W = negativeRank a E + weilNullity a E := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (negativeSpace a E) (operator a E).toLinearMap.ker
    rw [(PaperNegativePart.negativeSpace_disjoint_ker
      (operator a E) (operator_selfAdjoint a E)).eq_bot,
      finrank_bot, add_zero] at hd
    exact hd
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  by_contra hn
  push_neg at hn
  have hex : ∀ n, ∃ u : Space a, u ∈ negativeSpace a (E + ε n) ∧ ‖u‖ = 1 ∧ u ∈ Wᗮ := by
    intro n
    exact exists_unit_mem_orthogonal_of_finrank_lt (negativeSpace a (E + ε n)) W
      (by rw [hdim]; exact hn (ε n) (hε n))
  choose u hu hnorm horth using hex
  have hq : ∀ n, (inner ℂ (operator a E (u n)) (u n)).re ≤ ε n := by
    intro n
    have hne : u n ≠ 0 := fun hz => by
      simpa only [hz, norm_zero, zero_ne_one] using hnorm n
    have hneg := (PaperNegativePart.negativeSpace_strict _
      (operator_selfAdjoint a (E + ε n)) (hu n) hne).le
    have hJn : ‖ccmArchimedeanFormToAperture a (u n)‖ ≤ 1 := by
      have h := (ccmArchimedeanFormToAperture a).le_opNorm (u n)
      rw [hnorm, mul_one] at h
      exact h.trans (norm_ccmArchimedeanFormToAperture_le_one a)
    have hmass : ‖ccmArchimedeanFormToAperture a (u n)‖ ^ 2 ≤ 1 := by
      nlinarith only [hJn, norm_nonneg (ccmArchimedeanFormToAperture a (u n))]
    rw [operator_quadratic] at hneg ⊢
    nlinarith only [hneg, mul_le_mul_of_nonneg_left hmass (hε n).le]
  obtain ⟨v, φ, hφ, _, hweak⟩ := exists_weakConvC_subseq_of_bounded u (fun n => (hnorm n).le)
  have hlimit := compactPerturbation_unit_weakLimit_of_energy_upper_bound
    (isCompactOperator_ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a - (E : ℂ) • 1)
    hweak (fun n => hnorm (φ n)) (hεlim.comp hφ.tendsto_atTop)
    (fun n => by rw [← operator_quadratic_eq_compactEnergy]; exact hq (φ n))
  have hvq : (inner ℂ (operator a E v) v).re ≤ 0 := by
    rw [operator_quadratic_eq_compactEnergy]
    exact hlimit.2
  have hvorth : ∀ y ∈ W, inner ℂ y v = 0 := by
    intro y hy
    have ht := hweak (innerSL ℂ y)
    have hz : ∀ n, inner ℂ y (u (φ n)) = 0 := fun n =>
      (Submodule.mem_orthogonal _ _).mp (horth (φ n)) y hy
    have ht' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (inner ℂ y v)) := by
      simpa only [innerSL_apply_apply, Function.comp_apply, hz] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hvneg : v ∈ (negativeSpace a E)ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr fun y hy =>
      hvorth y ((show negativeSpace a E ≤ W from le_sup_left) hy)
  have hvker : operator a E v = 0 :=
    PaperNegativePart.apply_eq_zero_of_nonpositive_orthogonal
      (operator a E) (operator_selfAdjoint a E) hvneg hvq
  exact hlimit.1 (inner_self_eq_zero.mp
    (hvorth v ((show (operator a E).toLinearMap.ker ≤ W from le_sup_right) hvker)))

/-- Absence of a null mode permits a strictly positive mass shift without
changing the negative index. -/
theorem exists_positive_energyShift_negativeRank_eq_of_nullity_zero
    (a : SuzukiPositiveAperture) (E : ℝ) (hnull : weilNullity a E = 0) :
    ∃ δ : ℝ, 0 < δ ∧ negativeRank a (E + δ) = negativeRank a E := by
  obtain ⟨δ, hδ, hupper⟩ := exists_positive_energyShift_negativeRank_le a E
  rw [hnull, add_zero] at hupper
  exact ⟨δ, hδ, le_antisymm hupper (negativeRank_monotone a (by linarith only [hδ]))⟩

/-- After a small strict aperture enlargement and positive mass shift,
the index equals the original full nonpositive dimension. -/
theorem exists_wider_aperture_positive_shift_nonpositive_index
    (a : SuzukiPositiveAperture) (E : ℝ) :
    ∃ b : SuzukiPositiveAperture, ∃ δ : ℝ,
      a.1 < b.1 ∧ 0 < δ ∧
        negativeRank b (E + δ) = negativeRank a E + weilNullity a E := by
  obtain ⟨b, hab, heq⟩ := exists_right_interval_negativeRank_eq a E
  let c : SuzukiPositiveAperture := ⟨(a.1 + b.1) / 2, by positivity⟩
  have hac : a.1 < c.1 := by dsimp only [c]; linarith only [hab]
  have hcb : c.1 < b.1 := by dsimp only [c]; linarith only [hab]
  have hcindex := heq c hac hcb.le
  have hgrowth := negativeRank_add_nullity_le_of_aperture_lt hcb E
  rw [hcindex, heq b hab le_rfl] at hgrowth
  have hcnull : weilNullity c E = 0 := by omega
  obtain ⟨δ, hδ, hshift⟩ := exists_positive_energyShift_negativeRank_eq_of_nullity_zero c E hcnull
  exact ⟨c, δ, hac, hδ, hshift.trans hcindex⟩

/-- A nonresonant form tolerates simultaneous strict aperture enlargement
and a positive physical-mass error without changing its index. -/
theorem exists_wider_aperture_positive_shift_same_index
    (a : SuzukiPositiveAperture) (E : ℝ) (hnull : weilNullity a E = 0) :
    ∃ b : SuzukiPositiveAperture, ∃ δ : ℝ,
      a.1 < b.1 ∧ 0 < δ ∧ negativeRank b (E + δ) = negativeRank a E := by
  simpa only [hnull, add_zero] using
    exists_wider_aperture_positive_shift_nonpositive_index a E

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
