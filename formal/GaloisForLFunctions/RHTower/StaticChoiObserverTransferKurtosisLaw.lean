import GaloisForLFunctions.RHTower.StaticChoiKurtosisNearActionLaw

/-!
# Observer-matched energy-transfer kurtosis

The denominator is the fourth moment of energy actually transferred by the
target, not the fourth moment of the entire spectrum. Finite weighted Cauchy
gives Q^2 <= R4 * offDiagonalMass. Unitary centralizer control therefore gives
nearAction <= exp(-r*Q^2/R4), stronger than the global-moment receiver.

All public statements take only data. Empty dimensions, scalar spectra,
degeneracies and zero transfer moments are included using total division.
These are deterministic receiver improvements, not an ordinary-ensemble
incidence-action producer. The Cauchy mechanism carries no novelty claim.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fourth energy-transfer moment of this observer. -/
def normalizedSpectralTransferFourthMoment {d : ℕ} (energy : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, ∑ j, (energy i - energy j) ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)

theorem normalizedSpectralTransferFourthMoment_nonneg {d : ℕ}
    (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ normalizedSpectralTransferFourthMoment energy W := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg ((Even.add_self 2).pow_nonneg _) (sq_nonneg _))

theorem normalizedSpectralTransferFourthMoment_sub_const {d : ℕ}
    (energy : Fin d → ℝ) (a : ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralTransferFourthMoment (fun i => energy i - a) W =
      normalizedSpectralTransferFourthMoment energy W := by
  unfold normalizedSpectralTransferFourthMoment
  simp only [sub_sub_sub_cancel_right]

/-- The matched fourth moment is second energy of the first commutator. -/
theorem normalizedSpectralTransferFourthMoment_eq_commutatorEnergy {d : ℕ}
    (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralTransferFourthMoment energy W =
      normalizedSpectralCommutatorEnergy energy
        (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy) := by
  unfold normalizedSpectralTransferFourthMoment normalizedSpectralCommutatorEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [spectralDiagonalMatrix_commutator_apply]
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring

/-- Universal matched-moment Cauchy inequality; even unitarity is unnecessary. -/
theorem normalizedSpectralCommutatorEnergy_sq_le_transferFourth_offDiagonal
    {d : ℕ} (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) ≤
      normalizedSpectralTransferFourthMoment energy W *
        normalizedSpectralOffDiagonalMass W := by
  let f : Fin d × Fin d → ℝ := fun p => if p.1 = p.2 then 0 else
    (energy p.1 - energy p.2) ^ (2 : ℕ) * ‖W p.1 p.2‖ ^ (2 : ℕ)
  let g : Fin d × Fin d → ℝ := fun p =>
    if p.1 = p.2 then 0 else ‖W p.1 p.2‖ ^ (2 : ℕ)
  let h : Fin d × Fin d → ℝ := fun p =>
    (energy p.1 - energy p.2) ^ (4 : ℕ) * ‖W p.1 p.2‖ ^ (2 : ℕ)
  have hg : ∀ p ∈ (Finset.univ : Finset (Fin d × Fin d)), 0 ≤ g p := by
    intro p _
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hh : ∀ p ∈ (Finset.univ : Finset (Fin d × Fin d)), 0 ≤ h p := by
    intro p _
    dsimp [h]
    positivity
  have hp : ∀ p ∈ (Finset.univ : Finset (Fin d × Fin d)),
      f p ^ (2 : ℕ) ≤ g p * h p := by
    intro p _
    by_cases hij : p.1 = p.2
    · simp only [f, g, hij, ↓reduceIte, pow_two, zero_mul]
      exact le_rfl
    · simp only [f, g, h, hij, ↓reduceIte]
      exact le_of_eq (by ring)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin d × Fin d)) hg hh hp
  have hf : normalizedSpectralCommutatorEnergy energy W =
      (d : ℝ)⁻¹ * ∑ p : Fin d × Fin d, f p := by
    simp only [normalizedSpectralCommutatorEnergy, f, Fintype.sum_prod_type]
  have hR : normalizedSpectralTransferFourthMoment energy W =
      (d : ℝ)⁻¹ * ∑ p : Fin d × Fin d, h p := by
    simp only [normalizedSpectralTransferFourthMoment, h, Fintype.sum_prod_type]
  have hM : normalizedSpectralOffDiagonalMass W =
      (d : ℝ)⁻¹ * ∑ p : Fin d × Fin d, g p := by
    simp only [normalizedSpectralOffDiagonalMass, g, Fintype.sum_prod_type]
  rw [hf, hR, hM]
  calc
    ((d : ℝ)⁻¹ * ∑ p : Fin d × Fin d, f p) ^ (2 : ℕ) =
        ((d : ℝ)⁻¹) ^ (2 : ℕ) * (∑ p : Fin d × Fin d, f p) ^ (2 : ℕ) := by
      rw [mul_pow]
    _ ≤ ((d : ℝ)⁻¹) ^ (2 : ℕ) *
        ((∑ p : Fin d × Fin d, g p) * ∑ p : Fin d × Fin d, h p) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by ring

/-- The matched moment never exceeds the previous global spectral envelope. -/
theorem normalizedSpectralTransferFourthMoment_le_centeredFourthMoment
    (d : ℕ) (energy : Fin d → ℝ) (a : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralTransferFourthMoment energy (U : Matrix (Fin d) (Fin d) ℂ) ≤
      16 * normalizedSpectralFourthMoment (fun i => energy i - a) := by
  rw [← normalizedSpectralTransferFourthMoment_sub_const energy a]
  let e := fun i => energy i - a
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  have hrow : ∀ i, ∑ j, ‖W i j‖ ^ (2 : ℕ) = 1 :=
    sum_sq_norm_row_of_unitary U.2
  have hcol : ∀ j, ∑ i, ‖W i j‖ ^ (2 : ℕ) = 1 := by
    intro j
    simpa only [finiteUnitaryEntryWeight, Complex.sq_norm] using
      sum_finiteUnitaryEntryWeight_column U j
  have hrows : (∑ i, ∑ j, e i ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) =
      ∑ i, e i ^ (4 : ℕ) := by
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  have hcols : (∑ i, ∑ j, e j ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) =
      ∑ j, e j ^ (4 : ℕ) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_one]
  have hfourth : (∑ i, ∑ j, (e i - e j) ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ≤
      16 * ∑ i, e i ^ (4 : ℕ) := by
    calc
      _ ≤ ∑ i, ∑ j, (8 * (e i ^ (4 : ℕ) + e j ^ (4 : ℕ))) *
          ‖W i j‖ ^ (2 : ℕ) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (fourth_power_sub_le (e i) (e j)) (sq_nonneg _)
      _ = 8 * ((∑ i, ∑ j, e i ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) +
          ∑ i, ∑ j, e j ^ (4 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc]
      _ = _ := by rw [hrows, hcols]; ring
  unfold normalizedSpectralTransferFourthMoment normalizedSpectralFourthMoment
  change (d : ℝ)⁻¹ * _ ≤ 16 * ((d : ℝ)⁻¹ * ∑ i, e i ^ (4 : ℕ))
  exact (mul_le_mul_of_nonneg_left hfourth (inv_nonneg.mpr (Nat.cast_nonneg d))).trans_eq
    (by ring)

/-- Matched activation is bounded by the exact target's centralizer deficit. -/
theorem normalizedSpectralObserverActivation_le_centralizerDeficit
    (d : ℕ) (energy : Fin d → ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
        normalizedSpectralTransferFourthMoment energy (U : Matrix (Fin d) (Fin d) ℂ) ≤
      1 - unitaryDiagonalCentralizerMass (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) := by
  by_cases hd : d = 0
  · subst d
    simp [normalizedSpectralCommutatorEnergy, normalizedSpectralTransferFourthMoment,
      unitaryDiagonalCentralizerMass]
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  let R := normalizedSpectralTransferFourthMoment energy W
  have hR0 : 0 ≤ R := normalizedSpectralTransferFourthMoment_nonneg energy W
  have hb0 : 0 ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) :=
    sub_nonneg.mpr (pow_le_one₀ (unitaryDiagonalCentralizerMass_nonneg W)
      (unitaryDiagonalCentralizerMass_le_one (Nat.pos_of_ne_zero hd) U.2))
  change normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) / R ≤ _
  by_cases hR : R = 0
  · simpa only [hR, div_zero] using hb0
  · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR)
    apply (div_le_iff₀ hRpos).2
    exact (normalizedSpectralCommutatorEnergy_sq_le_transferFourth_offDiagonal energy W).trans
      ((mul_le_mul_of_nonneg_left
        (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq
          (Nat.pos_of_ne_zero hd) U.2) hR0).trans_eq (mul_comm _ _))

/-- No centered global-moment activation is stronger than matched activation. -/
theorem normalizedSpectralCenteredActivation_le_observerActivation
    (d : ℕ) (energy : Fin d → ℝ) (a : ℝ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
        (16 * normalizedSpectralFourthMoment (fun i => energy i - a)) ≤
      normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
        normalizedSpectralTransferFourthMoment energy (U : Matrix (Fin d) (Fin d) ℂ) := by
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  let R := normalizedSpectralTransferFourthMoment energy W
  by_cases hR : R = 0
  · have hQ := normalizedSpectralCommutatorEnergy_sq_le_transferFourth_offDiagonal energy W
    change _ ≤ R * normalizedSpectralOffDiagonalMass W at hQ
    rw [hR, zero_mul] at hQ
    have hQ0 := le_antisymm hQ (sq_nonneg _)
    change _ ≤ normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) / R
    rw [hQ0, zero_div, zero_div]
  · have hRpos : 0 < R := lt_of_le_of_ne
      (normalizedSpectralTransferFourthMoment_nonneg energy W) (Ne.symm hR)
    exact div_le_div_of_nonneg_left (sq_nonneg _) hRpos
      (normalizedSpectralTransferFourthMoment_le_centeredFourthMoment d energy a U)

/-- Replica suppression uses only this target's transferred-energy moment. -/
theorem directStaticChoiTargetNearActionMass_le_exp_observerTransferMoment
    (d : ℕ) (energy : Fin d → ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector (U : Matrix (Fin d) (Fin d) ℂ)) energy r δ ≤
      Real.exp (-(r : ℝ) *
        (normalizedSpectralCommutatorEnergy energy (U : Matrix (Fin d) (Fin d) ℂ) ^ (2 : ℕ) /
          normalizedSpectralTransferFourthMoment energy (U : Matrix (Fin d) (Fin d) ℂ))) := by
  let W := (U : Matrix (Fin d) (Fin d) ℂ)
  let b := normalizedSpectralCommutatorEnergy energy W ^ (2 : ℕ) /
    normalizedSpectralTransferFourthMoment energy W
  have hnear : directStaticChoiTargetNearActionMass
      (GaloisForLFunctions.RHTower.choiVector W) energy r δ ≤
      unitaryDiagonalCentralizerMass W ^ (2 * r) := by
    by_cases hd : d = 0
    · subst d
      simpa [directStaticChoiCentralizerMass, unitaryDiagonalCentralizerMass] using
        directStaticChoiTargetNearActionMass_le_centralizerMass_pow
          (GaloisForLFunctions.RHTower.choiVector W) energy r δ
    · exact directStaticChoiTargetNearActionMass_choiVector_le
        (Nat.pos_of_ne_zero hd) W energy r δ
  have hb := normalizedSpectralObserverActivation_le_centralizerDeficit d energy U
  have hbase : unitaryDiagonalCentralizerMass W ^ (2 : ℕ) ≤ Real.exp (-b) := by
    have hexp := Real.add_one_le_exp (-b)
    change b ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) at hb
    linarith only [hb, hexp]
  have hpow := pow_le_pow_left₀ (sq_nonneg (unitaryDiagonalCentralizerMass W)) hbase r
  rw [← pow_mul] at hpow
  refine hnear.trans (hpow.trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  dsimp [b, W]
  ring

end

end RHTower
