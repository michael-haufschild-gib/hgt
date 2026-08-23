import GaloisForLFunctions.RHTower.StaticChoiPhysicalActionTransportLaw

open scoped BigOperators Matrix ComplexConjugate NNReal
open Set Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Shift-safe spectral action scale with no Hilbert-space-dimension loss. -/
def staticChoiOscillationScale {d : ℕ} (energy : Fin d → ℝ) : ℝ :=
  2 * (Finset.univ.sup fun i => ‖energy i‖₊ : ℝ≥0) + 1

theorem staticChoiOscillationScale_pos {d : ℕ} (energy : Fin d → ℝ) :
    0 < staticChoiOscillationScale energy := by
  unfold staticChoiOscillationScale
  positivity

theorem abs_energy_sub_le_staticChoiOscillationScale
    {d : ℕ} (energy : Fin d → ℝ) (i j : Fin d) :
    |energy i - energy j| ≤ staticChoiOscillationScale energy := by
  let M : ℝ≥0 := Finset.univ.sup fun k => ‖energy k‖₊
  have hiNN : ‖energy i‖₊ ≤ M := by
    exact Finset.le_sup (f := fun k : Fin d => ‖energy k‖₊)
      (Finset.mem_univ i)
  have hjNN : ‖energy j‖₊ ≤ M := by
    exact Finset.le_sup (f := fun k : Fin d => ‖energy k‖₊)
      (Finset.mem_univ j)
  have hi : |energy i| ≤ (M : ℝ) := by
    simpa [Real.norm_eq_abs] using NNReal.coe_le_coe.mpr hiNN
  have hj : |energy j| ≤ (M : ℝ) := by
    simpa [Real.norm_eq_abs] using NNReal.coe_le_coe.mpr hjNN
  have htri := abs_sub (energy i) (energy j)
  unfold staticChoiOscillationScale
  change |energy i - energy j| ≤ 2 * (M : ℝ) + 1
  linarith

theorem normalizedSpectralCommutatorEnergy_le_oscillation_sq_mul_offDiagonal
    {d : ℕ} (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy W ≤
      staticChoiOscillationScale energy ^ 2 *
        normalizedSpectralOffDiagonalMass W := by
  have hscale0 : 0 ≤ staticChoiOscillationScale energy :=
    (staticChoiOscillationScale_pos energy).le
  have hterm : ∀ i j : Fin d,
      (if i = j then 0 else (energy i - energy j) ^ 2 * ‖W i j‖ ^ 2) ≤
        staticChoiOscillationScale energy ^ 2 *
          (if i = j then 0 else ‖W i j‖ ^ 2) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [← sq_abs (energy i - energy j)]
      exact (sq_le_sq₀ (abs_nonneg _) hscale0).2
        (abs_energy_sub_le_staticChoiOscillationScale energy i j)
  unfold normalizedSpectralCommutatorEnergy normalizedSpectralOffDiagonalMass
  have hsum :
      (∑ i, ∑ j, if i = j then 0 else
          (energy i - energy j) ^ 2 * ‖W i j‖ ^ 2) ≤
        staticChoiOscillationScale energy ^ 2 *
          ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ 2 := by
    calc
      _ ≤ ∑ i, ∑ j, staticChoiOscillationScale energy ^ 2 *
            (if i = j then 0 else ‖W i j‖ ^ 2) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := by simp_rw [Finset.mul_sum]
  calc
    (d : ℝ)⁻¹ * (∑ i, ∑ j, if i = j then 0 else
        (energy i - energy j) ^ 2 * ‖W i j‖ ^ 2) ≤
        (d : ℝ)⁻¹ * (staticChoiOscillationScale energy ^ 2 *
          ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg d))
    _ = staticChoiOscillationScale energy ^ 2 *
        ((d : ℝ)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ 2) := by ring

/-- Endpoint-adaptive transverse base using spectral oscillation rather than
the dimension-losing ℓ¹ speed surrogate. -/
def staticChoiOscillationAdaptiveReplicaBase
    {d : ℕ} (energy : Fin d → ℝ) (activation : ℝ) : ℝ :=
  max 0 (1 - activation / staticChoiOscillationScale energy ^ 2)

theorem directStaticChoiTargetNearActionMass_choiVector_le_oscillationAdaptive_add_carrier
    {d : ℕ} (hd : 0 < d)
    (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ activation : ℝ) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector W) energy r δ ≤
      staticChoiOscillationAdaptiveReplicaBase energy activation ^ r +
        if normalizedSpectralCommutatorEnergy energy W ≤ activation then 1 else 0 := by
  have hnear := directStaticChoiTargetNearActionMass_choiVector_le hd W energy r δ
  have hmass0 := unitaryDiagonalCentralizerMass_nonneg W
  have hmass1 := unitaryDiagonalCentralizerMass_le_one hd hW
  by_cases htube : normalizedSpectralCommutatorEnergy energy W ≤ activation
  · rw [if_pos htube]
    have hnearOne :
        directStaticChoiTargetNearActionMass
            (GaloisForLFunctions.RHTower.choiVector W) energy r δ ≤ 1 :=
      hnear.trans (pow_le_one₀ hmass0 hmass1)
    have hbase0 : 0 ≤ staticChoiOscillationAdaptiveReplicaBase energy activation :=
      le_max_left _ _
    nlinarith [pow_nonneg hbase0 r]
  · rw [if_neg htube, add_zero]
    have hscale : 0 < staticChoiOscillationScale energy ^ 2 :=
      sq_pos_of_pos (staticChoiOscillationScale_pos energy)
    have hcomm :
        normalizedSpectralCommutatorEnergy energy W ≤
          staticChoiOscillationScale energy ^ 2 *
            (1 - unitaryDiagonalCentralizerMass W ^ 2) := by
      calc
        normalizedSpectralCommutatorEnergy energy W ≤
            staticChoiOscillationScale energy ^ 2 *
              normalizedSpectralOffDiagonalMass W :=
          normalizedSpectralCommutatorEnergy_le_oscillation_sq_mul_offDiagonal energy W
        _ ≤ staticChoiOscillationScale energy ^ 2 *
              (1 - unitaryDiagonalCentralizerMass W ^ 2) :=
          mul_le_mul_of_nonneg_left
            (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq hd hW)
            (sq_nonneg _)
    have hstrict :
        unitaryDiagonalCentralizerMass W ^ 2 <
          1 - activation / staticChoiOscillationScale energy ^ 2 := by
      have hactlt : activation < normalizedSpectralCommutatorEnergy energy W :=
        lt_of_not_ge htube
      have hratio :
          activation / staticChoiOscillationScale energy ^ 2 <
            1 - unitaryDiagonalCentralizerMass W ^ 2 :=
        (div_lt_iff₀ hscale).2 (by
          simpa [mul_comm] using hactlt.trans_le hcomm)
      linarith
    have hbaseEq :
        staticChoiOscillationAdaptiveReplicaBase energy activation =
          1 - activation / staticChoiOscillationScale energy ^ 2 := by
      rw [staticChoiOscillationAdaptiveReplicaBase, max_eq_right]
      exact le_trans (sq_nonneg (unitaryDiagonalCentralizerMass W)) hstrict.le
    have hpow :
        unitaryDiagonalCentralizerMass W ^ (2 * r) ≤
          staticChoiOscillationAdaptiveReplicaBase energy activation ^ r := by
      calc
        unitaryDiagonalCentralizerMass W ^ (2 * r) =
            (unitaryDiagonalCentralizerMass W ^ 2) ^ r := by rw [pow_mul]
        _ ≤ (1 - activation / staticChoiOscillationScale energy ^ 2) ^ r :=
          pow_le_pow_left₀ (sq_nonneg _) hstrict.le r
        _ = staticChoiOscillationAdaptiveReplicaBase energy activation ^ r := by
          rw [hbaseEq]
    exact hnear.trans hpow

/-- Coordinate-free oscillation action law: spectral activation is exactly
the physical Hilbert--Schmidt commutator energy divided by dimension. -/
theorem directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_oscillationAdaptivePhysicalAction
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ activation : ℝ) :
    directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))
        hH.eigenvalues r δ ≤
      staticChoiOscillationAdaptiveReplicaBase hH.eigenvalues
          ((d : ℝ)⁻¹ * activation) ^ r +
        if finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H) ≤ activation
          then 1 else 0 := by
  have h :=
    directStaticChoiTargetNearActionMass_choiVector_le_oscillationAdaptive_add_carrier
      hd hH.eigenvalues (hermitianSpectralEndpoint hH U).2 r δ
        ((d : ℝ)⁻¹ * activation)
  rw [normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at h
  have hdInv : 0 < (d : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hd)
  by_cases hc : finiteMatrixHilbertSchmidtEnergy
      (H * (U : Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ) * H) ≤ activation
  · rw [if_pos hc]
    rw [if_pos] at h
    · exact h
    · exact mul_le_mul_of_nonneg_left hc hdInv.le
  · rw [if_neg hc]
    rw [if_neg] at h
    · exact h
    · exact fun hscaled => hc (le_of_mul_le_mul_left hscaled hdInv)

end

end RHTower
