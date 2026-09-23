import GaloisForLFunctions.RHTower.StaticChoiCentralizerCarrierReplicaLaw

open scoped BigOperators Matrix ComplexConjugate
open Matrix

namespace RHTower

open RHTower GaloisForLFunctions.RHTower

theorem sum_sq_norm_row_of_unitary
    {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    ∑ j, ‖W i j‖ ^ (2 : ℕ) = 1 := by
  have hmat : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have hi := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) hmat
  rw [Matrix.mul_apply] at hi
  simp only [star, Matrix.conjTranspose_apply, Matrix.one_apply, ↓reduceIte] at hi
  have hre := congrArg Complex.re hi
  simpa [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply] using hre

theorem sum_sq_norm_of_unitary
    {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ i, ∑ j, ‖W i j‖ ^ (2 : ℕ) = d := by
  simp_rw [sum_sq_norm_row_of_unitary hW]
  simp

noncomputable def normalizedSpectralOffDiagonalMass
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)

noncomputable def normalizedSpectralCommutatorEnergy
    {d : ℕ} (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, ∑ j,
    if i = j then 0 else (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)

noncomputable def spectralDiagonalMatrix
    {d : ℕ} (energy : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => (energy i : ℂ)

theorem spectralDiagonalMatrix_commutator_apply
    {d : ℕ} (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) :
    (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy) i j =
      ((energy i - energy j : ℝ) : ℂ) * W i j := by
  rw [Matrix.sub_apply, spectralDiagonalMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- The scalar energy is exactly normalized Hilbert--Schmidt commutator energy, expressed as the
squared norm of the normalized Choi vector of the commutator. -/
theorem norm_choiVector_spectralCommutator_sq
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    ‖GaloisForLFunctions.RHTower.choiVector
        (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy)‖ ^ (2 : ℕ) =
      normalizedSpectralCommutatorEnergy energy W := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [GaloisForLFunctions.RHTower.choiVector, Fintype.sum_prod_type]
  unfold normalizedSpectralCommutatorEnergy
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ^ (2 : ℕ) = d := Real.sq_sqrt hdR.le
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [spectralDiagonalMatrix_commutator_apply]
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrtNe : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hdR
    field_simp [hsqrtNe]
    rw [sq_abs, hsqrt]

theorem offDiagonal_add_diagonal_eq_total
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) +
        ∑ i, ‖W i i‖ ^ (2 : ℕ) =
      ∑ i, ∑ j, ‖W i j‖ ^ (2 : ℕ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ‖W i i‖ ^ (2 : ℕ) =
      ∑ j : Fin d, if i = j then ‖W i j‖ ^ (2 : ℕ) else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq
    {d : ℕ} (hd : 0 < d) {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralOffDiagonalMass W ≤
      1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by
  have htotal := sum_sq_norm_of_unitary hW
  have hsplit := offDiagonal_add_diagonal_eq_total W
  have hdiag : (∑ i, ‖W i i‖) ^ (2 : ℕ) ≤
      (d : ℝ) * ∑ i, ‖W i i‖ ^ (2 : ℕ) := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i : Fin d => ‖W i i‖))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold normalizedSpectralOffDiagonalMass unitaryDiagonalCentralizerMass
  field_simp
  nlinarith

theorem abs_energy_sub_le_two_staticChoiSpeed
    {d : ℕ} (energy : Fin d → ℝ) (i j : Fin d) :
    |energy i - energy j| ≤ 2 * staticChoiSpeed energy := by
  have hi : |energy i| ≤ ∑ k, |energy k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (energy k)) (Finset.mem_univ i)
  have hj : |energy j| ≤ ∑ k, |energy k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (energy k)) (Finset.mem_univ j)
  have htri := abs_sub (energy i) (energy j)
  unfold staticChoiSpeed
  linarith

theorem normalizedSpectralCommutatorEnergy_le_speed_sq_mul_offDiagonal
    {d : ℕ} (energy : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy W ≤
      (2 * staticChoiSpeed energy) ^ (2 : ℕ) * normalizedSpectralOffDiagonalMass W := by
  have hspeed0 : 0 ≤ 2 * staticChoiSpeed energy := by
    exact mul_nonneg (by norm_num) (staticChoiSpeed_pos energy).le
  have hterm : ∀ i j : Fin d,
      (if i = j then 0 else (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ≤
        (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
          (if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [← sq_abs (energy i - energy j)]
      exact (sq_le_sq₀ (abs_nonneg _) hspeed0).2
        (abs_energy_sub_le_two_staticChoiSpeed energy i j)
  unfold normalizedSpectralCommutatorEnergy normalizedSpectralOffDiagonalMass
  have hsum :
      (∑ i, ∑ j, if i = j then 0 else
          (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ≤
        (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
          ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ) := by
    calc
      _ ≤ ∑ i, ∑ j, (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
            (if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := by simp_rw [Finset.mul_sum]
  calc
    (d : ℝ)⁻¹ * (∑ i, ∑ j, if i = j then 0 else
        (energy i - energy j) ^ (2 : ℕ) * ‖W i j‖ ^ (2 : ℕ)) ≤
        (d : ℝ)⁻¹ * ((2 * staticChoiSpeed energy) ^ (2 : ℕ) *
          ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg d))
    _ = (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
        ((d : ℝ)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖W i j‖ ^ (2 : ℕ)) := by ring

theorem normalizedSpectralCommutatorEnergy_le_centralizerDefect
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy energy W ≤
      (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
        choiDist (unitaryRadialDiagonalMatrix W) W ^ (2 : ℕ) := by
  calc
    normalizedSpectralCommutatorEnergy energy W ≤
        (2 * staticChoiSpeed energy) ^ (2 : ℕ) * normalizedSpectralOffDiagonalMass W :=
      normalizedSpectralCommutatorEnergy_le_speed_sq_mul_offDiagonal energy W
    _ ≤ (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
        (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq hd hW)
        (sq_nonneg _)
    _ = (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
        choiDist (unitaryRadialDiagonalMatrix W) W ^ (2 : ℕ) := by
      rw [choiDist_radialDiagonal_exact hd, Real.sq_sqrt]
      have hmass0 := unitaryDiagonalCentralizerMass_nonneg W
      have hmass1 := unitaryDiagonalCentralizerMass_le_one hd hW
      nlinarith [mul_nonneg (sub_nonneg.mpr hmass1)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hmass0)]

/-- Projective closeness to the exact spectral centralizer forces small normalized
Hilbert--Schmidt commutator, with no minimum-gap premise. -/
theorem norm_choiVector_spectralCommutator_le_centralizerDistance
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ‖GaloisForLFunctions.RHTower.choiVector
        (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy)‖ ≤
      2 * staticChoiSpeed energy *
        choiDist (unitaryRadialDiagonalMatrix W) W := by
  have henergy := normalizedSpectralCommutatorEnergy_le_centralizerDefect
    hd energy hW
  rw [← norm_choiVector_spectralCommutator_sq hd energy W] at henergy
  have hleft := norm_nonneg (GaloisForLFunctions.RHTower.choiVector
    (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy))
  have hright : 0 ≤ 2 * staticChoiSpeed energy *
      choiDist (unitaryRadialDiagonalMatrix W) W :=
    mul_nonneg (mul_nonneg (by norm_num) (staticChoiSpeed_pos energy).le)
      (choiDist_nonneg _ _)
  rw [show (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
      choiDist (unitaryRadialDiagonalMatrix W) W ^ (2 : ℕ) =
      (2 * staticChoiSpeed energy *
        choiDist (unitaryRadialDiagonalMatrix W) W) ^ (2 : ℕ) by ring] at henergy
  exact (sq_le_sq₀ hleft hright).mp henergy

theorem norm_choiVector_spectralCommutator_lt_of_centralizerDistance_lt
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {ρ : ℝ}
    (hdist : choiDist (unitaryRadialDiagonalMatrix W) W < ρ) :
    ‖GaloisForLFunctions.RHTower.choiVector
        (spectralDiagonalMatrix energy * W - W * spectralDiagonalMatrix energy)‖ <
      2 * staticChoiSpeed energy * ρ := by
  exact (norm_choiVector_spectralCommutator_le_centralizerDistance hd energy hW).trans_lt
    (mul_lt_mul_of_pos_left hdist (mul_pos (by norm_num) (staticChoiSpeed_pos energy)))

end RHTower
