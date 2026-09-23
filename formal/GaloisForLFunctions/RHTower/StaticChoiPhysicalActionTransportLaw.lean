import GaloisForLFunctions.RHTower.StaticChoiAdaptiveActionCarrierLaw
import GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Physical transport of the adaptive static-Choi action law

Spectral commutator action is exactly physical Hilbert--Schmidt commutator
energy divided by Hilbert-space dimension.  Consequently the adaptive
action--carrier dichotomy is coordinate free and incurs no eigenbasis,
operator-norm, or minimum-gap loss.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

theorem norm_choiVector_sq_eq_normalized_finiteMatrixHilbertSchmidtEnergy
    {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖choiVector A‖ ^ (2 : ℕ) =
      (d : ℝ)⁻¹ * finiteMatrixHilbertSchmidtEnergy A := by
  rw [EuclideanSpace.norm_sq_eq,
    finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq, Finset.sum_comm]
  simp only [choiVector, Fintype.sum_prod_type, Fintype.card_fin,
    Complex.sq_norm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.sq_norm, ← Complex.sq_norm, norm_div,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ^ (2 : ℕ) = d := Real.sq_sqrt hdR.le
  have hsqrtNe : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hdR
  field_simp [hsqrtNe]
  nlinarith

def hermitianSpectralEndpoint
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  star hH.eigenvectorUnitary * U * hH.eigenvectorUnitary

theorem spectralCommutator_hermitianSpectralEndpoint
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    spectralDiagonalMatrix hH.eigenvalues *
          (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) -
        (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) *
          spectralDiagonalMatrix hH.eigenvalues =
      star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (H * (U : Matrix (Fin d) (Fin d) ℂ) -
          (U : Matrix (Fin d) (Fin d) ℂ) * H) *
        (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := by
  let K := hH.eigenvectorUnitary
  have hdiag : star (K : Matrix (Fin d) (Fin d) ℂ) * H *
      (K : Matrix (Fin d) (Fin d) ℂ) =
        spectralDiagonalMatrix hH.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, spectralDiagonalMatrix,
      Function.comp_apply] using
      GaloisForLFunctions.HTGeometry.conjTranspose_mul_mul_eigenvectorUnitary hH
  have hright : (K : Matrix (Fin d) (Fin d) ℂ) *
      star (K : Matrix (Fin d) (Fin d) ℂ) = 1 := Unitary.coe_mul_star_self K
  dsimp [hermitianSpectralEndpoint]
  rw [← hdiag]
  calc
    (star (K : Matrix (Fin d) (Fin d) ℂ) * H *
          (K : Matrix (Fin d) (Fin d) ℂ)) *
          (star (K : Matrix (Fin d) (Fin d) ℂ) *
            (U : Matrix (Fin d) (Fin d) ℂ) *
            (K : Matrix (Fin d) (Fin d) ℂ)) -
        (star (K : Matrix (Fin d) (Fin d) ℂ) *
          (U : Matrix (Fin d) (Fin d) ℂ) *
          (K : Matrix (Fin d) (Fin d) ℂ)) *
          (star (K : Matrix (Fin d) (Fin d) ℂ) * H *
            (K : Matrix (Fin d) (Fin d) ℂ)) =
      star (K : Matrix (Fin d) (Fin d) ℂ) *
        (H * (U : Matrix (Fin d) (Fin d) ℂ) -
          (U : Matrix (Fin d) (Fin d) ℂ) * H) *
        (K : Matrix (Fin d) (Fin d) ℂ) := by
      calc
        _ = star (K : Matrix (Fin d) (Fin d) ℂ) * H *
              ((K : Matrix (Fin d) (Fin d) ℂ) *
                star (K : Matrix (Fin d) (Fin d) ℂ)) *
              (U : Matrix (Fin d) (Fin d) ℂ) *
              (K : Matrix (Fin d) (Fin d) ℂ) -
            star (K : Matrix (Fin d) (Fin d) ℂ) *
              (U : Matrix (Fin d) (Fin d) ℂ) *
              ((K : Matrix (Fin d) (Fin d) ℂ) *
                star (K : Matrix (Fin d) (Fin d) ℂ)) * H *
              (K : Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
        _ = _ := by rw [hright]; noncomm_ring

theorem normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    normalizedSpectralCommutatorEnergy hH.eigenvalues
        (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ) =
      (d : ℝ)⁻¹ * finiteMatrixHilbertSchmidtEnergy
        (H * (U : Matrix (Fin d) (Fin d) ℂ) -
          (U : Matrix (Fin d) (Fin d) ℂ) * H) := by
  rw [← norm_choiVector_spectralCommutator_sq hd]
  rw [spectralCommutator_hermitianSpectralEndpoint hH U]
  rw [norm_choiVector_sq_eq_normalized_finiteMatrixHilbertSchmidtEnergy hd]
  rw [finiteMatrixHilbertSchmidtEnergy_unitaryConjugate]

/-- Coordinate-free action--carrier law.  The spectral carrier condition is
exactly physical Hilbert--Schmidt commutator activation divided by dimension. -/
theorem directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_adaptivePhysicalAction
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ activation : ℝ) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))
        hH.eigenvalues r δ ≤
      staticChoiAdaptiveReplicaBase hH.eigenvalues
          ((d : ℝ)⁻¹ * activation) ^ r +
        if finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H) ≤ activation
          then 1 else 0 := by
  have h :=
    directStaticChoiTargetNearActionMass_choiVector_le_adaptiveAction_add_carrier
      hd hH.eigenvalues
      (hermitianSpectralEndpoint hH U).2 r δ ((d : ℝ)⁻¹ * activation)
  rw [normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at h
  have hdInv : 0 < (d : ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast hd)
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
