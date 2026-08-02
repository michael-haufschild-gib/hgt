import GaloisForLFunctions.HTGeometry.SimpleSpectrumRankBridge
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Commuting Hermitian perturbations of prescribed temporal dimension

Transporting a perturbed spectrum back through the eigenbasis of a Hermitian matrix produces a
Hermitian matrix which commutes with it, is as close to it as the spectra are, and has the
perturbed spectrum.  Combined with the arithmetic perturbation of spectra, every Hermitian matrix
has commuting Hermitian matrices arbitrarily close to it, with simple spectrum and completed
observer time of any prescribed dimension.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Conjugating a real diagonal matrix by a unitary gives a Hermitian matrix. -/
theorem isHermitian_unitary_conj_diagonal
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (c : Fin (n + 1) → ℝ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) U)
      (Matrix.diagonal (RCLike.ofReal ∘ c))).IsHermitian := by
  have hD : IsSelfAdjoint
      (Matrix.diagonal (RCLike.ofReal ∘ c) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
    show star ((RCLike.ofReal (c i) : ℂ)) = RCLike.ofReal (c i)
    rw [RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  exact hD.map (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) U)

/-- Unitary conjugation is isometric for the operator norm. -/
theorem l2_opNorm_unitary_conj (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ‖(Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) U) X‖ ≤ ‖X‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    with hV
  have hU : ‖V‖ = 1 := CStarRing.norm_coe_unitary U
  have hUstar : ‖star V‖ = 1 := by
    rw [norm_star]
    exact hU
  calc ‖V * X * star V‖ ≤ ‖V * X‖ * ‖star V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖V‖ * ‖X‖ * ‖star V‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖X‖ := by rw [hU, hUstar]; ring

/-- **Commuting Hermitian perturbation with prescribed temporal dimension.**  Every Hermitian
matrix has, in every operator-norm neighbourhood, a commuting Hermitian matrix with simple spectrum
whose completed observer time has any prescribed positive dimension not exceeding the number of
gaps. -/
theorem exists_isHermitian_commuting_close_gapRank {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧ ‖B - A‖ < ε ∧
        B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hA.eigenvectorUnitary)
              (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
        rationalCoordinateRank (fun j : Fin n => E' j.succ - E' 0) = k := by
  obtain ⟨E', hinj, hclose, hrank⟩ :=
    exists_simpleSpectrum_close_gapRank hk hkn hA.eigenvalues hε
  set f := Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hA.eigenvectorUnitary
    with hf
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  set D' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ E') with hD'
  have hAeq : A = f D := hA.spectral_theorem
  refine ⟨f D', E', isHermitian_unitary_conj_diagonal _ E', ?_, hinj, ?_, rfl, hrank⟩
  · have hcomm : D' * D = D * D' := by
      rw [hD, hD', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      refine congrArg Matrix.diagonal ?_
      funext i
      exact mul_comm _ _
    calc f D' * A = f D' * f D := by rw [hAeq]
      _ = f (D' * D) := (map_mul f D' D).symm
      _ = f (D * D') := by rw [hcomm]
      _ = f D * f D' := map_mul f D D'
      _ = A * f D' := by rw [hAeq]
  · have hsub : f D' - A = f (D' - D) := by
      rw [hAeq, map_sub]
    have hdiag : D' - D = Matrix.diagonal (fun i => (RCLike.ofReal (E' i - hA.eigenvalues i) : ℂ)) := by
      rw [hD, hD']
      ext i j
      rw [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp [RCLike.ofReal_sub]
      · simp [hij]
    have hnorm : ‖D' - D‖ < ε := by
      rw [hdiag, Matrix.l2_opNorm_diagonal]
      refine (pi_norm_lt_iff hε).mpr fun i => ?_
      have hd := hclose i
      rw [Real.dist_eq] at hd
      calc ‖((E' i - hA.eigenvalues i : ℝ) : ℂ)‖ = |E' i - hA.eigenvalues i| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
        _ < ε := hd
    calc ‖f D' - A‖ = ‖f (D' - D)‖ := by rw [hsub]
      _ ≤ ‖D' - D‖ := l2_opNorm_unitary_conj _ _
      _ < ε := hnorm

end

end GaloisForLFunctions.HTGeometry
