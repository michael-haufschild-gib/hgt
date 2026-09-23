import GaloisForLFunctions.HTGeometry.HypercubeWalshDiagonalisation
import GaloisForLFunctions.HTGeometry.NearDiagonalOverlapFlatness
import GaloisForLFunctions.HTGeometry.CollisionEnsembleLaw

/-!
# The spectral collision of a strongly transverse hypercube Hamiltonian

In the Walsh frame a transverse-field Hamiltonian `D + ∑_i u_i T_i` is the diagonal of transverse
energies `∑_i ± u_i` plus the rotated diagonal part, and the all-zero product state is the flat
superposition.  `NearDiagonalOverlapFlatness.spectralCollision_le_of_near_diagonal` then bounds the
spectral collision of the all-zero product state by `(2^{-n/2} + 2‖D‖/γ)²`, with `γ` the separation
of the transverse energies.  No perturbation theory of eigenvectors, no Davis–Kahan.

## Main results

* `zeroState`, `walsh_conjTranspose_mulVec_zeroState` — the all-zero state is flat in the Walsh
  frame.
* `spectralCollision_transverseFamilyHam_le` — **the collision bound.**
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

namespace Walsh

set_option linter.unusedSectionVars false

noncomputable section

variable {n : ℕ}

/-- The all-zero computational basis state of the hypercube. -/
def zeroState (n : ℕ) : (Fin n → Bool) → ℂ := Pi.single (fun _ => false) 1

/-- **The all-zero state is flat in the Walsh frame.** -/
theorem walsh_conjTranspose_mulVec_zeroState (n : ℕ) (x : Fin n → Bool) :
    ((walshMatrix n)ᴴ *ᵥ zeroState n) x = ((cubeNorm n : ℝ) : ℂ) := by
  classical
  show ∑ y, (walshMatrix n)ᴴ x y * zeroState n y = ((cubeNorm n : ℝ) : ℂ)
  rw [Finset.sum_eq_single (fun _ => false)]
  · rw [zeroState, Pi.single_eq_same, mul_one, Matrix.conjTranspose_apply,
      walshMatrix_apply, cubeSign_zero_left, mul_one, Complex.star_def, Complex.conj_ofReal]
  · intro b _ hb
    rw [zeroState, Pi.single_eq_of_ne hb, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem finiteComplexInner_walsh_zeroState (n : ℕ) :
    finiteComplexInner ((walshMatrix n)ᴴ *ᵥ zeroState n)
      ((walshMatrix n)ᴴ *ᵥ zeroState n) = 1 := by
  classical
  rw [finiteComplexInner]
  have hterm : ∀ x : Fin n → Bool,
      (starRingEnd ℂ) (((walshMatrix n)ᴴ *ᵥ zeroState n) x) *
        ((walshMatrix n)ᴴ *ᵥ zeroState n) x
        = (((cubeNorm n * cubeNorm n : ℝ)) : ℂ) := by
    intro x
    rw [walsh_conjTranspose_mulVec_zeroState, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
    cubeNorm_sq]
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  rw [hcard, nsmul_eq_mul]
  push_cast
  field_simp

theorem norm_walsh_conjTranspose_mulVec_zeroState (n : ℕ) (x : Fin n → Bool) :
    ‖((walshMatrix n)ᴴ *ᵥ zeroState n) x‖ ≤ cubeNorm n := by
  rw [walsh_conjTranspose_mulVec_zeroState, Complex.norm_real, Real.norm_of_nonneg
    (le_of_lt (cubeNorm_pos n))]

/-- The Walsh frame turns the transverse family into a diagonal plus a rotated diagonal. -/
theorem conj_walsh_transverseFamilyHam (d : (Fin n → Bool) → ℝ) (u : Fin n → ℝ) :
    (walshMatrix n)ᴴ *
        (transverseFamilyHam (fun x => ((d x : ℝ) : ℂ)) (fun i => ((u i : ℝ) : ℂ))) *
        walshMatrix n
      - Matrix.diagonal (fun x => ((transverseEnergy u x : ℝ) : ℂ))
      = (walshMatrix n)ᴴ * Matrix.diagonal (fun x => ((d x : ℝ) : ℂ)) * walshMatrix n := by
  rw [transverseFamilyHam_eq_diagonal_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc (walshMatrix n)ᴴ (transverseOnly (fun i => ((u i : ℝ) : ℂ))),
    transverseOnly_mul_walsh, ← Matrix.mul_assoc, walshMatrix_conjTranspose_mul,
    Matrix.one_mul, add_sub_cancel_right]

theorem norm_conj_walsh_diagonal_le (v : (Fin n → Bool) → ℂ) :
    ‖(walshMatrix n)ᴴ * Matrix.diagonal v * walshMatrix n‖ ≤ ‖v‖ := by
  calc ‖(walshMatrix n)ᴴ * Matrix.diagonal v * walshMatrix n‖
      ≤ ‖(walshMatrix n)ᴴ * Matrix.diagonal v‖ * ‖walshMatrix n‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(walshMatrix n)ᴴ‖ * ‖Matrix.diagonal v‖) * ‖walshMatrix n‖ := by
        exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖v‖ := by
        rw [Matrix.l2_opNorm_conjTranspose, norm_walshMatrix, Matrix.l2_opNorm_diagonal]
        ring

/-- **The collision bound for a strongly transverse hypercube Hamiltonian.**  If the transverse
energies `∑_i ± u_i` are `γ`-separated, the spectral collision of the all-zero product state is at
most `(2^{-n/2} + 2‖d‖/γ)²`. -/
theorem spectralCollision_transverseFamilyHam_le (d : (Fin n → Bool) → ℝ) (u : Fin n → ℝ)
    {gap : ℝ} (hgap : 0 < gap)
    (hsep : ∀ x y : Fin n → Bool, x ≠ y →
      gap ≤ |transverseEnergy u x - transverseEnergy u y|)
    {e : (Fin n → Bool) → (Fin n → Bool) → ℂ} {lam : (Fin n → Bool) → ℝ}
    (heb : IsOrthoEigenBasis
      (transverseFamilyHam (fun x => ((d x : ℝ) : ℂ)) (fun i => ((u i : ℝ) : ℂ))) e lam) :
    spectralCollision e (zeroState n)
      ≤ (cubeNorm n + 2 * ‖fun x => ((d x : ℝ) : ℂ)‖ / gap) ^ (2 : ℕ) := by
  classical
  set H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    transverseFamilyHam (fun x => ((d x : ℝ) : ℂ)) (fun i => ((u i : ℝ) : ℂ)) with hH
  set W : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := walshMatrix n with hW
  set chi : (Fin n → Bool) → ℂ := Wᴴ *ᵥ zeroState n with hchi
  have hebconj : IsOrthoEigenBasis (Wᴴ * H * W) (fun j => Wᴴ *ᵥ e j) lam :=
    isOrthoEigenBasis_conj heb (walshMatrix_conjTranspose_mul n) (walshMatrix_mul_conjTranspose n)
  have hnear : ‖Wᴴ * H * W - Matrix.diagonal (fun x => ((transverseEnergy u x : ℝ) : ℂ))‖
      ≤ ‖fun x => ((d x : ℝ) : ℂ)‖ := by
    rw [hH, hW, conj_walsh_transverseFamilyHam]
    exact norm_conj_walsh_diagonal_le _
  have hsep' : ∀ k l : Fin n → Bool, k ≠ l →
      gap ≤ |transverseEnergy u k - transverseEnergy u l| := hsep
  have hchiunit : ‖eucVec chi‖ = 1 :=
    norm_eucVec_eq_one (finiteComplexInner_walsh_zeroState n)
  have hbound := spectralCollision_le_of_near_diagonal (En := transverseEnergy u) (gap := gap)
    hgap hsep' (delta := ‖fun x => ((d x : ℝ) : ℂ)‖) (norm_nonneg _) hnear hebconj
    (c := cubeNorm n) (le_of_lt (cubeNorm_pos n))
    (norm_walsh_conjTranspose_mulVec_zeroState n) hchiunit
  have htrans : spectralCollision (fun j => Wᴴ *ᵥ e j) chi = spectralCollision e (zeroState n) := by
    rw [spectralCollision_conjTranspose_mulVec W e chi, hchi, Matrix.mulVec_mulVec,
      walshMatrix_mul_conjTranspose, Matrix.one_mulVec]
  rw [htrans] at hbound
  exact hbound

end

end Walsh

end GaloisForLFunctions.HTGeometry
