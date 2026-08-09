import GaloisForLFunctions.HTGeometry.TwoReplicaLocalSingletSynchronization

/-!
# The single edge commutator on the local identity/swap basis

One fixed-orientation weight-two collective commutator annihilates both endpoint-matched swap words
and sends each mismatched word to a product of replica differences.  The computation is the swap
relations `F σ_a ⊗ I = I ⊗ σ_a F` applied once at each endpoint; no spectral input is used.

These are the four values a resolved edge-incidence argument reads off: the kernel is exactly the
matched sector, and the two mismatched outputs are visibly nonzero difference operators.
-/

open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The replica difference `σ_a ⊗ I - I ⊗ σ_a` at one site. -/
def twoReplicaLocalDiff (a : Fin 3) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  twoReplicaPauliLeft a - twoReplicaPauliRight a

theorem twoReplicaLocalDiff_mul_swap (a : Fin 3) :
    twoReplicaLocalDiff a * twoReplicaSwap =
      -(twoReplicaSwap * twoReplicaLocalDiff a) := by
  rw [twoReplicaLocalDiff, Matrix.sub_mul, Matrix.mul_sub,
    ← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_left a]
  module

/-- The matched word `I ⊗ I` is annihilated. -/
theorem twoReplicaEdgeCommutator_one_one (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ
          (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) = 0 := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = 0
  rw [Matrix.one_kronecker_one, Matrix.mul_one, Matrix.one_mul, sub_self]

/-- The matched word `F ⊗ F` is annihilated. -/
theorem twoReplicaEdgeCommutator_swap_swap (a b : Fin 3) :
    twoReplicaEdgeCommutator a b (twoReplicaSwap ⊗ₖ twoReplicaSwap) = 0 := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = 0
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul]
  rw [← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_right b,
    ← twoReplicaSwap_mul_left a, ← twoReplicaSwap_mul_left b]
  module

/-- The mismatched word `I ⊗ F` goes to a product of replica differences. -/
theorem twoReplicaEdgeCommutator_one_swap (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        ((1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) ⊗ₖ twoReplicaSwap) =
      -(twoReplicaLocalDiff a ⊗ₖ (twoReplicaSwap * twoReplicaLocalDiff b)) := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = _
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← twoReplicaSwap_mul_right b, ← twoReplicaSwap_mul_left b,
    twoReplicaLocalDiff, twoReplicaLocalDiff, Matrix.mul_sub]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.neg_apply]
  ring

/-- The mismatched word `F ⊗ I` goes to a product of replica differences. -/
theorem twoReplicaEdgeCommutator_swap_one (a b : Fin 3) :
    twoReplicaEdgeCommutator a b
        (twoReplicaSwap ⊗ₖ (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) =
      -((twoReplicaSwap * twoReplicaLocalDiff a) ⊗ₖ twoReplicaLocalDiff b) := by
  show twoReplicaEdgeCollective a b * _ - _ * twoReplicaEdgeCollective a b = _
  rw [twoReplicaEdgeCollective, Matrix.add_mul, Matrix.mul_add]
  simp only [twoReplicaKronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← twoReplicaSwap_mul_right a, ← twoReplicaSwap_mul_left a,
    twoReplicaLocalDiff, twoReplicaLocalDiff, Matrix.mul_sub]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.neg_apply]
  ring

end

end GaloisForLFunctions.HTGeometry
