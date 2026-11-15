import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.DiagonalCharacterWeightDescent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Nilpotence in a simple diagonal spectrum

An operator commuting with a diagonal operator with distinct eigenvalues
preserves every one-dimensional eigenspace. If it is nilpotent, its
scalar on each eigenspace vanishes, so the operator is zero.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- A commuting linear operator preserves each line in a simple diagonal spectrum. -/
theorem diagonal_commuting_basis (B : Module.Basis ι K V) (S T : V →ₗ[K] V)
    (eigenvalue : ι → K) (hinjective : Function.Injective eigenvalue)
    (hS : ∀ i, S (B i) = eigenvalue i • B i) (hcomm : ∀ v, S (T v) = T (S v)) (i : ι) :
    T (B i) = B.repr (T (B i)) i • B i := by
  classical
  have heig : S (T (B i)) = eigenvalue i • T (B i) := by rw [hcomm, hS, map_smul]
  apply B.repr.injective
  ext j
  by_cases hji : j = i
  · subst j
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_true, smul_eq_mul, mul_one]
  · have hzero := diagonal_eigenvector_coefficient_zero B S eigenvalue hS (T (B i))
      (eigenvalue i) heig j (fun h => hji (hinjective h))
    rw [hzero]
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, if_neg (Ne.symm hji), smul_zero]

/-- A nilpotent linear operator commuting with a simple diagonal spectrum is zero. -/
theorem diagonal_commuting_nilpotent_eq_zero (B : Module.Basis ι K V) (S T : V →ₗ[K] V)
    (eigenvalue : ι → K) (hinjective : Function.Injective eigenvalue)
    (hS : ∀ i, S (B i) = eigenvalue i • B i) (hcomm : ∀ v, S (T v) = T (S v))
    (n : ℕ) (hn : ∀ v, (T : V → V)^[n] v = 0) : T = 0 := by
  apply B.ext
  intro i
  let a := B.repr (T (B i)) i
  have hdiag : T (B i) = a • B i := diagonal_commuting_basis B S T eigenvalue hinjective hS hcomm i
  have hpow (k : ℕ) : (T : V → V)^[k] (B i) = a ^ k • B i := by
    induction k with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, hdiag, smul_smul, ← pow_succ]
  have hz : a ^ n • B i = 0 := (hpow n).symm.trans (hn (B i))
  have ha : a = 0 := eq_zero_of_pow_eq_zero ((smul_eq_zero.mp hz).resolve_right (B.ne_zero i))
  change T (B i) = 0
  rw [hdiag, ha, zero_smul]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
