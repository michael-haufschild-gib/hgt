import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.LinearAlgebra.Basis.Defs


/-!
# Character projectors from primitive roots

Summing powers of a nontrivial root of unity gives zero. For a diagonal
cyclic action this orthogonality extracts a chosen basis coordinate,
multiplied by the order of the group.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset

/-- Orthogonality of distinct powers of a primitive root over an arbitrary field. -/
theorem primitiveRoot_ratio_sum {F : Type*} [Field F] {N : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ N) (i j : Fin N) :
    ∑ k ∈ Finset.range N, (ζ ^ j.val / ζ ^ i.val) ^ k = if i = j then (N : F) else 0 := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Nat.ne_zero_of_lt i.isLt)
  by_cases hij : i = j
  · subst j
    simp only [div_self (pow_ne_zero _ hζ0), one_pow, sum_const, card_range, nsmul_eq_mul,
      mul_one, if_true]
  · have hratio : ζ ^ j.val / ζ ^ i.val ≠ 1 := by
      intro h
      have hp : ζ ^ j.val = ζ ^ i.val := (div_eq_one_iff_eq (pow_ne_zero _ hζ0)).mp h
      exact hij (Fin.ext (hζ.pow_inj j.isLt i.isLt hp).symm)
    have hpow : (ζ ^ j.val / ζ ^ i.val) ^ N = 1 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm j.val N, pow_mul, hζ.pow_eq_one, one_pow,
        ← pow_mul, Nat.mul_comm i.val N, pow_mul, hζ.pow_eq_one, one_pow, div_self one_ne_zero]
    rw [geom_sum_eq hratio, hpow, sub_self, zero_div, if_neg hij]

/-- Averaging a diagonal cyclic action against one inverse character extracts exactly one basis coordinate. -/
theorem diagonal_primitiveRoot_projection
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {N : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ N)
    (b : Module.Basis (Fin N) F V) (σ : ℕ → V →ₗ[F] V)
    (heigen : ∀ k j, σ k (b j) = ζ ^ (k * j.val) • b j) (x : V) (i : Fin N) :
    ∑ k ∈ Finset.range N, (ζ ^ (k * i.val))⁻¹ • σ k x =
      (N : F) • (b.repr x i • b i) := by
  classical
  have hσ (k : ℕ) : σ k x = ∑ j : Fin N, (b.repr x j * ζ ^ (k * j.val)) • b j := by
    calc
      σ k x = σ k (∑ j : Fin N, b.repr x j • b j) := congrArg (σ k) (b.sum_repr x).symm
      _ = _ := by simp only [map_sum, map_smul, heigen, smul_smul]
  simp_rw [hσ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoef (j : Fin N) :
      ∑ k ∈ Finset.range N, (ζ ^ (k * i.val))⁻¹ * (b.repr x j * ζ ^ (k * j.val)) =
        b.repr x j * (if i = j then (N : F) else 0) := by
    rw [← primitiveRoot_ratio_sum hζ i j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_pow, ← pow_mul, Nat.mul_comm j.val k, ← pow_mul, Nat.mul_comm i.val k]
    ring
  simp_rw [← Finset.sum_smul, hcoef]
  simp only [mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [mul_comm]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
