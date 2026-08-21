import GaloisForLFunctions.HTGeometry.GroupCharacter.Character
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The eigenvalue multiset of a group element acting on a `G`-stable subspace

`exists_eigen_multiset` produces, for each `g : G`, a multiset of `#G`-th roots of unity of
cardinality `finrank ℂ N` whose sum is `chi hN g`.  This is the source of both the bound
`‖chi hN g‖ ≤ finrank ℂ N` and the integrality of `chi hN g`.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
theorem rho_pow {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) (k : ℕ) :
    rho hN (g ^ k) = (rho hN g) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, rho_one]; rfl
  | succ k ih => rw [pow_succ, rho_mul, ih, pow_succ]; rfl

/-- The characters of a `G`-stable subspace are sums of `#G`-th roots of unity. -/
theorem exists_eigen_multiset {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    ∃ E : Multiset ℂ, E.card = Module.finrank ℂ ↥N ∧
      (∀ μ ∈ E, μ ^ (Fintype.card G) = 1) ∧ E.sum = chi hN g := by
  classical
  set d := Module.finrank ℂ ↥N with hd
  set b := Module.finBasis ℂ ↥N with hb
  set A : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (rho hN g) with hA
  have hApow : A ^ (Fintype.card G) = 1 := by
    rw [hA, LinearMap.toMatrix_pow, ← rho_pow, pow_card_eq_one, rho_one]
    simp
  refine ⟨A.charpoly.roots, ?_, ?_, ?_⟩
  · rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro μ hμ
    have hne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
    have hroot : A.charpoly.eval μ = 0 := (Polynomial.mem_roots hne).mp hμ
    rw [Matrix.eval_charpoly] at hroot
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
    have hAv : A.mulVec v = μ • v := by
      have : ((Matrix.scalar (Fin d)) μ - A).mulVec v = 0 := hv
      rw [Matrix.sub_mulVec, sub_eq_zero] at this
      rw [← this]
      simp [Matrix.scalar_apply]
    have hpow : ∀ k : ℕ, (A ^ k).mulVec v = (μ ^ k) • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have hfin := hpow (Fintype.card G)
    rw [hApow] at hfin
    simp only [Matrix.one_mulVec] at hfin
    have : (μ ^ (Fintype.card G) - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hfin, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  · rw [chi, LinearMap.trace_eq_matrix_trace ℂ b, ← hA, Matrix.trace_eq_sum_roots_charpoly]

end GaloisForLFunctions.HTGeometry.GroupCharacter
