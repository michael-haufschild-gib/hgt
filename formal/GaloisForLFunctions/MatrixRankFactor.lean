import Mathlib

/-!
# Rank factorization of a complex matrix

Every `M : Matrix A V ℂ` factors as `M = U · a` with inner dimension `M.rank`: choosing a basis
`b` of the column span (dimension `M.rank`), the factor `U` is the basis (columns) and `a` is the
coordinate map of the columns of `M` in that basis.  The basis columns are `ℂ`-linearly independent,
so the kernel of `a` equals the kernel of `M`.
-/

namespace GaloisForLFunctions

open scoped Matrix
open Module

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- **Rank factorization.**  `M = U · a` with inner dimension `M.rank`. -/
theorem rank_factor (M : Matrix A V ℂ) :
    ∃ (a : V → Fin M.rank → ℂ) (U : A → Fin M.rank → ℂ),
      (∀ B v, M B v = ∑ i, U B i * a v i) ∧
      LinearIndependent ℂ (fun i : Fin M.rank => (fun B => U B i : A → ℂ)) := by
  set S := Submodule.span ℂ (Set.range (fun v => (fun B => M B v : A → ℂ))) with hS
  have hcol : ∀ v, (fun B => M B v : A → ℂ) ∈ S := fun v => Submodule.subset_span ⟨v, rfl⟩
  have hdim : finrank ℂ S = M.rank := by rw [Matrix.rank_eq_finrank_span_cols]; congr 1
  set b : Basis (Fin M.rank) ℂ S := finBasisOfFinrankEq ℂ S hdim with hb
  refine ⟨fun v i => b.repr ⟨_, hcol v⟩ i, fun B i => (b i : A → ℂ) B, ?_, ?_⟩
  · intro B v
    have hrep : (⟨(fun B => M B v : A → ℂ), hcol v⟩ : S)
        = ∑ i, (b.repr ⟨_, hcol v⟩ i) • b i := (b.sum_repr _).symm
    have hval := congrArg (fun x : S => (x : A → ℂ) B) hrep
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hval
    rw [hval]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have hbli := b.linearIndependent
    have hcomp : (fun i : Fin M.rank => (fun B => (b i : A → ℂ) B))
        = (Submodule.subtype S) ∘ b := by
      funext i; rfl
    rw [hcomp]
    exact hbli.map' (Submodule.subtype S) (Submodule.ker_subtype S)

/-- **Rational-kernel bridge.**  For a factored entrywise product `N B v = ∑ i, U B i · a v i`
with the `U`-columns `ℂ`-linearly independent, the rational kernel of `N` equals the rational
kernel of the coordinate map `a`. -/
theorem qkernel_bridge {r : ℕ} (a : V → Fin r → ℂ) (U : A → Fin r → ℂ)
    (hU : LinearIndependent ℂ (fun i : Fin r => (fun B => U B i : A → ℂ)))
    (q : V → ℚ) :
    (∀ B, ∑ v, (q v : ℂ) * (∑ i, U B i * a v i) = 0) ↔ (∀ i, ∑ v, (q v : ℂ) * a v i = 0) := by
  have hrearr : ∀ B, ∑ v, (q v : ℂ) * (∑ i, U B i * a v i)
      = ∑ i, (∑ v, (q v : ℂ) * a v i) * U B i := by
    intro B
    rw [Finset.sum_congr rfl (fun v _ => by rw [Finset.mul_sum])]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro v _; ring
  constructor
  · intro hN
    have hfun : (∑ i, (∑ v, (q v : ℂ) * a v i) • (fun B => U B i : A → ℂ)) = 0 := by
      funext B
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hrearr B, hN B]
    exact fun i => Fintype.linearIndependent_iff.mp hU _ hfun i
  · intro ha B
    rw [hrearr B]
    exact Finset.sum_eq_zero fun i _ => by rw [ha i, zero_mul]

end GaloisForLFunctions
