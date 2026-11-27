import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier
import Mathlib.RepresentationTheory.Basic

/-! Finite Fourier projections split invariant subspaces under the
translation action of a column of a matrix over a finite residue ring. -/

noncomputable section
open scoped BigOperators Classical

namespace GlobalTheory.GLq

open RHTower.Sieve

/-- An invariant subspace containing a nonzero vector contains a nonzero
weight vector for some frequency of the column translation group. -/
theorem exists_column_weight {g k : ℕ} [NeZero g] {G V : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (C : Multiplicative (Fin k → ZMod g) →* G) (S : Submodule ℂ V)
    (hS : ∀ a w, w ∈ S → ρ (C (Multiplicative.ofAdd a)) w ∈ S)
    (v : V) (hv : v ≠ 0) (hvs : v ∈ S) :
    ∃ (ξ : Fin k → ZMod g) (w : V), w ≠ 0 ∧ w ∈ S ∧
      ∀ a, ρ (C (Multiplicative.ofAdd a)) w = finiteProductCharacter g k ξ a • w := by
  let T (a : Fin k → ZMod g) : Module.End ℂ V := ρ (C (Multiplicative.ofAdd a))
  have hT (a b : Fin k → ZMod g) : T a * T b = T (a + b) :=
    (map_mul (ρ.comp C) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)).symm
  have hT₀ : T 0 = 1 := map_one (ρ.comp C)
  let P (ξ : Fin k → ZMod g) : V :=
    ∑ a : Fin k → ZMod g, finiteProductCharacter g k ξ (-a) • T a v
  have hsum : ∑ ξ, P ξ = ((g : ℂ) ^ k) • v := by
    change (∑ ξ : Fin k → ZMod g, ∑ a : Fin k → ZMod g,
      finiteProductCharacter g k ξ (-a) • T a v) = _
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, sum_finiteProductCharacter, neg_eq_zero]
    refine (Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0) (fun a _ ha => ?_)).trans ?_
    · rw [if_neg ha, zero_smul]
    · rw [if_pos rfl, hT₀]
      rfl
  have hq : (g : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne g))
  have hP : ∃ ξ, P ξ ≠ 0 := by
    by_contra! hall
    exact (smul_ne_zero hq hv) (hsum.symm.trans (Finset.sum_eq_zero fun ξ _ => hall ξ))
  obtain ⟨ξ, hξ⟩ := hP
  refine ⟨ξ, P ξ, hξ, S.sum_mem (fun a _ => S.smul_mem _ (hS a v hvs)), fun a => ?_⟩
  change T a (P ξ) = _
  calc
    T a (P ξ) =
        ∑ b : Fin k → ZMod g, finiteProductCharacter g k ξ (-b) • T (a + b) v := by
      simp only [P, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul]
      exact congrArg (fun L : Module.End ℂ V => finiteProductCharacter g k ξ (-b) • L v) (hT a b)
    _ = ∑ b : Fin k → ZMod g, finiteProductCharacter g k ξ a •
          (finiteProductCharacter g k ξ (-(a + b)) • T (a + b) v) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, ← finiteProductCharacter_add]
      rw [show a + -(a + b) = -b by abel]
    _ = _ := by
      simp only [P, Finset.smul_sum]
      exact Equiv.sum_comp (Equiv.addLeft a)
        (fun b => finiteProductCharacter g k ξ a • (finiteProductCharacter g k ξ (-b) • T b v))

end GlobalTheory.GLq
