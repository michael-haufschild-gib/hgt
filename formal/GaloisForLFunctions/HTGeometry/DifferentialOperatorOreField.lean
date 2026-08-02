import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMatrix
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.OreLocalization.NonZeroDivisors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The skew field of rational pseudodifferential operators

The ring `K[∂;δ]` of linear differential operators over a differential field satisfies the Ore
condition: any two nonzero operators have a nonzero common left multiple.  The proof is the
classical dimension count.  Operators of order at most `n` form a `K`-space of dimension `n+1`, so
for `n` at least the maximum of the two orders the two spaces `{x r}` and `{y s}` of products both
sit inside operators of order at most `n + max`, whose dimension `n + max + 1` is smaller than
`2(n+1)`; a nonzero element of the kernel of the difference map gives the required relation.

Consequently the operator ring has a skew field of fractions, the rational pseudodifferential
operators.
-/

open scoped Differential
open nonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- The operator with prescribed coefficients up to order `m`. -/
def truncOp {m : ℕ} (c : Fin (m + 1) → K) : DiffOp K := ∑ i : Fin (m + 1), mono (i : ℕ) (c i)

theorem coeff_truncOp {m : ℕ} (c : Fin (m + 1) → K) (i : Fin (m + 1)) :
    coeff (truncOp c) (i : ℕ) = c i := by
  classical
  rw [truncOp, ← coeffAddHom_apply (i : ℕ), map_sum]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    rw [coeffAddHom_apply, coeff_mono_of_ne]
    intro hcon
    exact hji (Fin.ext hcon)
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon
  · rw [coeffAddHom_apply, coeff_mono_self]

theorem degree_truncOp_le {m : ℕ} (c : Fin (m + 1) → K) : degree (truncOp c) ≤ m := by
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun i _ => ?_)
  exact le_trans (degree_mono_le (i : ℕ) (c i)) (Nat.lt_succ_iff.mp i.2)

theorem truncOp_injective {m : ℕ} : Function.Injective (truncOp (K := K) (m := m)) := by
  intro c d hcd
  funext i
  rw [← coeff_truncOp c i, ← coeff_truncOp d i, hcd]

/-- Truncated operators, as a linear map. -/
def truncOpLin (m : ℕ) : (Fin (m + 1) → K) →ₗ[K] DiffOp K where
  toFun := truncOp
  map_add' c d := by
    rw [truncOp, truncOp, truncOp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, mono_add]
  map_smul' a c := by
    rw [RingHom.id_apply, truncOp, truncOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, smul_mono]

@[simp] theorem truncOpLin_apply (m : ℕ) (c : Fin (m + 1) → K) : truncOpLin m c = truncOp c := rfl

/-- The difference map whose kernel produces a common left multiple. -/
def oreDifference (r s : DiffOp K) (n N : ℕ) :
    ((Fin (n + 1) → K) × (Fin (n + 1) → K)) →ₗ[K] (Fin (n + N + 1) → K) where
  toFun cd := fun j => coeff (truncOp cd.1 * r - truncOp cd.2 * s) (j : ℕ)
  map_add' cd cd' := by
    funext j
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← truncOpLin_apply n, ← truncOpLin_apply n, map_add, map_add, truncOpLin_apply,
      truncOpLin_apply, truncOpLin_apply, truncOpLin_apply, add_mul', add_mul']
    rw [show truncOp cd.1 * r + truncOp cd'.1 * r - (truncOp cd.2 * s + truncOp cd'.2 * s)
        = (truncOp cd.1 * r - truncOp cd.2 * s) + (truncOp cd'.1 * r - truncOp cd'.2 * s) by abel,
      coeff_add]
  map_smul' a cd := by
    funext j
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [← truncOpLin_apply n, ← truncOpLin_apply n, map_smul, map_smul, truncOpLin_apply,
      truncOpLin_apply, smul_mul', smul_mul', ← smul_sub, coeff_smul]

@[simp] theorem oreDifference_apply (r s : DiffOp K) (n N : ℕ)
    (cd : (Fin (n + 1) → K) × (Fin (n + 1) → K)) (j : Fin (n + N + 1)) :
    oreDifference r s n N cd j = coeff (truncOp cd.1 * r - truncOp cd.2 * s) (j : ℕ) := rfl

/-- **The Ore condition.**  Any operator and any nonzero operator have a common left multiple with
nonzero left factor. -/
theorem exists_ore_left_multiple (r : DiffOp K) (s : DiffOp K) (hs : s ≠ 0) :
    ∃ (r' : DiffOp K) (s' : DiffOp K), s' ≠ 0 ∧ s' * r = r' * s := by
  classical
  by_cases hr : r = 0
  · exact ⟨0, 1, one_ne_zero, by rw [hr, mul_zero', zero_mul']⟩
  set N : ℕ := max (degree r) (degree s) with hN
  have hker : ¬ Function.Injective (oreDifference r s N N) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank K ((Fin (N + 1) → K) × (Fin (N + 1) → K)) = (N + 1) + (N + 1) := by
      simp [Module.finrank_prod]
    have hcod : Module.finrank K (Fin (N + N + 1) → K) = N + N + 1 := by
      simp
    rw [hdom, hcod] at hle
    omega
  obtain ⟨cd, hcd, hne⟩ : ∃ cd, oreDifference r s N N cd = 0 ∧ cd ≠ 0 := by
    by_contra hcon
    refine hker ((injective_iff_map_eq_zero (oreDifference r s N N)).mpr fun a ha => ?_)
    by_contra hane
    exact hcon ⟨a, ha, hane⟩
  -- the operator difference vanishes
  have hdegdiff : degree (truncOp cd.1 * r - truncOp cd.2 * s) ≤ N + N := by
    refine le_trans (degree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (degree_mul_le _ _)
        (Nat.add_le_add (degree_truncOp_le cd.1) (le_max_left _ _))
    · exact le_trans (degree_mul_le _ _)
        (Nat.add_le_add (degree_truncOp_le cd.2) (le_max_right _ _))
  have hzero : truncOp cd.1 * r - truncOp cd.2 * s = 0 := by
    refine eq_zero_iff.mpr fun m => ?_
    by_cases hm : m ≤ N + N
    · have hj := congrFun hcd (⟨m, by omega⟩ : Fin (N + N + 1))
      rw [oreDifference_apply] at hj
      exact hj
    · exact coeff_eq_zero_of_degree_lt (by omega)
  have heq : truncOp cd.1 * r = truncOp cd.2 * s := by
    rw [← sub_eq_zero]
    exact hzero
  have hc1 : truncOp cd.1 ≠ 0 := by
    intro hc
    rw [hc, zero_mul'] at heq
    have hd : truncOp cd.2 = 0 := by
      by_contra hd
      exact (mul_ne_zero' hd hs) heq.symm
    refine hne ?_
    have h1 : cd.1 = 0 := truncOp_injective (by rw [hc]; exact (map_zero (truncOpLin N)).symm)
    have h2 : cd.2 = 0 := truncOp_injective (by rw [hd]; exact (map_zero (truncOpLin N)).symm)
    exact Prod.ext h1 h2
  exact ⟨truncOp cd.2, truncOp cd.1, hc1, heq⟩

instance instOreSet : OreLocalization.OreSet (DiffOp K)⁰ :=
  OreLocalization.oreSetOfNoZeroDivisors
    (fun r s => Classical.choose (exists_ore_left_multiple r s.1
      (mem_nonZeroDivisors_iff_ne_zero.mp s.2)))
    (fun r s =>
      ⟨Classical.choose (Classical.choose_spec (exists_ore_left_multiple r s.1
        (mem_nonZeroDivisors_iff_ne_zero.mp s.2))),
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (Classical.choose_spec (Classical.choose_spec (exists_ore_left_multiple r s.1
            (mem_nonZeroDivisors_iff_ne_zero.mp s.2)))).1⟩)
    (fun r s =>
      (Classical.choose_spec (Classical.choose_spec (exists_ore_left_multiple r s.1
        (mem_nonZeroDivisors_iff_ne_zero.mp s.2)))).2)

/-- The skew field of rational pseudodifferential operators. -/
abbrev PseudoDiffOp (K : Type u) [Field K] [Differential K] : Type u :=
  OreLocalization (DiffOp K)⁰ (DiffOp K)

instance : DivisionRing (PseudoDiffOp K) := inferInstance

end

end DiffOp

end GaloisForLFunctions.HTGeometry
