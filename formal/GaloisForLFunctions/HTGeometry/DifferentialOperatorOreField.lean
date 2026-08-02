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


open OreLocalization in
/-- Nonzero operators are left regular. -/
theorem nonZeroDivisors_le_left : (DiffOp K)⁰ ≤ nonZeroDivisorsLeft (DiffOp K) := by
  intro s hs
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  intro y hy
  exact (mul_eq_zero.mp hy).resolve_left hs0

open OreLocalization in
theorem numeratorRingHom_injective :
    Function.Injective (numeratorRingHom : DiffOp K → PseudoDiffOp K) :=
  OreLocalization.numeratorHom_inj nonZeroDivisors_le_left

open OreLocalization in
/-- A finite family of rational pseudodifferential operators has a common left denominator. -/
theorem exists_common_denominator {ι : Type*} (x : ι → PseudoDiffOp K) (t : Finset ι) :
    ∃ d : DiffOp K, d ≠ 0 ∧ ∀ i ∈ t, ∃ y : DiffOp K,
      (numeratorRingHom d : PseudoDiffOp K) * x i = numeratorRingHom y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a t ha ih =>
    obtain ⟨d, hd, hclear⟩ := ih
    obtain ⟨r, s, hxa⟩ : ∃ (r : DiffOp K) (s : (DiffOp K)⁰), x a = r /ₒ s :=
      OreLocalization.ind (fun r s => ⟨r, s, rfl⟩) (x a)
    obtain ⟨r', s', hs', hore⟩ := exists_ore_left_multiple d (s : DiffOp K)
      (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
    refine ⟨s' * d, mul_ne_zero' hs' hd, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hit
    · refine ⟨r' * r, ?_⟩
      rw [hxa, hore]
      show ((r' * (s : DiffOp K)) /ₒ 1) * (r /ₒ s) = (r' * r) /ₒ 1
      exact OreLocalization.mul_cancel'
    · obtain ⟨y, hy⟩ := hclear i hit
      exact ⟨s' * y, by rw [map_mul, mul_assoc, hy, ← map_mul]⟩

section RowIndependence

open OreLocalization

variable {ι ι' : Type*} [Fintype ι']

/-- The image of an operator matrix in the skew field of fractions. -/
def toPseudoMatrix (P : ι' → ι → DiffOp K) : ι' → ι → PseudoDiffOp K :=
  fun i j => numeratorRingHom (P i j)

/-- **Row independence over the skew field.**  Rows that are left independent over the operator
ring stay independent over the rational pseudodifferential operators: a rational relation is
cleared by a common denominator. -/
theorem rowIndep_toPseudoMatrix (P : ι' → ι → DiffOp K) (hP : RowIndep P)
    (v : ι' → PseudoDiffOp K) (hv : ∀ j, ∑ i, v i * toPseudoMatrix P i j = 0) : v = 0 := by
  classical
  obtain ⟨d, hd, hclear⟩ := exists_common_denominator v Finset.univ
  choose y hy using fun i => hclear i (Finset.mem_univ i)
  have hyzero : (fun i => y i) = 0 := by
    refine hP (fun i => y i) ?_
    funext j
    have hsum : ∑ i, (numeratorRingHom (y i) : PseudoDiffOp K) * toPseudoMatrix P i j = 0 := by
      have hmul := congrArg (fun z : PseudoDiffOp K => (numeratorRingHom d : PseudoDiffOp K) * z)
        (hv j)
      rw [Finset.mul_sum, mul_zero] at hmul
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hmul
      rw [← hy i, mul_assoc]
    have hnum : (numeratorRingHom (∑ i, y i * P i j) : PseudoDiffOp K) = numeratorRingHom 0 := by
      rw [map_sum, map_zero]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
      rw [map_mul]
      rfl
    have := numeratorRingHom_injective hnum
    show DiffOp.vecMul (fun i => y i) P j = 0
    rw [DiffOp.vecMul, this]
  funext i
  have hyi : y i = 0 := congrFun hyzero i
  have hdv : (numeratorRingHom d : PseudoDiffOp K) * v i = 0 := by
    rw [hy i, hyi, map_zero]
  have hdne : (numeratorRingHom d : PseudoDiffOp K) ≠ 0 := by
    intro hzero
    exact hd (numeratorRingHom_injective (by rw [hzero, map_zero]))
  have := (mul_eq_zero.mp hdv).resolve_left hdne
  simpa using this


/-- The row map `v ↦ v · P` over the skew field of rational pseudodifferential operators. -/
def pseudoVecMul (P : ι' → ι → DiffOp K) (v : ι' → PseudoDiffOp K) : ι → PseudoDiffOp K :=
  fun j => ∑ i, v i * toPseudoMatrix P i j

theorem pseudoVecMul_sub (P : ι' → ι → DiffOp K) (v w : ι' → PseudoDiffOp K) :
    pseudoVecMul P (v - w) = pseudoVecMul P v - pseudoVecMul P w := by
  funext j
  simp only [pseudoVecMul, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- **Injectivity of the row map over the skew field.** -/
theorem pseudoVecMul_injective (P : ι' → ι → DiffOp K) (hP : RowIndep P) :
    Function.Injective (pseudoVecMul P) := by
  intro v w hvw
  have hzero : pseudoVecMul P (v - w) = 0 := by
    rw [pseudoVecMul_sub, hvw, sub_self]
  have hv := rowIndep_toPseudoMatrix P hP (v - w) fun j => congrFun hzero j
  have := sub_eq_zero.mp hv
  exact this

end RowIndependence

end

end DiffOp

end GaloisForLFunctions.HTGeometry
