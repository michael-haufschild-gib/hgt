import GaloisForLFunctions.RHTower.Sieve.MaynardGreedyGroupSelection
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicGreedyGroup

/-!
# Exact excision of sub-threshold factors

If a product is large and every discarded factor is bounded by its own
multiplicative threshold, the retained product is large at the same threshold.
For dyadic factors this lets us discard long, individually sub-threshold atoms
before applying the robust greedy grouping lemma to the short factors.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

theorem rpow_product_le_product_on_subset_of_complement_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A v : ι → ℝ) (e : ℝ) (u : Finset ι)
    (hA : ∀ i, 0 < A i) (hv : ∀ i, 0 ≤ v i)
    (hlarge : (∏ i, A i) ^ e ≤ ∏ i, v i)
    (hcomp : ∀ i ∉ u, v i ≤ A i ^ e) :
    (∏ i ∈ u, A i) ^ e ≤ ∏ i ∈ u, v i := by
  let uc : Finset ι := Finset.univ \ u
  have hu_sub : u ⊆ (Finset.univ : Finset ι) := Finset.subset_univ u
  have hsplitA : (∏ i, A i) = (∏ i ∈ u, A i) * (∏ i ∈ uc, A i) := by
    have h := Finset.prod_sdiff (f := A) hu_sub
    simpa [uc, mul_comm] using h.symm
  have hsplitv : (∏ i, v i) = (∏ i ∈ u, v i) * (∏ i ∈ uc, v i) := by
    have h := Finset.prod_sdiff (f := v) hu_sub
    simpa [uc, mul_comm] using h.symm
  have hAu : 0 < ∏ i ∈ u, A i := Finset.prod_pos fun i _ => hA i
  have hAuc : 0 < ∏ i ∈ uc, A i := Finset.prod_pos fun i _ => hA i
  have hvu : 0 ≤ ∏ i ∈ u, v i := Finset.prod_nonneg fun i _ => hv i
  have hvuc : ∏ i ∈ uc, v i ≤ ∏ i ∈ uc, A i ^ e := by
    apply Finset.prod_le_prod
    · intro i hi
      exact hv i
    · intro i hi
      apply hcomp i
      simpa [uc] using hi
  have hrpowu : ∏ i ∈ u, A i ^ e = (∏ i ∈ u, A i) ^ e :=
    Real.finsetProd_rpow u A (fun i _ => (hA i).le) e
  have hrpowuc : ∏ i ∈ uc, A i ^ e = (∏ i ∈ uc, A i) ^ e :=
    Real.finsetProd_rpow uc A (fun i _ => (hA i).le) e
  rw [hrpowuc] at hvuc
  have hglobal : (∏ i ∈ u, A i) ^ e * (∏ i ∈ uc, A i) ^ e ≤
      (∏ i ∈ u, v i) * (∏ i ∈ uc, v i) := by
    rw [← Real.mul_rpow (hAu.le) (hAuc.le), ← hsplitA, ← hsplitv]
    exact hlarge
  have hcancel : (∏ i ∈ u, A i) ^ e * (∏ i ∈ uc, A i) ^ e ≤
      (∏ i ∈ u, v i) * (∏ i ∈ uc, A i) ^ e :=
    hglobal.trans (mul_le_mul_of_nonneg_left hvuc hvu)
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hAuc e)).mp
  simpa [mul_comm] using hcancel

theorem norm_product_subset_large_of_complement_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℝ) (z : ι → ℂ) (e : ℝ) (u : Finset ι)
    (hA : ∀ i, 0 < A i)
    (hlarge : (∏ i, A i) ^ e ≤ ‖∏ i, z i‖)
    (hcomp : ∀ i ∉ u, ‖z i‖ ≤ A i ^ e) :
    (∏ i ∈ u, A i) ^ e ≤ ‖∏ i ∈ u, z i‖ := by
  have h := rpow_product_le_product_on_subset_of_complement_le
    A (fun i => ‖z i‖) e u hA (fun i => norm_nonneg _) ?_ hcomp
  · simpa [Complex.norm_prod] using h
  · simpa [Complex.norm_prod] using hlarge

def shortDyadicFactorSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T0 t : ℝ) (q : ι → ℕ) : Finset ι :=
  Finset.univ.filter fun i => dyadicLogExponent T0 (q i) ≤ 2 * t

@[simp] theorem mem_shortDyadicFactorSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T0 t : ℝ} {q : ι → ℕ} {i : ι} :
    i ∈ shortDyadicFactorSet T0 t q ↔
      dyadicLogExponent T0 (q i) ≤ 2 * t := by
  simp [shortDyadicFactorSet]

theorem exists_dyadic_robust_greedy_large_group_after_excision
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (z : ι → ℂ) {T0 t e : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t)
    (hlarge : (groupedDyadicLower q : ℝ) ^ e ≤ ‖∏ i, z i‖)
    (hlongUpper : ∀ i,
      2 * t < dyadicLogExponent T0 (q i) →
        ‖z i‖ ≤ (((2 ^ q i : ℕ) : ℝ)) ^ e)
    (htotalShort : t ≤ ∑ i ∈ shortDyadicFactorSet T0 t q,
      dyadicLogExponent T0 (q i)) :
    ∃ u : Finset ι, u.Nonempty ∧ u ⊆ shortDyadicFactorSet T0 t q ∧
      let alpha := ∑ i ∈ u, dyadicLogExponent T0 (q i)
      t ≤ alpha ∧ alpha < 4 * t ∧ u.card ≤ Fintype.card ι ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) =
          T0 ^ alpha ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, z i‖ := by
  let short := shortDyadicFactorSet T0 t q
  have hsubsetLarge : (∏ i ∈ short, (((2 ^ q i : ℕ) : ℝ))) ^ e ≤
      ‖∏ i ∈ short, z i‖ := by
    apply norm_product_subset_large_of_complement_le
      (fun i => (((2 ^ q i : ℕ) : ℝ))) z e short (fun i => by positivity)
    · simpa [groupedDyadicLower, Complex.norm_prod] using hlarge
    · intro i hi
      apply hlongUpper i
      have hnot : ¬ dyadicLogExponent T0 (q i) ≤ 2 * t := by
        simpa [short] using hi
      exact lt_of_not_ge hnot
  obtain ⟨u, hune, hus, hulower, huupper, hgroup⟩ :=
    exists_robust_greedy_large_group_subtype
      (fun i => dyadicLogExponent T0 (q i)) t short ht
      (fun i hi => (mem_shortDyadicFactorSet.mp (by simpa [short] using hi)))
      (by simpa [short] using htotalShort)
      (fun i => (((2 ^ q i : ℕ) : ℝ))) z e (fun i _ => by positivity) hsubsetLarge
  refine ⟨u, hune, ?_, hulower, huupper, Finset.card_le_univ u, ?_, ?_⟩
  · simpa [short] using hus
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) =
      T0 ^ ∑ i ∈ u, dyadicLogExponent T0 (q i)
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i)]
    exact cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT0 q u
  · simpa [groupedDyadicLower] using hgroup

end RHTower.Sieve
