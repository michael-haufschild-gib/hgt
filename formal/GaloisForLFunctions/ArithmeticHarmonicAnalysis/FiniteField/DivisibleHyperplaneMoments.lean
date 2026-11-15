import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.TriplyEvenOrthogonality

/-!
# Hyperplane divisibility and cubic moments

Affine hyperplane occupancies are the zero counts of an affine evaluation
code. Divisibility by eight therefore annihilates every cubic coordinate
moment in characteristic two. Conversely, a nonzero cubic moment detects
a nondegenerate hyperplane whose occupancy is not divisible by eight.
The indexed points may repeat.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Codes
variable {K ι ν : Type*} [Field K] [Fintype ι] [Fintype ν]

/-- Evaluations of all affine linear forms in a finite family of coordinates. -/
def affineHyperplaneCode (x : ν → ι → K) : Submodule K (ι → K) where
  carrier := {c | ∃ A : ν → K, ∃ C : K, ∀ i, c i = (∑ j, A j * x j i) + C}
  zero_mem' := ⟨0, 0, fun _ => by simp only [Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]⟩
  add_mem' := by
    rintro c d ⟨A, C, hc⟩ ⟨B, D, hd⟩
    refine ⟨A + B, C + D, fun i => ?_⟩
    change c i + d i = _
    rw [hc, hd]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  smul_mem' := by
    rintro a c ⟨A, C, hc⟩
    refine ⟨a • A, a * C, fun i => ?_⟩
    change a * c i = _
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

omit [Fintype ι] in
/-- Constants belong to every affine evaluation code. -/
theorem one_mem_affineHyperplaneCode (x : ν → ι → K) :
    (fun _ => (1 : K)) ∈ affineHyperplaneCode x :=
  ⟨0, 1, fun _ => by simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]⟩

omit [Fintype ι] in
/-- Every coordinate word belongs to the affine evaluation code. -/
theorem coordinate_mem_affineHyperplaneCode (x : ν → ι → K) (j : ν) :
    x j ∈ affineHyperplaneCode x := by
  refine ⟨Pi.single j 1, 0, fun i => ?_⟩
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero]

/-- Parallel hyperplanes partition the indexed points, so their common divisor divides the total. -/
theorem card_dvd_of_affineHyperplane_counts [Fintype K] [Nonempty ν]
    (Δ : ℕ) (x : ν → ι → K)
    (hplane : ∀ A : ν → K, ∀ C : K, A ≠ 0 →
      Δ ∣ (Finset.univ.filter (fun i => (∑ j, A j * x j i) = C)).card) :
    Δ ∣ Fintype.card ι := by
  let j₀ : ν := Classical.choice inferInstance
  have hA : (Pi.single j₀ (1 : K) : ν → K) ≠ 0 := by
    intro h
    simpa only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] using congrFun h j₀
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset K))
    (f := x j₀) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hpart
  rw [hpart]
  apply Finset.dvd_sum
  intro a _
  simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using hplane (Pi.single j₀ 1) a hA

/-- Hyperplane occupancy divisibility passes to every word in the affine evaluation code. -/
theorem affineHyperplaneCode_divisible [Fintype K] [Nonempty ν]
    (Δ : ℕ) (x : ν → ι → K)
    (hplane : ∀ A : ν → K, ∀ C : K, A ≠ 0 →
      Δ ∣ (Finset.univ.filter (fun i => (∑ j, A j * x j i) = C)).card) :
    Divisible Δ (affineHyperplaneCode x) := by
  have hn := card_dvd_of_affineHyperplane_counts Δ x hplane
  rintro c ⟨A, C, hc⟩
  by_cases hA : A = 0
  · have hword : c = fun _ => C := by
      funext i
      simpa only [hA, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] using hc i
    rw [hword]
    by_cases hC : C = 0
    · simp only [hC, weight, ne_eq, not_true_eq_false, Finset.filter_false,
        Finset.card_empty, dvd_zero]
    · simpa only [weight, hC, ne_eq, not_false_eq_true, Finset.filter_true,
        Finset.card_univ] using hn
  · have hz : Δ ∣ symbolCount c 0 := by
      have heq : symbolCount c 0 =
          (Finset.univ.filter (fun i => (∑ j, A j * x j i) = -C)).card := by
        unfold symbolCount
        congr 1
        apply Finset.filter_congr
        intro i _
        rw [hc, add_eq_zero_iff_eq_neg]
      rw [heq]
      exact hplane A (-C) hA
    have hp := symbolCount_add_weight_sub c 0
    simp only [sub_zero] at hp
    exact (Nat.dvd_add_iff_right hz).mpr (by rwa [hp])

/-- Eight-divisible hyperplane counts force all cubic coordinate moments to vanish. -/
theorem cubicMoment_eq_zero_of_affineHyperplane_counts [Fintype K] [CharP K 2]
    (x : ν → ι → K) (j k l : ν)
    (hplane : ∀ A : ν → K, ∀ C : K, A ≠ 0 →
      8 ∣ (Finset.univ.filter (fun i => (∑ v, A v * x v i) = C)).card) :
    ∑ i, x j i * x k i * x l i = 0 := by
  letI : Nonempty ν := ⟨j⟩
  have horth := eightDivisible_triorthogonal (affineHyperplaneCode x)
    (one_mem_affineHyperplaneCode x) (affineHyperplaneCode_divisible 8 x hplane)
  exact horth _ (coordinate_mem_affineHyperplaneCode x j)
    _ (coordinate_mem_affineHyperplaneCode x k) _ (coordinate_mem_affineHyperplaneCode x l)

/-- A nonzero cubic moment detects a hyperplane occupancy that survives modulo eight. -/
theorem exists_affineHyperplane_count_not_dvd_eight [Fintype K] [CharP K 2]
    (x : ν → ι → K) (j k l : ν)
    (h : ∑ i, x j i * x k i * x l i ≠ 0) :
    ∃ A : ν → K, ∃ C : K, A ≠ 0 ∧
      ¬8 ∣ (Finset.univ.filter (fun i => (∑ v, A v * x v i) = C)).card := by
  by_contra! hplane
  exact h (cubicMoment_eq_zero_of_affineHyperplane_counts x j k l hplane)

#print axioms cubicMoment_eq_zero_of_affineHyperplane_counts
#print axioms exists_affineHyperplane_count_not_dvd_eight

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
