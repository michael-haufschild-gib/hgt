import GaloisForLFunctions.HTGeometry.EulerianCrossingPolymerFreeEnergyLaw
import Mathlib.Analysis.Complex.Basic

/-!
# Sharp weights for finite truncation

Trybushnyi's Lemma 2.4 (arXiv:2611.14167) bounds an alternating bivariate
tail by evaluating its positive majorant at (2,2). The optimal uniform
factor is determined by the cheapest omitted monomial. The same argument
applies to signed compatible-polymer partitions with arbitrary activities.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence.Sieve.PositiveTruncation

variable {ι E : Type*} [NormedAddCommGroup E]

/-- The weighted variation of the discarded terms controls the entire error. -/
theorem tail_bound [DecidableEq ι] (s t : Finset ι) (w : ι → E) (price : ι → NNReal)
    (C : NNReal) (ht : t ⊆ s) (hp : ∀ i ∈ s, i ∉ t → C ≤ price i) :
    (C : ℝ) * ‖(∑ i ∈ s, w i) - ∑ i ∈ t, w i‖ ≤
      ∑ i ∈ s \ t, (price i : ℝ) * ‖w i‖ := by
  classical
  rw [← sum_sdiff_eq_sub ht]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) C.property).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (hp i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi).2) (norm_nonneg _)

/-- Testing individual real coefficients recovers every constraint on the uniform factor. -/
theorem uniform_factor_iff [DecidableEq ι] (s t : Finset ι) (price : ι → NNReal)
    (C : NNReal) (ht : t ⊆ s) :
    (∀ w : ι → ℝ, (C : ℝ) * |(∑ i ∈ s, w i) - ∑ i ∈ t, w i| ≤
      ∑ i ∈ s, (price i : ℝ)*|w i|) ↔ ∀ i ∈ s, i ∉ t → C ≤ price i := by
  constructor
  · intro H i hi hnot
    have h := H (fun j => if j = i then 1 else 0)
    simpa [hi,hnot,apply_ite abs,mul_ite] using h
  · intro h w
    have hb := tail_bound s t w price C ht h
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (sum_le_sum_of_subset_of_nonneg sdiff_subset fun i _ _ =>
      mul_nonneg (price i).property (abs_nonneg _))

/-- Unequal radii and independent cutoffs give the minimum of the two first
omitted axis weights. Mixed bidegrees can only improve the estimate. -/
theorem rectangular_tail (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ)
    (R S : NNReal) (hR : 1 ≤ R) (hS : 1 ≤ S) (k l : ℕ) :
    (min (R^(k+1)) (S^(l+1)) : NNReal) *
      ‖(∑ p ∈ s, w p) - ∑ p ∈ s.filter (fun p => p.1 ≤ k ∧ p.2 ≤ l), w p‖ ≤
      ∑ p ∈ s, ((R^p.1 * S^p.2 : NNReal) : ℝ)*‖w p‖ := by
  let t := s.filter (fun p => p.1 ≤ k ∧ p.2 ≤ l)
  have hprice (i : ℕ × ℕ) (hi : i ∈ s) (hn : i ∉ t) :
      min (R^(k+1)) (S^(l+1)) ≤ R^i.1 * S^i.2 := by
    by_cases h : i.1 ≤ k
    · have hl : l+1 ≤ i.2 := by
        by_contra! hc
        exact hn (mem_filter.mpr ⟨hi,h,by omega⟩)
      exact (min_le_right _ _).trans ((pow_le_pow_right₀ hS hl).trans
        (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hR)))
    · exact (min_le_left _ _).trans ((pow_le_pow_right₀ hR (by omega : k+1 ≤ i.1)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hS)))
  exact (tail_bound s t w (fun i => R^i.1*S^i.2) _ (filter_subset _ _) hprice).trans
    (sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => by positivity)

open GaloisForLFunctions.HTGeometry

/-- A cardinality cutoff in a compatible polymer gas costs at most the positive
partition at inflated activities divided by the first omitted power. -/
theorem polymer_tail [DecidableEq ι] (P : Finset ι) (allowed : Finset ι → Prop)
    [DecidablePred allowed] (w : ι → ℝ) (k : ℕ) (R : NNReal) (hR : 1 ≤ R) :
    (R : ℝ)^(k+1) *
      |compatiblePolymerPartition P allowed w -
        compatiblePolymerPartition P (fun a => allowed a ∧ a.card ≤ k) w| ≤
      compatiblePolymerPartition P allowed (fun i => (R : ℝ)*|w i|) := by
  classical
  let s := P.powerset.filter allowed
  let t := s.filter (fun a => a.card ≤ k)
  have he : t = P.powerset.filter (fun a => allowed a ∧ a.card ≤ k) := by
    ext a
    simp only [t,s,mem_filter,and_assoc]
  have h := (uniform_factor_iff s t (fun a => R^a.card) (R^(k+1)) (filter_subset _ _)).2
    (fun i hi hn => pow_le_pow_right₀ hR (show k+1 ≤ i.card from Nat.lt_of_not_ge
      (fun hc => hn (mem_filter.mpr ⟨hi,hc⟩)))) (fun a => ∏ i ∈ a, w i)
  rw [he] at h
  simpa only [compatiblePolymerPartition,s,NNReal.coe_pow,prod_mul_distrib,
    prod_const,Finset.abs_prod] using h

/-- Forgetting compatibility gives an explicit product bound for truncating a
gas of signed activities, uniform in the choice of allowed configurations. -/
theorem polymer_tail_product [DecidableEq ι] (P : Finset ι) (allowed : Finset ι → Prop)
    [DecidablePred allowed] (w : ι → ℝ) (k : ℕ) (R : NNReal) (hR : 1 ≤ R) :
    (R : ℝ)^(k+1) * |compatiblePolymerPartition P allowed w -
        compatiblePolymerPartition P (fun a => allowed a ∧ a.card ≤ k) w| ≤
      ∏ i ∈ P, (1+(R : ℝ)*|w i|) := by
  refine (polymer_tail P allowed w k R hR).trans ?_
  rw [prod_one_add,compatiblePolymerPartition]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ =>
    prod_nonneg fun i _ => mul_nonneg R.property (abs_nonneg _)

end GaloisForLFunctions.BezoutValuationIncidence.Sieve.PositiveTruncation
