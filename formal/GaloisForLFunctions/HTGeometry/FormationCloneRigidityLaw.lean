import GaloisForLFunctions.HTGeometry.MarkedVariationDynamics
import Mathlib.Analysis.Real.Sqrt

/-!
# Formation-cloning rigidity

Finite source copying and independent packet formation are different operations.  This module
formalizes their Hellinger obstruction:

* finite Markov observation can only increase Hellinger affinity;
* independent tensor-square formation squares affinity;
* a common Markov kernel cloning two packets therefore forces affinity to be `0` or `1`;
* every overlapping nonidentical pair is unclonable;
* adding the same split recovery kernel to both packets preserves affinity exactly.

This is the finite certified core of the universal-law-field broadcast--clone fracture theorem.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Classical Hellinger/Bhattacharyya affinity in finite square-root coordinates. -/
def finiteFormationAffinity {X : Type*} [Fintype X]
    (p q : X → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x) * Real.sqrt (q x)

/-- Independent two-copy formation of a finite real packet. -/
def finiteIndependentPair {X : Type*} (p : X → ℝ) : X × X → ℝ :=
  fun z => p z.1 * p z.2

/-- Extend a finite packet by a parameter-independent conditional recovery row. -/
def finiteSplitRecovery {X H : Type*} (p : X → ℝ)
    (kappa : X → H → ℝ) : X × H → ℝ :=
  fun z => p z.1 * kappa z.1 z.2

/-- Finite formation affinity is nonnegative without packet-normalization assumptions. -/
theorem finiteFormationAffinity_nonneg {X : Type*} [Fintype X]
    (p q : X → ℝ) :
    0 ≤ finiteFormationAffinity p q := by
  unfold finiteFormationAffinity
  positivity

/-- Affinity of two finite probability packets is at most one. -/
theorem finiteFormationAffinity_le_one {X : Type*} [Fintype X]
    (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationAffinity p q ≤ 1 := by
  unfold finiteFormationAffinity
  calc
    ∑ x, Real.sqrt (p x) * Real.sqrt (q x) ≤
        Real.sqrt (∑ x, p x) * Real.sqrt (∑ x, q x) := by
      simpa only using
        (Real.sum_sqrt_mul_sqrt_le Finset.univ hp hq)
    _ = 1 := by rw [hpsum, hqsum]; norm_num

/-- **Hellinger data processing.** A finite Markov kernel cannot decrease affinity. -/
theorem finiteFormationAffinity_markovDataProcessing
    {X Y : Type*} [Fintype X] [Fintype Y]
    (K : FiniteMarkovKernel X Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    finiteFormationAffinity p q ≤
      finiteFormationAffinity
        (K.toFinitePositiveKernel.applyReal p)
        (K.toFinitePositiveKernel.applyReal q) := by
  let P := K.toFinitePositiveKernel.applyReal p
  let Q := K.toFinitePositiveKernel.applyReal q
  have hP : ∀ y, 0 ≤ P y := by
    intro y
    unfold P FinitePositiveKernel.applyReal
    exact Finset.sum_nonneg fun x _ => mul_nonneg (K.nonneg y x) (hp x)
  have hQ : ∀ y, 0 ≤ Q y := by
    intro y
    unfold Q FinitePositiveKernel.applyReal
    exact Finset.sum_nonneg fun x _ => mul_nonneg (K.nonneg y x) (hq x)
  have hy : ∀ y,
      ∑ x, Real.sqrt (K.weight y x * p x) *
          Real.sqrt (K.weight y x * q x) ≤
        Real.sqrt (P y) * Real.sqrt (Q y) := by
    intro y
    simpa only [P, Q, FinitePositiveKernel.applyReal,
      mul_comm (K.weight y _)] using
      (Real.sum_sqrt_mul_sqrt_le Finset.univ
        (fun x => mul_nonneg (K.nonneg y x) (hp x))
        (fun x => mul_nonneg (K.nonneg y x) (hq x)))
  calc
    finiteFormationAffinity p q =
        ∑ y, ∑ x, K.weight y x *
          (Real.sqrt (p x) * Real.sqrt (q x)) := by
      unfold finiteFormationAffinity
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, K.column_sum x, one_mul]
    _ = ∑ y, ∑ x,
          Real.sqrt (K.weight y x * p x) *
            Real.sqrt (K.weight y x * q x) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.sqrt_mul (K.nonneg y x), Real.sqrt_mul (K.nonneg y x)]
      calc
        K.weight y x * (Real.sqrt (p x) * Real.sqrt (q x)) =
            Real.sqrt (K.weight y x) ^ 2 *
              (Real.sqrt (p x) * Real.sqrt (q x)) := by
                rw [Real.sq_sqrt (K.nonneg y x)]
        _ = Real.sqrt (K.weight y x) * Real.sqrt (p x) *
              (Real.sqrt (K.weight y x) * Real.sqrt (q x)) := by ring
    _ ≤ ∑ y, Real.sqrt (P y) * Real.sqrt (Q y) :=
      Finset.sum_le_sum fun y _ => hy y
    _ = finiteFormationAffinity P Q := rfl

/-- Independent tensor-square formation squares finite Hellinger affinity. -/
theorem finiteFormationAffinity_independentPair
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    finiteFormationAffinity (finiteIndependentPair p) (finiteIndependentPair q) =
      finiteFormationAffinity p q ^ 2 := by
  unfold finiteFormationAffinity finiteIndependentPair
  rw [Fintype.sum_prod_type]
  calc
    ∑ x, ∑ y,
        Real.sqrt (p x * p y) * Real.sqrt (q x * q y) =
        ∑ x, ∑ y,
          (Real.sqrt (p x) * Real.sqrt (q x)) *
            (Real.sqrt (p y) * Real.sqrt (q y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.sqrt_mul (hp x), Real.sqrt_mul (hq x)]
      ring
    _ = (∑ x, Real.sqrt (p x) * Real.sqrt (q x)) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]

/-- **Common-recovery affinity isometry.** Adding the same conditional history row preserves
finite Hellinger affinity exactly. -/
theorem finiteFormationAffinity_splitRecovery
    {X H : Type*} [Fintype X] [Fintype H]
    (p q : X → ℝ) (kappa : X → H → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hk : ∀ x h, 0 ≤ kappa x h)
    (hrow : ∀ x, ∑ h, kappa x h = 1) :
    finiteFormationAffinity (finiteSplitRecovery p kappa)
        (finiteSplitRecovery q kappa) = finiteFormationAffinity p q := by
  unfold finiteFormationAffinity finiteSplitRecovery
  rw [Fintype.sum_prod_type]
  calc
    ∑ x, ∑ h,
        Real.sqrt (p x * kappa x h) * Real.sqrt (q x * kappa x h) =
        ∑ x, ∑ h, kappa x h *
          (Real.sqrt (p x) * Real.sqrt (q x)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro h _
      rw [Real.sqrt_mul (hp x), Real.sqrt_mul (hq x)]
      calc
        Real.sqrt (p x) * Real.sqrt (kappa x h) *
            (Real.sqrt (q x) * Real.sqrt (kappa x h)) =
            Real.sqrt (kappa x h) ^ 2 *
              (Real.sqrt (p x) * Real.sqrt (q x)) := by ring
        _ = kappa x h * (Real.sqrt (p x) * Real.sqrt (q x)) := by
          rw [Real.sq_sqrt (hk x h)]
    _ = ∑ x, Real.sqrt (p x) * Real.sqrt (q x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, hrow x, one_mul]

/-- **Exact finite formation-cloning rigidity.** If one Markov kernel independently clones two
probability packets, their affinity is forced to an extreme value, zero or one. -/
theorem finiteFormationClone_affinity_extreme
    {X : Type*} [Fintype X]
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (K : FiniteMarkovKernel X (X × X))
    (hclonep : K.toFinitePositiveKernel.applyReal p = finiteIndependentPair p)
    (hcloneq : K.toFinitePositiveKernel.applyReal q = finiteIndependentPair q) :
    finiteFormationAffinity p q = 0 ∨ finiteFormationAffinity p q = 1 := by
  let a := finiteFormationAffinity p q
  have ha0 : 0 ≤ a := finiteFormationAffinity_nonneg p q
  have ha1 : a ≤ 1 := finiteFormationAffinity_le_one p q hp hq hpsum hqsum
  have hle : a ≤ a ^ 2 := by
    have hdp := finiteFormationAffinity_markovDataProcessing K p q hp hq
    rw [hclonep, hcloneq, finiteFormationAffinity_independentPair p q hp hq] at hdp
    exact hdp
  obtain ha | ha := ha0.eq_or_lt
  · exact Or.inl ha.symm
  · right
    nlinarith

/-- Every pair with strictly interior affinity forbids a common independent-formation kernel. -/
theorem no_finiteFormationClone_of_interiorAffinity
    {X : Type*} [Fintype X]
    (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (ha0 : 0 < finiteFormationAffinity p q)
    (ha1 : finiteFormationAffinity p q < 1) :
    ¬ ∃ K : FiniteMarkovKernel X (X × X),
      K.toFinitePositiveKernel.applyReal p = finiteIndependentPair p ∧
      K.toFinitePositiveKernel.applyReal q = finiteIndependentPair q := by
  rintro ⟨K, hclonep, hcloneq⟩
  rcases finiteFormationClone_affinity_extreme p q hp hq hpsum hqsum K
      hclonep hcloneq with hzero | hone
  · linarith
  · linarith

end

end GaloisForLFunctions.HTGeometry
