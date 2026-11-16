import GaloisForLFunctions.RepresentationLifting.Probability.NilpotentMatrixCardinality
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum

/-!
# Distribution of the generalized zero-eigenspace dimension

The uniform endomorphism count gives an exact rational probability.
Fitting decomposition and the nilpotent matrix count reduce this law to
a finite product of general-linear-group factors.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable (K : Type*) [Field K] [Finite K]

/-- Proportion of endomorphisms whose generalized zero-eigenspace has dimension `d`. -/
def fittingDegreeDensity (n d : ℕ) : ℚ :=
  (Nat.card (FittingDegreeStratum K (Fin n → K) d) : ℚ) / (Nat.card K : ℚ) ^ (n * n)

private theorem fieldCard_rat_pos : (0 : ℚ) < Nat.card K := by
  exact_mod_cast (Nat.card_pos (α := K))

/-- The automorphism recurrence, after embedding the counts in the rationals. -/
theorem finiteFieldAutomorphismCount_rat_succ (n : ℕ) :
    (finiteFieldAutomorphismCount K (n + 1) : ℚ) =
      (Nat.card K : ℚ) ^ n * ((Nat.card K : ℚ) ^ (n + 1) - 1) *
        finiteFieldAutomorphismCount K n := by
  have hp : 1 ≤ Nat.card K ^ (n + 1) :=
    Nat.succ_le_of_lt (pow_pos (Nat.card_pos (α := K)) (n + 1))
  rw [finiteFieldAutomorphismCount_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_sub hp, Nat.cast_pow, Nat.cast_one]

/-- Each extra dimension multiplies the invertible proportion by `1 - q^(-n-1)`. -/
theorem normalizedAutomorphismCount_succ (n : ℕ) :
    (finiteFieldAutomorphismCount K (n + 1) : ℚ) /
      (Nat.card K : ℚ) ^ ((n + 1) * (n + 1)) =
    (finiteFieldAutomorphismCount K n : ℚ) / (Nat.card K : ℚ) ^ (n * n) *
      (1 - 1 / (Nat.card K : ℚ) ^ (n + 1)) := by
  have hq := (fieldCard_rat_pos K).ne'
  rw [finiteFieldAutomorphismCount_rat_succ,
    show (n + 1) * (n + 1) = (n * n + n) + (n + 1) by ring]
  simp only [pow_add, pow_one]
  field_simp

/-- The ratio of invertible proportions is the product over the added dimensions. -/
theorem normalizedAutomorphismCount_add (d k : ℕ) :
    (finiteFieldAutomorphismCount K (d + k) : ℚ) /
      (Nat.card K : ℚ) ^ ((d + k) * (d + k)) =
    (finiteFieldAutomorphismCount K d : ℚ) / (Nat.card K : ℚ) ^ (d * d) *
      ∏ i : Fin k, (1 - 1 / (Nat.card K : ℚ) ^ (d + (i : ℕ) + 1)) := by
  induction k with
  | zero => simp only [Nat.add_zero, Fin.prod_univ_zero, mul_one]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show d + (k + 1) = (d + k) + 1 by omega,
      normalizedAutomorphismCount_succ, ih, mul_assoc]

/-- Multiplying the nilpotent count by `q^d` recovers the total matrix count. -/
theorem finiteFieldNilpotentCount_mul_pow (d : ℕ) :
    (finiteFieldNilpotentCount K d : ℚ) * (Nat.card K : ℚ) ^ d =
      (Nat.card K : ℚ) ^ (d * d) := by
  rw [finiteFieldNilpotentCount_eq, Nat.cast_pow, ← pow_add]
  congr 1
  cases d with
  | zero => rfl
  | succ d => simp only [Nat.add_sub_cancel]; ring

/-- Exact finite-field degree law, with ambient dimension `d+k`. -/
theorem fittingDegreeDensity_eq_product (d k : ℕ) :
    fittingDegreeDensity K (d + k) d =
      (∏ i : Fin k, (1 - 1 / (Nat.card K : ℚ) ^ (d + (i : ℕ) + 1))) /
        (Nat.card K : ℚ) ^ d := by
  let d' : Fin (Module.finrank K (Fin (d + k) → K) + 1) :=
    ⟨d, by simp only [Module.finrank_pi, Fintype.card_fin]; omega⟩
  have hc := card_fittingDegreeStratum_mul_standard_aut
    (K := K) (V := Fin (d + k) → K) d'
  change Nat.card (FittingDegreeStratum K (Fin (d + k) → K) d) *
    finiteFieldAutomorphismCount K d =
      finiteFieldAutomorphismCount K (d + k) * finiteFieldNilpotentCount K d at hc
  have hcq : (Nat.card (FittingDegreeStratum K (Fin (d + k) → K) d) : ℚ) *
      finiteFieldAutomorphismCount K d =
      (finiteFieldAutomorphismCount K (d + k) : ℚ) * finiteFieldNilpotentCount K d := by
    exact_mod_cast hc
  have hg : (finiteFieldAutomorphismCount K d : ℚ) ≠ 0 := by
    exact_mod_cast (finiteFieldAutomorphismCount_pos K d).ne'
  have hq := (fieldCard_rat_pos K).ne'
  have hn := finiteFieldNilpotentCount_mul_pow K d
  have hnp : (finiteFieldNilpotentCount K d : ℚ) =
      (Nat.card K : ℚ) ^ (d * d) / (Nat.card K : ℚ) ^ d :=
    (eq_div_iff (pow_ne_zero _ hq)).mpr hn
  change (Nat.card (FittingDegreeStratum K (Fin (d + k) → K) d) : ℚ) / _ = _
  have hcount : (Nat.card (FittingDegreeStratum K (Fin (d + k) → K) d) : ℚ) =
      (finiteFieldAutomorphismCount K (d + k) : ℚ) * finiteFieldNilpotentCount K d /
        finiteFieldAutomorphismCount K d := by
    exact (eq_div_iff hg).mpr hcq
  rw [hcount]
  calc
    _ = ((finiteFieldAutomorphismCount K (d + k) : ℚ) /
          (Nat.card K : ℚ) ^ ((d + k) * (d + k))) *
          (finiteFieldNilpotentCount K d : ℚ) / finiteFieldAutomorphismCount K d := by ring
    _ = _ := by
      rw [normalizedAutomorphismCount_add, hnp]
      field_simp

/-- The exact degree law is bounded by its geometric factor. -/
theorem fittingDegreeDensity_le (d k : ℕ) :
    fittingDegreeDensity K (d + k) d ≤ 1 / (Nat.card K : ℚ) ^ d := by
  have hq := fieldCard_rat_pos K
  have hp (m : ℕ) : (1 : ℚ) ≤ (Nat.card K : ℚ) ^ m := by
    exact_mod_cast Nat.succ_le_of_lt (pow_pos (Nat.card_pos (α := K)) m)
  rw [fittingDegreeDensity_eq_product]
  apply (div_le_div_iff_of_pos_right (pow_pos hq d)).mpr
  apply Finset.prod_le_one
  · intro i _
    exact sub_nonneg.mpr ((div_le_iff₀ (pow_pos hq _)).mpr (by
      simpa only [one_mul] using hp (d + (i : ℕ) + 1)))
  · intro i _
    exact sub_le_self _ (one_div_pos.mpr (pow_pos hq _)).le

/-- The proportions over all possible dimensions sum to one. -/
theorem sum_fittingDegreeDensity (n : ℕ) :
    (∑ d : Fin (n + 1), fittingDegreeDensity K n (d : ℕ)) = 1 := by
  have h := sum_card_fittingDegreeStratum (K := K) (V := Fin n → K)
  rw [Module.finrank_pi, Fintype.card_fin,
    Nat.card_congr (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin n)).toEquiv] at h
  simp only [Matrix, Nat.card_fun, Nat.card_fin, ← pow_mul] at h
  have hq := (fieldCard_rat_pos K).ne'
  simp only [fittingDegreeDensity, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
  rw [h, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ hq)]

/-- Uniform geometric tail bound for the generalized zero-eigenspace dimension. -/
theorem sum_fittingDegreeDensity_tail_le (d k : ℕ) :
    (∑ i : Fin (k + 1), fittingDegreeDensity K (d + k) (d + (i : ℕ))) ≤
      (1 / (Nat.card K : ℚ) ^ d) / (1 - 1 / (Nat.card K : ℚ)) := by
  have hq := fieldCard_rat_pos K
  have hq1 : (1 : ℚ) < Nat.card K := by
    letI := Fintype.ofFinite K
    exact_mod_cast (show 1 < Nat.card K by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card)
  have hr := one_div_pos.mpr hq
  have hrq := div_mul_cancel₀ (1 : ℚ) hq.ne'
  have hr1 : 1 / (Nat.card K : ℚ) < 1 := by nlinarith only [hq1, hrq]
  have hgeom := geom_sum_mul (1 / (Nat.card K : ℚ)) (k + 1)
  have hpow := pow_nonneg hr.le (k + 1)
  have hg : (∑ i ∈ Finset.range (k + 1), (1 / (Nat.card K : ℚ)) ^ i) ≤
      1 / (1 - 1 / (Nat.card K : ℚ)) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    nlinarith only [hgeom, hpow]
  calc
    _ ≤ ∑ i : Fin (k + 1), 1 / (Nat.card K : ℚ) ^ (d + (i : ℕ)) := by
      apply Finset.sum_le_sum
      intro i _
      have h := fittingDegreeDensity_le K (d + (i : ℕ)) (k - (i : ℕ))
      rw [show d + (i : ℕ) + (k - (i : ℕ)) = d + k by omega] at h
      exact h
    _ = (1 / (Nat.card K : ℚ) ^ d) *
        ∑ i ∈ Finset.range (k + 1), (1 / (Nat.card K : ℚ)) ^ i := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ => 1 / (Nat.card K : ℚ) ^ (d + i)) (k + 1), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add, div_pow, one_pow]
      field_simp
    _ ≤ (1 / (Nat.card K : ℚ) ^ d) * (1 / (1 - 1 / (Nat.card K : ℚ))) :=
      mul_le_mul_of_nonneg_left hg (one_div_pos.mpr (pow_pos hq d)).le
    _ = _ := by ring

#print axioms fittingDegreeDensity_eq_product
#print axioms sum_fittingDegreeDensity
#print axioms sum_fittingDegreeDensity_tail_le

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
