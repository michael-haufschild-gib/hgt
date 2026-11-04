import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeCovarianceGram

/-!
# Collision mass in a prime covariance block

A positive affine collision row controls the full quadratic main term.
Averaging that row in the prime multiplier supplies a second reciprocal
prime factor; the proper-prime-power remainder stays explicit.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- A collision row bound controls its quadratic mass by the total positive weight. -/
theorem collision_mass {α : Type*} (I : Finset α) (v : α → ℝ)
    (R : α → α → Prop) [∀ i j, Decidable (R i j)] {D C : ℝ}
    (hv : ∀ i ∈ I, 0 ≤ v i) (hC : 0 ≤ C)
    (htotal : (∑ i ∈ I, v i) ≤ D)
    (hrow : ∀ j ∈ I, (∑ i ∈ I, if R i j then v i else 0) ≤ C) :
    (∑ i ∈ I, ∑ j ∈ I, v i * v j * (if R i j then (1 : ℝ) else 0)) ≤ D * C := by
  rw [sum_comm]
  calc
    _ = ∑ j ∈ I, v j * ∑ i ∈ I, if R i j then v i else 0 := by
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ ≤ ∑ j ∈ I, v j * C :=
      sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hrow j hj) (hv j hj)
    _ = (∑ j ∈ I, v j) * C := by rw [sum_mul]
    _ ≤ D * C := mul_le_mul_of_nonneg_right htotal hC

/-- The absolute covariance has a collision term and a reciprocal-square term. -/
theorem abs_same_residue_mean_le (p a b : ℕ) :
    |(if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2| ≤
      (if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) + 1 / (p : ℝ) ^ 2 := by
  have hδ : 0 ≤ (if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) := by
    split_ifs <;> positivity
  simpa only [abs_of_nonneg hδ, abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ) ^ 2)]
    using abs_sub (if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) (1 / (p : ℝ) ^ 2)

/-- An averaged affine congruence gains a second reciprocal prime factor. -/
theorem same_prime_quadratic_mass {α : Type*} (I : Finset α)
    (v : α → ℝ) (a : α → ℕ) {p : ℕ} (hp : 0 < p) {D C E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hv : ∀ i ∈ I, 0 ≤ v i) (htotal : (∑ i ∈ I, v i) ≤ D)
    (hrow : ∀ j ∈ I,
      (∑ i ∈ I, if a i ≡ a j [MOD p] then v i else 0) ≤ C / (p : ℝ) + E) :
    (∑ i ∈ I, ∑ j ∈ I, v i * v j *
      |(if a i ≡ a j [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2|) ≤
      D * (C + D) / (p : ℝ) ^ 2 + D * E / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hcollision := collision_mass I v (fun i j => a i ≡ a j [MOD p]) hv
    (add_nonneg (div_nonneg hC hp0.le) hE) htotal hrow
  have htotal0 : 0 ≤ ∑ i ∈ I, v i := sum_nonneg hv
  have htotalSq : (∑ i ∈ I, v i) ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ htotal0 htotal 2
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, v i * v j *
        ((if a i ≡ a j [MOD p] then 1 / (p : ℝ) else 0) + 1 / (p : ℝ) ^ 2) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (abs_same_residue_mean_le p (a i) (a j))
        (mul_nonneg (hv i hi) (hv j hj))
    _ = (∑ i ∈ I, ∑ j ∈ I, v i * v j *
          (if a i ≡ a j [MOD p] then (1 : ℝ) else 0)) / p +
        (∑ i ∈ I, v i) ^ 2 / (p : ℝ) ^ 2 := by
      rw [pow_two, sum_mul_sum]
      simp only [sum_div, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ ≤ (D * (C / (p : ℝ) + E)) / p + D ^ 2 / (p : ℝ) ^ 2 :=
      add_le_add (div_le_div_of_nonneg_right hcollision hp0.le)
        (div_le_div_of_nonneg_right htotalSq (sq_nonneg _))
    _ = _ := by ring

#print axioms collision_mass
#print axioms same_prime_quadratic_mass

end GaloisForLFunctions.BezoutValuationIncidence
