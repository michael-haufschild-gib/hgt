import GaloisForLFunctions.RHTower.BakerGeneralProof.ContourHermite
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Repeated-frequency modulus bounds

This module packages the monic polynomial with a prescribed repeated zero at every additive
frequency. It proves exact degree and divisibility, submultiplicativity of the coefficient ℓ¹ norm,
and uniform upper/lower estimates that do not depend on frequency separation.
-/

open scoped Classical
open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

theorem coeffNormSum_eq_sum_support (p : Polynomial ℂ) :
    coeffNormSum p = ∑ k ∈ p.support, ‖p.coeff k‖ := by
  rw [coeffNormSum]
  symm
  apply Finset.sum_subset p.supp_subset_range_natDegree_succ
  intro k hk hknot
  have hz : p.coeff k = 0 := by
    simpa [Polynomial.mem_support_iff] using hknot
  simp [hz]

theorem sum_norm_coeff_eq_coeffNormSum_of_support_subset (p : Polynomial ℂ)
    (s : Finset ℕ) (hs : p.support ⊆ s) :
    (∑ k ∈ s, ‖p.coeff k‖) = coeffNormSum p := by
  rw [coeffNormSum_eq_sum_support]
  symm
  apply Finset.sum_subset hs
  intro k hk hknot
  have hz : p.coeff k = 0 := by
    simpa [Polynomial.mem_support_iff] using hknot
  simp [hz]

theorem coeffNormSum_add_le (p q : Polynomial ℂ) :
    coeffNormSum (p + q) ≤ coeffNormSum p + coeffNormSum q := by
  rw [coeffNormSum_eq_sum_support]
  calc
    (∑ k ∈ (p + q).support, ‖(p + q).coeff k‖)
        ≤ ∑ k ∈ p.support ∪ q.support, ‖(p + q).coeff k‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Polynomial.support_add
        (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ k ∈ p.support ∪ q.support, (‖p.coeff k‖ + ‖q.coeff k‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Polynomial.coeff_add] using norm_add_le (p.coeff k) (q.coeff k)
    _ = (∑ k ∈ p.support ∪ q.support, ‖p.coeff k‖) +
          ∑ k ∈ p.support ∪ q.support, ‖q.coeff k‖ := by
      rw [Finset.sum_add_distrib]
    _ = coeffNormSum p + coeffNormSum q := by
      rw [sum_norm_coeff_eq_coeffNormSum_of_support_subset p _ Finset.subset_union_left,
        sum_norm_coeff_eq_coeffNormSum_of_support_subset q _ Finset.subset_union_right]

theorem coeffNormSum_finset_sum_le {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial ℂ) :
    coeffNormSum (∑ i ∈ s, P i) ≤ ∑ i ∈ s, coeffNormSum (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffNormSum]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (coeffNormSum_add_le _ _).trans (add_le_add le_rfl ih)

theorem coeffNormSum_monomial (n : ℕ) (a : ℂ) :
    coeffNormSum (Polynomial.monomial n a) = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha, coeffNormSum]
  · rw [coeffNormSum_eq_sum_support]
    simp [ha]

theorem coeffNormSum_mul_le (p q : Polynomial ℂ) :
    coeffNormSum (p * q) ≤ coeffNormSum p * coeffNormSum q := by
  have hprod : p * q =
      ∑ i ∈ p.support, ∑ j ∈ q.support,
        Polynomial.monomial (i + j) (p.coeff i * q.coeff j) := by
    calc
      p * q = (∑ i ∈ p.support, Polynomial.monomial i (p.coeff i)) * q := by
        exact congrArg (fun r : Polynomial ℂ => r * q) p.as_sum_support
      _ = ∑ i ∈ p.support, Polynomial.monomial i (p.coeff i) * q := by
        rw [Finset.sum_mul]
      _ = ∑ i ∈ p.support,
          Polynomial.monomial i (p.coeff i) *
            (∑ j ∈ q.support, Polynomial.monomial j (q.coeff j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun r : Polynomial ℂ => Polynomial.monomial i (p.coeff i) * r)
          q.as_sum_support
      _ = ∑ i ∈ p.support, ∑ j ∈ q.support,
          Polynomial.monomial (i + j) (p.coeff i * q.coeff j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Polynomial.monomial_mul_monomial]
  rw [hprod]
  calc
    coeffNormSum
        (∑ i ∈ p.support, ∑ j ∈ q.support,
          Polynomial.monomial (i + j) (p.coeff i * q.coeff j))
        ≤ ∑ i ∈ p.support,
            coeffNormSum (∑ j ∈ q.support,
              Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) :=
      coeffNormSum_finset_sum_le p.support _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
          coeffNormSum (Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact coeffNormSum_finset_sum_le q.support _
    _ = ∑ i ∈ p.support, ∑ j ∈ q.support, ‖p.coeff i‖ * ‖q.coeff j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeffNormSum_monomial, norm_mul]
    _ = (∑ i ∈ p.support, ‖p.coeff i‖) *
          ∑ j ∈ q.support, ‖q.coeff j‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = coeffNormSum p * coeffNormSum q := by
      rw [← coeffNormSum_eq_sum_support, ← coeffNormSum_eq_sum_support]

theorem coeffNormSum_pow_le (p : Polynomial ℂ) (n : ℕ) :
    coeffNormSum (p ^ n) ≤ coeffNormSum p ^ n := by
  induction n with
  | zero => simp [coeffNormSum]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (coeffNormSum_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (coeffNormSum_nonneg p))

theorem coeffNormSum_prod_le {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial ℂ) :
    coeffNormSum (∏ i ∈ s, P i) ≤ ∏ i ∈ s, coeffNormSum (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffNormSum]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (coeffNormSum_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (coeffNormSum_nonneg (P a)))

theorem coeffNormSum_X_sub_C_le (u : ℂ) :
    coeffNormSum (Polynomial.X - Polynomial.C u) ≤ 1 + ‖u‖ := by
  rw [sub_eq_add_neg]
  calc
    coeffNormSum (Polynomial.X + -Polynomial.C u)
        ≤ coeffNormSum Polynomial.X + coeffNormSum (-Polynomial.C u) :=
      coeffNormSum_add_le _ _
    _ = 1 + ‖u‖ := by
      rw [← Polynomial.monomial_one_one_eq_X,
        show -(Polynomial.C u) = Polynomial.C (-u) by simp,
        ← Polynomial.monomial_zero_left,
        coeffNormSum_monomial, coeffNormSum_monomial]
      simp

noncomputable def repeatedFrequencyModulus {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) : Polynomial ℂ :=
  ∏ i, (Polynomial.X - Polynomial.C (μ i)) ^ K

theorem repeatedFrequencyModulus_monic {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) : (repeatedFrequencyModulus μ K).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C (μ i)).pow K

theorem power_dvd_repeatedFrequencyModulus {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) (i : ι) :
    (Polynomial.X - Polynomial.C (μ i)) ^ K ∣ repeatedFrequencyModulus μ K := by
  exact Finset.dvd_prod_of_mem (fun j => (Polynomial.X - Polynomial.C (μ j)) ^ K)
    (Finset.mem_univ i)

theorem natDegree_repeatedFrequencyModulus {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) :
    (repeatedFrequencyModulus μ K).natDegree = Fintype.card ι * K := by
  rw [repeatedFrequencyModulus,
    Polynomial.natDegree_prod_of_monic
      (s := Finset.univ) (f := fun i => (Polynomial.X - Polynomial.C (μ i)) ^ K)
      (fun i _ => (Polynomial.monic_X_sub_C (μ i)).pow K)]
  simp

theorem coeffNormSum_repeatedFrequencyModulus_le {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) :
    coeffNormSum (repeatedFrequencyModulus μ K) ≤
      ∏ i, (1 + ‖μ i‖) ^ K := by
  calc
    coeffNormSum (repeatedFrequencyModulus μ K)
        ≤ ∏ i, coeffNormSum ((Polynomial.X - Polynomial.C (μ i)) ^ K) := by
      exact coeffNormSum_prod_le Finset.univ _
    _ ≤ ∏ i, coeffNormSum (Polynomial.X - Polynomial.C (μ i)) ^ K := by
      apply Finset.prod_le_prod
      · intro i hi
        exact coeffNormSum_nonneg _
      · intro i hi
        exact coeffNormSum_pow_le _ _
    _ ≤ ∏ i, (1 + ‖μ i‖) ^ K := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (coeffNormSum_nonneg _) _
      · intro i hi
        exact pow_le_pow_left₀ (coeffNormSum_nonneg _)
          (coeffNormSum_X_sub_C_le (μ i)) K

theorem coeffNormSum_repeatedFrequencyModulus_le_uniform {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) {Ω : ℝ}
    (hμ : ∀ i, ‖μ i‖ ≤ Ω) :
    coeffNormSum (repeatedFrequencyModulus μ K) ≤
      (1 + Ω) ^ (Fintype.card ι * K) := by
  calc
    coeffNormSum (repeatedFrequencyModulus μ K)
        ≤ ∏ i, (1 + ‖μ i‖) ^ K :=
      coeffNormSum_repeatedFrequencyModulus_le μ K
    _ ≤ ∏ _i : ι, (1 + Ω) ^ K := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact pow_le_pow_left₀ (by positivity)
          (by simpa [add_comm] using add_le_add_left (hμ i) 1) K
    _ = (1 + Ω) ^ (Fintype.card ι * K) := by
      rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]

theorem norm_eval_repeatedFrequencyModulus_ge {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (K : ℕ) {Ω ρ : ℝ} (hΩρ : Ω < ρ)
    (hμ : ∀ i, ‖μ i‖ ≤ Ω) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) ρ) :
    (ρ - Ω) ^ (Fintype.card ι * K) ≤
      ‖(repeatedFrequencyModulus μ K).eval ζ‖ := by
  have hζnorm : ‖ζ‖ = ρ := by simpa [mem_sphere_iff_norm] using hζ
  have hfactor : ∀ i, ρ - Ω ≤ ‖ζ - μ i‖ := by
    intro i
    have htri : ‖ζ‖ ≤ ‖ζ - μ i‖ + ‖μ i‖ := by
      calc
        ‖ζ‖ = ‖(ζ - μ i) + μ i‖ := by ring_nf
        _ ≤ ‖ζ - μ i‖ + ‖μ i‖ := norm_add_le _ _
    linarith [hμ i]
  rw [repeatedFrequencyModulus, Polynomial.eval_prod, norm_prod]
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, norm_pow]
  calc
    (ρ - Ω) ^ (Fintype.card ι * K) = ∏ _i : ι, (ρ - Ω) ^ K := by
      rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]
    _ ≤ ∏ i, ‖ζ - μ i‖ ^ K := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact pow_le_pow_left₀ (by linarith) (hfactor i) K

end GaloisForLFunctions.RHTower.BakerGeneralProof

