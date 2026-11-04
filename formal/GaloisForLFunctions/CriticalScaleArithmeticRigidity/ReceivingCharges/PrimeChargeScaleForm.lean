import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCombinations

/-!
# The exact positive form of a prime-scale charge distribution

Integer cutoff exponents partition logarithmic prime scale into unit cells.
The complete limiting prefix kernel is the weighted square of its step
density, with weight `d-k-1/2` on cell `k`. Total receiving charge is the sum
of this density. The form vanishes exactly when the density vanishes.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

/-- Unit charge uniformly distributed over a prefix of logarithmic prime scale. -/
def primePrefixScaleDensity (a k : ℕ) : ℝ := if k < a then (a : ℝ)⁻¹ else 0

/-- The exact average cofactor logarithm on one unit cell. -/
def primeScaleCofactor (d k : ℕ) : ℝ := (d : ℝ) - k - 1 / 2

/-- The logarithmic prime-scale density of a finite coherent charge distribution. -/
def primeChargeScaleDensity {ι : Type*} (S : Finset ι) (a : ι → ℕ)
    (t : ι → ℝ) (k : ℕ) : ℝ := ∑ i ∈ S, t i * primePrefixScaleDensity (a i) k

/-- The complete limiting form on a finite logarithmic scale grid. -/
def primeChargeScaleForm (d : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range d, primeScaleCofactor d k * f k ^ 2

private theorem prefix_filter {a d : ℕ} (had : a ≤ d) :
    (range d).filter (fun k => k < a) = range a := by
  ext k
  simp only [mem_filter, mem_range]
  omega

private theorem sum_initial_cofactor (a d : ℕ) :
    (∑ k ∈ range a, primeScaleCofactor d k) = (a : ℝ) * d - (a : ℝ) ^ 2 / 2 := by
  induction a with
  | zero => simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, zero_pow two_ne_zero,
      zero_div, sub_zero]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, primeScaleCofactor, Nat.cast_succ]
    ring

theorem primeScaleCofactor_pos {d k : ℕ} (hk : k ∈ range d) :
    0 < primeScaleCofactor d k := by
  have h : (k : ℝ) + 1 ≤ d := by
    exact_mod_cast (show k + 1 ≤ d by have := mem_range.mp hk; omega)
  dsimp only [primeScaleCofactor]
  linarith only [h]

/-- Every prefix density has mass one on any grid containing that prefix. -/
theorem sum_primePrefixScaleDensity {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    (∑ k ∈ range d, primePrefixScaleDensity a k) = 1 := by
  simp only [primePrefixScaleDensity]
  rw [← sum_filter, prefix_filter had, sum_const, card_range, nsmul_eq_mul]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  exact mul_inv_cancel₀ haR

/-- The explicit complete prefix kernel is the cofactor-weighted Gram of prefix densities. -/
theorem primePrefixReceivingKernel_eq_scale_gram {a b d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ d) (hbd : b ≤ d) :
    primePrefixReceivingKernel a b d =
      ∑ k ∈ range d, primeScaleCofactor d k *
        primePrefixScaleDensity a k * primePrefixScaleDensity b k := by
  have hterm (k : ℕ) : primeScaleCofactor d k *
      primePrefixScaleDensity a k * primePrefixScaleDensity b k =
        if k < min a b then primeScaleCofactor d k / ((a : ℝ) * b) else 0 := by
    by_cases hka : k < a <;> by_cases hkb : k < b <;>
      simp [primePrefixScaleDensity, hka, hkb, div_eq_mul_inv] <;> ring
  have hmin : min a b ≤ d := (min_le_min had hbd).trans_eq (min_self d)
  rw [sum_congr rfl (fun k _ => hterm k), ← sum_filter,
    prefix_filter hmin, ← sum_div, sum_initial_cofactor]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rcases le_total a b with hab | hba
  · simp only [primePrefixReceivingKernel, max_eq_right hab, min_eq_left hab]
    field_simp [haR, hbR]
  · simp only [primePrefixReceivingKernel, max_eq_left hba, min_eq_right hba]
    field_simp [haR, hbR]

/-- Every finite complete prefix form is exactly the positive cofactor form of its scale density. -/
theorem primeCharge_kernel_eq_scale_form {ι : Type*} (S : Finset ι)
    (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    (∑ i ∈ S, ∑ j ∈ S, t i * t j * primePrefixReceivingKernel (a i) (a j) d) =
      primeChargeScaleForm d (primeChargeScaleDensity S a t) := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ range d,
        primeScaleCofactor d k * (t i * primePrefixScaleDensity (a i) k) *
          (t j * primePrefixScaleDensity (a j) k) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [primePrefixReceivingKernel_eq_scale_gram (ha i hi) (ha j hj) (had i hi) (had j hj), mul_sum]
      exact sum_congr rfl fun k _ => by ring
    _ = ∑ i ∈ S, ∑ k ∈ range d, ∑ j ∈ S,
        primeScaleCofactor d k * (t i * primePrefixScaleDensity (a i) k) *
          (t j * primePrefixScaleDensity (a j) k) :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ k ∈ range d, ∑ i ∈ S, ∑ j ∈ S,
        primeScaleCofactor d k * (t i * primePrefixScaleDensity (a i) k) *
          (t j * primePrefixScaleDensity (a j) k) := sum_comm
    _ = _ := by
      unfold primeChargeScaleForm primeChargeScaleDensity
      apply sum_congr rfl
      intro k _
      rw [pow_two, sum_mul, mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun j _ => by ring

/-- The receiving charge is the total mass of its logarithmic scale density. -/
theorem sum_primeChargeScaleDensity {ι : Type*} (S : Finset ι)
    (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    (∑ k ∈ range d, primeChargeScaleDensity S a t k) = ∑ i ∈ S, t i := by
  unfold primeChargeScaleDensity
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [← mul_sum, sum_primePrefixScaleDensity (ha i hi) (had i hi), mul_one]

theorem primeChargeScaleForm_nonneg (d : ℕ) (f : ℕ → ℝ) :
    0 ≤ primeChargeScaleForm d f :=
  sum_nonneg fun k hk => mul_nonneg (primeScaleCofactor_pos hk).le (sq_nonneg _)

/-- The cofactor form has no nonzero density in its kernel on a fixed scale grid. -/
theorem primeChargeScaleForm_eq_zero_iff (d : ℕ) (f : ℕ → ℝ) :
    primeChargeScaleForm d f = 0 ↔ ∀ k ∈ range d, f k = 0 := by
  constructor
  · intro hz k hk
    have hnonneg (j : ℕ) (hj : j ∈ range d) : 0 ≤ primeScaleCofactor d j * f j ^ 2 :=
      mul_nonneg (primeScaleCofactor_pos hj).le (sq_nonneg _)
    have hle := single_le_sum hnonneg hk
    change primeScaleCofactor d k * f k ^ 2 ≤ primeChargeScaleForm d f at hle
    rw [hz] at hle
    have hzero := le_antisymm hle (hnonneg k hk)
    have hsq := (mul_eq_zero.mp hzero).resolve_left (primeScaleCofactor_pos hk).ne'
    nlinarith only [hsq]
  · intro hf
    exact sum_eq_zero fun k hk => by rw [hf k hk, zero_pow two_ne_zero, mul_zero]

/-- At any fixed finite collection of scales, a nonzero total charge has strictly positive limiting energy. -/
theorem primeCharge_kernel_pos_of_charge_ne_zero {ι : Type*} (S : Finset ι)
    (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d)
    (ht : (∑ i ∈ S, t i) ≠ 0) :
    0 < ∑ i ∈ S, ∑ j ∈ S, t i * t j * primePrefixReceivingKernel (a i) (a j) d := by
  rw [primeCharge_kernel_eq_scale_form S a t ha had]
  by_contra h
  have hz := le_antisymm (le_of_not_gt h)
    (primeChargeScaleForm_nonneg d (primeChargeScaleDensity S a t))
  have hf := (primeChargeScaleForm_eq_zero_iff d (primeChargeScaleDensity S a t)).mp hz
  apply ht
  rw [← sum_primeChargeScaleDensity S a t ha had]
  exact sum_eq_zero hf

#print axioms primePrefixReceivingKernel_eq_scale_gram
#print axioms primeCharge_kernel_eq_scale_form
#print axioms primeChargeScaleForm_eq_zero_iff
#print axioms primeCharge_kernel_pos_of_charge_ne_zero

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
