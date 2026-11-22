import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Geometric weight of omitted windings

Deleting the multiples of m from a geometric series and counting both
orientations gives a rational function with no zeros in the punctured
open unit disk for m greater than one.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open scoped Classical

def factor (m : ℕ) (q : ℂ) := 2*q*(1-q^(m-1))/((1-q)*(1-q^m))

private def multiples (m : {m : ℕ // 0 < m}) : ℕ ≃ {n : ℕ // m.val ∣ n} :=
  Equiv.ofBijective (fun k : ℕ => (⟨m.val*k,dvd_mul_right _ _⟩ : {n : ℕ // m.val ∣ n}))
    ⟨fun _ _ h => Nat.mul_left_cancel m.property (congrArg Subtype.val h),
     fun ⟨_,k,hk⟩ => ⟨k,Subtype.ext hk.symm⟩⟩

theorem one_sub_pow_ne {q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : 1-q^k ≠ 0 := by
  intro h
  have hp : ‖q^k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hk
  rw [← sub_eq_zero.mp h,norm_one] at hp
  exact hp.false

private theorem missing_sum {q : ℂ} (hq : ‖q‖ < 1) (m : {m : ℕ // 0 < m}) :
    (∑' k : {k : ℕ // ¬m.val ∣ k}, q^k.val) = (1-q)⁻¹-(1-q^m.val)⁻¹ := by
  have hqm : ‖q^m.val‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq m.property.ne'
  have hsub : (∑' k : {k : ℕ // m.val ∣ k}, q^k.val) = (1-q^m.val)⁻¹ := by
    rw [← (multiples m).tsum_eq]
    change (∑' k : ℕ, q^(m.val*k)) = _
    simp only [pow_mul,tsum_geometric_of_norm_lt_one hqm]
  have hs := (summable_geometric_of_norm_lt_one hq).tsum_subtype_add_tsum_subtype_compl {k : ℕ | m.val ∣ k}
  change (∑' k : {k : ℕ // m.val ∣ k}, q^k.val)+(∑' k : {k : ℕ // ¬m.val ∣ k}, q^k.val) = _ at hs
  rw [hsub,tsum_geometric_of_norm_lt_one hq] at hs
  linear_combination hs

/-- Both signs of the nonmultiples give the closed rational factor. -/
theorem twice_missing_sum {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 1 < m) :
    2*(∑' k : {k : ℕ // ¬m ∣ k}, q^k.val) = factor m q := by
  rw [missing_sum hq ⟨m,by omega⟩]
  have hd : 1-q ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  have he : q^(m-1)*q = q^m := by rw [← pow_succ,Nat.sub_add_cancel hm.le]
  rw [← one_div (1-q),← one_div (1-q^m),div_sub_div 1 1 hd (one_sub_pow_ne hq (by omega : m ≠ 0))]
  rw [show 1*(1-q^m)-(1-q)*1 = q*(1-q^(m-1)) by rw [← he]; ring]
  unfold factor
  ring

theorem factor_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (hz : q ≠ 0) {m : ℕ} (hm : 1 < m) : factor m q ≠ 0 := by
  have hd : 1-q ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hz) (one_sub_pow_ne hq (by omega)))
    (mul_ne_zero hd (one_sub_pow_ne hq (by omega)))

#print axioms twice_missing_sum
#print axioms factor_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
