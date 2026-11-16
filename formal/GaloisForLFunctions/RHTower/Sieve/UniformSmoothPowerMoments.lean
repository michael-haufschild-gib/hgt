import GaloisForLFunctions.HTGeometry.Analysis.ReciprocalPowerProducts
import Mathlib.NumberTheory.EulerProduct.Basic

/-!+# Cutoff-independent smooth-number power moments

The reciprocal-power product envelope bounds every finite-prime Euler product.
The smooth-number Euler expansion transfers it to a uniform moment bound, including
the positive contribution of the integer one.
-/

namespace RHTower.Sieve

open Finset
open GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

/-- Prime deletion preserves the rational envelope for reciprocal-power products. -/
theorem primeFiltered_power_product_lt (k : ℕ) (P : Finset ℕ) :
    (∏ p ∈ P.filter Nat.Prime, (1 - 1 / (p : ℝ) ^ (k + 2))⁻¹) <
      (slope k + 1) / slope k := by
  have hinj : Set.InjOn (fun p : ℕ => p - 2) (P.filter Nat.Prime) := by
    intro p hp q hq heq
    have hp2 := (mem_filter.mp hp).2.two_le
    have hq2 := (mem_filter.mp hq).2.two_le
    change p - 2 = q - 2 at heq
    omega
  have h := subproduct_lt_uniform k ((P.filter Nat.Prime).image fun p => p - 2)
  rw [prod_image hinj] at h
  convert h using 1
  apply prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (mem_filter.mp hp).2.two_le]
  norm_num

/-- Every prime cutoff has the same explicit moment envelope. -/
theorem primesBelow_power_product_lt (k N : ℕ) :
    (∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (k + 2))⁻¹) <
      (slope k + 1) / slope k := by
  have hfilter : N.primesBelow.filter Nat.Prime = N.primesBelow :=
    filter_eq_self.mpr fun p hp => (Nat.mem_primesBelow.mp hp).2
  simpa only [hfilter] using primeFiltered_power_product_lt k N.primesBelow

/-- The exact finite Euler expansion for each integral power moment. -/
theorem hasSum_smoothNumbers_inv_pow (k N : ℕ) :
    HasSum (fun n : N.smoothNumbers => 1 / (n : ℝ) ^ (k + 2))
      (∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (k + 2))⁻¹) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => 1 / (n : ℝ) ^ (k + 2)
      map_one' := by simp
      map_mul' := fun m n => by simp only [Nat.cast_mul, mul_pow, one_div, mul_inv] }
  have hf (n : ℕ) : f n = 1 / (n : ℝ) ^ (k + 2) := rfl
  have hp {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [hf, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
  simpa only [hf] using
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp N).2

/-- Smooth-number moments of every integral order at least two are uniformly bounded. -/
theorem smoothNumbers_inv_pow_moment_lt (k N : ℕ) :
    (∑' n : N.smoothNumbers, 1 / (n : ℝ) ^ (k + 2)) <
      (slope k + 1) / slope k := by
  rw [(hasSum_smoothNumbers_inv_pow k N).tsum_eq]
  exact primesBelow_power_product_lt k N

#print axioms primeFiltered_power_product_lt
#print axioms smoothNumbers_inv_pow_moment_lt

end RHTower.Sieve
