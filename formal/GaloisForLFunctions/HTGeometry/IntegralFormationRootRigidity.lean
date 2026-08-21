import GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Integral formation-root rigidity

A formal power series with integer coefficients and constant term one that admits integral `n`-th
roots for an unbounded set of depths is trivial.  The mechanism is the same unbounded-divisibility
selection that annihilates a meromorphic divisor: the first nonvanishing coefficient of the series
is `n` times the corresponding coefficient of the root, so a fixed nonzero integer would have to be
divisible by arbitrarily large integers.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

theorem one_le_order_toNat {K : PowerSeries ℤ} (hK0 : K ≠ 0)
    (hK1 : PowerSeries.constantCoeff K = 0) : 1 ≤ K.order.toNat := by
  by_contra hlt
  have h0 : K.order.toNat = 0 := by omega
  have hne : K.order ≠ ⊤ := by
    rw [Ne, PowerSeries.order_eq_top]
    exact hK0
  have hcoeff := PowerSeries.coeff_order hK0
  rw [h0] at hcoeff
  exact hcoeff (by simpa using hK1)

theorem order_toNat_cast {K : PowerSeries ℤ} (hK0 : K ≠ 0) :
    ((K.order.toNat : ℕ) : ℕ∞) = K.order :=
  ENat.coe_toNat (by rw [Ne, PowerSeries.order_eq_top]; exact hK0)

theorem coeff_pow_eq_zero_of_lt {K : PowerSeries ℤ} (hK0 : K ≠ 0) {i j : ℕ} (_hi : 1 ≤ i)
    (hj : j < i * K.order.toNat) : PowerSeries.coeff j (K ^ i) = 0 := by
  refine PowerSeries.coeff_of_lt_order j ?_
  rw [PowerSeries.order_pow, ← order_toNat_cast hK0, nsmul_eq_mul]
  exact_mod_cast hj

/-- The binomial expansion of a root power, coefficient by coefficient. -/
theorem coeff_add_one_pow {K : PowerSeries ℤ} (n j : ℕ) :
    PowerSeries.coeff j ((K + 1) ^ n)
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * PowerSeries.coeff j (K ^ i) := by
  rw [add_pow]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one]
  rw [show (K ^ i * (n.choose i : PowerSeries ℤ)) = (n.choose i : ℤ) • K ^ i from by
    rw [zsmul_eq_mul]
    push_cast
    ring]
  rw [map_smul, smul_eq_mul]

/-- **Integral formation-root rigidity.**  An integral power series with constant term one that has
integral roots at unboundedly many depths is the constant one. -/
theorem powerSeries_eq_one_of_unbounded_roots {F : PowerSeries ℤ}
    (hF : PowerSeries.constantCoeff F = 1)
    (hroot : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : PowerSeries ℤ,
      PowerSeries.constantCoeff G = 1 ∧ G ^ n = F) :
    F = 1 := by
  by_contra hne
  have hH0 : F - 1 ≠ 0 := sub_ne_zero.2 hne
  set k := (F - 1).order.toNat with hkdef
  have hcoeffk : PowerSeries.coeff k (F - 1) ≠ 0 := PowerSeries.coeff_order hH0
  have hdvd : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (n : ℤ) ∣ PowerSeries.coeff k (F - 1) := by
    intro N
    obtain ⟨n, hn, G, hG1, hGpow⟩ := hroot (max N 1)
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    refine ⟨n, le_trans (le_max_left N 1) hn, ?_⟩
    set K := G - 1 with hKdef
    have hGK : G = K + 1 := by rw [hKdef]; ring
    have hK1 : PowerSeries.constantCoeff K = 0 := by
      rw [hKdef, map_sub, hG1, map_one, sub_self]
    have hK0 : K ≠ 0 := by
      intro h
      refine hne ?_
      rw [← hGpow, hGK, h, zero_add, one_pow]
    set l := K.order.toNat with hldef
    have hl1 : 1 ≤ l := one_le_order_toNat hK0 hK1
    have hcoeffl : PowerSeries.coeff l K ≠ 0 := PowerSeries.coeff_order hK0
    have hkey : ∀ j : ℕ, 1 ≤ j → j ≤ l →
        PowerSeries.coeff j F = (n : ℤ) * PowerSeries.coeff j K := by
      intro j hj1 hjl
      rw [← hGpow, hGK, coeff_add_one_pow]
      rw [Finset.sum_eq_single 1]
      · simp [Nat.choose_one_right]
      · intro i _ hi1
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega), mul_zero]
        · have hi2 : 2 ≤ i := by omega
          rw [coeff_pow_eq_zero_of_lt hK0 hipos ?_, mul_zero]
          calc j ≤ l := hjl
            _ < 2 * l := by omega
            _ ≤ i * l := Nat.mul_le_mul_right l hi2
      · intro hcon
        exact absurd (Finset.mem_range.2 (by omega)) hcon
    have hHj : ∀ j : ℕ, 1 ≤ j → PowerSeries.coeff j (F - 1) = PowerSeries.coeff j F := by
      intro j hj
      rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero]
    have hlow : ∀ j : ℕ, j < l → PowerSeries.coeff j (F - 1) = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, hF, map_one, sub_self]
      · rw [hHj j hj0, hkey j hj0 (le_of_lt hj)]
        have : PowerSeries.coeff j K = 0 := by
          refine PowerSeries.coeff_of_lt_order j ?_
          rw [← order_toNat_cast hK0]
          exact_mod_cast hj
        rw [this, mul_zero]
    have hlval : PowerSeries.coeff l (F - 1) = (n : ℤ) * PowerSeries.coeff l K := by
      rw [hHj l hl1, hkey l hl1 le_rfl]
    have hlne : PowerSeries.coeff l (F - 1) ≠ 0 := by
      rw [hlval]
      exact mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) hcoeffl
    have hkl : k = l := by
      have hge : (l : ℕ∞) ≤ (F - 1).order := by
        refine PowerSeries.le_order _ _ ?_
        intro j hj
        exact hlow j (by exact_mod_cast hj)
      have hle : (F - 1).order ≤ (l : ℕ∞) := PowerSeries.order_le _ hlne
      have : (F - 1).order = (l : ℕ∞) := le_antisymm hle hge
      rw [hkdef, this]
      simp
    rw [hkl, hlval]
    exact ⟨PowerSeries.coeff l K, rfl⟩
  exact hcoeffk (int_eq_zero_of_unbounded_natCast_dvd _ hdvd)

end GaloisForLFunctions.HTGeometry
