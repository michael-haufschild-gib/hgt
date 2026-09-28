import GaloisForLFunctions.RHTower.WeilPositivityHalfPoleRigidity
import Zeta23.FromPNTPlus.MediumPNT

/-!
# Weil positivity forces the prime powers

The von Mangoldt weights carry `log p` at every prime power `p^k`.  The part on the non-prime
prime powers has partial sums `ψ(n) − θ(n) = √n + O(√n e^{−c(log n)^{1/10}})`: exactly at the
`√n` barrier, where the perturbation symbol acquires the boundary pole of `ζ(2s)` at `s = 1/2`.

* **Summability** (`summable_exp_neg_log_rpow_div`).  `∑ e^{−b(log n)^{1/10}}/n < ∞` for `b > 0`
  (Cauchy condensation and `e^z ≥ z^{20}/20!`).
* **Explicit medium PNT** (`exists_psi_sub_bound`).  `|ψ(x) − x| ≤ C x e^{−c(log x)^{1/10}} + K₀`.
* **Prime-power rigidity** (`vonMangoldt_add_primePowerPart_weilPositive_eq_zero`).  Multiplying
  the weights on the non-prime prime powers by `1 + c` keeps Weil positivity only for `c = 0`.
  The remainder after the `√n` main term is summable against `n^{-3/2}` by the two bullets above
  and `ψ(√x) ≤ ψ(x) − θ(x) ≤ ψ(√x) + ψ(x^{1/3}) + ψ(x^{1/5})`.
* **Corollary** (`primeWeights_not_weilPositive`).  The weights `log p` on the primes alone are not
  Weil-positive.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23

/-- `∑_n exp(−b (log n)^{1/10})/n < ∞` for `b > 0`, by Cauchy condensation. -/
theorem summable_exp_neg_log_rpow_div {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℕ => Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) / n := by
  set g : ℕ → ℝ := fun n => Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) / n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → g n ≤ g m := by
    intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn'
    have hl0 : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hrp : Real.log m ^ ((1 : ℝ) / 10) ≤ Real.log n ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hl0 hlog (by norm_num)
    have he : Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) ≤
        Real.exp (-(b * Real.log m ^ ((1 : ℝ) / 10))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    simp only [hg]
    exact div_le_div₀ (Real.exp_pos _).le he (by linarith) hmn'
  rw [← summable_condensed_iff_of_nonneg hg0 hmono]
  set K : ℝ := 4 * ((Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) + 1) with hK
  have hsum : Summable fun k : ℕ => K / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr
      ((Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)).mul_left K)
    refine this.congr fun k => ?_
    push_cast; ring
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  simp only [hg, hcast]
  rw [mul_div_cancel₀ _ h2k.ne', Real.log_pow]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul, zero_add, one_pow, div_one]
    rw [Real.zero_rpow (by norm_num), mul_zero, neg_zero, Real.exp_zero, hK]
    have : 0 ≤ (Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) := by positivity
    linarith
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    set y : ℝ := (k : ℝ) * Real.log 2 with hy
    have hy0 : 0 < y := by positivity
    set z : ℝ := b * y ^ ((1 : ℝ) / 10) with hz
    have hz0 : 0 ≤ z := by positivity
    have hz20 : z ^ 20 = b ^ 20 * y ^ 2 := by
      rw [hz, mul_pow, ← Real.rpow_natCast (y ^ ((1 : ℝ) / 10)), ← Real.rpow_mul hy0.le]
      norm_num
    have hexp := Real.pow_div_factorial_le_exp z hz0 20
    have hbound : Real.exp (-z) ≤ (Nat.factorial 20 : ℝ) / (b ^ 20 * y ^ 2) := by
      rw [Real.exp_neg, ← hz20]
      have hzpos : 0 < z ^ 20 := by rw [hz20]; positivity
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      rw [div_le_iff₀ (by positivity)] at hexp
      rw [div_mul_eq_mul_div, le_div_iff₀ hzpos]
      nlinarith [Real.exp_pos z]
    calc Real.exp (-z) ≤ (Nat.factorial 20 : ℝ) / (b ^ 20 * y ^ 2) := hbound
      _ = (Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) * (1 / (k : ℝ) ^ 2) := by
          rw [hy]; field_simp
      _ ≤ ((Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) + 1) * (4 / ((k : ℝ) + 1) ^ 2) := by
          have h1 : 1 / (k : ℝ) ^ 2 ≤ 4 / ((k : ℝ) + 1) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          have h0 : 0 ≤ (Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) := by positivity
          calc (Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) * (1 / (k : ℝ) ^ 2)
              ≤ (Nat.factorial 20 : ℝ) / (b ^ 20 * Real.log 2 ^ 2) * (4 / ((k : ℝ) + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left h1 h0
            _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K / ((k : ℝ) + 1) ^ 2 := by rw [hK]; ring

/-- An explicit form of the medium prime number theorem: `|ψ(x) − x| ≤ C x e^{−c (log x)^{1/10}}`
for `x ≥ X₀`, and `|ψ(x) − x| ≤ K₀` below `X₀`. -/
theorem exists_psi_sub_bound :
    ∃ c > 0, ∃ C ≥ 0, ∃ K₀ ≥ 0, ∀ x : ℝ, 0 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) + K₀ := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hC
  set X₁ := max X₀ 1 with hX₁
  refine ⟨c, hc, max C 0, le_max_right _ _, (Real.log 4 + 5) * X₁, by positivity, fun x hx => ?_⟩
  have hK0 : 0 ≤ (Real.log 4 + 5) * X₁ := by positivity
  rcases le_or_gt X₁ x with hxX | hxX
  · have h := hX₀ x (le_trans (le_max_left _ _) hxX)
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at h
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hxX
    rw [abs_of_nonneg (by positivity : 0 ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))] at h
    have hm : C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) ≤
        max C 0 * x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hpsi := Chebyshev.psi_le_const_mul_self hx
    have hpsi0 := Chebyshev.psi_nonneg x
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * X₁ := by
      rw [abs_le]; constructor <;> nlinarith
    have : 0 ≤ max C 0 * x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by positivity
    linarith

/-- The prime-power part of the von Mangoldt weights: `Λ(n)` on the non-prime prime powers. -/
def primePowerPart (n : ℕ) : ℝ := if n.Prime then 0 else (Λ n : ℝ)

theorem partialFrom2_primePowerPart (n : ℕ) :
    partialFrom2 primePowerPart n = Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  unfold partialFrom2 primePowerPart
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hsplit : Finset.Ioc 0 n = insert 1 (Finset.Icc 2 n) := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp only [Nat.not_prime_one, not_false_eq_true, if_true, ArithmeticFunction.vonMangoldt_apply_one,
      zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

/-- `|(ψ(n) − θ(n)) − (√n − 1)| ≤ 2ψ(n^{1/3}) + |ψ(√n) − √n| + 1`. -/
theorem abs_psi_sub_theta_sub_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    |(Chebyshev.psi n - Chebyshev.theta n) - (Real.sqrt n - 1)| ≤
      2 * Chebyshev.psi ((n : ℝ) ^ ((1 : ℝ) / 3)) + |Chebyshev.psi (Real.sqrt n) - Real.sqrt n| + 1 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n : ℝ) ^ (2 : ℝ)⁻¹ = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hup := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (n : ℝ)
  have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hn0
  rw [hsq] at hup hlo
  have h35 : Chebyshev.psi ((n : ℝ) ^ (5 : ℝ)⁻¹) ≤ Chebyshev.psi ((n : ℝ) ^ ((1 : ℝ) / 3)) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
  have h3 : (n : ℝ) ^ (3 : ℝ)⁻¹ = (n : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
  rw [h3] at hup hlo
  have hp3 := Chebyshev.psi_nonneg ((n : ℝ) ^ ((1 : ℝ) / 3))
  have hp7 := Chebyshev.psi_nonneg ((n : ℝ) ^ (7 : ℝ)⁻¹)
  have hab := abs_nonneg (Chebyshev.psi (Real.sqrt n) - Real.sqrt n)
  have h1 := le_abs_self (Chebyshev.psi (Real.sqrt n) - Real.sqrt n)
  have h2 := neg_abs_le (Chebyshev.psi (Real.sqrt n) - Real.sqrt n)
  rw [abs_le]; constructor <;> linarith

/-- **Scaling the prime powers breaks Weil positivity.**  If the weights `Λ(n)` on the non-prime prime
powers `p^k`, `k ≥ 2`, are multiplied by `1 + c`, the resulting system is Weil-positive only for
`c = 0`.  The perturbation has partial sums `c(ψ(n) − θ(n)) = c√n + O(√n e^{−c'(log n)^{1/10}})`:
the `√n` main term is the pole of `ζ(2s)` at `s = 1/2`, and the medium prime number theorem makes
the remainder summable against `n^{-3/2}`. -/
theorem vonMangoldt_add_primePowerPart_weilPositive_eq_zero {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + c * primePowerPart n) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) : c = 0 := by
  obtain ⟨c₀, hc₀, C, hC, K₀, hK₀, hbd⟩ := exists_psi_sub_bound
  set b : ℝ := c₀ * ((1 : ℝ) / 2) ^ ((1 : ℝ) / 10) with hb
  have hb0 : 0 < b := by positivity
  have hS1 := summable_exp_neg_log_rpow_div hb0
  have hS2 := summable_growthWeight (θ := (1 : ℝ) / 3) (by norm_num)
  have hS3 := summable_growthWeight (θ := 0) (by norm_num)
  set L4 : ℝ := Real.log 4 + 4 with hL4
  have hL40 : 0 ≤ L4 := by rw [hL4]; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hE : Summable (partialSumWeight fun n => c * primePowerPart n - c * sqrtStep n) := by
    refine Summable.of_nonneg_of_le (partialSumWeight_nonneg _) (fun n => ?_)
      ((((hS2.mul_left (2 * L4)).add (hS1.mul_left C)).add (hS3.mul_left (K₀ + 1))).mul_left |c|)
    unfold partialSumWeight
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [partialFrom2, growthWeight]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hd : 0 < (n : ℝ) * Real.sqrt n := mul_pos hn0 hsqn
      rw [partialFrom2_sub_mul (fun k => c * primePowerPart k) sqrtStep c n]
      have hw : partialFrom2 (fun k => c * primePowerPart k) n = c * partialFrom2 primePowerPart n := by
        unfold partialFrom2; rw [Finset.mul_sum]
      rw [hw, partialFrom2_primePowerPart, partialFrom2_sqrtStep hn, ← mul_sub, abs_mul]
      have hmain := abs_psi_sub_theta_sub_sqrt_le hn
      have hpsi3 : Chebyshev.psi ((n : ℝ) ^ ((1 : ℝ) / 3)) ≤ L4 * (n : ℝ) ^ ((1 : ℝ) / 3) :=
        Chebyshev.psi_le_const_mul_self (by positivity)
      have hpnt := hbd (Real.sqrt n) (Real.sqrt_nonneg _)
      -- the logarithm of `√n`
      have hlogsq : Real.log (Real.sqrt n) ^ ((1 : ℝ) / 10) =
          ((1 : ℝ) / 2) ^ ((1 : ℝ) / 10) * Real.log n ^ ((1 : ℝ) / 10) := by
        rw [Real.log_sqrt hn0.le, div_eq_mul_inv, mul_comm, ← one_div,
          Real.mul_rpow (by norm_num) (Real.log_nonneg (by exact_mod_cast hn))]
      rw [hlogsq, show -c₀ * (((1 : ℝ) / 2) ^ ((1 : ℝ) / 10) * Real.log n ^ ((1 : ℝ) / 10)) =
        -(b * Real.log n ^ ((1 : ℝ) / 10)) by rw [hb]; ring] at hpnt
      have hbound : |Chebyshev.psi n - Chebyshev.theta n - (Real.sqrt n - 1)| ≤
          2 * L4 * (n : ℝ) ^ ((1 : ℝ) / 3) +
            C * Real.sqrt n * Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) + (K₀ + 1) := by
        linarith
      unfold growthWeight
      rw [Real.rpow_zero]
      have e1 : C * Real.sqrt n * Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) /
          ((n : ℝ) * Real.sqrt n) = C * (Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) / n) := by
        field_simp
      calc |c| * |Chebyshev.psi n - Chebyshev.theta n - (Real.sqrt n - 1)| / ((n : ℝ) * Real.sqrt n)
          ≤ |c| * (2 * L4 * (n : ℝ) ^ ((1 : ℝ) / 3) +
              C * Real.sqrt n * Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) + (K₀ + 1)) /
              ((n : ℝ) * Real.sqrt n) := by
            gcongr
        _ = |c| * (2 * L4 * ((n : ℝ) ^ ((1 : ℝ) / 3) / ((n : ℝ) * Real.sqrt n)) +
              C * (Real.exp (-(b * Real.log n ^ ((1 : ℝ) / 10))) / n) +
              (K₀ + 1) * (1 / ((n : ℝ) * Real.sqrt n))) := by
            rw [← e1]; field_simp
  have h := vonMangoldt_add_halfPole_eq_zero (w := fun n => c * primePowerPart n) (κ := c) hE hpos
    (n₀ := 4) (by norm_num)
  have h4 : primePowerPart 4 = Real.log 2 := by
    unfold primePowerPart
    rw [if_neg (by decide)]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    push_cast; ring
  rw [h4] at h
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  exact (mul_eq_zero.mp h).resolve_right hl2

/-- **The prime powers are forced.**  The weights `log p` on the primes alone (the von Mangoldt
weights with every prime power `p^k`, `k ≥ 2`, removed) are not Weil-positive. -/
theorem primeWeights_not_weilPositive :
    ¬ WeilPositive fun n => if n.Prime then (Λ n : ℝ) else 0 := by
  intro hW
  have h := vonMangoldt_add_primePowerPart_weilPositive_eq_zero (c := -1) (fun a ha f hf hfs hp hm => by
    have e : (fun n => (Λ n : ℝ) + -1 * primePowerPart n) =
        fun n => if n.Prime then (Λ n : ℝ) else 0 := by
      funext n; unfold primePowerPart; split_ifs <;> ring
    rw [e]; exact hW a ha f hf hfs hp hm)
  norm_num at h

end RHTower
