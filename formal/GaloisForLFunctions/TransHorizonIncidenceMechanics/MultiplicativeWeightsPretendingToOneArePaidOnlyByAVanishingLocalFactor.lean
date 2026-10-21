import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PretentiousMultiplicativeWeightsAndTheReceiverTrichotomy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# Multiplicative weights pretending to one are paid only by a vanishing local factor

Let `f` be multiplicative with `f(p) = 1` at every prime and `|f| ≤ B`. Then `f = g ⋆ 1` with
`g = f ⋆ μ` multiplicative, `g(p) = 0` and `|g(p^k)| ≤ 2B`, so `g d^{-ε}` is critical Wiener and
`f d^{-ε} = (g d^{-ε}) ⋆ d^{-ε}`. The value of the kernel at the pole is `Σ_n g(n)/n`, an absolutely
convergent Euler product `Π_p λ_p` with local factors

`λ_p = Σ_e g(p^e) p^{-e} = (1 − 1/p) L_p`,   `L_p = Σ_e f(p^e) p^{-e}`,

and `Σ_p |λ_p − 1| < ∞`. An absolutely convergent product of nonzero factors is nonzero, so by the
pole law of critical Wiener kernels:

* **if no local factor `L_p` vanishes, the receiver of `f d^{-ε}` is unbounded at every `ε ≤ 1/2`**;
* if `|f| ≤ 1`, then `L_p ≥ 1 + 1/p − 1/(p(p − 1)) ≥ 1`, so **every multiplicative `f` with `f(p) = 1`
  and `|f| ≤ 1` has unbounded receiver, whatever its signs on the higher prime powers.**

The receiver reads the higher prime powers only through the value at the pole of the local factor
at `p`: the steps `k ↦ pk` along a single prime, summed against `p^{-k}`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-- `(f ⋆ μ)(p^{m+1}) = f(p^{m+1}) − f(p^m)`. -/
theorem mul_moebius_apply_prime_pow (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f * μR) (p ^ (m + 1)) = f (p ^ (m + 1)) - f (p ^ m) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * μR b),
    Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∀ j ∈ range m, f (p ^ j) * μR (p ^ (m + 1) / p ^ j) = 0 := fun j hj => by
    have hj := mem_range.mp hj
    rw [Nat.pow_div (by omega) hp.pos, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [sum_eq_zero hzero, zero_add, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
    show m + 1 - m = 1 by omega, Nat.sub_self, pow_one, pow_zero]
  simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- `d^{-ε}` as the damped zeta function. -/
theorem dampedSignWeight_zeta {ε : ℝ} (hε : ε ≠ 0) :
    dampedSignWeight ⇑((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) ε =
      dampedSignWeight unitSign ε := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dampedSignWeight, unitSign, Real.zero_rpow (neg_ne_zero.mpr hε)]
  · simp [dampedSignWeight, unitSign, hn]

/-- The local factor `L_p = Σ_e f(p^e) p^{-e}` of `f` at the pole. -/
def poleLocalFactor (f : ℕ → ℝ) (p : ℕ) : ℝ := ∑' e : ℕ, f (p ^ e) * ((p : ℝ)⁻¹) ^ e

theorem summable_localFactor {p : ℕ} (hp : p.Prime) {C : ℝ} (c : ℕ → ℝ) (hc : ∀ e, |c e| ≤ C) :
    Summable (fun e : ℕ => c e * ((p : ℝ)⁻¹) ^ e) := by
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  refine ((summable_geometric_of_lt_one hx0 hx1).mul_left C).of_norm_bounded fun e => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 e)]
  exact mul_le_mul_of_nonneg_right (hc e) (pow_nonneg hx0 e)

section LocalFactors

variable {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1)
  {B : ℝ} (hB : ∀ n, |f n| ≤ B)
include hf hfp hB

omit hfp in
theorem abs_mul_moebius_apply_le {p : ℕ} (hp : p.Prime) (e : ℕ) :
    |(f * μR) (p ^ e)| ≤ 2 * B + 1 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  rcases e with _ | m
  · rw [pow_zero, (hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast).map_one, abs_one]
    linarith
  · rw [mul_moebius_apply_prime_pow f hp m]
    calc |f (p ^ (m + 1)) - f (p ^ m)| ≤ |f (p ^ (m + 1))| + |f (p ^ m)| := abs_sub _ _
      _ ≤ 2 * B + 1 := by linarith [hB (p ^ (m + 1)), hB (p ^ m)]

omit hfp in
/-- **The local factor of the kernel**: `λ_p = Σ_e g(p^e) p^{-e} = (1 − 1/p) L_p`. -/
theorem tsum_mul_moebius_localFactor {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, (f * μR) (p ^ e) * ((p : ℝ)⁻¹) ^ e = (1 - (p : ℝ)⁻¹) * poleLocalFactor f p := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  set x := (p : ℝ)⁻¹
  have hfB : ∀ e, |f (p ^ e)| ≤ 2 * B + 1 := fun e => by linarith [hB (p ^ e)]
  have hsf := summable_localFactor hp (fun e => f (p ^ e)) hfB
  have hsg := summable_localFactor hp (fun e => (f * μR) (p ^ e))
    (abs_mul_moebius_apply_le hf hB hp)
  rw [hsg.tsum_eq_zero_add, poleLocalFactor, hsf.tsum_eq_zero_add]
  have hsucc : ∀ e : ℕ, (f * μR) (p ^ (e + 1)) * x ^ (e + 1) =
      f (p ^ (e + 1)) * x ^ (e + 1) - x * (f (p ^ e) * x ^ e) := fun e => by
    rw [mul_moebius_apply_prime_pow f hp e]; ring
  rw [tsum_congr hsucc, ((summable_nat_add_iff 1).mpr hsf).tsum_sub (hsf.mul_left x), tsum_mul_left,
    hsf.tsum_eq_zero_add]
  simp only [pow_zero, mul_one, (hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast).map_one,
    hf.map_one]
  ring

/-- **The pole value is the Euler product of the local factors and does not vanish** unless one of
the local factors `L_p` does. -/
theorem tsum_mul_moebius_div_ne_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hL : ∀ p : ℕ, p.Prime → poleLocalFactor f p ≠ 0) :
    ∑' n : ℕ, (f * μR) n / n ≠ 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  set g := f * μR
  have hg : g.IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
    have := mul_moebius_apply_prime_pow f hp 0
    rwa [zero_add, pow_one, pow_zero, hf.map_one, hfp p hp, sub_self] at this
  have hW := criticalWiener_of_multiplicative hg hgp (B := 2 * B + 1) (by linarith)
    (fun p hp k hk => (abs_mul_moebius_apply_le hf hB hp k).trans
      (le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ k)))) hε
  -- absolute summability of `g(n)/n`
  have hsum : Summable (fun n : ℕ => ‖g n / n‖) := by
    refine hW.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, dampedSignWeight, abs_mul, abs_div, Nat.abs_cast,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_assoc, ← Real.rpow_add (by linarith),
      div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (abs_nonneg _)
  have heuler := EulerProduct.eulerProduct_tprod (f := fun n : ℕ => g n / n)
    (by simp [hg.map_one])
    (fun {m n} hmn => by
      simp only [hg.map_mul_of_coprime hmn, Nat.cast_mul]
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      field_simp)
    hsum (by simp)
  rw [← heuler]
  -- the local factors
  have hloc : ∀ p : Nat.Primes, ∑' e : ℕ, g ((p : ℕ) ^ e) / (((p : ℕ) ^ e : ℕ) : ℝ) =
      1 + ((1 - ((p : ℕ) : ℝ)⁻¹) * poleLocalFactor f p - 1) := fun p => by
    rw [← tsum_mul_moebius_localFactor hf hB p.prop]
    simp only [Nat.cast_pow, div_eq_mul_inv, inv_pow]
    ring
  simp_rw [hloc]
  refine tprod_one_add_ne_zero_of_summable (fun p => ?_) ?_
  · rw [add_sub_cancel]
    refine mul_ne_zero ?_ (hL p p.prop)
    have : ((p : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)
    linarith
  · -- `|λ_p − 1| ≤ 4(2B+1) p^{-2}`
    have hsq : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective Subtype.val_injective
    refine (hsq.mul_left (2 * (2 * B + 1))).of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    have hp := p.prop
    set x := ((p : ℕ) : ℝ)⁻¹
    have hx0 : 0 ≤ x := by positivity
    have hx2 : x ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp.two_le
      simp only [x]; rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    rw [← tsum_mul_moebius_localFactor hf hB hp]
    have hs := summable_localFactor hp (fun e => g ((p : ℕ) ^ e))
      (abs_mul_moebius_apply_le hf hB hp)
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
    simp only [pow_zero, mul_one, hg.map_one, zero_add, pow_one, hgp _ hp, zero_mul, add_sub_cancel_left,
      Real.norm_eq_abs]
    have hs2 : Summable (fun e : ℕ => g ((p : ℕ) ^ (e + 1 + 1)) * x ^ (e + 1 + 1)) :=
      (summable_nat_add_iff 2).mpr hs
    have hgeo : HasSum (fun e : ℕ => (2 * B + 1) * x ^ 2 * x ^ e) ((2 * B + 1) * x ^ 2 * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left _
    have hb := tsum_of_norm_bounded (f := fun e : ℕ => g ((p : ℕ) ^ (e + 1 + 1)) * x ^ (e + 1 + 1))
      hgeo fun e => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 _),
        show x ^ (e + 1 + 1) = x ^ 2 * x ^ e by ring]
      calc |g ((p : ℕ) ^ (e + 1 + 1))| * (x ^ 2 * x ^ e) ≤ (2 * B + 1) * (x ^ 2 * x ^ e) :=
            mul_le_mul_of_nonneg_right (abs_mul_moebius_apply_le hf hB hp _) (by positivity)
        _ = (2 * B + 1) * x ^ 2 * x ^ e := by ring
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    have hinv : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc (2 * B + 1) * x ^ 2 * (1 - x)⁻¹ ≤ (2 * B + 1) * x ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (2 * B + 1) * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by simp only [x]; rw [inv_pow]; ring

/-- **Multiplicative weights pretending to one are paid only by a vanishing local factor.** If `f`
is multiplicative, `f(p) = 1` at every prime, `|f| ≤ B`, and no local factor
`L_p = Σ_e f(p^e) p^{-e}` vanishes, then the receiver of `f(d) d^{-ε}` is unbounded for every
`0 < ε ≤ 1/2`. -/
theorem not_receiverBounded_of_primes_one_of_poleLocalFactor_ne_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hL : ∀ p : ℕ, p.Prime → poleLocalFactor f p ≠ 0) :
    ¬ ReceiverBounded (dampedSignWeight ⇑f ε) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  set g := f * μR
  have hg : g.IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
    have := mul_moebius_apply_prime_pow f hp 0
    rwa [zero_add, pow_one, pow_zero, hf.map_one, hfp p hp, sub_self] at this
  have hW := criticalWiener_of_multiplicative hg hgp (B := 2 * B + 1) (by linarith)
    (fun p hp k hk => (abs_mul_moebius_apply_le hf hB hp k).trans
      (le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ k)))) hε
  have hfg : f = g * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    simp only [g]
    rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  have hfun : dampedSignWeight ⇑f ε =
      RHTower.dirichletConv (dampedSignWeight ⇑g ε) (dampedSignWeight unitSign ε) := by
    funext n
    rw [← dampedSignWeight_zeta hε.ne', ← dampedSignWeight_dirichletConv]
    conv_lhs => rw [hfg]
    simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
  rw [hfun]
  refine not_receiverBounded_dirichletConv_of_drift_critical hε hε2
    (q := dampedSignWeight unitSign ε) (fun d => by simp [dampedSignWeight, unitSign, Real.rpow_nonneg])
    (K := 1) (fun d => by simp [dampedSignWeight, unitSign, abs_of_nonneg, Real.rpow_nonneg])
    (κ := (2 : ℝ) ^ (-(1 + ε))) (by positivity)
    (by filter_upwards [eventually_ge_atTop 1] with n hn using unit_drift hε.le hn) hW ?_
  -- the pole value is `Σ g(n)/n`
  have hpole : ∑' j : ℕ, dampedSignWeight ⇑g ε j * (j : ℝ) ^ (-(1 - ε)) = ∑' n : ℕ, g n / n := by
    refine tsum_congr fun j => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [dampedSignWeight, Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    rw [dampedSignWeight, mul_assoc, ← Real.rpow_add hj0, show -ε + -(1 - ε) = -1 by ring,
      Real.rpow_neg_one, div_eq_mul_inv]
  rw [hpole]
  exact tsum_mul_moebius_div_ne_zero hf hfp hB hε hε2 hL

end LocalFactors

/-- `L_p ≥ 1` when `f(p) = 1` and `|f| ≤ 1`. -/
theorem one_le_poleLocalFactor {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = 1) (hB : ∀ n, |f n| ≤ 1) {p : ℕ} (hp : p.Prime) :
    1 ≤ poleLocalFactor f p := by
  have hs := summable_localFactor hp (fun e => f (p ^ e)) fun e => hB (p ^ e)
  rw [poleLocalFactor, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  set x := (p : ℝ)⁻¹
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    simp only [x]; rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
  simp only [pow_zero, mul_one, hf.map_one, zero_add, pow_one, hfp p hp, one_mul]
  have hgeo : HasSum (fun e : ℕ => x ^ 2 * x ^ e) (x ^ 2 * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded (f := fun e : ℕ => f (p ^ (e + 1 + 1)) * x ^ (e + 1 + 1))
    hgeo fun e => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx0 _),
      show x ^ (e + 1 + 1) = x ^ 2 * x ^ e by ring]
    exact mul_le_of_le_one_left (by positivity) (hB _)
  rw [Real.norm_eq_abs] at hb
  have hR := neg_abs_le (∑' e : ℕ, f (p ^ (e + 1 + 1)) * x ^ (e + 1 + 1))
  have hq : x ^ 2 * (1 - x)⁻¹ ≤ x := by
    rw [mul_inv_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **No sign pattern on the higher prime powers pays a weight pretending to one.** Every
multiplicative `f` with `f(p) = 1` at all primes and `|f| ≤ 1` has unbounded receiver at every
`0 < ε ≤ 1/2`. -/
theorem not_receiverBounded_of_primes_one_of_abs_le_one {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfp : ∀ p : ℕ, p.Prime → f p = 1) (hB : ∀ n, |f n| ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑f ε) :=
  not_receiverBounded_of_primes_one_of_poleLocalFactor_ne_zero hf hfp hB hε hε2 fun _ hp =>
    (lt_of_lt_of_le one_pos (one_le_poleLocalFactor hf hfp hB hp)).ne'

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
