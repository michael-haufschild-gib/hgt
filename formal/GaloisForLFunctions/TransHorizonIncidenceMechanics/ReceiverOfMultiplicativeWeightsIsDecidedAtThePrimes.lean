import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusAndLiouvilleReceiversAreEquivalent
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass

/-!
# The receiver of a multiplicative weight is decided at the primes

Let `f` be multiplicative with `|f(p^k)| ≤ 1`.

* If `f(p) = −1` at every prime, then `f = g ⋆ μ` with `g = f ⋆ 1`, and `g(p) = f(1) + f(p) = 0`,
  `|g(p^k)| ≤ k − 1`. The Euler factors of `Σ_q |g(q)| q^{-1/2-ε}` are `1 + O(p^{-1-2ε})`, so `g d^{-ε}`
  lies in the critical Wiener algebra (Euler-product bound) and **`f(d)d^{-ε}` is paid wherever
  `μ(d)d^{-ε}` is** — in particular at half damping, unconditionally. The values on the higher prime
  powers are invisible to the receiver.
* If `f(p) = +1` at every prime and `f ≥ 0`, then `f ≥ μ²` and the squarefree drift makes the
  receiver diverge at every `ε ≤ 1/2`.

So for multiplicative weights the parity enters the receiver only through the dilations `k ↦ pk` by
primes: the sign of `f` at the primes decides, the higher prime powers do not.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

theorem mul_zeta_apply_prime_pow (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ k) =
      ∑ j ∈ range (k + 1), f (p ^ j) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hp, sum_map]
  rfl

/-- `g = f ⋆ 1` vanishes at the primes and grows at most linearly along prime powers. -/
theorem abs_mul_zeta_apply_prime_pow_le {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 1 ≤ k) :
    |(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ k)| ≤ (k : ℝ) - 1 := by
  rw [mul_zeta_apply_prime_pow f hp]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, hf.map_one, zero_add, pow_one,
    hfp p hp]
  simp only [add_assoc, neg_add_cancel, add_zero]
  calc |∑ j ∈ range m, f (p ^ (j + 1 + 1))| ≤ ∑ j ∈ range m, |f (p ^ (j + 1 + 1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range m, (1 : ℝ) := sum_le_sum fun j _ => hbd _
    _ = ((m + 1 : ℕ) : ℝ) - 1 := by simp

/-- **The kernel `g = f ⋆ 1` is critical Wiener** for every `ε > 0`. -/
theorem criticalWiener_mul_zeta {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε) := by
  set g := f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) with hgdef
  have hg : g.IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  set σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by simp only [σ]; linarith
  -- the multiplicative majorant `|g(n)| n^{-σ}`
  let M : ArithmeticFunction ℝ := ⟨fun n => |g n| * (n : ℝ) ^ (-σ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, hg.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, hg.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by
    simp only [M, ArithmeticFunction.coe_mk]; positivity
  -- local Euler factors
  have hloc : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, M (p ^ k) ≤
      (if k = 0 then 1 else 0) + (k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k -
        (if k = 1 then (p : ℝ) ^ (-σ) else 0) := by
    intro p hp k
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hx : ((p ^ k : ℕ) : ℝ) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ k := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hp0.le, mul_comm]
    have hxpos : 0 ≤ ((p : ℝ) ^ (-σ)) ^ k := by positivity
    simp only [M, ArithmeticFunction.coe_mk]
    rw [hx]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp [hg.map_one]
      · simp only [pow_one, one_ne_zero, if_false, if_true, Nat.cast_one, one_mul, zero_add,
          sub_self]
        rw [show g p = 0 by
          rw [hgdef, ← pow_one p, mul_zeta_apply_prime_pow f hp, Finset.sum_range_succ,
            Finset.sum_range_one, pow_zero, hf.map_one, pow_one, hfp p hp]; ring]
        simp
    · have hbound := abs_mul_zeta_apply_prime_pow_le hf hfp hbd hp (by omega : 1 ≤ k)
      rw [if_neg (by omega), if_neg (by omega), zero_add, sub_zero]
      exact mul_le_mul_of_nonneg_right (by linarith) hxpos
  have hlocsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) ∧
      ∑' k : ℕ, M (p ^ k) ≤ Real.exp (32 * (p : ℝ) ^ (-(1 + 2 * ε))) := by
    intro p hp
    set x := (p : ℝ) ^ (-σ) with hxdef
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx0 : 0 ≤ x := Real.rpow_nonneg (by linarith) _
    have hx2 : x ^ 2 = (p : ℝ) ^ (-(1 + 2 * ε)) := by
      rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1; simp only [σ]; push_cast; ring
    have hxsq : x ^ 2 ≤ 1 / 2 := by
      rw [hx2]
      calc (p : ℝ) ^ (-(1 + 2 * ε)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / 2 := by gcongr
    have hx34 : x ≤ 3 / 4 := by nlinarith
    have hxlt : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
    have hmaj : HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 0) + (k : ℝ) * x ^ k -
        (if k = 1 then x else 0)) (1 + x / (1 - x) ^ 2 - x) :=
      ((hasSum_ite_eq 0 (1 : ℝ)).add (hasSum_coe_mul_geometric_of_norm_lt_one hxlt)).sub
        (hasSum_ite_eq 1 x)
    have hsumM : Summable (fun k : ℕ => M (p ^ k)) :=
      hmaj.summable.of_nonneg_of_le (fun k => hM0 _) (hloc hp)
    refine ⟨hsumM, ?_⟩
    have hle := hsumM.tsum_le_tsum (hloc hp) hmaj.summable
    rw [hmaj.tsum_eq] at hle
    refine hle.trans ?_
    have hpoly : x / (1 - x) ^ 2 - x ≤ 32 * x ^ 2 := by
      have h1x : 0 < 1 - x := by linarith
      have hq : 0 ≤ 32 * x ^ 2 - 63 * x + 30 := by nlinarith [sq_nonneg (x - 3 / 4)]
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg x) hq]
    calc 1 + x / (1 - x) ^ 2 - x ≤ 32 * x ^ 2 + 1 := by linarith
      _ ≤ Real.exp (32 * x ^ 2) := Real.add_one_le_exp _
      _ = Real.exp (32 * (p : ℝ) ^ (-(1 + 2 * ε))) := by rw [hx2]
  -- the Euler-product summability
  set b : ℕ → ℝ := fun n => if n.Prime then 32 * (n : ℝ) ^ (-(1 + 2 * ε)) else 0
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> positivity
  have hb : Summable b :=
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * ε) < -1)).mul_left 32).of_nonneg_of_le
      hb0 fun n => by simp only [b]; split_ifs <;> [exact le_rfl; positivity]
  have hsum := RHTower.pm_summable_of_multiplicative_local_bound M hM hM0
    (fun hp => (hlocsum hp).1) b hb0 hb (fun {p} hp => by
      simpa only [b, if_pos hp] using (hlocsum hp).2)
  unfold CriticalWiener
  refine hsum.congr fun q => ?_
  simp only [M, ArithmeticFunction.coe_mk, dampedSignWeight]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [Real.zero_rpow (show -σ ≠ 0 by linarith), Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq0.le _), mul_assoc, ← Real.rpow_add hq0]
    congr 2; simp only [σ]; ring

/-- `f d^{-ε} = (f ⋆ 1) d^{-ε} ⋆ μ d^{-ε}` pointwise. -/
theorem dampedMultiplicative_eq_dirichletConv (f : ArithmeticFunction ℝ) (ε : ℝ) (n : ℕ) :
    dampedSignWeight ⇑f ε n = RHTower.dirichletConv
      (dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε)
      (pmPowerDampedRealWeight ε) n := by
  have hfg : f = (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
  have h : f n = ((f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) n := congrArg (fun F => F n) hfg
  rw [dampedSignWeight, h, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) a *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b), RHTower.dirichletConv, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hq
  have hq0 : 0 < q := Nat.pos_of_mem_divisors hq
  rw [Nat.mul_div_cancel_left k hq0]
  simp only [dampedSignWeight, pmPowerDampedRealWeight, moebiusReal, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ArithmeticFunction.intCoe_apply]
  ring

theorem summable_abs_dampedSign_div_of_abs_le {s : ℕ → ℝ} (hs : ∀ n, |s n| ≤ 1) {ε : ℝ}
    (hε : 0 < ε) : Summable (fun d : ℕ => |dampedSignWeight s ε d / d|) := by
  refine (Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs d)

/-- **Möbius-like multiplicative weights are paid by the Möbius receiver.** If `f` is
multiplicative, `f(p) = −1` at every prime and `|f| ≤ 1`, then a bounded receiver of `μ(d)d^{-ε}`
gives a bounded receiver of `f(d)d^{-ε}`. -/
theorem receiverBounded_of_primes_neg_one {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (h : ReceiverBounded (pmPowerDampedRealWeight ε)) :
    ReceiverBounded (dampedSignWeight ⇑f ε) := by
  rw [show dampedSignWeight ⇑f ε = RHTower.dirichletConv
      (dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε)
      (pmPowerDampedRealWeight ε) from funext (dampedMultiplicative_eq_dirichletConv f ε)]
  exact receiverBounded_dirichletConv (criticalWiener_mul_zeta hf hfp hbd hε)
    (summable_abs_pmPowerDamped_div hε) h

/-- At half damping, unconditionally: every multiplicative `f` with `f(p) = −1` and `|f| ≤ 1` has
bounded receiver. -/
theorem receiverBounded_half_of_primes_neg_one {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1) :
    ReceiverBounded (dampedSignWeight ⇑f (1 / 2)) :=
  receiverBounded_of_primes_neg_one hf hfp hbd (by norm_num) receiverBounded_pmPowerDamped_half

/-- **Positive weights `+1` at the primes diverge** at every `0 < ε ≤ 1/2`. -/
theorem not_receiverBounded_of_primes_one {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = 1) (hf0 : ∀ n, 0 ≤ f n) (hbd : ∀ n, |f n| ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight ⇑f ε) := by
  have hsq : ∀ n : ℕ, Squarefree n → f n = 1 := fun n hn => by
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      have hk1 : k = 1 := by
        by_contra h
        exact absurd hn (by
          rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega)
      rw [hk1, pow_one, hfp p hp]
    | zero => exact absurd hn not_squarefree_zero
    | one => exact hf.map_one
    | coprime a b ha hb hab iha ihb =>
      rw [hf.map_mul_of_coprime hab, iha (Squarefree.of_mul_left hn),
        ihb (Squarefree.of_mul_right hn), mul_one]
  set c := dampedSignWeight ⇑f ε
  have hc0 : ∀ d, 0 ≤ c d := fun d => mul_nonneg (hf0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hs := (summable_abs_dampedSign_div_of_abs_le hbd hε).of_abs
  rintro ⟨E, hE⟩
  have hdiv := tendsto_weightPronicEnergy_of_drift hc0 hs.hasSum (K := 1 / 16)
    (by norm_num) hε2 100 fun n hn => by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h2n : (0 : ℝ) < 2 * n := by linarith
      have hcount := squarefree_count_dyadic_ge hn
      rw [show n + n = 2 * n by ring] at hcount
      have hterm : ∀ d ∈ Ioc n (2 * n), ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) *
          ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) ≤ c d / d := fun d hd => by
        have hd := mem_Ioc.mp hd
        have hd0 : (0 : ℝ) < d := by
          have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
          exact_mod_cast this
        have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
        have hpow : (2 * (n : ℝ)) ^ (-ε) / (2 * n) ≤ (d : ℝ) ^ (-ε) / d := by
          rw [← Real.rpow_sub_one h2n.ne', ← Real.rpow_sub_one hd0.ne']
          exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
        by_cases hsf : Squarefree d
        · rw [show ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) = 1 by
            have := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf
            rw [← sq_abs]; exact_mod_cast (by rw [this]; norm_num : ((|ArithmeticFunction.moebius d| : ℤ) ^ 2 : ℤ) = 1),
            one_mul]
          simp only [c, dampedSignWeight, hsq d hsf, one_mul]
          exact hpow
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
          simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            zero_mul]
          exact div_nonneg (hc0 d) hd0.le
      have hsum := sum_le_sum hterm
      rw [← sum_mul] at hsum
      have hP : 0 ≤ (2 * (n : ℝ)) ^ (-ε) / (2 * n) := by positivity
      have h1 : (n : ℝ) / 8 * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) ≤
          ∑ d ∈ Ioc n (2 * n), c d / d := (mul_le_mul_of_nonneg_right hcount hP).trans hsum
      have h2 : 1 / 16 * (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) =
          (n : ℝ) * ((n : ℝ) / 8 * ((2 * (n : ℝ)) ^ (-ε) / (2 * n))) := by
        field_simp; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hn0.le
  obtain ⟨T, hT⟩ := (hdiv.eventually_gt_atTop E).exists
  exact absurd (hE T) (not_le.mpr hT)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
