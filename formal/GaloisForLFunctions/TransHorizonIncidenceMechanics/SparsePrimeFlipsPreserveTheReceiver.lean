import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnimodularCharacterCompletionsAreParityPartnersOfTheSmoothPower

/-!
# Sparse prime flips preserve the receiver

Let `f, f'` be completely multiplicative of modulus one. Then `f' = g ⋆ f` with `g = f' ⋆ μf`, and
`g(p^k) = f'(p)^{k−1} (f'(p) − f(p))`: the kernel vanishes at every prime power over a prime where `f`
and `f'` agree, and is at most `2` elsewhere. Its Euler factors for `Σ_q |g(q)| q^{-1/2-ε}` are `1` off
the flip set `P` and at most `1 + 8p^{-1/2-ε}` on it, so **if `Σ_{p∈P} p^{-1/2-ε} < ∞` the kernel is
critical Wiener and the two receivers are bounded together**: the receiver at damping `ε` is blind to
parity changes on prime sets of convergent `p^{-1/2-ε}`-mass, the sum over primes of the local
critical-line criterion of single Euler factors.

Consequence for parity pairs: every bounded unimodular completely multiplicative sign `s` must flip
(relative to `1`) a prime set of **divergent** `p^{-1/2-ε}`-mass — otherwise it is in the class of the
smooth power, whose receiver diverges for `ε ≤ 1/2`. The inert primes of a real character (positive
density) are such a set, which is why the character completions are parity partners of the smooth
power.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- A completely multiplicative sign of modulus one, as an arithmetic function. -/
structure UnimodularSign where
  toFun : ℕ → ℝ
  map_zero : toFun 0 = 0
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  abs_eq : ∀ n, n ≠ 0 → |toFun n| = 1

namespace UnimodularSign

variable (f : UnimodularSign)

def af : ArithmeticFunction ℝ := ⟨f.toFun, f.map_zero⟩

theorem map_one : f.toFun 1 = 1 := by
  have h := f.map_mul 1 1
  have h1 := f.abs_eq 1 one_ne_zero
  rw [mul_one] at h
  rcases (_root_.abs_eq zero_le_one).mp h1 with h' | h'
  · exact h'
  · rw [h'] at h; norm_num at h

theorem isMultiplicative : f.af.IsMultiplicative :=
  ⟨f.map_one, fun {m n} _ => f.map_mul m n⟩

/-- `μf`, the Dirichlet inverse of `f`. -/
def moebiusAF : ArithmeticFunction ℝ :=
  ⟨fun n => moebiusReal n * f.toFun n, by simp [f.map_zero]⟩

theorem moebiusAF_mul_af : f.moebiusAF * f.af = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have h : ∀ p ∈ n.divisorsAntidiagonal, f.moebiusAF p.1 * f.af p.2 =
      moebiusReal p.1 * f.toFun n := fun p hp => by
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    simp only [moebiusAF, af, ArithmeticFunction.coe_mk]
    rw [← hpn, f.map_mul]; ring
  rw [sum_congr rfl h, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => moebiusReal a)]
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ n.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) n from hμ]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [f.map_one]
  · simp [hn1]

theorem map_pow (n k : ℕ) : f.toFun (n ^ k) = f.toFun n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, f.map_one]
  | succ k ih => rw [pow_succ, f.map_mul, ih, pow_succ]

end UnimodularSign

/-- The flip kernel `g = f' ⋆ μf` at prime powers: `g(p^{m+1}) = f'(p)^m (f'(p) − f(p))`. -/
theorem flipKernel_apply_prime_pow (f f' : UnimodularSign) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f'.af * f.moebiusAF) (p ^ (m + 1)) = f'.toFun p ^ m * (f'.toFun p - f.toFun p) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f'.af a * f.moebiusAF b),
    Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∀ j ∈ range m, f'.af (p ^ j) * f.moebiusAF (p ^ (m + 1) / p ^ j) = 0 := fun j hj => by
    have hj := mem_range.mp hj
    rw [Nat.pow_div (by omega) hp.pos]
    have hsq : ¬ Squarefree (p ^ (m + 1 - j)) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega
    simp [UnimodularSign.moebiusAF, moebiusReal,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  rw [sum_eq_zero hzero, zero_add, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
    show m + 1 - m = 1 by omega, Nat.sub_self, pow_one, pow_zero]
  simp only [UnimodularSign.af, UnimodularSign.moebiusAF, ArithmeticFunction.coe_mk,
    f'.map_pow, f.map_one, moebiusReal, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_one]
  push_cast; ring

/-- **Sparse flips give critical Wiener kernels.** -/
theorem criticalWiener_flipKernel (f f' : UnimodularSign) {ε : ℝ} (hε : 0 < ε)
    (hsparse : Summable (fun n : ℕ => if n.Prime ∧ f'.toFun n ≠ f.toFun n then
      (n : ℝ) ^ (-(1 / 2 + ε)) else 0)) :
    CriticalWiener (dampedSignWeight ⇑(f'.af * f.moebiusAF) ε) := by
  set g := f'.af * f.moebiusAF
  have hg : g.IsMultiplicative := f'.isMultiplicative.mul ⟨by
    simp [UnimodularSign.moebiusAF, f.map_one, moebiusReal], fun {m n} hmn => by
      simp only [UnimodularSign.moebiusAF, ArithmeticFunction.coe_mk, moebiusReal, f.map_mul,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
      push_cast; ring⟩
  set σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by simp only [σ]; linarith
  let M : ArithmeticFunction ℝ := ⟨fun n => |g n| * (n : ℝ) ^ (-σ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, hg.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, hg.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by simp only [M, ArithmeticFunction.coe_mk]; positivity
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) ∧
      ∑' k : ℕ, M (p ^ k) ≤ Real.exp (if f'.toFun p ≠ f.toFun p then 8 * (p : ℝ) ^ (-σ) else 0) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    set x := (p : ℝ) ^ (-σ) with hxdef
    have hx : ∀ k : ℕ, ((p ^ k : ℕ) : ℝ) ^ (-σ) = x ^ k := fun k => by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hp0.le, mul_comm]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
    have hxsq : x ^ 2 ≤ 1 / 2 := by
      have : x ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
        rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
      rw [this]
      calc (p : ℝ) ^ (-(2 * σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / 2 := by gcongr
    have hx34 : x ≤ 3 / 4 := by nlinarith
    have hxlt : x < 1 := by linarith
    have hfp := f.abs_eq p hp.ne_zero
    have hf'p := f'.abs_eq p hp.ne_zero
    have hMk : ∀ m : ℕ, M (p ^ (m + 1)) = |f'.toFun p - f.toFun p| * x ^ (m + 1) := fun m => by
      simp only [M, ArithmeticFunction.coe_mk]
      rw [flipKernel_apply_prime_pow f f' hp m, hx, abs_mul, abs_pow, hf'p, one_pow, one_mul]
    by_cases hflip : f'.toFun p ≠ f.toFun p
    · rw [if_pos hflip]
      have hd : |f'.toFun p - f.toFun p| ≤ 2 := by
        calc |f'.toFun p - f.toFun p| ≤ |f'.toFun p| + |f.toFun p| := abs_sub _ _
          _ = 2 := by rw [hfp, hf'p]; norm_num
      have hgeo := hasSum_geometric_of_lt_one hx0 hxlt
      -- majorant `[k = 0] + 2 x^{k}` for `k ≥ 1` (bounded by `1 + 2x/(1−x)`)
      have hmaj : HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 0) + 2 * x ^ k -
          (if k = 0 then 2 else 0)) (1 + 2 * (1 - x)⁻¹ - 2) :=
        ((hasSum_ite_eq 0 (1 : ℝ)).add (hgeo.mul_left 2)).sub (hasSum_ite_eq 0 (2 : ℝ))
      have hbound : ∀ k : ℕ, M (p ^ k) ≤ (if k = 0 then (1 : ℝ) else 0) + 2 * x ^ k -
          (if k = 0 then 2 else 0) := fun k => by
        rcases k with _ | m
        · simp [M, hg.map_one]
        · rw [hMk m, if_neg (by omega), if_neg (by omega), zero_add, sub_zero]
          exact mul_le_mul_of_nonneg_right hd (by positivity)
      have hsumM : Summable (fun k : ℕ => M (p ^ k)) :=
        hmaj.summable.of_nonneg_of_le (fun k => hM0 _) hbound
      refine ⟨hsumM, ?_⟩
      have hle := hsumM.tsum_le_tsum hbound hmaj.summable
      rw [hmaj.tsum_eq] at hle
      refine hle.trans ?_
      have h1 : 1 + 2 * (1 - x)⁻¹ - 2 ≤ 8 * x + 1 := by
        have h1x : 0 < 1 - x := by linarith
        rw [show 1 + 2 * (1 - x)⁻¹ - 2 = 2 * (1 - x)⁻¹ - 1 by ring, sub_le_iff_le_add,
          show 8 * x + 1 + 1 = 8 * x + 2 by ring, ← div_eq_mul_inv, div_le_iff₀ h1x]
        nlinarith
      exact h1.trans (Real.add_one_le_exp _)
    · push Not at hflip
      rw [if_neg (not_not.mpr hflip), Real.exp_zero]
      have heq : (fun k : ℕ => M (p ^ k)) = fun k => if k = 0 then 1 else 0 := funext fun k => by
        rcases k with _ | m
        · simp [M, hg.map_one]
        · rw [hMk m, hflip, sub_self, abs_zero, zero_mul, if_neg (by omega)]
      rw [heq]
      exact ⟨summable_of_ne_finset_zero (s := {0}) fun k hk => by simp_all, by rw [tsum_ite_eq]⟩
  set b : ℕ → ℝ := fun n => if n.Prime then
    (if f'.toFun n ≠ f.toFun n then 8 * (n : ℝ) ^ (-σ) else 0) else 0
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> positivity
  have hb : Summable b := (hsparse.mul_left 8).congr fun n => by
    simp only [b, σ]
    by_cases hn : n.Prime <;> by_cases hne : f'.toFun n ≠ f.toFun n <;> simp [hn, hne]
  have hsum := RHTower.pm_summable_of_multiplicative_local_bound M hM hM0
    (fun hp => (hloc hp).1) b hb0 hb (fun {p} hp => by simpa only [b, if_pos hp] using (hloc hp).2)
  unfold CriticalWiener
  refine hsum.congr fun n => ?_
  simp only [M, ArithmeticFunction.coe_mk, dampedSignWeight]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show -σ ≠ 0 by linarith), Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), mul_assoc, ← Real.rpow_add hn0]
    congr 2; simp only [σ]; ring

/-- `f' d^{-ε} = g d^{-ε} ⋆ f d^{-ε}` with the flip kernel `g = f' ⋆ μf`. -/
theorem dampedSign_eq_dirichletConv_flip (f f' : UnimodularSign) (ε : ℝ) (n : ℕ) :
    dampedSignWeight f'.toFun ε n = RHTower.dirichletConv
      (dampedSignWeight ⇑(f'.af * f.moebiusAF) ε) (dampedSignWeight f.toFun ε) n := by
  have hfg : f'.af = (f'.af * f.moebiusAF) * f.af := by
    rw [mul_assoc, f.moebiusAF_mul_af, mul_one]
  have h : f'.toFun n = ((f'.af * f.moebiusAF) * f.af) n := congrArg (fun F => F n) hfg
  rw [dampedSignWeight, h, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (f'.af * f.moebiusAF) a * f.af b),
    RHTower.dirichletConv, sum_mul]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left k hd0]
  simp only [UnimodularSign.af, ArithmeticFunction.coe_mk, dampedSignWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- **Sparse prime flips preserve bounded receivers.** -/
theorem receiverBounded_of_sparse_flip (f f' : UnimodularSign) {ε : ℝ} (hε : 0 < ε)
    (hsparse : Summable (fun n : ℕ => if n.Prime ∧ f'.toFun n ≠ f.toFun n then
      (n : ℝ) ^ (-(1 / 2 + ε)) else 0))
    (h : ReceiverBounded (dampedSignWeight f.toFun ε)) :
    ReceiverBounded (dampedSignWeight f'.toFun ε) := by
  rw [show dampedSignWeight f'.toFun ε = RHTower.dirichletConv
      (dampedSignWeight ⇑(f'.af * f.moebiusAF) ε) (dampedSignWeight f.toFun ε) from
    funext (dampedSign_eq_dirichletConv_flip f f' ε)]
  refine receiverBounded_dirichletConv (criticalWiener_flipKernel f f' hε hsparse) ?_ h
  exact summable_abs_dampedSign_div_of_abs_le (fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f.map_zero]
    · rw [f.abs_eq n hn]) hε

/-- The constant sign `1`. -/
def UnimodularSign.one : UnimodularSign :=
  ⟨fun n => if n = 0 then 0 else 1, by simp, fun a b => by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    simp [ha, hb], fun n hn => by simp [hn]⟩

/-- **A bounded unimodular sign flips a non-sparse prime set.** If `s` is completely multiplicative of
modulus one and the primes with `s(p) = −1` have convergent `p^{-1/2-ε}`-mass, `0 < ε ≤ 1/2`, then the
receiver of `s(d)d^{-ε}` diverges: `s` lies in the class of the smooth power. -/
theorem not_receiverBounded_of_sparse_negative_primes (s : UnimodularSign) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2)
    (hsparse : Summable (fun n : ℕ => if n.Prime ∧ s.toFun n ≠ UnimodularSign.one.toFun n then
      (n : ℝ) ^ (-(1 / 2 + ε)) else 0)) :
    ¬ ReceiverBounded (dampedSignWeight s.toFun ε) := by
  intro hs
  -- flip back to `1`: the sparse set is the same
  have hsparse' : Summable (fun n : ℕ => if n.Prime ∧ UnimodularSign.one.toFun n ≠ s.toFun n then
      (n : ℝ) ^ (-(1 / 2 + ε)) else 0) := hsparse.congr fun n => by
    simp only [ne_comm]
  have h1 := receiverBounded_of_sparse_flip s UnimodularSign.one hε hsparse' hs
  -- the weight of `1` is the smooth power, which diverges
  have hone : dampedSignWeight UnimodularSign.one.toFun ε = dampedSignWeight unitSign ε := funext fun d => by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [dampedSignWeight, UnimodularSign.one, unitSign, Real.zero_rpow (show -ε ≠ 0 by linarith)]
    · simp [dampedSignWeight, UnimodularSign.one, unitSign, hd]
  rw [hone] at h1
  obtain ⟨E, hE⟩ := h1
  have hc0 : ∀ d, 0 ≤ dampedSignWeight unitSign ε d := fun d => by
    unfold dampedSignWeight unitSign; positivity
  have hm := (summable_unit_weight hε).hasSum
  have hdiv := tendsto_weightPronicEnergy_of_drift hc0 hm (K := 1 / 2) (by norm_num) hε2 1
    fun n hn => by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h2n : (0 : ℝ) < 2 * n := by linarith
      have hterm : ∀ d ∈ Ioc n (2 * n), (2 * (n : ℝ)) ^ (-ε) / (2 * n) ≤
          dampedSignWeight unitSign ε d / d := fun d hd => by
        have hd := mem_Ioc.mp hd
        have hd0 : (0 : ℝ) < d := by
          have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
          exact_mod_cast this
        have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
        rw [dampedSignWeight_div hε, unitSign, mul_one, ← Real.rpow_sub_one h2n.ne',
          show -ε - 1 = -(1 + ε) by ring]
        exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
      have hsum := sum_le_sum hterm
      rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul] at hsum
      have : (n : ℝ) * ((2 * (n : ℝ)) ^ (-ε) / (2 * n)) = 1 / 2 * (2 * (n : ℝ)) ^ (-ε) := by
        field_simp
      rw [this] at hsum
      calc 1 / 2 * n * (2 * (n : ℝ)) ^ (-ε) = (n : ℝ) * (1 / 2 * (2 * (n : ℝ)) ^ (-ε)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum hn0.le
  obtain ⟨T, hT⟩ := (hdiv.eventually_gt_atTop E).exists
  exact absurd (hE T) (not_le.mpr hT)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
