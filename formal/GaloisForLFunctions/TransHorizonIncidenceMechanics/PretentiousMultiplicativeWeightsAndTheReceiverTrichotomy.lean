import GaloisForLFunctions.TransHorizonIncidenceMechanics.ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes

/-!
# Pretentious multiplicative weights and the receiver trichotomy

A multiplicative kernel `g` with `g(p) = 0` and `|g(p^k)| ≤ Bk` has Euler factors
`1 + O(B p^{-1-2ε})` for `Σ_q |g(q)| q^{-1/2-ε}`, hence lies in the critical Wiener algebra. Writing
a multiplicative `f` with `|f| ≤ 1` as `f = g ⋆ F` for a model `F` with the same prime values:

* **model `χ`** (a real non-principal character): `g = f ⋆ μχ`, `g(p) = f(p) − χ(p) = 0`,
  `|g(p^k)| = |f(p^k) − χ(p) f(p^{k−1})| ≤ 2`; since `χ(d)d^{-ε}` has bounded receiver at every
  `ε > 0`, **every multiplicative `f` with `f(p) = χ(p)` has bounded receiver at every damping**;
* **model `μ`** (previous module): `f(p) = −1` ⇒ paid wherever `μ(d)d^{-ε}` is, unconditionally at
  `ε = 1/2`;
* **model `1`**: `f ≥ 0`, `f(p) = 1` ⇒ divergent at every `ε ≤ 1/2`.

The receiver classifies multiplicative weights by the values they pretend to at the primes: the
arithmetic enters only through the prime dilations `k ↦ pk`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- **Multiplicative kernels vanishing at the primes are critical Wiener.** -/
theorem criticalWiener_of_multiplicative {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (hgp : ∀ p : ℕ, p.Prime → g p = 0) {B : ℝ} (hB : 0 ≤ B)
    (hgk : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k → |g (p ^ k)| ≤ B * k) {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight ⇑g ε) := by
  set σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by simp only [σ]; linarith
  let M : ArithmeticFunction ℝ := ⟨fun n => |g n| * (n : ℝ) ^ (-σ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, hg.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, hg.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by
    simp only [M, ArithmeticFunction.coe_mk]; positivity
  have hloc : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, M (p ^ k) ≤
      (if k = 0 then 1 else 0) + B * ((k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k) -
        (if k = 1 then B * (p : ℝ) ^ (-σ) else 0) := by
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
          sub_self, hgp p hp, abs_zero, zero_mul, le_refl]
    · rw [if_neg (by omega), if_neg (by omega), zero_add, sub_zero, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hgk p hp k hk) hxpos
  have hlocsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) ∧
      ∑' k : ℕ, M (p ^ k) ≤ Real.exp (32 * B * (p : ℝ) ^ (-(1 + 2 * ε))) := by
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
    have hmaj : HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 0) + B * ((k : ℝ) * x ^ k) -
        (if k = 1 then B * x else 0)) (1 + B * (x / (1 - x) ^ 2) - B * x) :=
      ((hasSum_ite_eq 0 (1 : ℝ)).add ((hasSum_coe_mul_geometric_of_norm_lt_one hxlt).mul_left B)).sub
        (hasSum_ite_eq 1 (B * x))
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
    calc 1 + B * (x / (1 - x) ^ 2) - B * x = 1 + B * (x / (1 - x) ^ 2 - x) := by ring
      _ ≤ 32 * B * x ^ 2 + 1 := by nlinarith [mul_le_mul_of_nonneg_left hpoly hB]
      _ ≤ Real.exp (32 * B * x ^ 2) := Real.add_one_le_exp _
      _ = Real.exp (32 * B * (p : ℝ) ^ (-(1 + 2 * ε))) := by rw [hx2]
  set b : ℕ → ℝ := fun n => if n.Prime then 32 * B * (n : ℝ) ^ (-(1 + 2 * ε)) else 0
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> positivity
  have hb : Summable b :=
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * ε) < -1)).mul_left (32 * B)).of_nonneg_of_le
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

/-! ### The character model -/

variable {q : ℕ} [NeZero q]

/-- A real character as an arithmetic function. -/
def charAF (χ : MulChar (ZMod q) ℤ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else charSign χ n, rfl⟩

/-- `μχ`, the Dirichlet inverse of `χ`. -/
def charMoebiusAF (χ : MulChar (ZMod q) ℤ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else moebiusReal n * charSign χ n, rfl⟩

omit [NeZero q] in
theorem charMoebiusAF_mul_charAF (χ : MulChar (ZMod q) ℤ) :
    charMoebiusAF χ * charAF χ = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have h : ∀ p ∈ n.divisorsAntidiagonal, charMoebiusAF χ p.1 * charAF χ p.2 =
      moebiusReal p.1 * charSign χ n := fun p hp => by
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : p.1 ≠ 0 := fun h => hn (by rw [← hpn, h, zero_mul])
    have h2 : p.2 ≠ 0 := fun h => hn (by rw [← hpn, h, mul_zero])
    simp only [charMoebiusAF, charAF, ArithmeticFunction.coe_mk, if_neg h1, if_neg h2]
    rw [← hpn, charSign_mul]; ring
  rw [sum_congr rfl h, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => moebiusReal a)]
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ n.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) n from hμ]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [charSign_one]
  · simp [hn1]

omit [NeZero q] in
/-- The kernel `g = f ⋆ μχ` at prime powers: `g(p^k) = f(p^k) − χ(p) f(p^{k−1})`. -/
theorem mul_charMoebius_apply_prime_pow (f : ArithmeticFunction ℝ) (χ : MulChar (ZMod q) ℤ)
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f * charMoebiusAF χ) (p ^ (m + 1)) = f (p ^ (m + 1)) - charSign χ p * f (p ^ m) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * charMoebiusAF χ b),
    Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∀ j ∈ range m, f (p ^ j) * charMoebiusAF χ (p ^ (m + 1) / p ^ j) = 0 := fun j hj => by
    have hj := mem_range.mp hj
    rw [Nat.pow_div (by omega) hp.pos]
    have hsq : ¬ Squarefree (p ^ (m + 1 - j)) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega
    simp [charMoebiusAF, moebiusReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  rw [sum_eq_zero hzero, zero_add, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
    show m + 1 - m = 1 by omega, Nat.sub_self, pow_one, pow_zero]
  simp [charMoebiusAF, hp.ne_zero, moebiusReal, ArithmeticFunction.moebius_apply_prime hp,
    charSign_one]
  ring

/-- **Character-pretentious multiplicative weights are paid at every damping.** If `f` is
multiplicative, `|f| ≤ 1` and `f(p) = χ(p)` at every prime for a real non-principal `χ`, then the
receiver of `f(d)d^{-ε}` is bounded for every `ε > 0`. -/
theorem receiverBounded_of_primes_char {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1)
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) (hbd : ∀ n, |f n| ≤ 1)
    (hfp : ∀ p : ℕ, p.Prime → f p = charSign χ p) {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (dampedSignWeight ⇑f ε) := by
  set g := f * charMoebiusAF χ
  have hcm : (charMoebiusAF χ).IsMultiplicative := by
    refine ⟨by simp [charMoebiusAF, charSign_one, moebiusReal], fun {m n} hmn => ?_⟩
    rcases eq_or_ne m 0 with rfl | hm
    · simp [charMoebiusAF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [charMoebiusAF]
    simp only [charMoebiusAF, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn,
      if_neg (mul_ne_zero hm hn), moebiusReal, charSign_mul,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast; ring
  have hg : g.IsMultiplicative := hf.mul hcm
  have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
    have := mul_charMoebius_apply_prime_pow f χ hp 0
    rw [zero_add, pow_one, pow_zero, hf.map_one, mul_one, hfp p hp, sub_self] at this
    exact this
  have hgk : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 2 ≤ k → |g (p ^ k)| ≤ 1 * k := fun p hp k hk => by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [mul_charMoebius_apply_prime_pow f χ hp m]
    calc |f (p ^ (m + 1)) - charSign χ p * f (p ^ m)| ≤
          |f (p ^ (m + 1))| + |charSign χ p| * |f (p ^ m)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 + 1 * 1 := add_le_add (hbd _) (mul_le_mul (abs_charSign_le χ p) (hbd _)
          (abs_nonneg _) zero_le_one)
      _ ≤ 1 * ((m + 1 : ℕ) : ℝ) := by
          have h2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
          push_cast; linarith
  have hW := criticalWiener_of_multiplicative hg hgp zero_le_one hgk hε
  have hfg : f = g * charAF χ := by
    simp only [g]; rw [mul_assoc, charMoebiusAF_mul_charAF, mul_one]
  have hweight : dampedSignWeight ⇑f ε =
      RHTower.dirichletConv (dampedSignWeight ⇑g ε) (dampedSignWeight (charSign χ) ε) := by
    funext n
    have h : f n = (g * charAF χ) n := congrArg (fun F => F n) hfg
    rw [dampedSignWeight, h, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => g a * charAF χ b), RHTower.dirichletConv, sum_mul]
    refine sum_congr rfl fun d hd => ?_
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hk0 : k ≠ 0 := by
      rintro rfl; simp at hd
    rw [Nat.mul_div_cancel_left k hd0]
    simp only [charAF, ArithmeticFunction.coe_mk, if_neg hk0, dampedSignWeight, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  rw [hweight]
  refine receiverBounded_dirichletConv hW
    (summable_abs_dampedSign_div_of_abs_le (abs_charSign_le χ) hε) ?_
  exact exists_weightPronicEnergy_dampedSign_le (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ)

/-- **The receiver trichotomy for multiplicative weights** with `|f| ≤ 1`: pretending to a real
non-principal character at the primes, the receiver is bounded at every damping; pretending to `μ`,
it is bounded at half damping; pretending to `1` with `f ≥ 0`, it diverges at every `ε ≤ 1/2`. -/
theorem receiver_trichotomy {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hbd : ∀ n, |f n| ≤ 1) :
    ((∀ p : ℕ, p.Prime → f p = charSign χ p) → ∀ ε : ℝ, 0 < ε →
        ReceiverBounded (dampedSignWeight ⇑f ε)) ∧
    ((∀ p : ℕ, p.Prime → f p = -1) → ReceiverBounded (dampedSignWeight ⇑f (1 / 2))) ∧
    ((∀ p : ℕ, p.Prime → f p = 1) → (∀ n, 0 ≤ f n) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ¬ ReceiverBounded (dampedSignWeight ⇑f ε)) :=
  ⟨fun hfp _ hε => receiverBounded_of_primes_char hχ hf hbd hfp hε,
    fun hfp => receiverBounded_half_of_primes_neg_one hf hfp hbd,
    fun hfp hf0 _ hε hε2 => not_receiverBounded_of_primes_one hf hfp hf0 hbd hε hε2⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
