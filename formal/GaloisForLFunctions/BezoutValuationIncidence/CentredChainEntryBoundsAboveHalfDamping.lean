import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveDampingOne

/-!
# Entry bounds for the centred damping chain above half damping

The centred chain `C_η` has entries `C(N, K) = (K/N)(K^{−η} G − (K+1)^{−η} G')` for `K ≤ N`
(`SignedArithmeticEnergyIncidence.centeredRow_eq`), with `a = ⌊N/K⌋`, `a' = ⌊N/(K+1)⌋`,
`G = ρ(a − N/K) + P(a)`, `G' = ρ(a' − N/(K+1)) + P(a')`, and `P` the centred damped divisor
prefix. Above damping one `P` is bounded; for `½ < η ≤ 1` this module proves the three source laws
that replace boundedness, with `η' = 1/8 + 3η/4 ∈ (½, η]` and `β = 1 − η' < ½`:

* `abs_centeredPrefix_le_rpow` (growth): `|P(m)| ≤ c_P m^β`;
* `abs_centeredPrefix_sub_le_mul` (increments): `|P(a) − P(a')| ≤ (1 + ρ)(a − a')`;
* `abs_centeredPrefix_sub_le_short` (short intervals): `|P(a) − P(a')| ≤ c_P L^β + J(a', a)`,
  `L = a − a'`, where `J(a', a) = Σ_{a' < j ≤ a} Σ_{d ∣ j, d > L} d^{−η}` collects the large divisors.
  Small divisors `d ≤ L` see the interval as `L/d` up to one, and the tail of `1/ζ(1+η)` beyond
  `L` costs `L^{1−η}/η`.

They give three entry bounds (`abs_centeredRow_le_large`, `abs_centeredRow_le_small`,
`abs_centeredRow_le_entrance`), sized for a Schur test with weight `n^{−1/2}`
(`TheCentredChainIsBoundedAboveHalfDamping`). No cancellation of `μ` is used: only sizes and the
divisor structure of short intervals.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Power sums -/

/-- Head sums: `Σ_{1 ≤ d ≤ m} d^{−s} ≤ m^{1−s}/(1 − s)` for `0 ≤ s < 1`. -/
theorem sum_Icc_rpow_neg_le_div {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-s) ≤ (m : ℝ) ^ (1 - s) / (1 - s) := by
  have hp : 0 < 1 - s := by linarith
  induction m with
  | zero => simp [Real.zero_rpow hp.ne']
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hB := Real.rpow_one_add_le_one_add_mul_self (s := -1 / ((m : ℝ) + 1))
      (by rw [neg_div, neg_le_neg_iff, div_le_one hx]; linarith) (p := 1 - s) hp.le (by linarith)
    have hm : (m : ℝ) = ((m : ℝ) + 1) * (1 + -1 / ((m : ℝ) + 1)) := by field_simp; ring
    have hnn : 0 ≤ 1 + -1 / ((m : ℝ) + 1) := by
      rw [neg_div, ← sub_eq_add_neg, sub_nonneg, div_le_one hx]; linarith
    have hmr : (m : ℝ) ^ (1 - s) =
        ((m : ℝ) + 1) ^ (1 - s) * (1 + -1 / ((m : ℝ) + 1)) ^ (1 - s) := by
      conv_lhs => rw [hm]
      exact Real.mul_rpow hx.le hnn
    have hxs : ((m : ℝ) + 1) ^ (1 - s) * (1 / ((m : ℝ) + 1)) = ((m : ℝ) + 1) ^ (-s) := by
      rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_neg hx.le]
      field_simp
    have hpos : 0 ≤ ((m : ℝ) + 1) ^ (1 - s) := Real.rpow_nonneg hx.le _
    have key : (m : ℝ) ^ (1 - s) + (1 - s) * ((m : ℝ) + 1) ^ (-s) ≤ ((m : ℝ) + 1) ^ (1 - s) := by
      rw [hmr, ← hxs]
      have := mul_le_mul_of_nonneg_left hB hpos
      nlinarith
    push_cast
    rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]
    linarith

/-- Telescoped tails: `Σ_{i < n} (X + 1 + i)^{−s} ≤ X^{1−s}/(s − 1)` for `s > 1`, `X > 0`. -/
theorem sum_range_rpow_neg_tail_le {s X : ℝ} (hs : 1 < s) (hX : 0 < X) (n : ℕ) :
    ∑ i ∈ range n, (X + 1 + i) ^ (-s) ≤ X ^ (1 - s) / (s - 1) := by
  have hr : 0 < s - 1 := by linarith
  have key : ∀ n : ℕ, ∑ i ∈ range n, (X + 1 + i) ^ (-s) ≤
      (X ^ (1 - s) - (X + n) ^ (1 - s)) / (s - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hxn : 0 < X + n := by positivity
      have hstep := le_rpow_neg_sub_rpow_neg' hxn (s := s - 1) (b := X + n + 1)
        (by linarith) hr.le
      have e1 : (X + n + 1) ^ (-(s - 1 + 1)) = (X + 1 + n) ^ (-s) := by
        rw [show -(s - 1 + 1) = -s by ring, show X + n + 1 = X + 1 + n by ring]
      have e2 : (X + n) ^ (-(s - 1)) = (X + n) ^ (1 - s) := by ring_nf
      have e3 : (X + n + 1) ^ (-(s - 1)) = (X + ((n + 1 : ℕ) : ℝ)) ^ (1 - s) := by
        push_cast; ring_nf
      rw [e1, e2, e3] at hstep
      rw [div_le_div_iff_of_pos_right hr] at *
      rw [div_le_iff₀ hr] at ih ⊢
      nlinarith
  refine (key n).trans ?_
  have : 0 ≤ (X + n) ^ (1 - s) := Real.rpow_nonneg (by positivity) _
  exact div_le_div_of_nonneg_right (by linarith) hr.le
where
  le_rpow_neg_sub_rpow_neg' {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) :
      s * (b - a) * b ^ (-(s + 1)) ≤ a ^ (-s) - b ^ (-s) := by
    have hb : 0 < b := ha.trans_le hab
    have hlog : 1 - a / b ≤ Real.log (b / a) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
      rwa [inv_div] at h
    have hexp : 1 + s * Real.log (b / a) ≤ (b / a) ^ s := by
      rw [Real.rpow_def_of_pos (div_pos hb ha)]
      linarith [Real.add_one_le_exp (Real.log (b / a) * s), mul_comm s (Real.log (b / a))]
    have has : a ^ (-s) = b ^ (-s) * (b / a) ^ s := by
      rw [Real.div_rpow hb.le ha.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le]
      have : b ^ s ≠ 0 := (Real.rpow_pos_of_pos hb s).ne'
      field_simp
    have hbs : b ^ (-(s + 1)) = b ^ (-s) / b := by
      rw [show -(s + 1) = -s - 1 by ring, Real.rpow_sub_one hb.ne']
    rw [has, hbs]
    have hpos : 0 < b ^ (-s) := Real.rpow_pos_of_pos hb _
    have key : s * (b - a) / b ≤ (b / a) ^ s - 1 := by
      have : s * (b - a) / b = s * (1 - a / b) := by field_simp
      rw [this]
      nlinarith
    calc s * (b - a) * (b ^ (-s) / b) = b ^ (-s) * (s * (b - a) / b) := by ring
      _ ≤ b ^ (-s) * ((b / a) ^ s - 1) := mul_le_mul_of_nonneg_left key hpos.le
      _ = _ := by ring

/-- `x^{−s} − (x+1)^{−s} ≤ s x^{−s−1}` for `x > 0`, `s ≥ 0`. -/
theorem rpow_neg_sub_rpow_neg_succ_le' {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    x ^ (-s) - (x + 1) ^ (-s) ≤ s * x ^ (-s - 1) := by
  have hb : 0 < x + 1 := by linarith
  have hlog : 1 - (x + 1) / x ≤ Real.log (x / (x + 1)) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hb)
    rwa [inv_div] at h
  have hexp : 1 + s * Real.log (x / (x + 1)) ≤ (x / (x + 1)) ^ s := by
    rw [Real.rpow_def_of_pos (div_pos hx hb)]
    linarith [Real.add_one_le_exp (Real.log (x / (x + 1)) * s),
      mul_comm s (Real.log (x / (x + 1)))]
  have hbs : (x + 1) ^ (-s) = x ^ (-s) * (x / (x + 1)) ^ s := by
    rw [Real.div_rpow hx.le hb.le, Real.rpow_neg hx.le, Real.rpow_neg hb.le]
    have : x ^ s ≠ 0 := (Real.rpow_pos_of_pos hx s).ne'
    field_simp
  have has : x ^ (-s - 1) = x ^ (-s) / x := Real.rpow_sub_one hx.ne' _
  rw [hbs, has]
  have hpos : 0 < x ^ (-s) := Real.rpow_pos_of_pos hx _
  have key : 1 - (x / (x + 1)) ^ s ≤ s / x := by
    have : (x + 1) / x = 1 + 1 / x := by field_simp
    rw [this] at hlog
    nlinarith
  calc x ^ (-s) - x ^ (-s) * (x / (x + 1)) ^ s = x ^ (-s) * (1 - (x / (x + 1)) ^ s) := by ring
    _ ≤ x ^ (-s) * (s / x) := mul_le_mul_of_nonneg_left key hpos.le
    _ = s * (x ^ (-s) / x) := by ring

/-! ### Exponents of the source -/

/-- The source exponent `η' = 1/8 + 3η/4`. On `(½, 1]` it lies in `(½, η]` and below one. -/
def chainSourceExponent (η : ℝ) : ℝ := 1 / 8 + 3 * η / 4

/-- The source constant `c_P = 1 + 1/(1 − η') + 1/η'`. -/
def chainSourceConstant (η : ℝ) : ℝ :=
  1 + 1 / (1 - chainSourceExponent η) + 1 / chainSourceExponent η

section Exponents

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

theorem chainSourceExponent_gt_half : 1 / 2 < chainSourceExponent η := by
  unfold chainSourceExponent; linarith

theorem chainSourceExponent_le : chainSourceExponent η ≤ η := by
  unfold chainSourceExponent; linarith

theorem chainSourceExponent_lt_one : chainSourceExponent η < 1 := by
  unfold chainSourceExponent; linarith

theorem chainSourceConstant_pos : 0 < chainSourceConstant η := by
  have := chainSourceExponent_gt_half h1 h2
  have := chainSourceExponent_lt_one h1 h2
  unfold chainSourceConstant
  have : 0 < 1 / (1 - chainSourceExponent η) := by apply div_pos one_pos; linarith
  have : 0 < 1 / chainSourceExponent η := by apply div_pos one_pos; linarith
  linarith

end Exponents

/-! ### The source: growth, increments, short intervals -/

private theorem abs_moebius_real_le (d : ℕ) : |(moebius d : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one

/-- The tail of `1/ζ(1+η)` beyond `m`: `|Σ_{d > m} μ(d) d^{−1−η}| ≤ m^{−η}/η`. -/
theorem abs_densityTail_le {η : ℝ} (hη : 0 < η) {m : ℕ} (hm : 1 ≤ m) :
    |∑' j : ℕ, (moebius (j + (m + 1)) : ℝ) * ((j + (m + 1) : ℕ) : ℝ) ^ (-(1 + η))| ≤
      (m : ℝ) ^ (-η) / η := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : ∀ j : ℕ, ‖(moebius (j + (m + 1)) : ℝ) * ((j + (m + 1) : ℕ) : ℝ) ^ (-(1 + η))‖ ≤
      ((m : ℝ) + 1 + j) ^ (-(1 + η)) := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have : ((j + (m + 1) : ℕ) : ℝ) = (m : ℝ) + 1 + j := by push_cast; ring
    rw [this]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (abs_moebius_real_le _)
  have hsg : Summable fun j : ℕ => ((m : ℝ) + 1 + j) ^ (-(1 + η)) := by
    have := (summable_nat_add_iff (m + 1)).2 (Real.summable_nat_rpow.2 (by linarith : -(1 + η) < -1))
    refine this.congr fun j => ?_
    push_cast; ring_nf
  have hsf := Summable.of_norm_bounded hsg hb
  have htail : ∑' j : ℕ, ((m : ℝ) + 1 + j) ^ (-(1 + η)) ≤ (m : ℝ) ^ (-η) / η := by
    refine Real.tsum_le_of_sum_range_le (fun j => Real.rpow_nonneg (by positivity) _) fun n => ?_
    have := sum_range_rpow_neg_tail_le (s := 1 + η) (by linarith) hm0 n
    rwa [show 1 - (1 + η) = -η by ring, show 1 + η - 1 = η by ring] at this
  exact (norm_tsum_le_tsum_norm hsf.norm).trans ((hsf.norm.tsum_le_tsum hb hsg).trans htail)

/-- The density split at `m`: `ρ = Σ_{d ≤ m} μ(d) d^{−1−η} + Σ_{d > m} μ(d) d^{−1−η}`. -/
theorem density_re_split {η : ℝ} (hη : 0 < η) (m : ℕ) :
    (pmPowerDampedDivisorDensity η).re =
      ∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) +
        ∑' j : ℕ, (moebius (j + (m + 1)) : ℝ) * ((j + (m + 1) : ℕ) : ℝ) ^ (-(1 + η)) := by
  set f : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (g := fun d : ℕ => (d : ℝ) ^ (-(1 + η))) ?_ fun d => ?_
    · exact Real.summable_nat_rpow.2 (by linarith)
    · rw [Real.norm_eq_abs, hfdef, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (abs_moebius_real_le d)
  rw [density_re_eq_tsum hη, ← hfs.sum_add_tsum_nat_add (m + 1)]
  congr 1
  rw [range_eq_Ico, show Ico 0 (m + 1) = insert 0 (Icc 1 m) by
    ext d; simp only [mem_Ico, mem_insert, mem_Icc]; omega, sum_insert (by simp), hf0, zero_add]

section Source

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

private theorem sum_Icc_rpow_neg_le_source (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-η) ≤
      (1 / (1 - chainSourceExponent η)) * (m : ℝ) ^ (1 - chainSourceExponent η) := by
  have he1 := chainSourceExponent_gt_half h1 h2
  have he2 := chainSourceExponent_le h1 h2
  have he3 := chainSourceExponent_lt_one h1 h2
  calc ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-η)
      ≤ ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-chainSourceExponent η) := sum_le_sum fun d hd =>
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_Icc.mp hd).1) (by linarith)
    _ ≤ (m : ℝ) ^ (1 - chainSourceExponent η) / (1 - chainSourceExponent η) :=
        sum_Icc_rpow_neg_le_div (by linarith) he3 m
    _ = _ := by ring

private theorem tail_term_le (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * ((m : ℝ) ^ (-η) / η) ≤
      (1 / chainSourceExponent η) * (m : ℝ) ^ (1 - chainSourceExponent η) := by
  have he1 := chainSourceExponent_gt_half h1 h2
  have he2 := chainSourceExponent_le h1 h2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hη : 0 < η := by linarith
  have e : (m : ℝ) * ((m : ℝ) ^ (-η) / η) = (m : ℝ) ^ (1 - η) / η := by
    rw [Real.rpow_sub hm0, Real.rpow_one, Real.rpow_neg hm0.le]; field_simp
  rw [e]
  have hp1 : (m : ℝ) ^ (1 - η) ≤ (m : ℝ) ^ (1 - chainSourceExponent η) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hp0 : 0 ≤ (m : ℝ) ^ (1 - η) := Real.rpow_nonneg hm0.le _
  calc (m : ℝ) ^ (1 - η) / η ≤ (m : ℝ) ^ (1 - chainSourceExponent η) / chainSourceExponent η :=
        div_le_div₀ (Real.rpow_nonneg hm0.le _) hp1 (by linarith) he2
    _ = _ := by ring

/-- **Growth of the source.** `|P(m)| ≤ c_P m^{1−η'}` for `m ≥ 1`. -/
theorem abs_centeredPrefix_le_rpow {m : ℕ} (hm : 1 ≤ m) :
    |pmPowerDampedCenteredDivisorPrefix η m| ≤
      chainSourceConstant η * (m : ℝ) ^ (1 - chainSourceExponent η) := by
  have hη : 0 < η := by linarith
  set T := ∑' j : ℕ, (moebius (j + (m + 1)) : ℝ) * ((j + (m + 1) : ℕ) : ℝ) ^ (-(1 + η))
  have hsplit : pmPowerDampedCenteredDivisorPrefix η m =
      ∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) * (((m / d : ℕ) : ℝ) - (m : ℝ) / d) -
        T * m := by
    rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum, density_re_split hη m, add_mul, sum_mul,
      ← sub_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Icc.1 hd).1; positivity
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0]
    field_simp
    ring
  have hhead : |∑ d ∈ Icc 1 m, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
      (((m / d : ℕ) : ℝ) - (m : ℝ) / d)| ≤ ∑ d ∈ Icc 1 m, (d : ℝ) ^ (-η) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hfl := abs_natDiv_sub_div_le m d (mem_Icc.mp hd).1
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) * |((m / d : ℕ) : ℝ) - (m : ℝ) / d|
        ≤ 1 * (d : ℝ) ^ (-η) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebius_real_le d)
            (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hfl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have htail : |T * m| ≤ (m : ℝ) * ((m : ℝ) ^ (-η) / η) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m), mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_densityTail_le hη hm) (Nat.cast_nonneg m)
  have hA := sum_Icc_rpow_neg_le_source h1 h2 m hm
  have hB := tail_term_le h1 h2 m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 - chainSourceExponent η) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by linarith [chainSourceExponent_lt_one h1 h2])
  rw [hsplit]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add hhead htail
    _ ≤ (1 / (1 - chainSourceExponent η)) * (m : ℝ) ^ (1 - chainSourceExponent η) +
          (1 / chainSourceExponent η) * (m : ℝ) ^ (1 - chainSourceExponent η) := add_le_add hA hB
    _ ≤ chainSourceConstant η * (m : ℝ) ^ (1 - chainSourceExponent η) := by
        unfold chainSourceConstant; nlinarith

end Source

/-- The centred prefix on an interval: `P(a) − P(a') = Σ_{a' < j ≤ a} (τ(j) − ρ)`. -/
theorem centeredPrefix_sub_eq (η : ℝ) {a' a : ℕ} (h : a' ≤ a) :
    pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a' =
      ∑ j ∈ Ioc a' a, pmPowerDampedCenteredDivisorCoeff η j := by
  unfold pmPowerDampedCenteredDivisorPrefix
  have e : ∀ x : ℕ, Icc 1 x = Ioc 0 x := fun x => by ext j; simp only [mem_Icc, mem_Ioc]; omega
  rw [e, e, ← sum_Ioc_consecutive _ (Nat.zero_le a') h, add_sub_cancel_left]

/-- **Increments of the source.** `|P(a) − P(a')| ≤ (1 + ρ)(a − a')`. -/
theorem abs_centeredPrefix_sub_le_mul {η : ℝ} (hη : 0 < η) {a' a : ℕ} (h : a' ≤ a) :
    |pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a'| ≤
      (1 + (pmPowerDampedDivisorDensity η).re) * ((a - a' : ℕ) : ℝ) := by
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  rw [centeredPrefix_sub_eq η h]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Ioc a' a, |pmPowerDampedCenteredDivisorCoeff η j|
      ≤ ∑ _j ∈ Ioc a' a, (1 + (pmPowerDampedDivisorDensity η).re) := sum_le_sum fun j _ => by
        unfold pmPowerDampedCenteredDivisorCoeff
        have h0 := pmPowerDampedDivisorCoeff_nonneg hη.le j
        have h1 := pmPowerDampedDivisorCoeff_le_one hη.le j
        rw [abs_le]; constructor <;> linarith
    _ = _ := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_comm]

/-- Multiples of `d` in `(a', a]`. -/
theorem card_filter_dvd_Ioc (d : ℕ) {a' a : ℕ} (h : a' ≤ a) :
    #{j ∈ Ioc a' a | d ∣ j} = a / d - a' / d := by
  have hu : Ioc 0 a = Ioc 0 a' ∪ Ioc a' a := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le a') h).symm
  have hd : Disjoint (Ioc 0 a') (Ioc a' a) := Ioc_disjoint_Ioc_of_le le_rfl
  have hc : #{j ∈ Ioc 0 a | d ∣ j} = #{j ∈ Ioc 0 a' | d ∣ j} + #{j ∈ Ioc a' a | d ∣ j} := by
    rw [hu, filter_union, card_union_of_disjoint (disjoint_filter_filter hd)]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hc
  omega

/-- The count of multiples differs from the length by less than one. -/
theorem abs_div_sub_div_sub_le (d : ℕ) (hd : 1 ≤ d) {a' a : ℕ} (h : a' ≤ a) :
    |(((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - ((a - a' : ℕ) : ℝ) / d| ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha := Nat.div_add_mod a d
  have ha' := Nat.div_add_mod a' d
  have hr : ((a % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt a hd
  have hr' : ((a' % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt a' hd
  have haR : (d : ℝ) * ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) = a := by exact_mod_cast ha
  have haR' : (d : ℝ) * ((a' / d : ℕ) : ℝ) + ((a' % d : ℕ) : ℝ) = a' := by exact_mod_cast ha'
  have hsub : ((a - a' : ℕ) : ℝ) = (a : ℝ) - a' := by rw [Nat.cast_sub h]
  have e : (((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - ((a - a' : ℕ) : ℝ) / d =
      (((a' % d : ℕ) : ℝ) - ((a % d : ℕ) : ℝ)) / d := by
    rw [hsub]; field_simp; linarith
  rw [e, abs_div, abs_of_pos hd0, div_le_one hd0, abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (a % d), Nat.cast_nonneg (α := ℝ) (a' % d)]

/-- The large-divisor sum `J(a', a) = Σ_{a' < j ≤ a} Σ_{d ∣ j, d > a − a'} d^{−η}`. -/
def largeDivisorSum (η : ℝ) (a' a : ℕ) : ℝ :=
  ∑ j ∈ Ioc a' a, ∑ d ∈ j.divisors with a - a' < d, (d : ℝ) ^ (-η)

theorem largeDivisorSum_nonneg (η : ℝ) (a' a : ℕ) : 0 ≤ largeDivisorSum η a' a :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

section ShortInterval

variable {η : ℝ} (h1 : 1 / 2 < η) (h2 : η ≤ 1)
include h1 h2

/-- **The source on short intervals.** For `a' < a`, `L = a − a'`:
`|P(a) − P(a')| ≤ c_P L^{1−η'} + J(a', a)`. -/
theorem abs_centeredPrefix_sub_le_short {a' a : ℕ} (h : a' < a) :
    |pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a'| ≤
      chainSourceConstant η * ((a - a' : ℕ) : ℝ) ^ (1 - chainSourceExponent η) +
        largeDivisorSum η a' a := by
  have hη : 0 < η := by linarith
  set L := a - a' with hL
  have hL1 : 1 ≤ L := by omega
  set ρ := (pmPowerDampedDivisorDensity η).re with hρdef
  set g : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-η) with hg
  set T := ∑' j : ℕ, (moebius (j + (L + 1)) : ℝ) * ((j + (L + 1) : ℕ) : ℝ) ^ (-(1 + η))
  -- split each `τ(j)` into divisors `≤ L` and `> L`
  have hτ : ∀ j : ℕ, pmPowerDampedDivisorCoeff η j =
      ∑ d ∈ j.divisors with d ≤ L, g d + ∑ d ∈ j.divisors with L < d, g d := by
    intro j
    rw [pmPowerDampedDivisorCoeff, ← sum_filter_add_sum_filter_not j.divisors (· ≤ L)]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext d; simp only [mem_filter, not_le]
  -- the small divisors count multiples
  have hsmall : ∑ j ∈ Ioc a' a, ∑ d ∈ j.divisors with d ≤ L, g d =
      ∑ d ∈ Icc 1 L, g d * (((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) := by
    rw [sum_comm' (t' := fun d => {j ∈ Ioc a' a | d ∣ j}) (s' := Icc 1 L)]
    · refine sum_congr rfl fun d hd => ?_
      rw [sum_const, card_filter_dvd_Ioc d h.le, nsmul_eq_mul, Nat.cast_sub
        (Nat.div_le_div_right h.le), mul_comm]
    · intro j d
      simp only [mem_Ioc, mem_filter, Nat.mem_divisors, mem_Icc]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, ⟨hdj, -⟩, hdL⟩
        exact ⟨⟨⟨hj1, hj2⟩, hdj⟩, Nat.pos_of_dvd_of_pos hdj (by omega), hdL⟩
      · rintro ⟨⟨⟨hj1, hj2⟩, hdj⟩, -, hdL⟩
        exact ⟨⟨hj1, hj2⟩, ⟨hdj, by omega⟩, hdL⟩
  -- the density over the interval
  have hρL : ρ * (L : ℝ) = ∑ d ∈ Icc 1 L, g d * ((L : ℝ) / d) + T * L := by
    rw [hρdef, density_re_split hη L, add_mul, sum_mul]
    congr 1
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Icc.1 hd).1; positivity
    simp only [hg]
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0]
    field_simp
  have hdiff : pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a' =
      ∑ d ∈ Icc 1 L, g d * ((((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - (L : ℝ) / d) - T * L +
        ∑ j ∈ Ioc a' a, ∑ d ∈ j.divisors with L < d, g d := by
    rw [centeredPrefix_sub_eq η h.le]
    simp only [pmPowerDampedCenteredDivisorCoeff]
    rw [sum_sub_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul, ← hL]
    simp only [hτ, sum_add_distrib]
    rw [hsmall, mul_comm (L : ℝ), hρL]
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [hdiff]
  have hA : |∑ d ∈ Icc 1 L, g d * ((((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - (L : ℝ) / d)| ≤
      ∑ d ∈ Icc 1 L, (d : ℝ) ^ (-η) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hfl := abs_div_sub_div_sub_le d (mem_Icc.mp hd).1 h.le
    simp only [hg]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) *
          |(((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - (L : ℝ) / d|
        ≤ 1 * (d : ℝ) ^ (-η) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebius_real_le d)
            (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hfl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hT : |T * L| ≤ (L : ℝ) * ((L : ℝ) ^ (-η) / η) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg L), mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_densityTail_le hη hL1) (Nat.cast_nonneg L)
  have hJ : |∑ j ∈ Ioc a' a, ∑ d ∈ j.divisors with L < d, g d| ≤ largeDivisorSum η a' a := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le rfl (sum_le_sum fun d _ => ?_))
    simp only [hg]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (abs_moebius_real_le d)
  have hS := sum_Icc_rpow_neg_le_source h1 h2 L hL1
  have hB := tail_term_le h1 h2 L hL1
  have hL1' : (1 : ℝ) ≤ (L : ℝ) ^ (1 - chainSourceExponent η) :=
    Real.one_le_rpow (by exact_mod_cast hL1) (by linarith [chainSourceExponent_lt_one h1 h2])
  calc _ ≤ |∑ d ∈ Icc 1 L, g d * ((((a / d : ℕ) : ℝ) - ((a' / d : ℕ) : ℝ)) - (L : ℝ) / d) - T * L| +
        |∑ j ∈ Ioc a' a, ∑ d ∈ j.divisors with L < d, g d| := abs_add_le _ _
    _ ≤ (∑ d ∈ Icc 1 L, (d : ℝ) ^ (-η) + (L : ℝ) * ((L : ℝ) ^ (-η) / η)) +
        largeDivisorSum η a' a := add_le_add ((abs_sub _ _).trans (add_le_add hA hT)) hJ
    _ ≤ chainSourceConstant η * (L : ℝ) ^ (1 - chainSourceExponent η) + largeDivisorSum η a' a := by
        have : ∑ d ∈ Icc 1 L, (d : ℝ) ^ (-η) + (L : ℝ) * ((L : ℝ) ^ (-η) / η) ≤
            chainSourceConstant η * (L : ℝ) ^ (1 - chainSourceExponent η) := by
          unfold chainSourceConstant; nlinarith
        linarith

end ShortInterval

end

end GaloisForLFunctions.BezoutValuationIncidence
