import GaloisForLFunctions.TransHorizonIncidenceMechanics.SparsePrimeFlipsPreserveTheReceiver

/-!
# The logarithmic moment hierarchy separates every pair with a positive member

The higher von Mangoldt functions `Λ_{k+1} = Λ_k · log + Λ_k ⋆ Λ` (`Λ_1 = Λ`) satisfy
`Σ_{e|d} Λ_{k}(e) = log^k d`; they are nonnegative and positive exactly on the moduli `e ≥ 2` with at
most `k` distinct prime factors. The first pronic moment of the log-power weight `c · log^k` is
`M(c·log^k) = −Σ_d c(d) log^{k+1} d / d = −Σ_e Λ_{k+1}(e) W_c(e)`: **the logarithmic pronic moments are
additive observables reading the Ramanujan coefficients on the moduli with at most `k + 1` prime
factors.**

For a pair with a positive member `c₊` (`W_{c₊} = |W_c|`) every moment orders the pair,
`M(c·log^k) − M(c₊·log^k) = Σ_e Λ_{k+1}(e)(|W_c(e)| − W_c(e)) ≥ 0`. If all of them agree, then
`W_c ≥ 0` at every `e ≥ 2` (choose `k + 1 = ω(e)`), so `W_c = W_{c₊}` off `e = 1`; Möbius inversion over
multiples (`c(d)/d = Σ_m μ(m) W_c(dm)`) then makes `c` equal to `c₊` or to `c₊ − 2m₊δ₁`, and both have
the receiver of `c₊`. Hence **no parity pair with a positive member is invisible to the logarithmic
moment hierarchy**: some `M(c·log^k)` separates it, and the order of the first separating moment is
the least `ω(e)` with `W_c(e) < 0`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `higherVonMangoldt k = Λ_{k+1}`: `Λ_1 = Λ`, `Λ_{k+2} = Λ_{k+1} · log + Λ_{k+1} ⋆ Λ`. -/
def higherVonMangoldt : ℕ → ArithmeticFunction ℝ
  | 0 => ArithmeticFunction.vonMangoldt
  | k + 1 => (higherVonMangoldt k).pmul ArithmeticFunction.log +
      higherVonMangoldt k * ArithmeticFunction.vonMangoldt

theorem higherVonMangoldt_nonneg : ∀ (k n : ℕ), 0 ≤ higherVonMangoldt k n
  | 0, n => ArithmeticFunction.vonMangoldt_nonneg
  | k + 1, n => by
    rw [higherVonMangoldt, ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply]
    exact add_nonneg (mul_nonneg (higherVonMangoldt_nonneg k n) (Real.log_natCast_nonneg n))
      (sum_nonneg fun p _ => mul_nonneg (higherVonMangoldt_nonneg k p.1)
        ArithmeticFunction.vonMangoldt_nonneg)

/-- `Σ_{e|d} Λ_{k+1}(e) = log^{k+1} d`. -/
theorem sum_divisors_higherVonMangoldt : ∀ (k : ℕ) {d : ℕ}, d ≠ 0 →
    ∑ e ∈ d.divisors, higherVonMangoldt k e = Real.log d ^ (k + 1)
  | 0, d, _ => by simp [higherVonMangoldt, ArithmeticFunction.vonMangoldt_sum]
  | k + 1, d, hd => by
    have ih := sum_divisors_higherVonMangoldt k hd
    rw [← ArithmeticFunction.coe_mul_zeta_apply, higherVonMangoldt, add_mul, mul_assoc,
      ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.add_apply,
      ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.mul_apply]
    simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
    rw [← Nat.sum_divisorsAntidiagonal (fun a _ => higherVonMangoldt k a * Real.log a),
      ← sum_add_distrib]
    have h : ∀ p ∈ d.divisorsAntidiagonal, higherVonMangoldt k p.1 * Real.log p.1 +
        higherVonMangoldt k p.1 * Real.log p.2 = higherVonMangoldt k p.1 * Real.log d := fun p hp => by
      obtain ⟨hpd, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have h1 : (p.1 : ℝ) ≠ 0 := by
        have : p.1 ≠ 0 := fun h => hd (by rw [← hpd, h, zero_mul])
        exact_mod_cast this
      have h2 : (p.2 : ℝ) ≠ 0 := by
        have : p.2 ≠ 0 := fun h => hd (by rw [← hpd, h, mul_zero])
        exact_mod_cast this
      rw [← mul_add, ← Real.log_mul h1 h2, ← Nat.cast_mul, hpd]
    rw [sum_congr rfl h, ← sum_mul, Nat.sum_divisorsAntidiagonal (fun a _ => higherVonMangoldt k a),
      ih]
    ring

theorem higherVonMangoldt_le (k n : ℕ) : higherVonMangoldt k n ≤ Real.log n ^ (k + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [(higherVonMangoldt k).map_zero]
  · rw [← sum_divisors_higherVonMangoldt k hn]
    exact single_le_sum (fun e _ => higherVonMangoldt_nonneg k e) (Nat.mem_divisors_self n hn)

theorem higherVonMangoldt_prime_pow_pos {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    ∀ k : ℕ, 0 < higherVonMangoldt k (p ^ n)
  | 0 => by
    rw [higherVonMangoldt, ArithmeticFunction.vonMangoldt_apply_pow hn.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  | k + 1 => by
    have ih := higherVonMangoldt_prime_pow_pos hp hn k
    have hlog : 0 < Real.log ((p ^ n : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast Nat.one_lt_pow hn.ne' hp.one_lt)
    rw [higherVonMangoldt, ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.log_apply]
    have hconv : 0 ≤ (higherVonMangoldt k * ArithmeticFunction.vonMangoldt) (p ^ n) := by
      rw [ArithmeticFunction.mul_apply]
      exact sum_nonneg fun q _ => mul_nonneg (higherVonMangoldt_nonneg k q.1)
        ArithmeticFunction.vonMangoldt_nonneg
    nlinarith [mul_pos ih hlog]

/-- `Λ_{k+1}(e) > 0` whenever `e ≥ 2` has at most `k + 1` distinct prime factors. -/
theorem higherVonMangoldt_pos : ∀ e : ℕ, 2 ≤ e → ∀ k : ℕ, e.primeFactors.card ≤ k + 1 →
    0 < higherVonMangoldt k e := by
  intro e
  induction e using Nat.recOnPrimePow with
  | zero => intro h; omega
  | one => intro h; omega
  | prime_pow_mul a p n hp hpa hn ih =>
    intro he k hk
    rcases eq_or_ne a 1 with rfl | ha1
    · rw [mul_one]; exact higherVonMangoldt_prime_pow_pos hp hn k
    have ha0 : a ≠ 0 := by rintro rfl; simp at he
    have ha2 : 2 ≤ a := by omega
    have hcop : Nat.Coprime (p ^ n) a :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
    have hcard : (p ^ n * a).primeFactors.card = a.primeFactors.card + 1 := by
      rw [Nat.Coprime.primeFactors_mul hcop, Finset.card_union_of_disjoint hcop.disjoint_primeFactors,
        Nat.primeFactors_prime_pow hn.ne' hp, card_singleton, add_comm]
    have hapos : 0 < a.primeFactors.card := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr ha2)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have iha := ih ha2 k' (by omega)
    rw [higherVonMangoldt, ArithmeticFunction.add_apply, ArithmeticFunction.pmul_apply]
    have hfirst : 0 ≤ higherVonMangoldt k' (p ^ n * a) * ArithmeticFunction.log (p ^ n * a) := by
      rw [ArithmeticFunction.log_apply]
      exact mul_nonneg (higherVonMangoldt_nonneg k' _) (Real.log_natCast_nonneg _)
    have hconv : higherVonMangoldt k' a * Λ (p ^ n) ≤
        (higherVonMangoldt k' * ArithmeticFunction.vonMangoldt) (p ^ n * a) := by
      rw [ArithmeticFunction.mul_apply]
      have hmem : ((a, p ^ n) : ℕ × ℕ) ∈ (p ^ n * a).divisorsAntidiagonal := by
        rw [Nat.mem_divisorsAntidiagonal, mul_comm]; exact ⟨rfl, by omega⟩
      exact single_le_sum (f := fun q : ℕ × ℕ => higherVonMangoldt k' q.1 * Λ q.2) (fun q _ =>
        mul_nonneg (higherVonMangoldt_nonneg k' q.1) ArithmeticFunction.vonMangoldt_nonneg) hmem
    have hΛ : 0 < Λ (p ^ n) := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow hn.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith [mul_pos iha hΛ]

/-! ### Logarithmic moments -/

/-- The log-power weight `c(d) log^k d`. -/
def logPowWeight (c : ℕ → ℝ) (k : ℕ) (d : ℕ) : ℝ := c d * Real.log d ^ k

theorem logPowWeight_mem_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (k : ℕ) : DampedClass (K * ((2 * (k + 1)) / ε) ^ k) (ε / 2) (logPowWeight c k) := fun d => by
  have hK := nonneg_of_dampedClass hc
  set δ : ℝ := ε / (2 * (k + 1))
  have hδ : 0 < δ := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h0 := hc 0
      simp only [Nat.cast_zero, Real.zero_rpow (show -ε ≠ 0 by linarith), mul_zero] at h0
      simp [logPowWeight, Real.zero_rpow (show -(ε / 2) ≠ 0 by linarith), abs_nonpos_iff.mp h0]
    · simp [logPowWeight, Real.zero_rpow (show -(ε / 2) ≠ 0 by linarith), zero_pow hk.ne']
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog0 := Real.log_natCast_nonneg d
    have hlog := Real.log_le_rpow_div (x := d) hd0.le hδ
    have hpowlog : Real.log d ^ k ≤ ((d : ℝ) ^ δ / δ) ^ k := pow_le_pow_left₀ hlog0 hlog k
    have hpowd : ((d : ℝ) ^ δ / δ) ^ k = (d : ℝ) ^ (δ * k) * (1 / δ) ^ k := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; ring
    have hexp : (d : ℝ) ^ (δ * k) ≤ (d : ℝ) ^ (ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hd1 (by
        simp only [δ]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    rw [logPowWeight, abs_mul, abs_of_nonneg (pow_nonneg hlog0 k)]
    have h1δ : (1 / δ) ^ k = ((2 * (k + 1)) / ε) ^ k := by simp only [δ]; rw [one_div_div]
    calc |c d| * Real.log d ^ k ≤ K * (d : ℝ) ^ (-ε) * ((d : ℝ) ^ (ε / 2) * (1 / δ) ^ k) := by
          refine mul_le_mul (hc d) (hpowlog.trans ?_) (pow_nonneg hlog0 k) (by positivity)
          rw [hpowd]
          exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * ((2 * (k + 1)) / ε) ^ k * (d : ℝ) ^ (-(ε / 2)) := by
          rw [h1δ, show -(ε / 2) = -ε + ε / 2 by ring, Real.rpow_add hd0]; ring

/-- **The logarithmic moment law.** On the damped class,
`M(c·log^k) = −Σ_e Λ_{k+1}(e) W_c(e)`. -/
theorem firstPronicMoment_logPowWeight {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (k : ℕ) :
    firstPronicMoment (logPowWeight c k) =
      -∑' e : ℕ, higherVonMangoldt k e * weightRamanujanCoeff c e := by
  have hcl := logPowWeight_mem_dampedClass hε hc k
  have hε2 : 0 < ε / 2 := by linarith
  unfold firstPronicMoment
  rw [(hasSum_weightCenteredPrefix_div_pronic (summable_div_of_dampedClass hε2 hcl)
    (summable_abs_mul_log_div_of_dampedClass hε2 hcl)).tsum_eq]
  congr 1
  have hsq : ∀ d : ℕ, logPowWeight c k d * Real.log d / d = c d * Real.log d ^ (k + 1) / d :=
    fun d => by rw [logPowWeight, pow_succ]; ring
  rw [tsum_congr hsq]
  refine tsum_divisorPairing (higherVonMangoldt_nonneg k)
    (fun d hd => sum_divisors_higherVonMangoldt k hd) (summable_div_of_dampedClass hε hc) ?_
  refine (summable_abs_mul_log_div_of_dampedClass hε2 hcl).congr fun d => ?_
  rw [logPowWeight, abs_mul, abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg d) k), pow_succ]
  ring

theorem summable_higherVonMangoldt_mul_weightRamanujanCoeff {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (k : ℕ) :
    Summable (fun e : ℕ => higherVonMangoldt k e * weightRamanujanCoeff c e) := by
  have hK := nonneg_of_dampedClass hc
  set Z := ∑' j : ℕ, dampedSignWeight unitSign ε j / j
  have hZ := (unitDampedMass_pos hε).le
  have hu : DampedClass 1 ε (dampedSignWeight unitSign ε) := fun d => by
    rw [dampedSignWeight, unitSign, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have hε2 : 0 < ε / 2 := by linarith
  have hlog := summable_abs_mul_log_div_of_dampedClass hε2 (logPowWeight_mem_dampedClass hε hu k)
  refine (hlog.mul_left (K * Z)).of_norm_bounded fun e => ?_
  have hW := abs_weightRamanujanCoeff_le_of_dampedClass hε hc e
  have hΛ := higherVonMangoldt_le k e
  have hl := Real.log_natCast_nonneg e
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (higherVonMangoldt_nonneg k e), logPowWeight,
    dampedSignWeight, unitSign, one_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _), abs_of_nonneg (pow_nonneg hl k)]
  have hp : 0 ≤ K * Z * ((e : ℝ) ^ (-ε) / e) := by positivity
  calc higherVonMangoldt k e * |weightRamanujanCoeff c e| ≤
        Real.log e ^ (k + 1) * (K * Z * ((e : ℝ) ^ (-ε) / e)) :=
        mul_le_mul hΛ hW (abs_nonneg _) (pow_nonneg hl _)
    _ = K * Z * ((e : ℝ) ^ (-ε) * Real.log e ^ k * Real.log e / e) := by rw [pow_succ]; ring

/-- **Every logarithmic moment orders a pair with a positive member.** -/
theorem logMoment_sub_of_positive_twin {K K₁ ε : ℝ} (hε : 0 < ε) {c c₁ : ℕ → ℝ}
    (hc : DampedClass K ε c) (hc₁ : DampedClass K₁ ε c₁) (hpos : ∀ d, 0 ≤ c₁ d)
    (hamp : ∀ e, |weightRamanujanCoeff c₁ e| = |weightRamanujanCoeff c e|) (k : ℕ) :
    firstPronicMoment (logPowWeight c k) - firstPronicMoment (logPowWeight c₁ k) =
      ∑' e : ℕ, higherVonMangoldt k e * (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) := by
  have hW₁ : ∀ e, weightRamanujanCoeff c₁ e = |weightRamanujanCoeff c e| := fun e => by
    rw [← hamp e, abs_of_nonneg (weightRamanujanCoeff_nonneg hpos e)]
  rw [firstPronicMoment_logPowWeight hε hc, firstPronicMoment_logPowWeight hε hc₁, neg_sub_neg,
    ← (summable_higherVonMangoldt_mul_weightRamanujanCoeff hε hc₁ k).tsum_sub
      (summable_higherVonMangoldt_mul_weightRamanujanCoeff hε hc k)]
  exact tsum_congr fun e => by rw [hW₁]; ring

/-! ### Möbius inversion over multiples -/

theorem sum_divisors_moebiusReal (j : ℕ) :
    ∑ m ∈ j.divisors, moebiusReal m = if j = 1 then 1 else 0 := by
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F j)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ j.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) j from hμ]
  rcases eq_or_ne j 1 with rfl | hj
  · simp
  · simp [hj]

/-- **Möbius inversion over multiples.** On the damped class `c(d)/d = Σ_m μ(m) W_c(dm)`, `d ≥ 1`. -/
theorem hasSum_moebius_mul_weightRamanujanCoeff {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) {d : ℕ} (hd : 0 < d) :
    HasSum (fun m : ℕ => moebiusReal m * weightRamanujanCoeff c (d * m)) (c d / d) := by
  have hK := nonneg_of_dampedClass hc
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set H : ℕ × ℕ → ℝ := fun p =>
    moebiusReal p.1 * (c (d * (p.1 * p.2)) / ((d * (p.1 * p.2) : ℕ) : ℝ))
  have hz : Summable (fun m : ℕ => ‖(m : ℝ) ^ (-1 - ε)‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1))
  have hprod : Summable (fun p : ℕ × ℕ => (p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) :=
    summable_mul_of_summable_norm (f := fun m : ℕ => (m : ℝ) ^ (-1 - ε))
      (g := fun m : ℕ => (m : ℝ) ^ (-1 - ε)) hz hz
  have hμ1 : ∀ m : ℕ, |moebiusReal m| ≤ 1 := fun m => by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]
  have hHb : ∀ p : ℕ × ℕ, ‖H p‖ ≤ K * (d : ℝ) ^ (-1 - ε) *
      ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) := fun p => by
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos p.1 with h1 | h1
    · simp only [H, h1, zero_mul, mul_zero, Nat.cast_zero, div_zero, abs_zero]; positivity
    rcases Nat.eq_zero_or_pos p.2 with h2 | h2
    · simp only [H, h2, mul_zero, Nat.cast_zero, div_zero, abs_zero]; positivity
    have hn : (0 : ℝ) < ((d * (p.1 * p.2) : ℕ) : ℝ) := by positivity
    have hcast : ((d * (p.1 * p.2) : ℕ) : ℝ) = (d : ℝ) * ((p.1 : ℝ) * p.2) := by push_cast; ring
    simp only [H]
    rw [abs_mul, abs_div, abs_of_pos hn]
    have hcn : |c (d * (p.1 * p.2))| / ((d * (p.1 * p.2) : ℕ) : ℝ) ≤
        K * (((d * (p.1 * p.2) : ℕ) : ℝ) ^ (-1 - ε)) := by
      rw [div_le_iff₀ hn]
      calc |c (d * (p.1 * p.2))| ≤ K * ((d * (p.1 * p.2) : ℕ) : ℝ) ^ (-ε) := hc _
        _ = K * ((d * (p.1 * p.2) : ℕ) : ℝ) ^ (-1 - ε) * ((d * (p.1 * p.2) : ℕ) : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add_one hn.ne', show -1 - ε + 1 = -ε by ring]
    have hsplit : (((d * (p.1 * p.2) : ℕ) : ℝ)) ^ (-1 - ε) =
        (d : ℝ) ^ (-1 - ε) * ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) := by
      rw [hcast, Real.mul_rpow (Nat.cast_nonneg _) (by positivity),
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    calc |moebiusReal p.1| * (|c (d * (p.1 * p.2))| / ((d * (p.1 * p.2) : ℕ) : ℝ)) ≤
          1 * (K * (((d * (p.1 * p.2) : ℕ) : ℝ) ^ (-1 - ε))) :=
          mul_le_mul (hμ1 _) hcn (by positivity) zero_le_one
      _ = _ := by rw [one_mul, hsplit]; ring
  have hH : Summable H := (hprod.mul_left _).of_norm_bounded hHb
  have hrow : ∀ m : ℕ, HasSum (fun k => H (m, k)) (moebiusReal m * weightRamanujanCoeff c (d * m)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [H, moebiusReal]
    · have hinj : Function.Injective (fun k : ℕ => d * m * k) := fun a b h =>
        Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hd hm) h
      have hs := (summable_div_of_dampedClass hε hc).comp_injective hinj
      refine (hs.hasSum.mul_left (moebiusReal m)).congr_fun fun k => ?_
      simp only [H, Function.comp_apply, mul_assoc]
  have hval : ∀ j : ℕ, ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p =
      if j = 1 then c d / d else 0 := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · have h0 : ∀ p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), H p = 0 := fun p => by
        have hp : p.1.1 * p.1.2 = 0 := p.2
        simp only [H, hp, mul_zero, Nat.cast_zero, div_zero]
      rw [tsum_congr h0, tsum_zero, if_neg (by norm_num)]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j} = j.divisorsAntidiagonal by ext; simp [hj],
        Finset.tsum_subtype' j.divisorsAntidiagonal H]
      have hfac : ∀ p ∈ j.divisorsAntidiagonal, H p = moebiusReal p.1 *
          (c (d * j) / ((d * j : ℕ) : ℝ)) := fun p hp => by
        simp only [H]; rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      rw [sum_congr rfl hfac, ← sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a _ => moebiusReal a), sum_divisors_moebiusReal]
      split_ifs with h1
      · subst h1; simp
      · simp
  have hfib := hH.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  rw [show (fun j => ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p) =
    fun j => if j = 1 then c d / d else 0 from funext hval] at hfib
  have htot : ∑' p, H p = c d / d := hfib.unique (hasSum_ite_eq 1 _)
  rw [← htot]
  exact hH.hasSum.prod_fiberwise hrow

/-- **Ramanujan coefficients determine the damped weight.** -/
theorem eq_of_weightRamanujanCoeff_eq {K K' ε : ℝ} (hε : 0 < ε) {c c' : ℕ → ℝ}
    (hc : DampedClass K ε c) (hc' : DampedClass K' ε c')
    (hW : ∀ e, 0 < e → weightRamanujanCoeff c e = weightRamanujanCoeff c' e) {d : ℕ} (hd : 0 < d) :
    c d = c' d := by
  have h1 := hasSum_moebius_mul_weightRamanujanCoeff hε hc hd
  have h2 := hasSum_moebius_mul_weightRamanujanCoeff hε hc' hd
  have hfun : (fun m : ℕ => moebiusReal m * weightRamanujanCoeff c (d * m)) =
      fun m => moebiusReal m * weightRamanujanCoeff c' (d * m) := funext fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [moebiusReal]
    · rw [hW (d * m) (Nat.mul_pos hd hm)]
  rw [hfun] at h1
  have h := h1.unique h2
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp at h
  exact h

theorem receiverBounded_congr {c c' : ℕ → ℝ} (h : ∀ d, 0 < d → c d = c' d) :
    ReceiverBounded c ↔ ReceiverBounded c' := by
  have hm : ∑' d : ℕ, c d / d = ∑' d : ℕ, c' d / d := tsum_congr fun d => by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [h d hd]
  have hA : ∀ m n, weightCenteredPrefix c m n = weightCenteredPrefix c' m n := fun m n => by
    unfold weightCenteredPrefix
    congr 1
    exact sum_congr rfl fun j _ => sum_congr rfl fun e he => h e (Nat.pos_of_mem_divisors he)
  unfold ReceiverBounded weightPronicEnergy
  simp only [hm, hA]

/-! ### The δ₁-shift -/

theorem weightRamanujanCoeff_sub_unitMass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (a : ℝ) {e : ℕ} (he : 0 < e) :
    weightRamanujanCoeff (fun d => c d - a * unitMass d) e =
      weightRamanujanCoeff c e - a * (if e = 1 then 1 else 0) := by
  have hinj : Function.Injective (fun k : ℕ => e * k) := fun x y h => Nat.eq_of_mul_eq_mul_left he h
  have hs : Summable (fun k : ℕ => c (e * k) / ((e * k : ℕ) : ℝ)) :=
    (summable_div_of_dampedClass hε hc).comp_injective hinj
  unfold weightRamanujanCoeff
  simp_rw [sub_div, mul_div_assoc]
  rw [hs.tsum_sub ((summable_unitMass_mul e).mul_left a), tsum_mul_left]
  congr 2
  exact weightRamanujanCoeff_unitMass e

theorem receiverBounded_sub_unitMass {c : ℕ → ℝ} (hs : Summable (fun d : ℕ => c d / d)) :
    ReceiverBounded (fun d => c d - 2 * (∑' k : ℕ, c k / k) * unitMass d) ↔ ReceiverBounded c := by
  set m := ∑' k : ℕ, c k / k
  have hu : HasSum (fun d : ℕ => unitMass d / d) 1 := by
    have h := hasSum_ite_eq (1 : ℕ) (1 : ℝ)
    refine h.congr_fun fun d => ?_
    by_cases hd : d = 1 <;> simp [unitMass, hd]
  have hmean : ∑' d : ℕ, (c d - 2 * m * unitMass d) / d = -m := by
    have h := hs.hasSum.sub (hu.mul_left (2 * m))
    rw [show m - 2 * m * 1 = -m by ring] at h
    refine (h.congr_fun fun d => ?_).tsum_eq
    ring
  have hA : ∀ n, weightCenteredPrefix (fun d => c d - 2 * m * unitMass d) (-m) n =
      weightCenteredPrefix c m n := fun n => by
    have hu1 : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, unitMass d = 1 := fun j hj => by
      have hj : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
      rw [Finset.sum_eq_single 1 (fun d _ hd => by simp [unitMass, hd]) (fun h => absurd
        (Nat.one_mem_divisors.mpr hj) h)]
      simp [unitMass]
    unfold weightCenteredPrefix
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hu1]
    simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    ring
  unfold ReceiverBounded weightPronicEnergy
  rw [hmean]
  simp only [hA]
  exact Iff.rfl

/-! ### The separation theorem -/

/-- **No parity pair with a positive member is invisible to the logarithmic moment hierarchy.** If
`c₁ ≥ 0` has the Ramanujan amplitudes of `c` (both damped) and exactly one of them has bounded
receiver, then some logarithmic pronic moment separates them strictly:
`M(c₁·log^k) < M(c·log^k)`. -/
theorem exists_logMoment_separating {K K₁ ε : ℝ} (hε : 0 < ε) {c c₁ : ℕ → ℝ}
    (hc : DampedClass K ε c) (hc₁ : DampedClass K₁ ε c₁) (hpos : ∀ d, 0 ≤ c₁ d)
    (hamp : ∀ e, |weightRamanujanCoeff c₁ e| = |weightRamanujanCoeff c e|)
    (hdiff : ¬ (ReceiverBounded c ↔ ReceiverBounded c₁)) :
    ∃ k : ℕ, firstPronicMoment (logPowWeight c₁ k) < firstPronicMoment (logPowWeight c k) := by
  by_contra hnone
  push Not at hnone
  have hW₁ : ∀ e, weightRamanujanCoeff c₁ e = |weightRamanujanCoeff c e| := fun e => by
    rw [← hamp e, abs_of_nonneg (weightRamanujanCoeff_nonneg hpos e)]
  -- every gap vanishes termwise
  have hterm : ∀ k e, higherVonMangoldt k e *
      (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) = 0 := by
    intro k
    have hgap := logMoment_sub_of_positive_twin hε hc hc₁ hpos hamp k
    have hnn : ∀ e, 0 ≤ higherVonMangoldt k e *
        (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) := fun e =>
      mul_nonneg (higherVonMangoldt_nonneg k e) (sub_nonneg.mpr (le_abs_self _))
    have hsum : Summable (fun e => higherVonMangoldt k e *
        (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e)) :=
      ((summable_higherVonMangoldt_mul_weightRamanujanCoeff hε hc₁ k).sub
        (summable_higherVonMangoldt_mul_weightRamanujanCoeff hε hc k)).congr fun e => by
          rw [hW₁]; ring
    have hzero : ∑' e, higherVonMangoldt k e *
        (|weightRamanujanCoeff c e| - weightRamanujanCoeff c e) = 0 :=
      le_antisymm (by linarith [hnone k, hgap]) (tsum_nonneg hnn)
    have := (hasSum_zero_iff_of_nonneg hnn).mp (hzero ▸ hsum.hasSum)
    exact fun e => congrFun this e
  -- hence `W_c = W_{c₁}` at every `e ≥ 2`
  have hge : ∀ e, 2 ≤ e → weightRamanujanCoeff c e = weightRamanujanCoeff c₁ e := by
    intro e he
    have hcard : 0 < e.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hpos' := higherVonMangoldt_pos e he (e.primeFactors.card - 1) (by omega)
    have h := hterm (e.primeFactors.card - 1) e
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hpos'.ne'
    · rw [hW₁]; linarith
  -- the mean: `W_c(1) = ±W_{c₁}(1)`
  have h1 : weightRamanujanCoeff c 1 = weightRamanujanCoeff c₁ 1 ∨
      weightRamanujanCoeff c 1 = -weightRamanujanCoeff c₁ 1 := by
    rw [hW₁]
    rcases le_or_gt 0 (weightRamanujanCoeff c 1) with h | h
    · left; rw [abs_of_nonneg h]
    · right; rw [abs_of_neg h, neg_neg]
  apply hdiff
  rcases h1 with h1 | h1
  · -- `c = c₁` on the positive integers
    refine receiverBounded_congr fun d hd => eq_of_weightRamanujanCoeff_eq hε hc hc₁
      (fun e he => ?_) hd
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · obtain rfl : e = 1 := by omega
      exact h1
    · exact hge e he2
  · -- `c = c₁ − 2m₁δ₁` on the positive integers
    set m₁ := ∑' k : ℕ, c₁ k / k
    have hm₁ : weightRamanujanCoeff c₁ 1 = m₁ := by
      simp only [weightRamanujanCoeff, one_mul, m₁]
    have hK₁ := nonneg_of_dampedClass hc₁
    have hclass : DampedClass (K₁ + 2 * |m₁|) ε (fun d => c₁ d - 2 * m₁ * unitMass d) := fun d => by
      have hp : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
      dsimp only
      unfold unitMass
      split_ifs with hd
      · subst hd
        simp only [Nat.cast_one, Real.one_rpow, mul_one]
        have := hc₁ 1
        simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
        calc |c₁ 1 - 2 * m₁| ≤ |c₁ 1| + |2 * m₁| := abs_sub _ _
          _ ≤ K₁ + 2 * |m₁| := by rw [abs_mul, abs_two]; linarith
      · rw [mul_zero, sub_zero]
        exact (hc₁ d).trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg m₁]) hp)
    rw [← receiverBounded_sub_unitMass (summable_div_of_dampedClass hε hc₁)]
    refine receiverBounded_congr fun d hd => eq_of_weightRamanujanCoeff_eq hε hc hclass
      (fun e he => ?_) hd
    rw [weightRamanujanCoeff_sub_unitMass hε hc₁ _ he]
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · obtain rfl : e = 1 := by omega
      rw [if_pos rfl, h1, hm₁]; ring
    · rw [if_neg (by omega), mul_zero, sub_zero]; exact hge e he2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
