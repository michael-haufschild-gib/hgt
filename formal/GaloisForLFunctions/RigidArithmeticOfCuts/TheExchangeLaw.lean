import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The exchange law

Exchange the rational primes for another integer multiset: remove some primes and add integers as new primes. The
exchange is `e : ℕ → ℤ`, the new multiplicities are `b(n) = 1_{prime}(n) + e(n)`, and the zeta function is
`ζ(s) G(s)`, with `G = exp Σ_n e(n) (−log(1 − n^{-s}))`.

**The Hamming law.** If `Σ |e(n)| n^{-σ} < ∞`, then `G` is holomorphic and zero-free on `Re s > σ`. So `ζ G` has exactly
the zeros of `ζ` there. A new zero at `β` needs exchange mass of exponent at least `β`: the zeros right of `σ` are
invariants of the primes modulo sets of exponent `< σ`.

**The count law.** For a family of letters `m_i` with weights `w_i` and `Σ |w_i| m_i^{-σ} < ∞`, `0 ≤ σ ≤ 1`,
`|Σ w_i ⌊x/m_i⌋ − x Σ w_i/m_i| ≤ x^σ Σ |w_i| m_i^{-σ}`. So an exchange with `G(1) = 1` has `N(x) = x + O(x^σ)`.

**An explicit system.** Remove `2`, double `3`, and add `4` as a prime. Then
`G(s) = (1 − 2^{-s}) / ((1 − 3^{-s}) (1 − 4^{-s}))` with `G(1) = 1`, and `N(x) = x + O(x^σ)` for every `σ > 0`. It has
integer norms, positive multiplicities and the zeros of `ζ` on `Re s > 0`. So closeness of counts does not force the
rational primes above the integrality gap, and it does not produce a new zero either.
-/

open Finset Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### The count law -/

private lemma abs_floor_sub_le (y : ℝ) (hy : 0 ≤ y) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    |((⌊y⌋₊ : ℕ) : ℝ) - y| ≤ y ^ σ := by
  rcases le_or_gt 1 y with hy1 | hy1
  · have h2 : (1 : ℝ) ≤ y ^ σ := Real.one_le_rpow hy1 h0
    have h3 := Nat.floor_le hy
    have h4 := Nat.lt_floor_add_one y
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [Nat.floor_eq_zero.mpr hy1]
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hy]
    rcases hy.eq_or_lt with rfl | hpos
    · simp [Real.zero_rpow_nonneg]
    · calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_ge hpos hy1.le h1

/-- **The count law.** -/
theorem abs_tsum_mul_floor_sub_le {ι : Type*} {m : ι → ℕ} {w : ι → ℝ} (hm : ∀ i, 1 ≤ m i) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hs : Summable fun i => |w i| * (m i : ℝ) ^ (-σ)) {x : ℕ} (hx : 1 ≤ x) :
    Summable (fun i => w i * ((x / m i : ℕ) : ℝ)) ∧ Summable (fun i => w i / (m i : ℝ)) ∧
      |∑' i, w i * ((x / m i : ℕ) : ℝ) - (x : ℝ) * ∑' i, w i / (m i : ℝ)| ≤
        (x : ℝ) ^ σ * ∑' i, |w i| * (m i : ℝ) ^ (-σ) := by
  have hmR : ∀ i, (1 : ℝ) ≤ m i := fun i => by exact_mod_cast hm i
  have hmpos : ∀ i, (0 : ℝ) < m i := fun i => lt_of_lt_of_le one_pos (hmR i)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hle : ∀ i, |w i / (m i : ℝ)| ≤ |w i| * (m i : ℝ) ^ (-σ) := by
    intro i
    rw [abs_div, abs_of_pos (hmpos i), div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (hmR i) (by linarith)
  have hs1 : Summable fun i => w i / (m i : ℝ) := Summable.of_norm_bounded hs hle
  have hterm : ∀ i, |w i * (((x / m i : ℕ) : ℝ) - (x : ℝ) / m i)| ≤
      (x : ℝ) ^ σ * (|w i| * (m i : ℝ) ^ (-σ)) := by
    intro i
    have hfloor : ((x / m i : ℕ) : ℝ) = ((⌊(x : ℝ) / m i⌋₊ : ℕ) : ℝ) := by
      rw [Nat.floor_div_eq_div]
    have hy : (0 : ℝ) ≤ (x : ℝ) / m i := by positivity
    have h2 := abs_floor_sub_le _ hy h0 h1
    rw [← hfloor, Real.div_rpow hxR.le (hmpos i).le] at h2
    rw [abs_mul]
    calc |w i| * |((x / m i : ℕ) : ℝ) - (x : ℝ) / m i|
        ≤ |w i| * ((x : ℝ) ^ σ / (m i : ℝ) ^ σ) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = _ := by
          rw [Real.rpow_neg (hmpos i).le]
          field_simp
  have hs2 : Summable fun i => (x : ℝ) ^ σ * (|w i| * (m i : ℝ) ^ (-σ)) := hs.mul_left _
  have hs3 : Summable fun i => w i * (((x / m i : ℕ) : ℝ) - (x : ℝ) / m i) :=
    Summable.of_norm_bounded hs2 hterm
  have hs4 : Summable fun i => (x : ℝ) * (w i / (m i : ℝ)) := hs1.mul_left _
  have hs5 : Summable fun i => w i * ((x / m i : ℕ) : ℝ) := by
    refine (hs3.add hs4).congr fun i => ?_
    ring
  refine ⟨hs5, hs1, ?_⟩
  have heq : ∑' i, w i * ((x / m i : ℕ) : ℝ) - (x : ℝ) * ∑' i, w i / (m i : ℝ) =
      ∑' i, w i * (((x / m i : ℕ) : ℝ) - (x : ℝ) / m i) := by
    rw [← tsum_mul_left, ← hs5.tsum_sub hs4]
    exact tsum_congr fun i => by ring
  rw [heq, ← tsum_mul_left]
  have hnorm : ‖∑' i, w i * (((x / m i : ℕ) : ℝ) - (x : ℝ) / m i)‖ ≤
      ∑' i, ‖w i * (((x / m i : ℕ) : ℝ) - (x : ℝ) / m i)‖ := norm_tsum_le_tsum_norm hs3.norm
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (Summable.tsum_le_tsum (fun i => ?_) hs3.norm hs2)
  exact hterm i

/-! ### The explicit system -/

/-- The letters `3^a 4^b`. -/
def exchangeLetter (y : ℕ × ℕ) : ℕ := 3 ^ y.1 * 4 ^ y.2

theorem one_le_exchangeLetter (y : ℕ × ℕ) : 1 ≤ exchangeLetter y :=
  Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

/-- The count of the system with `2` removed, `3` doubled and `4` added:
`N(x) = Σ_{a,b} (⌊x/(3^a 4^b)⌋ − ⌊x/(2·3^a 4^b)⌋)`. -/
def exchangeCount (x : ℕ) : ℝ :=
  ∑' y : ℕ × ℕ, (((x / exchangeLetter y : ℕ) : ℝ) - ((x / (2 * exchangeLetter y) : ℕ) : ℝ))

private lemma summable_letter_rpow {σ : ℝ} (hσ : 0 < σ) :
    Summable fun y : ℕ × ℕ => ((exchangeLetter y : ℕ) : ℝ) ^ (-σ) := by
  have hr : (3 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs : (4 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1 : Summable fun a : ℕ => ((3 : ℝ) ^ (-σ)) ^ a :=
    summable_geometric_of_lt_one (by positivity) hr
  have h2 : Summable fun b : ℕ => ((4 : ℝ) ^ (-σ)) ^ b :=
    summable_geometric_of_lt_one (by positivity) hs
  have h := h1.mul_of_nonneg h2 (fun a => by positivity) (fun b => by positivity)
  refine h.congr fun y => ?_
  simp only [exchangeLetter]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  congr 2 <;> ring

private lemma tsum_inv_letter : ∑' y : ℕ × ℕ, (1 : ℝ) / (exchangeLetter y : ℕ) = 2 := by
  have h3 : ‖(1 : ℝ) / 3‖ < 1 := by norm_num [Real.norm_eq_abs]
  have h4 : ‖(1 : ℝ) / 4‖ < 1 := by norm_num [Real.norm_eq_abs]
  have hprod := tsum_mul_tsum_of_summable_norm (summable_geometric_of_norm_lt_one h3).norm
    (summable_geometric_of_norm_lt_one h4).norm
  rw [tsum_geometric_of_norm_lt_one h3, tsum_geometric_of_norm_lt_one h4] at hprod
  have hval : (1 - (1 : ℝ) / 3)⁻¹ * (1 - (1 : ℝ) / 4)⁻¹ = 2 := by norm_num
  rw [hval] at hprod
  rw [hprod]
  refine tsum_congr fun y => ?_
  simp only [exchangeLetter]
  push_cast
  rw [one_div_pow, one_div_pow]
  field_simp

/-- **The explicit system has `N(x) = x + O(x^σ)`.** For every `0 < σ ≤ 1` there is a constant `C` with
`|N(x) − x| ≤ C x^σ` for all `x ≥ 1`. -/
theorem exists_abs_exchangeCount_sub_le {σ : ℝ} (hσ : 0 < σ) (h1 : σ ≤ 1) :
    ∃ C : ℝ, ∀ x : ℕ, 1 ≤ x → |exchangeCount x - x| ≤ C * (x : ℝ) ^ σ := by
  have hs₁ := summable_letter_rpow hσ
  have hw₁ : Summable fun y : ℕ × ℕ => |(1 : ℝ)| * ((exchangeLetter y : ℕ) : ℝ) ^ (-σ) := by
    simpa using hs₁
  have hm₂ : ∀ y : ℕ × ℕ, 1 ≤ 2 * exchangeLetter y := fun y => by
    have := one_le_exchangeLetter y
    omega
  have hw₂ : Summable fun y : ℕ × ℕ => |(1 : ℝ)| * ((2 * exchangeLetter y : ℕ) : ℝ) ^ (-σ) := by
    have h2 : ∀ y : ℕ × ℕ, |(1 : ℝ)| * ((2 * exchangeLetter y : ℕ) : ℝ) ^ (-σ) =
        (2 : ℝ) ^ (-σ) * ((exchangeLetter y : ℕ) : ℝ) ^ (-σ) := by
      intro y
      rw [abs_one, one_mul]
      push_cast
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    simp_rw [h2]
    exact hs₁.mul_left _
  refine ⟨∑' y : ℕ × ℕ, |(1 : ℝ)| * ((exchangeLetter y : ℕ) : ℝ) ^ (-σ) +
    ∑' y : ℕ × ℕ, |(1 : ℝ)| * ((2 * exchangeLetter y : ℕ) : ℝ) ^ (-σ), fun x hx => ?_⟩
  obtain ⟨a1, a2, a3⟩ := abs_tsum_mul_floor_sub_le (w := fun _ => (1 : ℝ)) one_le_exchangeLetter
    hσ.le h1 hw₁ hx
  obtain ⟨b1, b2, b3⟩ := abs_tsum_mul_floor_sub_le (w := fun _ => (1 : ℝ)) hm₂ hσ.le h1 hw₂ hx
  simp only [one_mul] at a1 a3 b1 b3
  have hinv₁ : ∑' y : ℕ × ℕ, (1 : ℝ) / (exchangeLetter y : ℕ) = 2 := tsum_inv_letter
  have hinv₂ : ∑' y : ℕ × ℕ, (1 : ℝ) / (2 * exchangeLetter y : ℕ) = 1 := by
    have h : ∀ y : ℕ × ℕ, (1 : ℝ) / ((2 * exchangeLetter y : ℕ) : ℝ) =
        (1 / 2) * ((1 : ℝ) / (exchangeLetter y : ℕ)) := by
      intro y
      push_cast
      field_simp
    simp_rw [h]
    rw [tsum_mul_left, hinv₁]
    norm_num
  rw [hinv₁] at a3
  rw [hinv₂] at b3
  have hN : exchangeCount x =
      ∑' y : ℕ × ℕ, ((x / exchangeLetter y : ℕ) : ℝ) -
        ∑' y : ℕ × ℕ, ((x / (2 * exchangeLetter y) : ℕ) : ℝ) := by
    rw [exchangeCount]
    exact a1.tsum_sub b1
  rw [hN]
  have habs1 := abs_le.mp a3
  have habs2 := abs_le.mp b3
  have hcomb : |∑' y : ℕ × ℕ, ((x / exchangeLetter y : ℕ) : ℝ) -
      ∑' y : ℕ × ℕ, ((x / (2 * exchangeLetter y) : ℕ) : ℝ) - x| ≤
      (x : ℝ) ^ σ * ∑' y : ℕ × ℕ, |(1 : ℝ)| * ((exchangeLetter y : ℕ) : ℝ) ^ (-σ) +
      (x : ℝ) ^ σ * ∑' y : ℕ × ℕ, |(1 : ℝ)| * ((2 * exchangeLetter y : ℕ) : ℝ) ^ (-σ) := by
    rw [abs_le]
    constructor <;> linarith [habs1.1, habs1.2, habs2.1, habs2.2]
  refine hcomb.trans (le_of_eq ?_)
  ring

/-- The factor `G` of the explicit system. -/
def exchangeFactorExample (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-s)) / ((1 - (3 : ℂ) ^ (-s)) * (1 - (4 : ℂ) ^ (-s)))

private lemma one_sub_cpow_ne_zero {n : ℕ} (hn : 2 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    1 - ((n : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : ((n : ℕ) : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, norm_one] at h2
  have h3 : (n : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  linarith

/-- **The explicit system adds no zero on `Re s > 0`.** -/
theorem exchangeFactorExample_ne_zero {s : ℂ} (hs : 0 < s.re) : exchangeFactorExample s ≠ 0 := by
  have h2 := one_sub_cpow_ne_zero (n := 2) le_rfl hs
  have h3 := one_sub_cpow_ne_zero (n := 3) (by norm_num) hs
  have h4 := one_sub_cpow_ne_zero (n := 4) (by norm_num) hs
  push_cast at h2 h3 h4
  exact div_ne_zero h2 (mul_ne_zero h3 h4)

/-- The value `G(1) = 1`: the density of the system is that of `ℤ`. -/
theorem exchangeFactorExample_one : exchangeFactorExample 1 = 1 := by
  rw [exchangeFactorExample, Complex.cpow_neg_one, Complex.cpow_neg_one, Complex.cpow_neg_one]
  norm_num

/-! ### The Hamming law -/

/-- The logarithm of an exchange: `H(s) = Σ_n e(n) (−log(1 − n^{-s}))`, for `n ≥ 2`. -/
def exchangeLog (e : ℕ → ℤ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (e (n + 2) : ℂ) * (-Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s)))

/-- The factor `G = exp H` of an exchange. -/
def exchangeFactor (e : ℕ → ℤ) (s : ℂ) : ℂ := Complex.exp (exchangeLog e s)

/-- **`G` has no zero.** -/
theorem exchangeFactor_ne_zero (e : ℕ → ℤ) (s : ℂ) : exchangeFactor e s ≠ 0 := Complex.exp_ne_zero _

/-- **The Hamming law: zeros of the exchanged system.** `ζ G` has the zeros of `ζ`, wherever `G` is defined. -/
theorem exchange_eq_zero_iff (e : ℕ → ℤ) (s : ℂ) :
    riemannZeta s * exchangeFactor e s = 0 ↔ riemannZeta s = 0 := by
  rw [mul_eq_zero, or_iff_left (exchangeFactor_ne_zero e s)]

private lemma norm_log_one_sub_le {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖Complex.log (1 - ((n : ℕ) : ℂ) ^ (-s))‖ ≤ (n : ℝ) ^ (-σ) / (1 - (2 : ℝ) ^ (-σ)) := by
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hz : ‖-(((n : ℕ) : ℂ) ^ (-s))‖ = (n : ℝ) ^ (-s.re) := by
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have hzle : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hnR.le (by linarith)
  have hzle2 : (n : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by linarith)
  have hsmall : ‖-(((n : ℕ) : ℂ) ^ (-s))‖ < 1 := by rw [hz]; linarith
  have h := Complex.norm_log_one_add_le hsmall
  rw [sub_eq_add_neg]
  refine h.trans ?_
  rw [hz]
  set t := (n : ℝ) ^ (-s.re) with ht
  set A := (n : ℝ) ^ (-σ) with hA
  set r := (2 : ℝ) ^ (-σ) with hr
  have ht0 : 0 ≤ t := by positivity
  have htr : t ≤ r := hzle.trans hzle2
  have h1t : 0 < 1 - t := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hstep : t ^ 2 * (1 - t)⁻¹ / 2 + t ≤ t / (1 - t) := by
    rw [← div_eq_mul_inv, div_div, div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) h1t]
    nlinarith [sq_nonneg t, mul_nonneg ht0 ht0, mul_nonneg ht0 h1t.le]
  refine hstep.trans ?_
  exact div_le_div₀ (by positivity) hzle h1r (by linarith)

private lemma mem_slitPlane_one_sub {n : ℕ} (hn : 2 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    1 - ((n : ℕ) : ℂ) ^ (-s) ∈ Complex.slitPlane := by
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnorm : ‖((n : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hnR (by linarith)
  refine Or.inl ?_
  have hre := Complex.abs_re_le_norm (((n : ℕ) : ℂ) ^ (-s))
  have := (abs_le.mp hre).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- The terms of the exchange logarithm are bounded on `Re s ≥ σ`. -/
private lemma norm_exchange_term_le (e : ℕ → ℤ) {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (n : ℕ) :
    ‖(e (n + 2) : ℂ) * (-Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s)))‖ ≤
      |(e (n + 2) : ℝ)| * (((n + 2 : ℕ) : ℝ) ^ (-σ)) / (1 - (2 : ℝ) ^ (-σ)) := by
  rw [norm_mul, norm_neg, Complex.norm_intCast, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_log_one_sub_le (by omega) hσ hs) (abs_nonneg _)

variable {e : ℕ → ℤ} {σ : ℝ}

/-- The exchange series converges on `Re s ≥ σ`. -/
theorem summable_exchange_term (hσ : 0 < σ)
    (he : Summable fun n : ℕ => |(e (n + 2) : ℝ)| * ((n + 2 : ℕ) : ℝ) ^ (-σ)) {s : ℂ} (hs : σ ≤ s.re) :
    Summable fun n : ℕ => (e (n + 2) : ℂ) * (-Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s))) :=
  Summable.of_norm_bounded (he.div_const _) (norm_exchange_term_le e hσ hs)

/-- **`G` is holomorphic on `Re s > σ`.** -/
theorem differentiableOn_exchangeLog (hσ : 0 < σ)
    (he : Summable fun n : ℕ => |(e (n + 2) : ℝ)| * ((n + 2 : ℕ) : ℝ) ^ (-σ)) :
    DifferentiableOn ℂ (exchangeLog e) {s | σ < s.re} := by
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine differentiableOn_tsum_of_summable_norm (he.div_const _) (fun n s hs => ?_) hopen
    (fun n s hs => norm_exchange_term_le e hσ (le_of_lt hs) n)
  have hs' : σ < s.re := hs
  have hn0 : (((n + 2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - (((n + 2 : ℕ) : ℂ)) ^ (-w)) s :=
    (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hn0))
  have hlog := hd.clog (mem_slitPlane_one_sub (by omega) (by linarith))
  exact ((hlog.neg).const_mul _).differentiableWithinAt

/-- **The Euler product of the exchanged system.** On `Re s > max(σ, 1)`, `ζ G` is the Euler product of the
multiset with multiplicities `b(n) = 1_{prime}(n) + e(n)`. -/
theorem zeta_mul_exchangeFactor_eq_exp (hσ : 0 < σ)
    (he : Summable fun n : ℕ => |(e (n + 2) : ℝ)| * ((n + 2 : ℕ) : ℝ) ^ (-σ)) {s : ℂ} (hs1 : 1 < s.re)
    (hsσ : σ ≤ s.re) :
    riemannZeta s * exchangeFactor e s =
      Complex.exp (∑' n : ℕ, (((if (n + 2).Prime then 1 else 0 : ℤ) + e (n + 2) : ℤ) : ℂ) *
        (-Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s)))) := by
  classical
  set F : ℕ → ℂ := fun n => ((if (n + 2).Prime then 1 else 0 : ℤ) : ℂ) *
    (-Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s))) with hF
  have hinj : Function.Injective fun p : Nat.Primes => (p : ℕ) - 2 := by
    intro p q h
    have h1 := p.2.two_le
    have h2 := q.2.two_le
    exact Subtype.ext (by simp only at h; omega)
  have hsupp : Function.support F ⊆ Set.range fun p : Nat.Primes => (p : ℕ) - 2 := by
    intro n hn
    by_cases hp : (n + 2).Prime
    · exact ⟨⟨n + 2, hp⟩, by simp⟩
    · simp [hF, hp] at hn
  have heuler : ∑' n, F n = ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun p => ?_
    have hp2 := p.2.two_le
    simp only [hF]
    have heq : (p : ℕ) - 2 + 2 = p := by omega
    rw [heq, if_pos p.2]
    simp
  have hζ : Complex.exp (∑' n, F n) = riemannZeta s := by
    rw [heuler]
    exact riemannZeta_eulerProduct_exp_log hs1
  have hsF : Summable F := by
    have hsum : Summable fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(s.re)) / (1 - (2 : ℝ) ^ (-(s.re))) := by
      refine Summable.div_const ?_ _
      have h := (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
      refine h.congr fun n => ?_
      push_cast
      rfl
    refine Summable.of_norm_bounded hsum fun n => ?_
    have hbound := norm_log_one_sub_le (n := n + 2) (by omega) (by linarith : 0 < s.re) (le_refl s.re)
    simp only [hF, norm_mul, norm_neg]
    have hcoef : ‖(((if (n + 2).Prime then 1 else 0 : ℤ) : ℤ) : ℂ)‖ ≤ 1 := by
      split_ifs <;> simp
    calc _ ≤ 1 * ‖Complex.log (1 - ((n + 2 : ℕ) : ℂ) ^ (-s))‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hbound
  have hsE := summable_exchange_term hσ he hsσ
  rw [← hζ, exchangeFactor, exchangeLog, ← Complex.exp_add, ← hsF.tsum_add hsE]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [hF]
  push_cast
  ring

end GaloisForLFunctions.RigidArithmeticOfCuts
