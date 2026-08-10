import GaloisForLFunctions.RHTower.MobiusCofactorAmplifiedToken
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Forbidden-support stability of an all-interval three-prime count

Deleting the prime divisors of an adversarial modulus `A ≤ x^B` from each of the three prime
variables of an all-interval `E₃` count costs nothing.  This file proves the elementary layer of
that stability, in the parameter regime

```text
P₁ = (log x)^a,   a = 11/10,   R = √(x/P₁)/2,   h = √x (log x)^(1+a/2).
```

- an adversarial support has few prime divisors above a threshold, because their product divides
  `A`, so their number is at most `log A / log T`;
- consequently its Dirichlet polynomial is uniformly `O(log A/(T log T))` on `Re s ≥ 1`, and so is
  the harmonic mass it removes;
- the perturbed mixed mean square is controlled by the unperturbed one plus the sup-norm square
  times the second factor's mean square;
- a fixed large prime forces the remaining variable into a window carrying at most `4 log x + 1`
  integers, and the resulting polylogarithmic count is negligible against `√x`;
- the small and large prime ranges are eventually disjoint, which is what makes the surviving
  products squarefree.

The all-interval count itself, and the mean-value and sieve estimates it rests on, are external
analytic inputs and are not stated here.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

namespace ForbiddenSupport

/-! ## The size of an adversarial prime support -/

/-- Distinct prime divisors of `A` above a threshold are few: their product divides `A`, so the
sum of their logarithms is at most `log A`. -/
theorem card_mul_log_le_log {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ} (hS : S ⊆ A.primeFactors)
    {T : ℝ} (hT : 1 < T) (hge : ∀ p ∈ S, T ≤ (p : ℝ)) :
    (S.card : ℝ) * Real.log T ≤ Real.log A := by
  have hppos : ∀ p ∈ S, (1 : ℝ) < (p : ℝ) := fun p hp => lt_of_lt_of_le hT (hge p hp)
  have hdvd : (∏ p ∈ S, p) ∣ A :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hS).trans (Nat.prod_primeFactors_dvd A)
  have hpos : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hS hp)).pos
  have hle : (∏ p ∈ S, p) ≤ A := Nat.le_of_dvd (Nat.pos_of_ne_zero hA) hdvd
  have hprod : ((∏ p ∈ S, p : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by push_cast; ring
  have hlog : Real.log (∏ p ∈ S, (p : ℝ)) ≤ Real.log A := by
    rw [← hprod]
    exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  rw [Real.log_prod fun p hp => ne_of_gt (lt_trans one_pos (hppos p hp))] at hlog
  have hsum : (S.card : ℝ) * Real.log T ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    have h := Finset.card_nsmul_le_sum S (fun p => Real.log (p : ℝ)) (Real.log T)
      fun p hp => Real.log_le_log (by linarith) (hge p hp)
    simpa [nsmul_eq_mul] using h
  linarith

/-- **(FS11).**  The number of prime divisors of `A` above `T` is at most `log A / log T`; in
particular it is bounded when `T` is a fixed power of `A`. -/
theorem card_le_log_div_log {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ} (hS : S ⊆ A.primeFactors)
    {T : ℝ} (hT : 1 < T) (hge : ∀ p ∈ S, T ≤ (p : ℝ)) :
    (S.card : ℝ) ≤ Real.log A / Real.log T := by
  rw [le_div_iff₀ (Real.log_pos hT)]
  exact card_mul_log_le_log hA hS hT hge

/-! ## The deleted Dirichlet polynomial -/

/-- Each deleted term is at most `1/T` in modulus on the closed half-plane `Re s ≥ 1`. -/
theorem norm_cpow_le {T : ℝ} (hT : 1 ≤ T) {p : ℕ} (hp : T ≤ (p : ℝ)) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ 1 / T := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := le_trans hT hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
  have hstep : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hval : (p : ℝ) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  have hTle : 1 / (p : ℝ) ≤ 1 / T := one_div_le_one_div_of_le (by linarith) hp
  rw [hval] at hstep
  linarith

/-- **(FS5), sup-norm form.**  The forbidden-support Dirichlet polynomial is uniformly small. -/
theorem norm_supportSum_le_card_div {S : Finset ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hge : ∀ p ∈ S, T ≤ (p : ℝ)) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ S, ((p : ℝ) : ℂ) ^ (-s)‖ ≤ (S.card : ℝ) / T := by
  calc ‖∑ p ∈ S, ((p : ℝ) : ℂ) ^ (-s)‖
      ≤ ∑ p ∈ S, ‖((p : ℝ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, 1 / T := Finset.sum_le_sum fun p hp => norm_cpow_le hT (hge p hp) hs
    _ = (S.card : ℝ) / T := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **(FS5).**  Against an adversarial modulus the deleted polynomial is `O(log A/(T log T))`
uniformly on `Re s ≥ 1`. -/
theorem norm_supportSum_le_log {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ} (hS : S ⊆ A.primeFactors)
    {T : ℝ} (hT : 1 < T) (hge : ∀ p ∈ S, T ≤ (p : ℝ)) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∑ p ∈ S, ((p : ℝ) : ℂ) ^ (-s)‖ ≤ Real.log A / (T * Real.log T) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hstep := norm_supportSum_le_card_div (S := S) hT.le hge hs
  have hmono : (S.card : ℝ) / T ≤ Real.log A / Real.log T / T :=
    div_le_div_of_nonneg_right (card_le_log_div_log hA hS hT hge) hT0.le
  have hrw : Real.log A / Real.log T / T = Real.log A / (T * Real.log T) := by
    rw [div_div]
    ring
  linarith [hrw.le, hrw.ge]

/-- **(FS10).**  The harmonic mass carried by the deleted support obeys the same bound, so the
long-interval main term keeps `1 - o(1)` of its size. -/
theorem sum_inv_le_log {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ} (hS : S ⊆ A.primeFactors)
    {T : ℝ} (hT : 1 < T) (hge : ∀ p ∈ S, T ≤ (p : ℝ)) :
    ∑ p ∈ S, ((p : ℝ))⁻¹ ≤ Real.log A / (T * Real.log T) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hterm : ∑ p ∈ S, ((p : ℝ))⁻¹ ≤ (S.card : ℝ) / T := by
    calc ∑ p ∈ S, ((p : ℝ))⁻¹
        ≤ ∑ _p ∈ S, T⁻¹ := Finset.sum_le_sum fun p hp => by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le hT0 (hge p hp)
      _ = (S.card : ℝ) / T := by
          rw [Finset.sum_const, nsmul_eq_mul, inv_eq_one_div, mul_one_div]
  have hmono : (S.card : ℝ) / T ≤ Real.log A / Real.log T / T :=
    div_le_div_of_nonneg_right (card_le_log_div_log hA hS hT hge) hT0.le
  have hrw : Real.log A / Real.log T / T = Real.log A / (T * Real.log T) := by
    rw [div_div]
    ring
  linarith [hrw.le, hrw.ge]

/-! ## The perturbed mixed mean square -/

/-- **(FS6), pointwise.** -/
theorem norm_sq_sub_mul_le {u v w : ℂ} {M : ℝ} (hv : ‖v‖ ≤ M) :
    ‖(u - v) * w‖ ^ 2 ≤ 2 * ‖u * w‖ ^ 2 + 2 * M ^ 2 * ‖w‖ ^ 2 := by
  have hM : 0 ≤ M := le_trans (norm_nonneg v) hv
  have hsub : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * M ^ 2 := by
    have h1 : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v),
      sq_nonneg (‖u‖ - ‖v‖), hv, hM]
  have hw : (0 : ℝ) ≤ ‖w‖ ^ 2 := sq_nonneg _
  calc ‖(u - v) * w‖ ^ 2 = ‖u - v‖ ^ 2 * ‖w‖ ^ 2 := by rw [norm_mul, mul_pow]
    _ ≤ (2 * ‖u‖ ^ 2 + 2 * M ^ 2) * ‖w‖ ^ 2 := by nlinarith
    _ = 2 * ‖u * w‖ ^ 2 + 2 * M ^ 2 * ‖w‖ ^ 2 := by rw [norm_mul, mul_pow]; ring

/-- **(FS6).**  Deleting a uniformly small polynomial perturbs the mixed mean square by at most its
sup-norm square times the second factor's mean square. -/
theorem integral_norm_sq_sub_mul_le {a b M : ℝ} (hab : a ≤ b) {u v w : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc a b, ‖v t‖ ≤ M)
    (h1 : IntervalIntegrable (fun t => ‖(u t - v t) * w t‖ ^ 2) volume a b)
    (h2 : IntervalIntegrable (fun t => ‖u t * w t‖ ^ 2) volume a b)
    (h3 : IntervalIntegrable (fun t => ‖w t‖ ^ 2) volume a b) :
    (∫ t in a..b, ‖(u t - v t) * w t‖ ^ 2)
      ≤ 2 * (∫ t in a..b, ‖u t * w t‖ ^ 2) + 2 * M ^ 2 * ∫ t in a..b, ‖w t‖ ^ 2 := by
  have hstep := intervalIntegral.integral_mono_on hab h1
    ((h2.const_mul 2).add (h3.const_mul (2 * M ^ 2)))
    fun t ht => norm_sq_sub_mul_le (hv t ht)
  rwa [intervalIntegral.integral_add (h2.const_mul 2) (h3.const_mul (2 * M ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep

/-! ## The window parameters -/

/-- The small-prime exponent `a = 11/10` of `(FS1)`. -/
noncomputable def fsExponent : ℝ := 11 / 10

/-- The small-prime scale `P₁ = (log x)^a`. -/
noncomputable def fsSmallScale (x : ℝ) : ℝ := Real.log x ^ fsExponent

/-- The large-prime scale `R = √(x/P₁)/2`. -/
noncomputable def fsLargeScale (x : ℝ) : ℝ := Real.sqrt (x / fsSmallScale x) / 2

/-- The window length `h = √x (log x)^(1+a/2)`. -/
noncomputable def fsWindow (x : ℝ) : ℝ := Real.sqrt x * Real.log x ^ (1 + fsExponent / 2)

theorem fsSmallScale_pos {x : ℝ} (hx : 1 < x) : 0 < fsSmallScale x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

theorem fsWindow_pos {x : ℝ} (hx : 1 < x) : 0 < fsWindow x :=
  mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.rpow_pos_of_pos (Real.log_pos hx) _)

theorem fsLargeScale_pos {x : ℝ} (hx : 1 < x) : 0 < fsLargeScale x :=
  div_pos (Real.sqrt_pos.mpr (div_pos (by linarith) (fsSmallScale_pos hx))) (by norm_num)

theorem sqrt_fsSmallScale {x : ℝ} (hx : 1 < x) :
    Real.sqrt (fsSmallScale x) = Real.log x ^ (fsExponent / 2) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsplit : Real.log x ^ fsExponent
      = Real.log x ^ (fsExponent / 2) * Real.log x ^ (fsExponent / 2) := by
    rw [← Real.rpow_add hlog]
    congr 1
    ring
  rw [fsSmallScale, hsplit, Real.sqrt_mul_self (Real.rpow_nonneg hlog.le _)]

theorem fsLargeScale_eq {x : ℝ} (hx : 1 < x) :
    fsLargeScale x = Real.sqrt x / Real.log x ^ (fsExponent / 2) / 2 := by
  rw [fsLargeScale, Real.sqrt_div (by linarith : (0 : ℝ) ≤ x), sqrt_fsSmallScale hx]

/-- **(FS12), exact form.**  At the lower endpoints of the two prime ranges the window carries
exactly `4 log x` scaled units. -/
theorem fsWindow_div_eq {x : ℝ} (hx : 1 < x) :
    fsWindow x / (fsSmallScale x * (fsLargeScale x / 2)) = 4 * Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hL2 : (0 : ℝ) < Real.log x ^ (fsExponent / 2) := Real.rpow_pos_of_pos hlog _
  have hsqx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hcomb : Real.log x ^ (1 + fsExponent / 2)
      = Real.log x * Real.log x ^ (fsExponent / 2) := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  have hLa : fsSmallScale x
      = Real.log x ^ (fsExponent / 2) * Real.log x ^ (fsExponent / 2) := by
    rw [fsSmallScale, ← Real.rpow_add hlog]
    congr 1
    ring
  rw [fsWindow, fsLargeScale_eq hx, hcomb, hLa]
  field_simp
  ring

/-! ## The integer count in a scaled window -/

theorem mem_scaledWindow {c x h : ℝ} (hc : 0 < c) (m : ℤ) :
    m ∈ Finset.Ioc ⌊x / c⌋ ⌊(x + h) / c⌋ ↔ x < c * (m : ℝ) ∧ c * (m : ℝ) ≤ x + h := by
  rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor, div_lt_iff₀ hc, le_div_iff₀ hc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The integers in a half-open interval number at most its length plus one. -/
theorem card_Ioc_floor_le {α β : ℝ} (hαβ : α ≤ β) :
    ((Finset.Ioc ⌊α⌋ ⌊β⌋).card : ℝ) ≤ β - α + 1 := by
  have hmono : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_le_floor hαβ
  have h0 : (0 : ℤ) ≤ ⌊β⌋ - ⌊α⌋ := by omega
  rw [Int.card_Ioc]
  have hcast : (((⌊β⌋ - ⌊α⌋).toNat : ℕ) : ℝ) = (⌊β⌋ : ℝ) - (⌊α⌋ : ℝ) := by
    have hz := Int.toNat_of_nonneg h0
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hz
  rw [hcast]
  have h1 : (⌊β⌋ : ℝ) ≤ β := Int.floor_le _
  have h2 : α - 1 < (⌊α⌋ : ℝ) := Int.sub_one_lt_floor _
  linarith

/-- **(FS12).**  A scaled window of length `h` carries at most `h/c + 1` integers. -/
theorem card_scaledWindow_le {c x h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) :
    ((Finset.Ioc ⌊x / c⌋ ⌊(x + h) / c⌋).card : ℝ) ≤ h / c + 1 := by
  have hle : x / c ≤ (x + h) / c := div_le_div_of_nonneg_right (by linarith) hc.le
  have h3 : (x + h) / c = x / c + h / c := by ring
  have := card_Ioc_floor_le hle
  linarith

/-- **(FS12), applied.**  With a fixed large prime and a small prime in the `(FS1)` ranges, the
remaining variable ranges over at most `4 log x + 1` integers. -/
theorem card_window_le {x : ℝ} (hx : 1 < x) {p q : ℝ} (hp : fsSmallScale x ≤ p)
    (hq : fsLargeScale x / 2 ≤ q) :
    ((Finset.Ioc ⌊x / (p * q)⌋ ⌊(x + fsWindow x) / (p * q)⌋).card : ℝ)
      ≤ 4 * Real.log x + 1 := by
  have hP : 0 < fsSmallScale x := fsSmallScale_pos hx
  have hR : 0 < fsLargeScale x / 2 := by
    have := fsLargeScale_pos hx
    linarith
  have hW : 0 ≤ fsWindow x := (fsWindow_pos hx).le
  have hD : 0 < fsSmallScale x * (fsLargeScale x / 2) := mul_pos hP hR
  have hDpq : fsSmallScale x * (fsLargeScale x / 2) ≤ p * q :=
    mul_le_mul hp hq hR.le (le_trans hP.le hp)
  have hpq : 0 < p * q := lt_of_lt_of_le hD hDpq
  have hinv : 1 / (p * q) ≤ 1 / (fsSmallScale x * (fsLargeScale x / 2)) :=
    one_div_le_one_div_of_le hD hDpq
  have hdiv : fsWindow x / (p * q) ≤ 4 * Real.log x := by
    have hinv' : (p * q)⁻¹ ≤ (fsSmallScale x * (fsLargeScale x / 2))⁻¹ := by
      rw [← one_div, ← one_div]
      exact hinv
    have hstep : fsWindow x / (p * q)
        ≤ fsWindow x / (fsSmallScale x * (fsLargeScale x / 2)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv' hW
    rwa [fsWindow_div_eq hx] at hstep
  have hcount := card_scaledWindow_le (c := p * q) (x := x) (h := fsWindow x) hpq hW
  linarith

/-! ## Polylogarithmic negligibility -/

/-- Every polylogarithmic quantity is negligible against the square root. -/
theorem tendsto_logRpow_div_sqrt (r : ℝ) :
    Tendsto (fun x : ℝ => Real.log x ^ r / Real.sqrt x) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop r (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr fun x => ?_
  rw [Real.sqrt_eq_rpow]

/-- **(FS13).**  The triple count through a fixed large prime, weighted against the main term's
`(log x)^{-0.45}` normalisation, is negligible. -/
theorem tendsto_fsNegligible :
    Tendsto (fun x : ℝ =>
      fsSmallScale x * (4 * Real.log x + 1) * Real.log x ^ (45 / 100 : ℝ) / Real.sqrt x)
      atTop (nhds 0) := by
  have hmaj : Tendsto
      (fun x : ℝ => 5 * (Real.log x ^ (51 / 20 : ℝ) / Real.sqrt x)) atTop (nhds 0) := by
    have h := (tendsto_logRpow_div_sqrt (51 / 20 : ℝ)).const_mul 5
    rwa [mul_zero] at h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have h1 : 0 < fsSmallScale x := fsSmallScale_pos hx
    have h2 : (0 : ℝ) < Real.log x ^ (45 / 100 : ℝ) := Real.rpow_pos_of_pos hlog _
    have h3 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by
      have := Real.exp_pos (1 : ℝ)
      have h1 : (1 : ℝ) < Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      exact h1) hx
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hx
    have hlog : 0 < Real.log x := by linarith
    have h3 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hcomb : fsSmallScale x * Real.log x ^ (45 / 100 : ℝ)
        = Real.log x ^ (31 / 20 : ℝ) := by
      rw [fsSmallScale, ← Real.rpow_add hlog, fsExponent]
      congr 1
      norm_num
    have hfull : Real.log x * Real.log x ^ (31 / 20 : ℝ) = Real.log x ^ (51 / 20 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add hlog]
      congr 1
      norm_num
    have hbound : fsSmallScale x * (4 * Real.log x + 1) * Real.log x ^ (45 / 100 : ℝ)
        ≤ 5 * Real.log x ^ (51 / 20 : ℝ) := by
      have hstep : (4 * Real.log x + 1) ≤ 5 * Real.log x := by linarith
      have hpos : (0 : ℝ) < Real.log x ^ (31 / 20 : ℝ) := Real.rpow_pos_of_pos hlog _
      calc fsSmallScale x * (4 * Real.log x + 1) * Real.log x ^ (45 / 100 : ℝ)
          = (4 * Real.log x + 1) * (fsSmallScale x * Real.log x ^ (45 / 100 : ℝ)) := by ring
        _ = (4 * Real.log x + 1) * Real.log x ^ (31 / 20 : ℝ) := by rw [hcomb]
        _ ≤ (5 * Real.log x) * Real.log x ^ (31 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_right hstep hpos.le
        _ = 5 * (Real.log x * Real.log x ^ (31 / 20 : ℝ)) := by ring
        _ = 5 * Real.log x ^ (51 / 20 : ℝ) := by rw [hfull]
    calc fsSmallScale x * (4 * Real.log x + 1) * Real.log x ^ (45 / 100 : ℝ) / Real.sqrt x
        ≤ 5 * Real.log x ^ (51 / 20 : ℝ) / Real.sqrt x :=
          div_le_div_of_nonneg_right hbound h3.le
      _ = 5 * (Real.log x ^ (51 / 20 : ℝ) / Real.sqrt x) := by ring

/-- The small and large prime ranges of `(FS1)` are eventually disjoint, which is what makes the
surviving triples squarefree. -/
theorem eventually_smallScale_lt_largeScale :
    ∀ᶠ x : ℝ in atTop, 2 * fsSmallScale x < fsLargeScale x / 2 := by
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x ^ (33 / 20 : ℝ) / Real.sqrt x < 1 / 8 :=
    (tendsto_logRpow_div_sqrt (33 / 20 : ℝ)).eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hsqx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hL2 : (0 : ℝ) < Real.log x ^ (fsExponent / 2) := Real.rpow_pos_of_pos hlog _
  have hcomb : fsSmallScale x * Real.log x ^ (fsExponent / 2)
      = Real.log x ^ (33 / 20 : ℝ) := by
    rw [fsSmallScale, ← Real.rpow_add hlog, fsExponent]
    congr 1
    norm_num
  have hkey : 8 * Real.log x ^ (33 / 20 : ℝ) < Real.sqrt x := by
    rw [div_lt_iff₀ hsqx] at hx
    linarith
  rw [fsLargeScale_eq hx1, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2),
    lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), lt_div_iff₀ hL2]
  nlinarith [hkey, hcomb]

/-! ## The block-admission corollary -/

/-- **(FS14), parity.**  A prime cofactor times an exact-three-prime token has Möbius `+1`, the
opposite of the single-prime block it replaces. -/
theorem mobiusComplexCoefficient_prime_mul_threePrime {l q₁ q₂ q₃ : ℕ}
    (hl : l.Prime) (h1 : q₁.Prime) (h2 : q₂.Prime) (h3 : q₃.Prime)
    (hl1 : l.Coprime q₁) (hl2 : l.Coprime q₂) (hl3 : l.Coprime q₃)
    (h13 : q₁.Coprime q₃) (h23 : q₂.Coprime q₃) (h12 : q₁.Coprime q₂) :
    mobiusComplexCoefficient (l * (q₁ * q₂ * q₃)) = 1 := by
  rw [mobiusComplexCoefficient_mul_of_coprime ((hl1.mul_right hl2).mul_right hl3),
    mobiusComplexCoefficient_mul_of_coprime (Nat.Coprime.mul_left h13 h23),
    mobiusComplexCoefficient_mul_of_coprime h12,
    mobiusComplexCoefficient_prime hl, mobiusComplexCoefficient_prime h1,
    mobiusComplexCoefficient_prime h2, mobiusComplexCoefficient_prime h3]
  ring

/-- Amplifying a reduced centre by its cofactor turns the square root at `u/ℓ` into the square
root at `u ℓ`. -/
theorem mul_sqrt_div_eq_sqrt_mul {u l : ℝ} (hu : 0 ≤ u) (hl : 0 < l) :
    l * Real.sqrt (u / l) = Real.sqrt (u * l) := by
  have hspos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hs : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
  rw [Real.sqrt_div hu, Real.sqrt_mul hu]
  field_simp
  nlinarith [hs, hspos, Real.sqrt_nonneg u]

/-- **(FS14).**  A near-square-root token at the reduced centre `u/ℓ`, amplified by the prime
cofactor `ℓ`, stays within `√(u ℓ)` times the same polylogarithmic factor of `u`. -/
theorem abs_amplified_gap_le {u l m C r : ℝ} (hu : 0 ≤ u) (hl : 0 < l)
    (hm : |m - u / l| ≤ C * Real.sqrt (u / l) * r) :
    |l * m - u| ≤ C * Real.sqrt (u * l) * r := by
  have h1 : |l * m - l * (u / l)| ≤ l * (C * Real.sqrt (u / l) * r) :=
    abs_cofactor_scaled_gap_le hl.le hm
  have h2 : l * (u / l) = u := by field_simp
  have h3 : l * (C * Real.sqrt (u / l) * r) = C * (l * Real.sqrt (u / l)) * r := by ring
  rw [h2, h3, mul_sqrt_div_eq_sqrt_mul hu hl] at h1
  exact h1

/-! ## The diagonal -/

/-- The square root increases by at most `h/(2√x)` over a window of length `h`. -/
theorem sqrt_add_sub_sqrt_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    Real.sqrt (x + h) - Real.sqrt x ≤ h / (2 * Real.sqrt x) := by
  have hb : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt (x + h) * Real.sqrt (x + h) = x + h := Real.mul_self_sqrt (by linarith)
  have hsq2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hsq, hsq2, sq_nonneg (Real.sqrt (x + h) - Real.sqrt x)]

/-- **(FS12), diagonal form.**  On the diagonal `p₂ = p₃` the square constraint leaves at most
`log x / 2 + 1` integers, so the diagonal carries the same polylogarithmic bound as `(FS13)` and
the surviving triples have three distinct primes. -/
theorem card_diagonalWindow_le {x : ℝ} (hx : 1 < x) {p : ℝ} (hp : fsSmallScale x ≤ p) :
    ((Finset.Ioc ⌊Real.sqrt (x / p)⌋ ⌊Real.sqrt ((x + fsWindow x) / p)⌋).card : ℝ)
      ≤ Real.log x / 2 + 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hP : 0 < fsSmallScale x := fsSmallScale_pos hx
  have hp0 : 0 < p := lt_of_lt_of_le hP hp
  have hW : 0 ≤ fsWindow x := (fsWindow_pos hx).le
  have hsqp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsqx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsplit1 : Real.sqrt (x / p) = Real.sqrt x / Real.sqrt p := Real.sqrt_div hx0.le p
  have hsplit2 : Real.sqrt ((x + fsWindow x) / p)
      = Real.sqrt (x + fsWindow x) / Real.sqrt p := Real.sqrt_div (by linarith) p
  have hmono : Real.sqrt (x / p) ≤ Real.sqrt ((x + fsWindow x) / p) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hp0.le)
  have hcard := card_Ioc_floor_le hmono
  -- the window of square roots
  have hstep : Real.sqrt ((x + fsWindow x) / p) - Real.sqrt (x / p)
      ≤ fsWindow x / (2 * Real.sqrt x) / Real.sqrt p := by
    rw [hsplit1, hsplit2, div_sub_div_same, div_le_div_iff₀ hsqp hsqp]
    have h := sqrt_add_sub_sqrt_le hx0 hW
    nlinarith [h, hsqp]
  -- the polylogarithmic evaluation
  have hsqP : Real.log x ^ (fsExponent / 2) ≤ Real.sqrt p := by
    rw [← sqrt_fsSmallScale hx]
    exact Real.sqrt_le_sqrt hp
  have hLpos : (0 : ℝ) < Real.log x ^ (fsExponent / 2) := Real.rpow_pos_of_pos hlog _
  have hval : fsWindow x / (2 * Real.sqrt x) / Real.log x ^ (fsExponent / 2)
      = Real.log x / 2 := by
    rw [fsWindow]
    have hcomb : Real.log x ^ (1 + fsExponent / 2)
        = Real.log x * Real.log x ^ (fsExponent / 2) := by
      rw [Real.rpow_add hlog, Real.rpow_one]
    rw [hcomb]
    field_simp
  have hfinal : fsWindow x / (2 * Real.sqrt x) / Real.sqrt p ≤ Real.log x / 2 := by
    rw [← hval]
    have hnum : (0 : ℝ) ≤ fsWindow x / (2 * Real.sqrt x) := by positivity
    have hinv : 1 / Real.sqrt p ≤ 1 / Real.log x ^ (fsExponent / 2) :=
      one_div_le_one_div_of_le hLpos hsqP
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv' : (Real.sqrt p)⁻¹ ≤ (Real.log x ^ (fsExponent / 2))⁻¹ := by
      rw [← one_div, ← one_div]
      exact hinv
    exact mul_le_mul_of_nonneg_left hinv' hnum
  linarith

end ForbiddenSupport

end RHTower
