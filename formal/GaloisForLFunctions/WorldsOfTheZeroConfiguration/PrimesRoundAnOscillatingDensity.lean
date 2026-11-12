import GaloisForLFunctions.WorldsOfTheZeroConfiguration.GreedyRoundingOfASignedTarget
import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct
import Mathlib.NumberTheory.Chebyshev

/-!
# Primes round an oscillating density

The greedy rounding of a target `m : ℕ → ℝ` on the primes with the weights `log p` gives signs
`ε(p) ∈ {−1, 0, 1}` (`gedit m`): `+1` on primes to be doubled, `−1` on primes to be deleted.

* **Thinness** (`sum_abs_gedit_le`, `summable_abs_gedit_rpow`).  The edited primes up to `n` have
  logarithmic mass at most `Σ_{k ≤ n} |m(k)|`.
* **Discrepancy** (`abs_gdisc_le`).  Let the primes satisfy the window bound
  `θ(y + L) − θ(y) ≥ (L − (y + L)^α)/2` for `y ≥ X`.  If beyond `n₁ ≥ X` the drift of the target on
  an interval `(a, n]` is at most `(n − a)/4 + B(n)`, and at most `B(n)` when `n − a ≤ 2n^α`, then
  `|Σ_{k ≤ n} (m(k) − ε(k) log k)| ≤ log(n + 1) + Σ_{k ≤ n₁} |m(k)| + B(n)`: a long interval
  carries prime mass `≥ (n − a)/4`.

**The target of a zero pair.**  For `0 < Re ρ < 1`, `η = 1 − Re ρ`, the target
`m(k) = −2 Re k^{ρ−1}` (`target ρ`) is minus the coefficient of `ζ(s + 1 − ρ) + ζ(s + 1 − ρ̄)`.
Its greedy edit (`edit ρ`) edits `O(n^{Re ρ})` primes up to `n` (`sum_abs_edit_le`) and has
discrepancy `O(n^c)` for every `c > 0` with `c ≥ α − η` (`exists_abs_editDisc_le_rpow`).
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits

open GreedyRounding GaloisForLFunctions.HTGeometry.BoundedPartialSums

/-! ## The greedy edit of the primes against a target -/

/-- The greedy edit of the primes against the target `m`: `+1` on doubled primes, `−1` on deleted
primes. -/
def gedit (m : ℕ → ℝ) (k : ℕ) : ℤ := sgn Nat.Prime (fun j : ℕ => Real.log j) m k

/-- The discrepancy `Σ_{0<k≤n} (m(k) − ε(k) log k)` of the greedy edit. -/
def gdisc (m : ℕ → ℝ) (n : ℕ) : ℝ := disc Nat.Prime (fun j : ℕ => Real.log j) m n

@[simp] theorem gedit_zero (m : ℕ → ℝ) : gedit m 0 = 0 := rfl

theorem gedit_eq_zero_of_not_prime (m : ℕ → ℝ) {k : ℕ} (hk : ¬ k.Prime) : gedit m k = 0 :=
  sgn_eq_zero_of_not _ _ _ hk

theorem gedit_cases (m : ℕ → ℝ) (k : ℕ) : gedit m k = 1 ∨ gedit m k = -1 ∨ gedit m k = 0 :=
  sgn_cases _ _ _ k

theorem abs_gedit_le_one (m : ℕ → ℝ) (k : ℕ) : |(gedit m k : ℝ)| ≤ 1 := abs_sgn_le_one _ _ _ k

theorem gdisc_eq_sum (m : ℕ → ℝ) (n : ℕ) :
    gdisc m n = ∑ k ∈ Ioc 0 n, (m k - gedit m k * Real.log k) :=
  disc_eq_sum _ _ _ n

/-! ## Elementary sums -/

theorem primeLog_nonneg (k : ℕ) : (0 : ℝ) ≤ if k.Prime then Real.log k else 0 := by
  split_ifs
  · exact Real.log_natCast_nonneg k
  · exact le_rfl

/-- `θ(n) − θ(a)` is the prime mass of `(a, n]`. -/
theorem theta_sub_theta {a n : ℕ} (han : a ≤ n) :
    Chebyshev.theta n - Chebyshev.theta a = ∑ k ∈ Ioc a n, if k.Prime then Real.log k else 0 := by
  have h : ∀ j : ℕ, Chebyshev.theta j = ∑ k ∈ Ioc 0 j, if k.Prime then Real.log k else 0 := by
    intro j
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, Finset.sum_filter]
  rw [h n, h a, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) han]
  ring

theorem sum_Ioc_le_of_le {f : ℕ → ℝ} {c : ℝ} {a n : ℕ} (han : a ≤ n)
    (h : ∀ k ∈ Ioc a n, f k ≤ c) : ∑ k ∈ Ioc a n, f k ≤ ((n : ℝ) - a) * c := by
  calc ∑ k ∈ Ioc a n, f k ≤ ∑ _k ∈ Ioc a n, c := Finset.sum_le_sum h
    _ = ((n : ℝ) - a) * c := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub han]

/-- A nonnegative sequence with partial sums `O(n^θ)` is summable against `k^{−σ}`, `σ > θ`. -/
theorem summable_mul_rpow_of_sum_le {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 = 0)
    {θ K σ : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hsum : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Ioc 0 n, c k ≤ K * (n : ℝ) ^ θ) (hσ : θ < σ) :
    Summable fun k : ℕ => c k * (k : ℝ) ^ (-σ) := by
  have hA : ∀ n : ℕ, 1 ≤ n →
      ‖partialSum (fun k => (c k : ℂ)) (n + 1)‖ ≤ K * (n : ℝ) ^ θ := by
    intro n hn
    have e : partialSum (fun k => (c k : ℂ)) (n + 1) = ((∑ k ∈ Ioc 0 n, c k : ℝ) : ℂ) := by
      unfold partialSum
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), hc0,
        Complex.ofReal_zero, zero_add, Complex.ofReal_sum]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext m; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => hc k)]
    exact hsum n hn
  have hbd := norm_sum_mul_powNeg_le_of_growth (a := fun k => (c k : ℂ)) hθ hK (by simp [hc0]) hA
    (z := (σ : ℂ)) (by simpa using hσ)
  refine summable_of_sum_range_le
    (c := K * (1 + ‖(σ : ℂ)‖ * ∑' i : ℕ, (i : ℝ) ^ (θ - (σ : ℂ).re - 1)))
    (fun k => mul_nonneg (hc k) (Real.rpow_nonneg (Nat.cast_nonneg k) _)) fun N => ?_
  have e : ((∑ k ∈ range N, c k * (k : ℝ) ^ (-σ) : ℝ) : ℂ) =
      ∑ k ∈ range N, (c k : ℂ) * powNeg (σ : ℂ) k := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul, powNeg, Complex.ofReal_cpow (Nat.cast_nonneg k),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  have h := hbd N
  rw [← e, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-! ## Thinness of a greedy edit -/

/-- The edited primes up to `n` have logarithmic mass at most the mass of the target. -/
theorem sum_abs_gedit_mul_log_le (m : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)| * Real.log k ≤ ∑ k ∈ Ioc 0 n, |m k| := by
  have h : |gdisc m n| + ∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)| * Real.log k ≤
      ∑ k ∈ Ioc 0 n, |m k| :=
    abs_disc_add_sum_le Nat.Prime (fun j : ℕ => Real.log j) m n
  linarith [abs_nonneg (gdisc m n)]

/-- The number of edited primes up to `n`. -/
theorem sum_abs_gedit_le (m : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)| ≤ (∑ k ∈ Ioc 0 n, |m k|) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Ioc 0 n,
      |(gedit m k : ℝ)| ≤ (|(gedit m k : ℝ)| * Real.log k) / Real.log 2 := by
    intro k _
    by_cases hp : k.Prime
    · rw [le_div_iff₀ hlog2]
      have h2k : Real.log 2 ≤ Real.log k :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      exact mul_le_mul_of_nonneg_left h2k (abs_nonneg _)
    · rw [gedit_eq_zero_of_not_prime m hp]; simp
  calc ∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)|
      ≤ ∑ k ∈ Ioc 0 n, (|(gedit m k : ℝ)| * Real.log k) / Real.log 2 := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)| * Real.log k) / Real.log 2 := by rw [Finset.sum_div]
    _ ≤ (∑ k ∈ Ioc 0 n, |m k|) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv (∑ k ∈ Ioc 0 n, |m k|)]
        exact mul_le_mul_of_nonneg_right (sum_abs_gedit_mul_log_le m n)
          (inv_nonneg.mpr hlog2.le)

/-- If the target has mass `O(n^θ)`, the edited primes are summable against `p^{−σ}`, `σ > θ`. -/
theorem summable_abs_gedit_rpow {m : ℕ → ℝ} {θ K σ : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hsum : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Ioc 0 n, |m k| ≤ K * (n : ℝ) ^ θ) (hσ : θ < σ) :
    Summable fun k : ℕ => |(gedit m k : ℝ)| * (k : ℝ) ^ (-σ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine summable_mul_rpow_of_sum_le (c := fun k => |(gedit m k : ℝ)|) (fun k => abs_nonneg _)
    (by simp) hθ (K := K / Real.log 2) (div_nonneg hK hlog2.le) (fun n hn => ?_) hσ
  calc ∑ k ∈ Ioc 0 n, |(gedit m k : ℝ)| ≤ (∑ k ∈ Ioc 0 n, |m k|) / Real.log 2 :=
        sum_abs_gedit_le m n
    _ ≤ (K * (n : ℝ) ^ θ) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv (K * (n : ℝ) ^ θ)]
        exact mul_le_mul_of_nonneg_right (hsum n hn) (inv_nonneg.mpr hlog2.le)
    _ = K / Real.log 2 * (n : ℝ) ^ θ := by ring

/-! ## Discrepancy of a greedy edit -/

theorem log_le_log_succ (k : ℕ) : Real.log k ≤ Real.log ((k : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact Real.log_le_log (by exact_mod_cast hk) (by linarith)

/-- **The primes pay the drift.**  If beyond `n₁` the drift of the target on `(a, n]` is at most
`(n − a)/4 + B(n)`, and at most `B(n)` on intervals of length `≤ 2n^α`, the discrepancy of the
greedy edit is at most `log(n + 1) + Σ_{k ≤ n₁} |m(k)| + B(n)`. -/
theorem abs_gdisc_le {m : ℕ → ℝ} {α X : ℝ}
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    {n₁ : ℕ} (hn₁ : X ≤ n₁) {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (hlong : ∀ a n : ℕ, n₁ ≤ a → a ≤ n →
      ∑ k ∈ Ioc a n, |m k| ≤ ((n : ℝ) - a) / 4 + B n)
    (hshort : ∀ a n : ℕ, n₁ ≤ a → a ≤ n → (n : ℝ) - a ≤ 2 * (n : ℝ) ^ α →
      ∑ k ∈ Ioc a n, |m k| ≤ B n) (n : ℕ) :
    |gdisc m n| ≤ Real.log ((n : ℝ) + 1) + (∑ k ∈ Ioc 0 n₁, |m k| + B n) := by
  set B₀ : ℝ := ∑ k ∈ Ioc 0 n₁, |m k| with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_disc_le_of_window (P := Nat.Prime) (w := fun j : ℕ => Real.log j) (m := m)
    (τ := fun k : ℕ => Real.log ((k : ℝ) + 1)) (B := fun n : ℕ => B₀ + B n)
    (fun k => Real.log_natCast_nonneg k)
    (fun a b hab => Real.log_le_log (by positivity)
      (by have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
    (by simp) log_le_log_succ (fun a n han => ?_) n
  have hPm : ∀ b : ℕ, 0 ≤ ∑ k ∈ Ioc b n, if k.Prime then Real.log k else 0 :=
    fun b => Finset.sum_nonneg fun k _ => primeLog_nonneg k
  rcases le_or_gt n n₁ with hnn | hnn
  · -- below `n₁` the drift is part of `B₀`
    have h : ∑ k ∈ Ioc a n, |m k| ≤ B₀ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc (Nat.zero_le a) hnn)
        fun _ _ _ => abs_nonneg _
    linarith [hPm a, hB n]
  · set a' : ℕ := max a n₁ with ha'
    have haa' : a ≤ a' := le_max_left _ _
    have hn₁a' : n₁ ≤ a' := le_max_right _ _
    have ha'n : a' ≤ n := max_le han hnn.le
    have hsplit := Finset.sum_Ioc_consecutive (fun k => |m k|) haa' ha'n
    have hhead : ∑ k ∈ Ioc a a', |m k| ≤ B₀ := by
      rcases le_total n₁ a with h | h
      · rw [ha', max_eq_left h, Finset.Ioc_self, Finset.sum_empty]
        exact hB₀0
      · rw [ha', max_eq_right h]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_left (Nat.zero_le a)) fun _ _ _ => abs_nonneg _
    have hprime : ∑ k ∈ Ioc a' n, (if k.Prime then Real.log k else 0) ≤
        ∑ k ∈ Ioc a n, if k.Prime then Real.log k else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left haa')
        fun k _ _ => primeLog_nonneg k
    have ha'r : (n₁ : ℝ) ≤ a' := by exact_mod_cast hn₁a'
    have hℓ0 : 0 ≤ (n : ℝ) - a' := sub_nonneg.mpr (by exact_mod_cast ha'n)
    rcases le_or_gt ((n : ℝ) - a') (2 * (n : ℝ) ^ α) with hs | hl
    · have h := hshort a' n hn₁a' ha'n hs
      linarith [hPm a]
    · -- on a long tail the primes carry a quarter of the length
      have hw := hwin a' ((n : ℝ) - a') (hn₁.trans ha'r) hℓ0
      rw [show (a' : ℝ) + ((n : ℝ) - a') = n by ring, theta_sub_theta ha'n] at hw
      have h := hlong a' n hn₁a' ha'n
      linarith

/-- **Discrepancy as a power.**  With drift slack `K₁ n^c` the discrepancy is `O(n^c)`. -/
theorem exists_abs_gdisc_le_rpow {m : ℕ → ℝ} {α X c : ℝ} (hc : 0 < c)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    {n₁ : ℕ} (hn₁ : X ≤ n₁) {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hlong : ∀ a n : ℕ, n₁ ≤ a → a ≤ n →
      ∑ k ∈ Ioc a n, |m k| ≤ ((n : ℝ) - a) / 4 + K₁ * (n : ℝ) ^ c)
    (hshort : ∀ a n : ℕ, n₁ ≤ a → a ≤ n → (n : ℝ) - a ≤ 2 * (n : ℝ) ^ α →
      ∑ k ∈ Ioc a n, |m k| ≤ K₁ * (n : ℝ) ^ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |gdisc m n| ≤ K * (n : ℝ) ^ c := by
  set B₀ : ℝ := ∑ k ∈ Ioc 0 n₁, |m k| with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB := abs_gdisc_le hwin hn₁ (B := fun n : ℕ => K₁ * (n : ℝ) ^ c)
    (fun n => mul_nonneg hK₁ (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hlong hshort
  refine ⟨1 + 1 / c + B₀ + K₁, by positivity, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnc : 1 ≤ (n : ℝ) ^ c := Real.one_le_rpow hn1 hc.le
  have hlog : Real.log ((n : ℝ) + 1) ≤ (1 + 1 / c) * (n : ℝ) ^ c := by
    have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
      rw [← Real.log_mul (by norm_num) hn0.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log n ≤ (1 / c) * ((n : ℝ) ^ c - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn0 c)
      rw [Real.log_rpow hn0] at h
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
      linarith
    have h4 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h5 : (1 / c) * ((n : ℝ) ^ c - 1) ≤ (1 / c) * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h6 : (1 + 1 / c) * (n : ℝ) ^ c = (n : ℝ) ^ c + (1 / c) * (n : ℝ) ^ c := by ring
    linarith
  have hB' : B₀ ≤ B₀ * (n : ℝ) ^ c := le_mul_of_one_le_right hB₀0 hnc
  calc |gdisc m n| ≤ Real.log ((n : ℝ) + 1) + (B₀ + K₁ * (n : ℝ) ^ c) := hB n
    _ ≤ (1 + 1 / c) * (n : ℝ) ^ c + (B₀ * (n : ℝ) ^ c + K₁ * (n : ℝ) ^ c) := by linarith
    _ = (1 + 1 / c + B₀ + K₁) * (n : ℝ) ^ c := by ring

/-! ## The target of a zero pair -/

/-- The target `m(k) = −2 Re k^{ρ−1}`. -/
def target (ρ : ℂ) (k : ℕ) : ℝ := -(2 * ((k : ℂ) ^ (ρ - 1)).re)

/-- The edit of the primes at the frequency `ρ`: the greedy edit of `target ρ`. -/
abbrev edit (ρ : ℂ) : ℕ → ℤ := gedit (target ρ)

/-- The discrepancy `Σ_{0<k≤n} (m(k) − ε(k) log k)` of the edit at `ρ`. -/
abbrev editDisc (ρ : ℂ) : ℕ → ℝ := gdisc (target ρ)

theorem edit_eq_zero_of_not_prime (ρ : ℂ) {k : ℕ} (hk : ¬ k.Prime) : edit ρ k = 0 :=
  gedit_eq_zero_of_not_prime _ hk

theorem abs_edit_le_one (ρ : ℂ) (k : ℕ) : |(edit ρ k : ℝ)| ≤ 1 := abs_gedit_le_one _ k

theorem editDisc_eq_sum (ρ : ℂ) (n : ℕ) :
    editDisc ρ n = ∑ k ∈ Ioc 0 n, (target ρ k - edit ρ k * Real.log k) :=
  gdisc_eq_sum _ n

theorem abs_target_le (ρ : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    |target ρ k| ≤ 2 * (k : ℝ) ^ (ρ.re - 1) := by
  have h := Complex.abs_re_le_norm ((k : ℂ) ^ (ρ - 1))
  rw [Complex.norm_natCast_cpow_of_pos hk, show (ρ - 1).re = ρ.re - 1 by simp] at h
  unfold target
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem abs_target_le_two {ρ : ℂ} (hρ1 : ρ.re ≤ 1) {k : ℕ} (hk : 1 ≤ k) : |target ρ k| ≤ 2 := by
  have h1 : (k : ℝ) ^ (ρ.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
  linarith [abs_target_le ρ hk]

/-- The target of a zero pair has mass at most `2 n^{Re ρ} / Re ρ`. -/
theorem sum_abs_target_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |target ρ k| ≤ 2 / ρ.re * (n : ℝ) ^ ρ.re := by
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have h2 : ∑ k ∈ Ioc 0 n, |target ρ k| ≤ 2 * ∑ k ∈ Icc 1 n, (k : ℝ) ^ (ρ.re - 1) := by
    rw [Finset.mul_sum, hI]
    exact Finset.sum_le_sum fun k hk => abs_target_le ρ (Finset.mem_Icc.mp hk).1
  have h3 := RHTower.BeurlingDeletion.DeletionData.sum_rpow_le hρ0 hρ1.le n
  have h4 : 2 / ρ.re * (n : ℝ) ^ ρ.re = 2 * ((n : ℝ) ^ ρ.re / ρ.re) := by ring
  linarith

/-- At most `O(n^{Re ρ})` primes up to `n` are edited. -/
theorem sum_abs_edit_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| ≤ 2 / ρ.re / Real.log 2 * (n : ℝ) ^ ρ.re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| ≤ (∑ k ∈ Ioc 0 n, |target ρ k|) / Real.log 2 :=
        sum_abs_gedit_le _ n
    _ ≤ (2 / ρ.re * (n : ℝ) ^ ρ.re) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv (2 / ρ.re * (n : ℝ) ^ ρ.re)]
        exact mul_le_mul_of_nonneg_right (sum_abs_target_le hρ0 hρ1 n) (inv_nonneg.mpr hlog2.le)
    _ = 2 / ρ.re / Real.log 2 * (n : ℝ) ^ ρ.re := by ring

/-- The edited primes are summable against `p^{−σ}` for `σ > Re ρ`. -/
theorem summable_abs_edit_rpow {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {σ : ℝ}
    (hσ : ρ.re < σ) : Summable fun k : ℕ => |(edit ρ k : ℝ)| * (k : ℝ) ^ (-σ) :=
  summable_abs_gedit_rpow hρ0.le (by positivity) (fun n _ => sum_abs_target_le hρ0 hρ1 n) hσ

/-- Beyond a threshold a real power exceeds a constant. -/
theorem exists_nat_forall_le_rpow {X A₁ A₂ e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) :
    ∃ n₀ : ℕ, X ≤ n₀ ∧ (1 : ℝ) ≤ n₀ ∧ (∀ x : ℝ, (n₀ : ℝ) ≤ x → A₁ ≤ x ^ e₁) ∧
      ∀ x : ℝ, (n₀ : ℝ) ≤ x → A₂ ≤ x ^ e₂ := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (max X 1) (max (A₁ ^ (1 / e₁)) (A₂ ^ (1 / e₂))))
  have h1 : A₁ ^ (1 / e₁) ≤ n₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn₀.le
  have h2 : A₂ ^ (1 / e₂) ≤ n₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hn₀.le
  refine ⟨n₀, ((le_max_left _ _).trans (le_max_left _ _)).trans hn₀.le,
    ((le_max_right _ _).trans (le_max_left _ _)).trans hn₀.le, fun x hx => ?_, fun x hx => ?_⟩
  · calc A₁ = (A₁ ^ (1 / e₁)) ^ e₁ := by
          rw [← Real.rpow_mul hA₁, one_div_mul_cancel he₁.ne', Real.rpow_one]
      _ ≤ x ^ e₁ := Real.rpow_le_rpow (Real.rpow_nonneg hA₁ _) (h1.trans hx) he₁.le
  · calc A₂ = (A₂ ^ (1 / e₂)) ^ e₂ := by
          rw [← Real.rpow_mul hA₂, one_div_mul_cancel he₂.ne', Real.rpow_one]
      _ ≤ x ^ e₂ := Real.rpow_le_rpow (Real.rpow_nonneg hA₂ _) (h2.trans hx) he₂.le

/-- On a short interval below `n ≥ n₀`, where `4 ≤ n₀^{1−α}`, every `k ∈ (a, n]` has
`k^{−η} ≤ 2 n^{−η}`. -/
theorem rpow_neg_le_of_short {α η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {a n k : ℕ} (hn : 0 < n)
    (h4 : 4 ≤ (n : ℝ) ^ (1 - α)) (hshort : (n : ℝ) - a ≤ 2 * (n : ℝ) ^ α) (hak : a < k) :
    (k : ℝ) ^ (-η) ≤ 2 * (n : ℝ) ^ (-η) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnα : 4 * (n : ℝ) ^ α ≤ n := by
    have hmul : (n : ℝ) ^ α * (n : ℝ) ^ (1 - α) = n := by
      rw [← Real.rpow_add hn0]; simp
    have hpos : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg hn0.le _
    nlinarith
  have hkr : (a : ℝ) + 1 ≤ k := by exact_mod_cast hak
  have hk2 : (n : ℝ) ≤ 2 * k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hkη : 0 < (k : ℝ) ^ η := Real.rpow_pos_of_pos hk0 η
  have hnη : 0 < (n : ℝ) ^ η := Real.rpow_pos_of_pos hn0 η
  have h1 : (n : ℝ) ^ η ≤ 2 * (k : ℝ) ^ η := by
    calc (n : ℝ) ^ η ≤ (2 * (k : ℝ)) ^ η := Real.rpow_le_rpow hn0.le hk2 hη0.le
      _ = (2 : ℝ) ^ η * (k : ℝ) ^ η := Real.mul_rpow (by norm_num) hk0.le
      _ ≤ 2 * (k : ℝ) ^ η := by
          have h2 : (2 : ℝ) ^ η ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
          rw [Real.rpow_one] at h2
          exact mul_le_mul_of_nonneg_right h2 hkη.le
  rw [Real.rpow_neg hk0.le, Real.rpow_neg hn0.le]
  have hA : ((k : ℝ) ^ η)⁻¹ ≤ ((n : ℝ) ^ η / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  rw [inv_div, div_eq_mul_inv] at hA
  exact hA

/-- **Discrepancy for a target of size `A k^{−η}`.**  If the primes satisfy the window bound and
`|m(k)| ≤ A k^{−η}`, `0 < η ≤ 1`, the discrepancy of the greedy edit is `O(n^c)` for every `c > 0`
with `c ≥ α − η`: beyond a threshold every term is at most `1/4`, and a short interval below `n`
has drift at most `4A n^{α−η}`. -/
theorem exists_abs_gdisc_le_rpow_of_abs_le {m : ℕ → ℝ} {A η α X c : ℝ} (hA : 0 ≤ A)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ A * (k : ℝ) ^ (-η))
    (hα1 : α < 1) (hc : 0 < c) (hαc : α - η ≤ c)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |gdisc m n| ≤ K * (n : ℝ) ^ c := by
  obtain ⟨n₀, hX, hn₀1, hF1, hF2⟩ := exists_nat_forall_le_rpow (X := X) (A₁ := 4 * A) (A₂ := 4)
    hη0 (show 0 < 1 - α by linarith) (by positivity) (by norm_num)
  have hpos : ∀ {a k : ℕ}, n₀ ≤ a → a < k → 1 ≤ k := fun _ hak => by omega
  refine exists_abs_gdisc_le_rpow hc hwin hX (K₁ := 4 * A) (by positivity)
    (fun a n ha han => ?_) (fun a n ha han hshort => ?_)
  · -- beyond `n₀` every term is at most `1/4`
    have hkbound : ∀ k ∈ Ioc a n, |m k| ≤ 1 / 4 := by
      intro k hkm
      have hak : a < k := (Finset.mem_Ioc.mp hkm).1
      have hkr : (n₀ : ℝ) ≤ k := by exact_mod_cast ha.trans hak.le
      have hk0 : (0 : ℝ) < k := by linarith
      have hkη : 0 < (k : ℝ) ^ η := Real.rpow_pos_of_pos hk0 η
      have h4 : A * (k : ℝ) ^ (-η) ≤ 1 / 4 := by
        rw [Real.rpow_neg hk0.le, ← div_eq_mul_inv, div_le_iff₀ hkη]
        linarith [hF1 k hkr]
      exact (hm k (hpos ha hak)).trans h4
    have h := sum_Ioc_le_of_le han hkbound
    have h0 : 0 ≤ 4 * A * (n : ℝ) ^ c :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have h1 : 1 ≤ n₀ := by exact_mod_cast hn₀1
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn₀n : (n₀ : ℝ) ≤ n := by exact_mod_cast ha.trans han
    have hnη : 0 ≤ (n : ℝ) ^ (-η) := Real.rpow_nonneg hn0.le _
    have hkbound : ∀ k ∈ Ioc a n, |m k| ≤ 2 * A * (n : ℝ) ^ (-η) := by
      intro k hkm
      have hak : a < k := (Finset.mem_Ioc.mp hkm).1
      have h2 := rpow_neg_le_of_short (α := α) hη0 hη1 hn (hF2 n hn₀n) hshort hak
      have h3 := mul_le_mul_of_nonneg_left h2 hA
      linarith [hm k (hpos ha hak)]
    have htail := sum_Ioc_le_of_le han hkbound
    have hnn' : (n : ℝ) ^ α * (n : ℝ) ^ (-η) = (n : ℝ) ^ (α - η) := by
      rw [← Real.rpow_add hn0, sub_eq_add_neg]
    have hprod := mul_le_mul_of_nonneg_right hshort hnη
    have hpow : (n : ℝ) ^ (α - η) ≤ (n : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hn1 hαc
    have hAn : 0 ≤ A * (n : ℝ) ^ (-η) := mul_nonneg hA hnη
    have hfin : ((n : ℝ) - a) * (2 * A * (n : ℝ) ^ (-η)) ≤ 4 * A * (n : ℝ) ^ (α - η) := by
      rw [← hnn']
      nlinarith [mul_le_mul_of_nonneg_left hprod hA]
    have hfin2 : 4 * A * (n : ℝ) ^ (α - η) ≤ 4 * A * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith

/-- **Discrepancy of the edit at `ρ`.**  If the primes satisfy the window bound, the discrepancy
is `O(n^c)` for every `c > 0` with `c ≥ α − η`, `η = 1 − Re ρ`. -/
theorem exists_abs_editDisc_le_rpow {ρ : ℂ} {α X c : ℝ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hα1 : α < 1) (hc : 0 < c) (hαc : α - (1 - ρ.re) ≤ c)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |editDisc ρ n| ≤ K * (n : ℝ) ^ c :=
  exists_abs_gdisc_le_rpow_of_abs_le (A := 2) (η := 1 - ρ.re) (by norm_num) (by linarith)
    (by linarith) (fun k hk => by
      have h := abs_target_le ρ hk
      rwa [show ρ.re - 1 = -(1 - ρ.re) by ring] at h) hα1 hc hαc hwin

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
