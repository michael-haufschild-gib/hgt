import GaloisForLFunctions.WorldsOfTheZeroConfiguration.GreedyRoundingOfASignedTarget
import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct
import Mathlib.NumberTheory.Chebyshev

/-!
# Primes round an oscillating density

Fix `ρ` with `0 < Re ρ < 1` and put `η = 1 − Re ρ`.  The target
`m(k) = −2 Re k^{ρ−1} = −2 k^{−η} cos(Im ρ · log k)` is minus the coefficient of
`ζ(s + 1 − ρ) + ζ(s + 1 − ρ̄)`.  The greedy rounding of `m` on the primes with the weights `log p`
gives signs `ε(p) ∈ {−1, 0, 1}` (`edit`): `+1` on primes to be doubled, `−1` on primes to be
deleted.

* **Thinness** (`sum_abs_edit_le`, `summable_abs_edit_rpow`).  At most `O(n^{Re ρ})` primes up to
  `n` are edited, so `Σ |ε(p)| p^{−σ}` converges for `σ > Re ρ`.
* **Discrepancy** (`exists_abs_editDisc_le_rpow`).  If the primes satisfy the window bound
  `θ(y + L) − θ(y) ≥ (L − (y + L)^α)/2` for `y ≥ X`, then
  `|Σ_{k ≤ n} (m(k) − ε(k) log k)| ≤ K n^c` for every `c > 0` with `c ≥ α − η`.
  On an interval longer than `2n^α` the primes carry mass `≥ ℓ/4`, more than the drift
  `≤ 2ℓ n₀^{−η}`; a shorter interval has drift `≤ 8 n^{α−η}`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits

open GreedyRounding GaloisForLFunctions.HTGeometry.BoundedPartialSums

/-- The target `m(k) = −2 Re k^{ρ−1}`. -/
def target (ρ : ℂ) (k : ℕ) : ℝ := -(2 * ((k : ℂ) ^ (ρ - 1)).re)

/-- The edit of the primes at the frequency `ρ`: `+1` on doubled primes, `−1` on deleted primes. -/
def edit (ρ : ℂ) (k : ℕ) : ℤ := sgn Nat.Prime (fun j : ℕ => Real.log j) (target ρ) k

/-- The discrepancy `Σ_{0<k≤n} (m(k) − ε(k) log k)` of the edit. -/
def editDisc (ρ : ℂ) (n : ℕ) : ℝ := disc Nat.Prime (fun j : ℕ => Real.log j) (target ρ) n

@[simp] theorem edit_zero (ρ : ℂ) : edit ρ 0 = 0 := rfl

theorem edit_eq_zero_of_not_prime (ρ : ℂ) {k : ℕ} (hk : ¬ k.Prime) : edit ρ k = 0 :=
  sgn_eq_zero_of_not _ _ _ hk

theorem abs_edit_le_one (ρ : ℂ) (k : ℕ) : |(edit ρ k : ℝ)| ≤ 1 := abs_sgn_le_one _ _ _ k

theorem editDisc_eq_sum (ρ : ℂ) (n : ℕ) :
    editDisc ρ n = ∑ k ∈ Ioc 0 n, (target ρ k - edit ρ k * Real.log k) :=
  disc_eq_sum _ _ _ n

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

/-! ## Thinness of the edit -/

/-- The edited primes up to `n` have logarithmic mass at most `2 n^{Re ρ} / Re ρ`. -/
theorem sum_abs_edit_mul_log_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| * Real.log k ≤ 2 * ((n : ℝ) ^ ρ.re / ρ.re) := by
  have h : |editDisc ρ n| + ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| * Real.log k ≤
      ∑ k ∈ Ioc 0 n, |target ρ k| :=
    abs_disc_add_sum_le Nat.Prime (fun j : ℕ => Real.log j) (target ρ) n
  have h2 : ∑ k ∈ Ioc 0 n, |target ρ k| ≤ 2 * ∑ k ∈ Icc 1 n, (k : ℝ) ^ (ρ.re - 1) := by
    have hI : Ioc 0 n = Icc 1 n := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [Finset.mul_sum, hI]
    exact Finset.sum_le_sum fun k hk => abs_target_le ρ (Finset.mem_Icc.mp hk).1
  have h3 := RHTower.BeurlingDeletion.DeletionData.sum_rpow_le hρ0 hρ1.le n
  linarith [abs_nonneg (editDisc ρ n)]

/-- At most `O(n^{Re ρ})` primes up to `n` are edited. -/
theorem sum_abs_edit_le {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (n : ℕ) :
    ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| ≤ 2 / ρ.re / Real.log 2 * (n : ℝ) ^ ρ.re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Ioc 0 n,
      |(edit ρ k : ℝ)| ≤ (|(edit ρ k : ℝ)| * Real.log k) / Real.log 2 := by
    intro k _
    by_cases hp : k.Prime
    · rw [le_div_iff₀ hlog2]
      have h2k : Real.log 2 ≤ Real.log k :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      exact mul_le_mul_of_nonneg_left h2k (abs_nonneg _)
    · rw [edit_eq_zero_of_not_prime ρ hp]; simp
  calc ∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)|
      ≤ ∑ k ∈ Ioc 0 n, (|(edit ρ k : ℝ)| * Real.log k) / Real.log 2 := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Ioc 0 n, |(edit ρ k : ℝ)| * Real.log k) / Real.log 2 := by rw [Finset.sum_div]
    _ ≤ (2 * ((n : ℝ) ^ ρ.re / ρ.re)) / Real.log 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv (2 * ((n : ℝ) ^ ρ.re / ρ.re))]
        exact mul_le_mul_of_nonneg_right (sum_abs_edit_mul_log_le hρ0 hρ1 n)
          (inv_nonneg.mpr hlog2.le)
    _ = 2 / ρ.re / Real.log 2 * (n : ℝ) ^ ρ.re := by ring

/-- The edited primes are summable against `p^{−σ}` for `σ > Re ρ`. -/
theorem summable_abs_edit_rpow {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {σ : ℝ}
    (hσ : ρ.re < σ) : Summable fun k : ℕ => |(edit ρ k : ℝ)| * (k : ℝ) ^ (-σ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact summable_mul_rpow_of_sum_le (c := fun k => |(edit ρ k : ℝ)|) (fun k => abs_nonneg _)
    (by simp) hρ0.le (by positivity) (fun n _ => sum_abs_edit_le hρ0 hρ1 n) hσ

/-! ## Discrepancy of the edit -/

/-- **The primes pay the drift.**  On every interval `(a, n]` the drift of the target is at most
`B₀ + 8 n^{α−η}` plus the prime mass of the interval. -/
theorem exists_window {ρ : ℂ} {α X : ℝ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hα1 : α < 1)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ a n : ℕ, a ≤ n →
      ∑ k ∈ Ioc a n, |target ρ k| ≤ (B₀ + 8 * (n : ℝ) ^ (α - (1 - ρ.re))) +
        ∑ k ∈ Ioc a n, if k.Prime then Real.log k else 0 := by
  set η : ℝ := 1 - ρ.re with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt
    (max (max X 1) (max ((8 : ℝ) ^ (1 / η)) ((4 : ℝ) ^ (1 / (1 - α)))))
  have hX : X ≤ n₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans hn₀.le
  have h8 : (8 : ℝ) ^ (1 / η) ≤ n₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn₀.le
  have h4 : (4 : ℝ) ^ (1 / (1 - α)) ≤ n₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hn₀.le
  -- beyond `n₀`: `8 ≤ x^η` and `4 ≤ x^{1−α}`
  have hF1 : ∀ x : ℝ, (n₀ : ℝ) ≤ x → 8 ≤ x ^ η := by
    intro x hx
    calc (8 : ℝ) = ((8 : ℝ) ^ (1 / η)) ^ η := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη0.ne', Real.rpow_one]
      _ ≤ x ^ η := Real.rpow_le_rpow (by positivity) (h8.trans hx) hη0.le
  have hF2 : ∀ x : ℝ, (n₀ : ℝ) ≤ x → 4 ≤ x ^ (1 - α) := by
    intro x hx
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / (1 - α))) ^ (1 - α) := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel h1α.ne', Real.rpow_one]
      _ ≤ x ^ (1 - α) := Real.rpow_le_rpow (by positivity) (h4.trans hx) h1α.le
  refine ⟨2 * n₀, by positivity, fun a n han => ?_⟩
  have hPm : ∀ b : ℕ, 0 ≤ ∑ k ∈ Ioc b n, if k.Prime then Real.log k else 0 :=
    fun b => Finset.sum_nonneg fun k _ => primeLog_nonneg k
  have hpow0 : 0 ≤ 8 * (n : ℝ) ^ (α - η) := by positivity
  have hterm2 : ∀ b c : ℕ, b ≤ c → ∑ k ∈ Ioc b c, |target ρ k| ≤ ((c : ℝ) - b) * 2 :=
    fun b c hbc => sum_Ioc_le_of_le hbc fun k hk =>
      abs_target_le_two hρ1.le (by have := (Finset.mem_Ioc.mp hk).1; omega)
  rcases le_or_gt n n₀ with hnn | hnn
  · -- below `n₀` every term is at most `2`
    have h := hterm2 a n han
    have hn : (n : ℝ) ≤ n₀ := by exact_mod_cast hnn
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith [hPm a]
  · set a' : ℕ := max a n₀ with ha'
    have haa' : a ≤ a' := le_max_left _ _
    have hn₀a' : n₀ ≤ a' := le_max_right _ _
    have ha'n : a' ≤ n := max_le han hnn.le
    have hsplit := Finset.sum_Ioc_consecutive (fun k => |target ρ k|) haa' ha'n
    have hhead : ∑ k ∈ Ioc a a', |target ρ k| ≤ 2 * n₀ := by
      have h := hterm2 a a' haa'
      have hle : (a' : ℝ) - a ≤ n₀ := by
        have h1 : a' - a ≤ n₀ := by omega
        have h2 : ((a' - a : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast h1
        rwa [Nat.cast_sub haa'] at h2
      linarith
    have hprime : ∑ k ∈ Ioc a' n, (if k.Prime then Real.log k else 0) ≤
        ∑ k ∈ Ioc a n, if k.Prime then Real.log k else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left haa')
        fun k _ _ => primeLog_nonneg k
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hnn
    have hn₀n : (n₀ : ℝ) ≤ n := by exact_mod_cast hnn.le
    have ha'r : (n₀ : ℝ) ≤ a' := by exact_mod_cast hn₀a'
    have hn₀1 : (1 : ℝ) ≤ n₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans hn₀.le
    have hℓ0 : 0 ≤ (n : ℝ) - a' := sub_nonneg.mpr (by exact_mod_cast ha'n)
    -- every term of the tail is at most `2 k^{−η}`
    have hk : ∀ k ∈ Ioc a' n, |target ρ k| ≤ 2 * (k : ℝ) ^ (-η) := by
      intro k hk
      have h := abs_target_le ρ (k := k) (by have := (Finset.mem_Ioc.mp hk).1; omega)
      rwa [show ρ.re - 1 = -η by rw [hη]; ring] at h
    rcases le_or_gt ((n : ℝ) - a') (2 * (n : ℝ) ^ α) with hshort | hlong
    · -- a short tail lies in `[n/2, n]`
      have hnα : 4 * (n : ℝ) ^ α ≤ n := by
        have h := hF2 n hn₀n
        have hmul : (n : ℝ) ^ α * (n : ℝ) ^ (1 - α) = n := by
          rw [← Real.rpow_add hn0]; simp
        have hpos : 0 ≤ (n : ℝ) ^ α := by positivity
        nlinarith
      have hkbound : ∀ k ∈ Ioc a' n, |target ρ k| ≤ 4 * (n : ℝ) ^ (-η) := by
        intro k hkm
        have hka : a' < k := (Finset.mem_Ioc.mp hkm).1
        have hkr : (a' : ℝ) + 1 ≤ k := by exact_mod_cast hka
        have hk2 : (n : ℝ) ≤ 2 * k := by linarith
        have hk0 : (0 : ℝ) < k := by linarith
        have hkη : 0 < (k : ℝ) ^ η := Real.rpow_pos_of_pos hk0 η
        have hnη : 0 < (n : ℝ) ^ η := Real.rpow_pos_of_pos hn0 η
        have h1 : (n : ℝ) ^ η ≤ 2 * (k : ℝ) ^ η := by
          calc (n : ℝ) ^ η ≤ (2 * (k : ℝ)) ^ η := Real.rpow_le_rpow hn0.le hk2 hη0.le
            _ = (2 : ℝ) ^ η * (k : ℝ) ^ η := Real.mul_rpow (by norm_num) hk0.le
            _ ≤ 2 * (k : ℝ) ^ η := by
                have h2 : (2 : ℝ) ^ η ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1.le
                rw [Real.rpow_one] at h2
                exact mul_le_mul_of_nonneg_right h2 hkη.le
        have h2 : (k : ℝ) ^ (-η) ≤ 2 * (n : ℝ) ^ (-η) := by
          rw [Real.rpow_neg hk0.le, Real.rpow_neg hn0.le]
          have hA : ((k : ℝ) ^ η)⁻¹ ≤ ((n : ℝ) ^ η / 2)⁻¹ :=
            inv_anti₀ (by positivity) (by linarith)
          rw [inv_div, div_eq_mul_inv] at hA
          exact hA
        linarith [hk k hkm]
      have htail := sum_Ioc_le_of_le ha'n hkbound
      have hnn' : (n : ℝ) ^ α * (n : ℝ) ^ (-η) = (n : ℝ) ^ (α - η) := by
        rw [← Real.rpow_add hn0, sub_eq_add_neg]
      have hnη : 0 ≤ (n : ℝ) ^ (-η) := by positivity
      have hprod := mul_le_mul_of_nonneg_right hshort hnη
      have hfin : ((n : ℝ) - a') * (4 * (n : ℝ) ^ (-η)) ≤ 8 * (n : ℝ) ^ (α - η) := by
        rw [← hnn']
        nlinarith
      linarith [hPm a]
    · -- on a long tail the primes carry a quarter of the length
      have hw := hwin a' ((n : ℝ) - a') (hX.trans ha'r) hℓ0
      rw [show (a' : ℝ) + ((n : ℝ) - a') = n by ring, theta_sub_theta ha'n] at hw
      have hkbound : ∀ k ∈ Ioc a' n, |target ρ k| ≤ 1 / 4 := by
        intro k hkm
        have hka : a' < k := (Finset.mem_Ioc.mp hkm).1
        have hkr : (n₀ : ℝ) ≤ k := ha'r.trans (by exact_mod_cast hka.le)
        have hk0 : (0 : ℝ) < k := by linarith
        have h8k := hF1 k hkr
        have h8' : (k : ℝ) ^ (-η) ≤ 1 / 8 := by
          rw [Real.rpow_neg hk0.le, one_div]
          exact inv_anti₀ (by norm_num) h8k
        linarith [hk k hkm]
      have htail := sum_Ioc_le_of_le ha'n hkbound
      linarith

theorem log_le_log_succ (k : ℕ) : Real.log k ≤ Real.log ((k : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact Real.log_le_log (by exact_mod_cast hk) (by linarith)

/-- The discrepancy of the edit is at most `log(n + 1) + B₀ + 8 n^{α−η}`. -/
theorem exists_abs_editDisc_le {ρ : ℂ} {α X : ℝ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hα1 : α < 1)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ n : ℕ,
      |editDisc ρ n| ≤ Real.log ((n : ℝ) + 1) + (B₀ + 8 * (n : ℝ) ^ (α - (1 - ρ.re))) := by
  obtain ⟨B₀, hB₀, hW⟩ := exists_window hρ0 hρ1 hα1 hwin
  refine ⟨B₀, hB₀, fun n => ?_⟩
  exact abs_disc_le_of_window (P := Nat.Prime) (w := fun j : ℕ => Real.log j) (m := target ρ)
    (τ := fun k : ℕ => Real.log ((k : ℝ) + 1))
    (B := fun n : ℕ => B₀ + 8 * (n : ℝ) ^ (α - (1 - ρ.re)))
    (fun k => Real.log_natCast_nonneg k)
    (fun a b hab => Real.log_le_log (by positivity)
      (by have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
    (by simp) log_le_log_succ hW n

/-- **Discrepancy of the edit as a power.**  For `c > 0` with `c ≥ α − η` the discrepancy is
`O(n^c)`. -/
theorem exists_abs_editDisc_le_rpow {ρ : ℂ} {α X c : ℝ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hα1 : α < 1) (hc : 0 < c) (hαc : α - (1 - ρ.re) ≤ c)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |editDisc ρ n| ≤ K * (n : ℝ) ^ c := by
  obtain ⟨B₀, hB₀, hB⟩ := exists_abs_editDisc_le hρ0 hρ1 hα1 hwin
  refine ⟨1 + 1 / c + B₀ + 8, by positivity, fun n hn => ?_⟩
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
  have hpow : (n : ℝ) ^ (α - (1 - ρ.re)) ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hn1 hαc
  have hB' : B₀ ≤ B₀ * (n : ℝ) ^ c := le_mul_of_one_le_right hB₀ hnc
  calc |editDisc ρ n| ≤ Real.log ((n : ℝ) + 1) + (B₀ + 8 * (n : ℝ) ^ (α - (1 - ρ.re))) := hB n
    _ ≤ (1 + 1 / c) * (n : ℝ) ^ c + (B₀ * (n : ℝ) ^ c + 8 * (n : ℝ) ^ c) := by linarith
    _ = (1 + 1 / c + B₀ + 8) * (n : ℝ) ^ c := by ring

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
