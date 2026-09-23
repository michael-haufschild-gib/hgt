import GaloisForLFunctions.HTGeometry.ShiftTermFactorialBound

/-!
# The two limits a shift-sum estimate consumes

The comparison of a coefficient recursion with its leading shift produces two error terms.

* A **power** term, decaying like `(n+1)^{-γ}` with `γ` the uniform Newton gap.
* A **factorial** term, `(n+1)^M κ^n ((⌊n/2⌋)!/(n−ν)!)^s`, in which a fixed geometric growth and a
  fixed polynomial growth compete with the ratio of two factorials whose indices differ by about
  `n/2`.

The second is the one that needs an argument.  Every index above `⌊n/2⌋` contributes a factor at
least `⌊n/2⌋ + 1` to the ratio, so the ratio is at most `(⌊n/2⌋+1)^{-p}` with `4p ≥ n` eventually;
once `(⌊n/2⌋+1)^s` exceeds `(2κ)^(4 : ℕ)` — which it does, since it tends to infinity — the whole geometric
factor is beaten and only a polynomial times `2^{-n}` survives.
-/

open scoped Nat
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem inv_le_inv_of_le' {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have h1 := one_div_le_one_div_of_le ha h
  rwa [one_div, one_div] at h1

theorem rpow_natPow_comm {a : ℝ} (ha : 0 ≤ a) (p : ℕ) (s : ℝ) : (a ^ p) ^ s = (a ^ s) ^ p := by
  rw [← Real.rpow_natCast a p, ← Real.rpow_mul ha, mul_comm ((p : ℕ) : ℝ) s,
    Real.rpow_mul ha, Real.rpow_natCast]

theorem tendsto_rpow_neg_succ {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-δ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
  exact h.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

theorem tendsto_natDiv_two_atTop : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩

theorem tendsto_halfIndex_rpow_atTop {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (((n / 2 : ℕ) : ℝ) + 1) ^ s) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => (((n / 2 : ℕ) : ℝ)) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp tendsto_natDiv_two_atTop)
  exact (tendsto_rpow_atTop hs).comp hcast

/-- **The factorial ratio across the halfway point beats every geometric growth.** -/
theorem tendsto_halfFactorial_ratio_mul {s : ℝ} (hs : 0 < s) {κ : ℝ} (hκ : 1 ≤ κ) (M ν : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ M * κ ^ n *
      ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) atTop (𝓝 0) := by
  have hκ0 : (0 : ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have h2κ : (1 : ℝ) < 2 * κ := by linarith
  have h2κ0 : (0 : ℝ) < 2 * κ := by linarith
  have hbig : ∀ᶠ n : ℕ in atTop, (2 * κ) ^ 4 ≤ (((n / 2 : ℕ) : ℝ) + 1) ^ s :=
    (tendsto_halfIndex_rpow_atTop hs).eventually_ge_atTop _
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 * ν + 4 ≤ n := eventually_atTop.mpr ⟨4 * ν + 4, fun n hn => hn⟩
  have hone : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  have hkey : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ M * κ ^ n * ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s
        ≤ (2 : ℝ) ^ M * ((n : ℝ) ^ M * (1 / 2 : ℝ) ^ n) := by
    filter_upwards [hbig, hlarge, hone] with n hy hn hn1
    have hle : n / 2 ≤ n - ν := by omega
    have h4p : n ≤ 4 * ((n - ν) - n / 2) := by omega
    have hbase : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) + 1 := by positivity
    have hXpos : (0 : ℝ) < (((n / 2 : ℕ) : ℝ) + 1) ^ ((n - ν) - n / 2) := by positivity
    have hden : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hnum : (0 : ℝ) < ((((n / 2)! : ℕ) : ℝ)) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hfac := IsRegularFactorialProfile.pow_le_factorial_div hle
    have hratio : ((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))
        ≤ ((((n / 2 : ℕ) : ℝ) + 1) ^ ((n - ν) - n / 2))⁻¹ := by
      have hinvd : ((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))
          = (((((n - ν)! : ℕ) : ℝ)) / ((((n / 2)! : ℕ) : ℝ)))⁻¹ := (inv_div _ _).symm
      rw [hinvd]
      exact inv_le_inv_of_le' hXpos hfac
    have hratio0 : (0 : ℝ) ≤ ((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ)) := by positivity
    have hrpow : (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
        ≤ (((((n / 2 : ℕ) : ℝ) + 1) ^ ((n - ν) - n / 2))⁻¹) ^ s :=
      Real.rpow_le_rpow hratio0 hratio hs.le
    have hinv : (((((n / 2 : ℕ) : ℝ) + 1) ^ ((n - ν) - n / 2))⁻¹) ^ s
        = (((((n / 2 : ℕ) : ℝ) + 1) ^ s) ^ ((n - ν) - n / 2))⁻¹ := by
      rw [Real.inv_rpow (le_of_lt hXpos)]
      congr 1
      exact rpow_natPow_comm hbase _ s
    have hpow : ((2 * κ) ^ 4) ^ ((n - ν) - n / 2)
        ≤ ((((n / 2 : ℕ) : ℝ) + 1) ^ s) ^ ((n - ν) - n / 2) :=
      pow_le_pow_left₀ (by positivity) hy _
    have h2κn : (2 * κ) ^ n ≤ ((2 * κ) ^ 4) ^ ((n - ν) - n / 2) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (le_of_lt h2κ) h4p
    have hchain : (2 * κ) ^ n ≤ ((((n / 2 : ℕ) : ℝ) + 1) ^ s) ^ ((n - ν) - n / 2) :=
      le_trans h2κn hpow
    have hκn : (0 : ℝ) < κ ^ n := pow_pos hκ0 n
    have hfinal : κ ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
        ≤ (1 / 2 : ℝ) ^ n := by
      have hstep : (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s ≤ ((2 * κ) ^ n)⁻¹ := by
        refine le_trans hrpow ?_
        rw [hinv]
        exact inv_le_inv_of_le' (pow_pos h2κ0 n) hchain
      calc κ ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
          ≤ κ ^ n * ((2 * κ) ^ n)⁻¹ := mul_le_mul_of_nonneg_left hstep hκn.le
        _ = (1 / 2 : ℝ) ^ n := by
            rw [mul_pow, mul_inv, ← mul_assoc, mul_comm (κ ^ n) (((2 : ℝ) ^ n)⁻¹), mul_assoc,
              mul_inv_cancel₀ (ne_of_gt hκn), mul_one, one_div, inv_pow]
    have hnn : ((n : ℝ) + 1) ^ M ≤ (2 : ℝ) ^ M * (n : ℝ) ^ M := by
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      calc ((n : ℝ) + 1) ^ M ≤ (2 * (n : ℝ)) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
        _ = (2 : ℝ) ^ M * (n : ℝ) ^ M := by rw [mul_pow]
    have hposA : (0 : ℝ) ≤ κ ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s := by
      positivity
    calc ((n : ℝ) + 1) ^ M * κ ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s
        = ((n : ℝ) + 1) ^ M *
            (κ ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s) := by ring
      _ ≤ ((2 : ℝ) ^ M * (n : ℝ) ^ M) * (1 / 2 : ℝ) ^ n :=
          mul_le_mul hnn hfinal hposA (by positivity)
      _ = (2 : ℝ) ^ M * ((n : ℝ) ^ M * (1 / 2 : ℝ) ^ n) := by ring
  have hmaj : Tendsto (fun n : ℕ => (2 : ℝ) ^ M * ((n : ℝ) ^ M * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one M (by norm_num : |(1 / 2 : ℝ)| < 1)
    simpa using h.const_mul ((2 : ℝ) ^ M)
  refine squeeze_zero' ?_ hkey hmaj
  filter_upwards with n
  positivity

end GaloisForLFunctions.HTGeometry
