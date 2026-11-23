import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightOneHundredFifty

/-!
# The Riemann hypothesis through height 184 via bandwidth-`11/2` prime-phase-coupled Bohman analysis

Advancing the bandwidth from `L = 9/2` (`N = 91`, exact coupled integer ceiling `150`) to
`L = 11/2` (`N = 245`, `53` primes `p ≤ 241`) raises the edge budget from `2.236881` to `2.495516`
and establishes without locating any zero or computing any value of `ζ`:

* **`rhVerifiedThrough_oneHundredEightyFour` (`RHVerifiedThrough 184`)**: every zero of `ξ` in the
  critical strip with `0 < Im ρ ≤ 184` lies on `Re ρ = 1/2`.
* **`bohman_eleven_halves_coupled_saturates_at_oneHundredEightyFive`**: at the coupled real height
  `γ = 185`, the `L = 11/2` Bohman explicit-formula inequality strictly reverses even without the
  positive `O(1/1215 + 1/γ²)` archimedean terms, proving `184` is the exact integer ceiling of the
  coupled `L = 11/2` Bohman test.
* **Upgraded rungs**: `PF_551` at the centre of `ξ`, slice nonnegativity across `|t| ≤ 367/2`,
  `Re(2 λ_n) ≥ 0` for `n ≤ 864`, and real-rootedness of unshifted `Ξ` Jensen polynomials and all
  positive-integer Euler root filters through degree `240,808`.
-/

open Complex Set Polynomial FiniteFreeProbability
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

private theorem nonneg_of_deriv_nonneg11 {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ f u := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hpos x (interior_subset hx))
  simpa only [hf0] using hmono self_mem_Ici hu hu

private theorem hasDerivAt_monomial_div11 (n : ℕ) (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ n / c) ((n : ℝ) * x ^ (n - 1) / c) x := by
  simpa only [mul_div_assoc] using ((hasDerivAt_pow n x).div_const c)

private theorem pi_bounds_d10_11 : (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < 3.1415926536 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

private theorem cos_abs_eq11 (x : ℝ) : Real.cos |x| = Real.cos x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.cos_neg]

private theorem cos_sub_nat_mul_two_pi11 (θ : ℝ) (m : ℕ) :
    Real.cos (θ - 2 * (m : ℝ) * Real.pi) = Real.cos θ := by
  induction m with
  | zero => simp
  | succ k ih =>
    have heq : θ - 2 * (k : ℝ) * Real.pi =
        (θ - 2 * ((k + 1 : ℕ) : ℝ) * Real.pi) + 2 * Real.pi := by push_cast; ring
    rw [← ih, heq, Real.cos_add_two_pi]

private theorem cos_sub_odd_mul_pi11 (θ : ℝ) (m : ℕ) :
    Real.cos (θ - (2 * (m : ℝ) + 1) * Real.pi) = -Real.cos θ := by
  have heq : θ - (2 * (m : ℝ) + 1) * Real.pi = (θ - 2 * (m : ℝ) * Real.pi) - Real.pi := by ring
  rw [heq, Real.cos_sub_pi, cos_sub_nat_mul_two_pi11]

private theorem cos_mul_ge_of_even_shift11 {γ g_lo g_hi lp lp_lo lp_hi x_hi u_lo : ℝ} (m : ℕ)
    (hg0 : 0 ≤ g_lo) (hlo : g_lo ≤ γ) (hhi : γ ≤ g_hi)
    (hlp0 : 0 ≤ lp_lo) (hlp_lo : lp_lo ≤ lp) (hlp_hi : lp ≤ lp_hi)
    (hx_pi : x_hi ≤ 3.1415926535)
    (hsh_lo : -x_hi ≤ g_lo * lp_lo - 2 * (m : ℝ) * 3.1415926536)
    (hsh_hi : g_hi * lp_hi - 2 * (m : ℝ) * 3.1415926535 ≤ x_hi)
    (hu : u_lo ≤ cosPoly10 x_hi) :
    u_lo ≤ Real.cos (γ * lp) := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10_11
  have hmul_lo : g_lo * lp_lo ≤ γ * lp := mul_le_mul hlo hlp_lo hlp0 (hg0.trans hlo)
  have hmul_hi : γ * lp ≤ g_hi * lp_hi :=
    mul_le_mul hhi hlp_hi (hlp0.trans hlp_lo) (hg0.trans (hlo.trans hhi))
  have hmπ_lo : 2 * (m : ℝ) * 3.1415926535 ≤ 2 * (m : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_left hπ_lo.le (by positivity)
  have hmπ_hi : 2 * (m : ℝ) * Real.pi ≤ 2 * (m : ℝ) * 3.1415926536 :=
    mul_le_mul_of_nonneg_left hπ_hi.le (by positivity)
  set d : ℝ := γ * lp - 2 * (m : ℝ) * Real.pi
  have hd_abs : |d| ≤ x_hi := abs_le.mpr ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hx_le_pi : x_hi ≤ Real.pi := hx_pi.trans hπ_lo.le
  have hcos_mono : Real.cos x_hi ≤ Real.cos |d| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) hx_le_pi hd_abs
  rw [cos_abs_eq11] at hcos_mono
  dsimp only [d] at hcos_mono
  rw [cos_sub_nat_mul_two_pi11] at hcos_mono
  exact hu.trans ((cosPoly10_le_cos x_hi).trans hcos_mono)

private theorem cos_mul_le_of_odd_shift11 {c lp lp_lo lp_hi s_hi u_hi : ℝ} (m : ℕ)
    (hc0 : 0 ≤ c) (hlp_lo : lp_lo ≤ lp) (hlp_hi : lp ≤ lp_hi)
    (hs_pi : s_hi ≤ 3.1415926535)
    (hsh_lo : -s_hi ≤ c * lp_lo - (2 * (m : ℝ) + 1) * 3.1415926536)
    (hsh_hi : c * lp_hi - (2 * (m : ℝ) + 1) * 3.1415926535 ≤ s_hi)
    (hu : -cosPoly10 s_hi ≤ u_hi) :
    Real.cos (c * lp) ≤ u_hi := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10_11
  have h2m1 : 0 ≤ 2 * (m : ℝ) + 1 := by positivity
  have hmul_lo : c * lp_lo ≤ c * lp := mul_le_mul_of_nonneg_left hlp_lo hc0
  have hmul_hi : c * lp ≤ c * lp_hi := mul_le_mul_of_nonneg_left hlp_hi hc0
  have hmπ_lo : (2 * (m : ℝ) + 1) * 3.1415926535 ≤ (2 * (m : ℝ) + 1) * Real.pi :=
    mul_le_mul_of_nonneg_left hπ_lo.le h2m1
  have hmπ_hi : (2 * (m : ℝ) + 1) * Real.pi ≤ (2 * (m : ℝ) + 1) * 3.1415926536 :=
    mul_le_mul_of_nonneg_left hπ_hi.le h2m1
  set d : ℝ := c * lp - (2 * (m : ℝ) + 1) * Real.pi
  have hd_abs : |d| ≤ s_hi := abs_le.mpr ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hs_le_pi : s_hi ≤ Real.pi := hs_pi.trans hπ_lo.le
  have hcos_mono : Real.cos s_hi ≤ Real.cos |d| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) hs_le_pi hd_abs
  rw [cos_abs_eq11] at hcos_mono
  dsimp only [d] at hcos_mono
  rw [cos_sub_odd_mul_pi11] at hcos_mono
  have hle : Real.cos (c * lp) ≤ -cosPoly10 s_hi := by
    linarith [cosPoly10_le_cos s_hi, hcos_mono]
  exact hle.trans hu

/-! ## Fast inverse-hyperbolic-tangent logarithm enclosures through `p = 241` -/

private theorem log_one_add_div_one_sub_bounds11 {t : ℝ} (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2) :
    2 * (t + t ^ 3 / 3) ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ 2 * (t + t ^ 3 / 3 + t ^ 5) := by
  have hd_log : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivAt (fun y => Real.log ((1 + y) / (1 - y))) (2 / (1 - x ^ 2)) x := by
    intro x hx
    have h1p : 0 < 1 + x := by linarith [hx.1]
    have h1m : 0 < 1 - x := by linarith [hx.2]
    have hm1x : -1 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2]
    have hfg : ∀ᶠ y in nhds x, Real.log ((1 + y) / (1 - y)) = Real.log (1 + y) - Real.log (1 - y) := by
      filter_upwards [lt_mem_nhds hm1x, gt_mem_nhds hx1] with y hy1 hy2
      exact Real.log_div (by linarith) (by linarith)
    have hd1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log h1p.ne')
    have hd2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
      refine (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log h1m.ne').congr_deriv ?_
      simp only [Pi.sub_apply, id_eq]; ring
    exact ((hd1.sub hd2).congr_of_eventuallyEq hfg).congr_deriv (by
      have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
      field_simp [h1p.ne', h1m.ne', hne]; ring)
  have hd_lo : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 2 * (y + y ^ 3 / 3)) (2 * (1 + x ^ 2)) x := fun x => by
    refine (((hasDerivAt_id x).add (hasDerivAt_monomial_div11 3 3 x)).const_mul 2).congr_deriv ?_
    norm_num
  have hd_hi : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 2 * (y + y ^ 3 / 3 + y ^ 5))
      (2 * (1 + x ^ 2 + 5 * x ^ 4)) x := fun x => by
    refine ((((hasDerivAt_id x).add (hasDerivAt_monomial_div11 3 3 x)).add
      (hasDerivAt_pow 5 x)).const_mul 2).congr_deriv ?_
    norm_num
  have hmono_lo : MonotoneOn (fun x => Real.log ((1 + x) / (1 - x)) - 2 * (x + x ^ 3 / 3))
      (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (fun x hx => ((hd_log x hx).sub (hd_lo x)).continuousAt.continuousWithinAt)
      (fun x hx => ((hd_log x (interior_subset hx)).sub (hd_lo x)).hasDerivWithinAt)
      fun x hx => by
        have hx' := interior_subset hx
        have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        rw [sub_nonneg, le_div_iff₀ hden]
        nlinarith [sq_nonneg (x ^ 2)]
  have hmono_hi : MonotoneOn (fun x => 2 * (x + x ^ 3 / 3 + x ^ 5) - Real.log ((1 + x) / (1 - x)))
      (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (fun x hx => ((hd_hi x).sub (hd_log x hx)).continuousAt.continuousWithinAt)
      (fun x hx => ((hd_hi x).sub (hd_log x (interior_subset hx))).hasDerivWithinAt)
      fun x hx => by
        have hx' := interior_subset hx
        have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        rw [sub_nonneg, div_le_iff₀ hden]
        have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [hx'.1, hx'.2]
        have h4 : 0 ≤ x ^ 4 * (4 - 5 * x ^ 2) := mul_nonneg (by positivity) (by linarith)
        nlinarith [h4]
  have hlo := hmono_lo ⟨le_rfl, by norm_num⟩ ⟨ht0, ht_half⟩ ht0
  have hhi := hmono_hi ⟨le_rfl, by norm_num⟩ ⟨ht0, ht_half⟩ ht0
  simp only [add_zero, sub_zero, div_one, Real.log_one] at hlo hhi
  norm_num at hlo hhi
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

private theorem log_atanh_pos_step11 {p M t lo hi base_lo base_hi : ℝ} {kp : ℕ}
    (hp : 0 < p) (hM : 0 < M) (hkp : 0 < kp) (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2)
    (heq : p ^ kp / M = (1 + t) / (1 - t))
    (hbase_lo : base_lo ≤ Real.log M) (hbase_hi : Real.log M ≤ base_hi)
    (hlo : lo ≤ (base_lo + 2 * (t + t ^ 3 / 3)) / kp)
    (hhi : (base_hi + 2 * (t + t ^ 3 / 3 + t ^ 5)) / kp ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  obtain ⟨hat_lo, hat_hi⟩ := log_one_add_div_one_sub_bounds11 ht0 ht_half
  have hkp' : (0 : ℝ) < kp := by exact_mod_cast hkp
  have hlog : (kp : ℝ) * Real.log p - Real.log M = Real.log ((1 + t) / (1 - t)) := by
    rw [← Real.log_pow, ← Real.log_div (pow_pos hp kp).ne' hM.ne', heq]
  refine ⟨hlo.trans ?_, ?_⟩
  · rw [div_le_iff₀ hkp']; linarith only [hlog, hbase_lo, hat_lo]
  · refine le_trans ?_ hhi
    rw [le_div_iff₀ hkp']; linarith only [hlog, hbase_hi, hat_hi]

private theorem log_atanh_neg_step11 {p M t lo hi base_lo base_hi : ℝ} {kp : ℕ}
    (hp : 0 < p) (hM : 0 < M) (hkp : 0 < kp) (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2)
    (heq : M / p ^ kp = (1 + t) / (1 - t))
    (hbase_lo : base_lo ≤ Real.log M) (hbase_hi : Real.log M ≤ base_hi)
    (hlo : lo ≤ (base_lo - 2 * (t + t ^ 3 / 3 + t ^ 5)) / kp)
    (hhi : (base_hi - 2 * (t + t ^ 3 / 3)) / kp ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  obtain ⟨hat_lo, hat_hi⟩ := log_one_add_div_one_sub_bounds11 ht0 ht_half
  have hkp' : (0 : ℝ) < kp := by exact_mod_cast hkp
  have hlog : Real.log M - (kp : ℝ) * Real.log p = Real.log ((1 + t) / (1 - t)) := by
    rw [← Real.log_pow, ← Real.log_div hM.ne' (pow_pos hp kp).ne', heq]
  refine ⟨hlo.trans ?_, ?_⟩
  · rw [div_le_iff₀ hkp']; linarith only [hlog, hbase_lo, hat_hi]
  · refine le_trans ?_ hhi
    rw [le_div_iff₀ hkp']; linarith only [hlog, hbase_hi, hat_lo]

private theorem log_smooth_bounds11 {M : ℝ} {a2 b3 c5 d7 : ℕ}
    (hM : M = (2 : ℝ) ^ a2 * (3 : ℝ) ^ b3 * (5 : ℝ) ^ c5 * (7 : ℝ) ^ d7)
    {l3a l3b l5a l5b l7a l7b : ℝ}
    (hl3a : l3a ≤ Real.log 3) (hl3b : Real.log 3 ≤ l3b)
    (hl5a : l5a ≤ Real.log 5) (hl5b : Real.log 5 ≤ l5b)
    (hl7a : l7a ≤ Real.log 7) (hl7b : Real.log 7 ≤ l7b) :
    (a2 : ℝ) * 0.6931471803 + (b3 : ℝ) * l3a + (c5 : ℝ) * l5a + (d7 : ℝ) * l7a ≤ Real.log M ∧
      Real.log M ≤ (a2 : ℝ) * 0.6931471808 + (b3 : ℝ) * l3b + (c5 : ℝ) * l5b + (d7 : ℝ) * l7b := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  rw [hM, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  exact ⟨add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hl2a (Nat.cast_nonneg a2))
      (mul_le_mul_of_nonneg_left hl3a (Nat.cast_nonneg b3)))
      (mul_le_mul_of_nonneg_left hl5a (Nat.cast_nonneg c5)))
      (mul_le_mul_of_nonneg_left hl7a (Nat.cast_nonneg d7)),
    add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hl2b (Nat.cast_nonneg a2))
      (mul_le_mul_of_nonneg_left hl3b (Nat.cast_nonneg b3)))
      (mul_le_mul_of_nonneg_left hl5b (Nat.cast_nonneg c5)))
      (mul_le_mul_of_nonneg_left hl7b (Nat.cast_nonneg d7))⟩

private theorem sharp_log_prime_3 : 1.0986121 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0986129 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have hM : (3 : ℝ) * 0.6931471803 ≤ Real.log 8 ∧ Real.log 8 ≤ (3 : ℝ) * 0.6931471808 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  exact log_atanh_pos_step11 (p := 3) (M := 8) (t := (1 / 17)) (lo := 1.0986121) (hi := 1.0986129) (kp := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM.1 hM.2 (by norm_num) (by norm_num)
private theorem sharp_log_prime_5 : 1.6094379 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.609438 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have hM : (7 : ℝ) * 0.6931471803 ≤ Real.log 128 ∧ Real.log 128 ≤ (7 : ℝ) * 0.6931471808 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  exact log_atanh_neg_step11 (p := 5) (M := 128) (t := (3 / 253)) (lo := 1.6094379) (hi := 1.609438) (kp := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM.1 hM.2 (by norm_num) (by norm_num)
private theorem sharp_log_prime_7 : 1.945908 ≤ Real.log 7 ∧ Real.log 7 ≤ 1.9459107 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have hM : (3 : ℝ) * 0.6931471803 ≤ Real.log 8 ∧ Real.log 8 ≤ (3 : ℝ) * 0.6931471808 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  exact log_atanh_neg_step11 (p := 7) (M := 8) (t := (1 / 15)) (lo := 1.945908) (hi := 1.9459107) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM.1 hM.2 (by norm_num) (by norm_num)
private theorem sharp_log_prime_11 : 2.3978951 ≤ Real.log 11 ∧ Real.log 11 ≤ 2.3978957 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 120) (a2 := 3) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 11) (M := 120) (t := (1 / 241)) (lo := 2.3978951) (hi := 2.3978957) (kp := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_13 : 2.5649481 ≤ Real.log 13 ∧ Real.log 13 ≤ 2.56495 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 168) (a2 := 3) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 13) (M := 168) (t := (1 / 337)) (lo := 2.5649481) (hi := 2.56495) (kp := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_17 : 2.8332129 ≤ Real.log 17 ∧ Real.log 17 ≤ 2.8332146 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 18) (a2 := 1) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 17) (M := 18) (t := (1 / 35)) (lo := 2.8332129) (hi := 2.8332146) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_19 : 2.9444389 ≤ Real.log 19 ∧ Real.log 19 ≤ 2.9444391 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 20) (a2 := 2) (b3 := 0) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 19) (M := 20) (t := (1 / 39)) (lo := 2.9444389) (hi := 2.9444391) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_23 : 3.135494 ≤ Real.log 23 ∧ Real.log 23 ≤ 3.1354949 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 24) (a2 := 3) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 23) (M := 24) (t := (1 / 47)) (lo := 3.135494) (hi := 3.1354949) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_29 : 3.3672956 ≤ Real.log 29 ∧ Real.log 29 ≤ 3.3672966 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 30) (a2 := 1) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 29) (M := 30) (t := (1 / 59)) (lo := 3.3672956) (hi := 3.3672966) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_31 : 3.4339872 ≤ Real.log 31 ∧ Real.log 31 ≤ 3.4339873 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 32) (a2 := 5) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 31) (M := 32) (t := (1 / 63)) (lo := 3.4339872) (hi := 3.4339873) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_37 : 3.6109175 ≤ Real.log 37 ∧ Real.log 37 ≤ 3.6109192 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 36) (a2 := 2) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 37) (M := 36) (t := (1 / 73)) (lo := 3.6109175) (hi := 3.6109192) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_41 : 3.7135697 ≤ Real.log 41 ∧ Real.log 41 ≤ 3.7135733 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 42) (a2 := 1) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 41) (M := 42) (t := (1 / 83)) (lo := 3.7135697) (hi := 3.7135733) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_43 : 3.7611977 ≤ Real.log 43 ∧ Real.log 43 ≤ 3.7612013 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 42) (a2 := 1) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 43) (M := 42) (t := (1 / 85)) (lo := 3.7611977) (hi := 3.7612013) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_47 : 3.8501474 ≤ Real.log 47 ∧ Real.log 47 ≤ 3.8501483 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 48) (a2 := 4) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 47) (M := 48) (t := (1 / 95)) (lo := 3.8501474) (hi := 3.8501483) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_53 : 3.9702913 ≤ Real.log 53 ∧ Real.log 53 ≤ 3.9702938 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 54) (a2 := 1) (b3 := 3) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 53) (M := 54) (t := (1 / 107)) (lo := 3.9702913) (hi := 3.9702938) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_59 : 4.0775372 ≤ Real.log 59 ∧ Real.log 59 ≤ 4.0775382 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 60) (a2 := 2) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 59) (M := 60) (t := (1 / 119)) (lo := 4.0775372) (hi := 4.0775382) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_61 : 4.1108736 ≤ Real.log 61 ∧ Real.log 61 ≤ 4.1108746 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 60) (a2 := 2) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 61) (M := 60) (t := (1 / 121)) (lo := 4.1108736) (hi := 4.1108746) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_67 : 4.2046904 ≤ Real.log 67 ∧ Real.log 67 ≤ 4.2046933 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 70) (a2 := 1) (b3 := 0) (c5 := 1) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 67) (M := 70) (t := (3 / 137)) (lo := 4.2046904) (hi := 4.2046933) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_71 : 4.2626794 ≤ Real.log 71 ∧ Real.log 71 ≤ 4.2626812 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 72) (a2 := 3) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 71) (M := 72) (t := (1 / 143)) (lo := 4.2626794) (hi := 4.2626812) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_73 : 4.290459 ≤ Real.log 73 ∧ Real.log 73 ≤ 4.2904607 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 72) (a2 := 3) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 73) (M := 72) (t := (1 / 145)) (lo := 4.290459) (hi := 4.2904607) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_79 : 4.3694478 ≤ Real.log 79 ∧ Real.log 79 ≤ 4.369448 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 80) (a2 := 4) (b3 := 0) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 79) (M := 80) (t := (1 / 159)) (lo := 4.3694478) (hi := 4.369448) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_83 : 4.4188382 ≤ Real.log 83 ∧ Real.log 83 ≤ 4.4188418 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 84) (a2 := 2) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 83) (M := 84) (t := (1 / 167)) (lo := 4.4188382) (hi := 4.4188418) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_89 : 4.4886359 ≤ Real.log 89 ∧ Real.log 89 ≤ 4.4886377 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 90) (a2 := 1) (b3 := 2) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 89) (M := 90) (t := (1 / 179)) (lo := 4.4886359) (hi := 4.4886377) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_97 : 4.5747066 ≤ Real.log 97 ∧ Real.log 97 ≤ 4.5747121 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 98) (a2 := 1) (b3 := 0) (c5 := 0) (d7 := 2) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 97) (M := 98) (t := (1 / 195)) (lo := 4.5747066) (hi := 4.5747121) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_101 : 4.6151204 ≤ Real.log 101 ∧ Real.log 101 ≤ 4.6151207 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 100) (a2 := 2) (b3 := 0) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 101) (M := 100) (t := (1 / 201)) (lo := 4.6151204) (hi := 4.6151207) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_103 : 4.6347266 ≤ Real.log 103 ∧ Real.log 103 ≤ 4.6347303 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 105) (a2 := 0) (b3 := 1) (c5 := 1) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 103) (M := 105) (t := (1 / 104)) (lo := 4.6347266) (hi := 4.6347303) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_107 : 4.6728282 ≤ Real.log 107 ∧ Real.log 107 ≤ 4.6728307 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 108) (a2 := 2) (b3 := 3) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 107) (M := 108) (t := (1 / 215)) (lo := 4.6728282) (hi := 4.6728307) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_109 : 4.6913473 ≤ Real.log 109 ∧ Real.log 109 ≤ 4.6913498 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 108) (a2 := 2) (b3 := 3) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 109) (M := 108) (t := (1 / 217)) (lo := 4.6913473) (hi := 4.6913498) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_113 : 4.7273856 ≤ Real.log 113 ∧ Real.log 113 ≤ 4.7273884 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 112) (a2 := 4) (b3 := 0) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 113) (M := 112) (t := (1 / 225)) (lo := 4.7273856) (hi := 4.7273884) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_127 : 4.844187 ≤ Real.log 127 ∧ Real.log 127 ≤ 4.8441871 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 128) (a2 := 7) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 127) (M := 128) (t := (1 / 255)) (lo := 4.844187) (hi := 4.8441871) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_131 : 4.8751973 ≤ Real.log 131 ∧ Real.log 131 ≤ 4.8751974 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 128) (a2 := 7) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 131) (M := 128) (t := (3 / 259)) (lo := 4.8751973) (hi := 4.8751974) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_137 : 4.9199803 ≤ Real.log 137 ∧ Real.log 137 ≤ 4.9199829 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 135) (a2 := 0) (b3 := 3) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 137) (M := 135) (t := (1 / 136)) (lo := 4.9199803) (hi := 4.9199829) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_139 : 4.9344717 ≤ Real.log 139 ∧ Real.log 139 ≤ 4.9344746 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 140) (a2 := 2) (b3 := 0) (c5 := 1) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 139) (M := 140) (t := (1 / 279)) (lo := 4.9344717) (hi := 4.9344746) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_149 : 5.003946 ≤ Real.log 149 ∧ Real.log 149 ≤ 5.0039471 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 150) (a2 := 1) (b3 := 1) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 149) (M := 150) (t := (1 / 299)) (lo := 5.003946) (hi := 5.0039471) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_151 : 5.0172796 ≤ Real.log 151 ∧ Real.log 151 ≤ 5.0172807 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 150) (a2 := 1) (b3 := 1) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 151) (M := 150) (t := (1 / 301)) (lo := 5.0172796) (hi := 5.0172807) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_157 : 5.0562457 ≤ Real.log 157 ∧ Real.log 157 ≤ 5.0562459 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 160) (a2 := 5) (b3 := 0) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 157) (M := 160) (t := (3 / 317)) (lo := 5.0562457) (hi := 5.0562459) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_163 : 5.0937494 ≤ Real.log 163 ∧ Real.log 163 ≤ 5.0937527 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 162) (a2 := 1) (b3 := 4) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 163) (M := 162) (t := (1 / 325)) (lo := 5.0937494) (hi := 5.0937527) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_167 : 5.1179914 ≤ Real.log 167 ∧ Real.log 167 ≤ 5.117995 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 168) (a2 := 3) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 167) (M := 168) (t := (1 / 335)) (lo := 5.1179914) (hi := 5.117995) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_173 : 5.1532894 ≤ Real.log 173 ∧ Real.log 173 ≤ 5.1532924 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 175) (a2 := 0) (b3 := 0) (c5 := 2) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 173) (M := 175) (t := (1 / 174)) (lo := 5.1532894) (hi := 5.1532924) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_179 : 5.1873854 ≤ Real.log 179 ∧ Real.log 179 ≤ 5.1873872 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 180) (a2 := 2) (b3 := 2) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 179) (M := 180) (t := (1 / 359)) (lo := 5.1873854) (hi := 5.1873872) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_181 : 5.1984966 ≤ Real.log 181 ∧ Real.log 181 ≤ 5.1984984 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 180) (a2 := 2) (b3 := 2) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 181) (M := 180) (t := (1 / 361)) (lo := 5.1984966) (hi := 5.1984984) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_191 : 5.2522732 ≤ Real.log 191 ∧ Real.log 191 ≤ 5.2522741 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 192) (a2 := 6) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 191) (M := 192) (t := (1 / 383)) (lo := 5.2522732) (hi := 5.2522741) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_193 : 5.2626899 ≤ Real.log 193 ∧ Real.log 193 ≤ 5.2626909 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 192) (a2 := 6) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 193) (M := 192) (t := (1 / 385)) (lo := 5.2626899) (hi := 5.2626909) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_197 : 5.2831994 ≤ Real.log 197 ∧ Real.log 197 ≤ 5.2832049 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 196) (a2 := 2) (b3 := 0) (c5 := 0) (d7 := 2) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 197) (M := 196) (t := (1 / 393)) (lo := 5.2831994) (hi := 5.2832049) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_199 : 5.2933047 ≤ Real.log 199 ∧ Real.log 199 ≤ 5.2933051 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 200) (a2 := 3) (b3 := 0) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 199) (M := 200) (t := (1 / 399)) (lo := 5.2933047) (hi := 5.2933051) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_211 : 5.3518557 ≤ Real.log 211 ∧ Real.log 211 ≤ 5.3518594 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 210) (a2 := 1) (b3 := 1) (c5 := 1) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 211) (M := 210) (t := (1 / 421)) (lo := 5.3518557) (hi := 5.3518594) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_223 : 5.4071696 ≤ Real.log 223 ∧ Real.log 223 ≤ 5.4071724 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 224) (a2 := 5) (b3 := 0) (c5 := 0) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 223) (M := 224) (t := (1 / 447)) (lo := 5.4071696) (hi := 5.4071724) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_227 : 5.4249496 ≤ Real.log 227 ∧ Real.log 227 ≤ 5.4249515 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 225) (a2 := 0) (b3 := 2) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 227) (M := 225) (t := (1 / 226)) (lo := 5.4249496) (hi := 5.4249515) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_229 : 5.4337216 ≤ Real.log 229 ∧ Real.log 229 ≤ 5.4337235 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 225) (a2 := 0) (b3 := 2) (c5 := 2) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 229) (M := 225) (t := (2 / 227)) (lo := 5.4337216) (hi := 5.4337235) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_233 : 5.4510382 ≤ Real.log 233 ∧ Real.log 233 ≤ 5.4510392 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 240) (a2 := 4) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 233) (M := 240) (t := (7 / 473)) (lo := 5.4510382) (hi := 5.4510392) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_239 : 5.4764633 ≤ Real.log 239 ∧ Real.log 239 ≤ 5.4764643 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 240) (a2 := 4) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_neg_step11 (p := 239) (M := 240) (t := (1 / 479)) (lo := 5.4764633) (hi := 5.4764643) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
private theorem sharp_log_prime_241 : 5.4847967 ≤ Real.log 241 ∧ Real.log 241 ≤ 5.4847977 := by
  obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds11 (M := 240) (a2 := 4) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
  exact log_atanh_pos_step11 (p := 241) (M := 240) (t := (1 / 481)) (lo := 5.4847967) (hi := 5.4847977) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)

private theorem sin_cos_taylor_chain11 {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u ∧
      Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 := by
  have h1 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg11 (by simp)
      (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
      (fun y _ => sub_nonneg.mpr (Real.cos_le_one y)) hx
  have h2 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2) := fun x hx =>
    nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div11 2 2 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h1 y hy) hx
  have h3 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6) := fun x hx =>
    nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((hasDerivAt_id y).sub (hasDerivAt_monomial_div11 3 6 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h2 y hy) hx
  have h4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x := fun x hx =>
    nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div11 2 2 y)).add
        (hasDerivAt_monomial_div11 4 24 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h3 y hy) hx
  have h5 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div11 3 6 y)).add
        (hasDerivAt_monomial_div11 5 120 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h4 y hy) hx
  have h6 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    fun x hx => nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div11 2 2 y)).add
          (hasDerivAt_monomial_div11 4 24 y)).sub
          (hasDerivAt_monomial_div11 6 720 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h5 y hy) hx
  have h7 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    fun x hx => nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div11 3 6 y)).add
          (hasDerivAt_monomial_div11 5 120 y)).sub
          (hasDerivAt_monomial_div11 7 5040 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h6 y hy) hx
  have h8 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x :=
    fun x hx => nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div11 2 2 y)).add
          (hasDerivAt_monomial_div11 4 24 y)).sub
          (hasDerivAt_monomial_div11 6 720 y)).add
          (hasDerivAt_monomial_div11 8 40320 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h7 y hy) hx
  have h9 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    fun x hx => nonneg_of_deriv_nonneg11 (by norm_num)
      (fun y => ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div11 3 6 y)).add
          (hasDerivAt_monomial_div11 5 120 y)).sub
          (hasDerivAt_monomial_div11 7 5040 y)).add
          (hasDerivAt_monomial_div11 9 362880 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h8 y hy) hx
  exact ⟨sub_nonneg.mp (h7 u hu), sub_nonneg.mp (h9 u hu)⟩

private theorem hasDerivAt_sin_sub_mul_cos11 (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y - y * Real.cos y) (x * Real.sin x) x := by
  refine ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv ?_
  dsimp only [id]; ring

private theorem monotoneOn_sin_sub_mul_cos11 :
    MonotoneOn (fun u : ℝ => Real.sin u - u * Real.cos u) (Icc 0 Real.pi) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos11 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos11 x).hasDerivWithinAt)
    fun x hx => by
      have hx' : x ∈ Ioo 0 Real.pi := by rwa [interior_Icc] at hx
      exact mul_nonneg hx'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hx'.1.le hx'.2.le)

private theorem bohmanP9_le_and_le_bohmanP11_11 {u : ℝ} (hu : 0 ≤ u) :
    bohmanP9 u ≤ Real.sin u - u * Real.cos u ∧ Real.sin u - u * Real.cos u ≤ bohmanP11 u := by
  have hd9 : ∀ x : ℝ, HasDerivAt bohmanP9
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)) x := fun x => by
    unfold bohmanP9
    refine ((((hasDerivAt_monomial_div11 3 3 x).sub
        (hasDerivAt_monomial_div11 5 30 x)).add
        (hasDerivAt_monomial_div11 7 840 x)).sub
        (hasDerivAt_monomial_div11 9 45360 x)).congr_deriv (by norm_num; ring)
  have hd11 : ∀ x : ℝ, HasDerivAt bohmanP11
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)) x := fun x => by
    unfold bohmanP11
    refine ((hd9 x).add (hasDerivAt_monomial_div11 11 3991680 x)).congr_deriv (by norm_num; ring)
  have hlo := nonneg_of_deriv_nonneg11 (by simp [bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos11 x).sub (hd9 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_cos_taylor_chain11 hx).1)) hu
  have hhi := nonneg_of_deriv_nonneg11 (by simp [bohmanP11, bohmanP9])
    (fun x => ((hd11 x).sub (hasDerivAt_sin_sub_mul_cos11 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_cos_taylor_chain11 hx).2)) hu
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

private theorem bohmanFn_eq_sin_sub_mul_cos11 {L x : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    bohmanFn L x =
      (Real.sin (Real.pi * (1 - x / L)) -
        Real.pi * (1 - x / L) * Real.cos (Real.pi * (1 - x / L))) / Real.pi := by
  rw [bohmanFn_of_nonneg_of_le hL hx0 hxL]
  set u : ℝ := Real.pi * (1 - x / L)
  have hu_eq : Real.pi * x / L = Real.pi - u := by dsimp only [u]; ring
  have h1x : 1 - x / L = u / Real.pi := by
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    dsimp only [u]; field_simp [hπ]
  rw [hu_eq, h1x, Real.cos_pi_sub, Real.sin_pi_sub]
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hπ]; ring

private theorem bohman_coeff_bounds11 {p pk k lp_lo lp_hi u_lo u_hi c_lo c_hi : ℝ}
    (hpk : 0 < pk) (hk : 0 < k) (hlp0 : 0 ≤ lp_lo)
    (hlp_lo : lp_lo ≤ Real.log p) (hlp_hi : Real.log p ≤ lp_hi)
    (hk_hi : k * lp_hi ≤ 11 / 2) (hu_lo0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ 3.1415926535 * (1 - k * lp_hi / (11 / 2)))
    (hu_hi : 3.1415926536 * (1 - k * lp_lo / (11 / 2)) ≤ u_hi)
    (hu_hi_pi : u_hi ≤ 3.1415926535)
    (h_clo : c_lo ≤ lp_lo / pk * (bohmanP9 u_lo / 3.1415926536))
    (h_chi : lp_hi / pk * (bohmanP11 u_hi / 3.1415926535) ≤ c_hi) :
    c_lo ≤ Real.log p / pk * bohmanFn (11 / 2) (k * Real.log p) ∧
      Real.log p / pk * bohmanFn (11 / 2) (k * Real.log p) ≤ c_hi := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10_11
  have hπ_pos := Real.pi_pos
  have hlp_nonneg : 0 ≤ Real.log p := hlp0.trans hlp_lo
  have hkx0 : 0 ≤ k * Real.log p := mul_nonneg hk.le hlp_nonneg
  have hkxL : k * Real.log p ≤ 11 / 2 := (mul_le_mul_of_nonneg_left hlp_hi hk.le).trans hk_hi
  set u : ℝ := Real.pi * (1 - k * Real.log p / (11 / 2))
  have h1_lo : 0 ≤ 1 - k * lp_hi / (11 / 2) := by linarith
  have h1_le : 1 - k * lp_hi / (11 / 2) ≤ 1 - k * Real.log p / (11 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_hi hk.le; linarith
  have h1_ge : 1 - k * Real.log p / (11 / 2) ≤ 1 - k * lp_lo / (11 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_lo hk.le; linarith
  have hu_ge_lo : u_lo ≤ u := hu_lo.trans (mul_le_mul hπ_lo.le h1_le h1_lo hπ_pos.le)
  have hu_le_hi : u ≤ u_hi :=
    (mul_le_mul hπ_hi.le h1_ge (by linarith) (by norm_num)).trans hu_hi
  have hu0 : 0 ≤ u := hu_lo0.trans hu_ge_lo
  have hu_hi_lt_pi : u_hi ≤ Real.pi := hu_hi_pi.trans hπ_lo.le
  have hu_pi : u ≤ Real.pi := hu_le_hi.trans hu_hi_lt_pi
  have hH_lo : bohmanP9 u_lo ≤ Real.sin u - u * Real.cos u :=
    (bohmanP9_le_and_le_bohmanP11_11 hu_lo0).1.trans
      (monotoneOn_sin_sub_mul_cos11 ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hH_hi : Real.sin u - u * Real.cos u ≤ bohmanP11 u_hi :=
    (monotoneOn_sin_sub_mul_cos11 ⟨hu0, hu_pi⟩ ⟨hu_lo0.trans (hu_ge_lo.trans hu_le_hi), hu_hi_lt_pi⟩
      hu_le_hi).trans (bohmanP9_le_and_le_bohmanP11_11 (hu_lo0.trans (hu_ge_lo.trans hu_le_hi))).2
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos11 (L := 11 / 2) (x := k * Real.log p) (by norm_num) hkx0 hkxL
  have hW_nonneg : 0 ≤ bohmanFn (11 / 2) (k * Real.log p) := bohmanFn_nonneg (by norm_num) _
  have hW_lo : bohmanP9 u_lo / 3.1415926536 ≤ bohmanFn (11 / 2) (k * Real.log p) := by
    rw [hW_eq]
    by_cases hp9 : 0 ≤ bohmanP9 u_lo
    · exact (div_le_div_of_nonneg_left hp9 hπ_pos hπ_hi.le).trans
        (div_le_div_of_nonneg_right hH_lo hπ_pos.le)
    · exact (div_nonpos_of_nonpos_of_nonneg (not_le.mp hp9).le (by norm_num)).trans
        (by rw [← hW_eq]; exact hW_nonneg)
  have hW_hi : bohmanFn (11 / 2) (k * Real.log p) ≤ bohmanP11 u_hi / 3.1415926535 := by
    rw [hW_eq]
    have hH0 : 0 ≤ Real.sin u - u * Real.cos u := by
      have := mul_nonneg hW_nonneg hπ_pos.le
      rw [hW_eq, div_mul_cancel₀ _ hπ_pos.ne'] at this; exact this
    exact (div_le_div_of_nonneg_right hH_hi hπ_pos.le).trans
      (div_le_div_of_nonneg_left (hH0.trans hH_hi) (by norm_num) hπ_lo.le)
  refine ⟨h_clo.trans ?_, ?_⟩
  · by_cases hw0 : 0 ≤ bohmanP9 u_lo / 3.1415926536
    · exact mul_le_mul (div_le_div_of_nonneg_right hlp_lo hpk.le) hW_lo hw0
        (div_nonneg hlp_nonneg hpk.le)
    · exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlp0 hpk.le) (not_le.mp hw0).le).trans
        (mul_nonneg (div_nonneg hlp_nonneg hpk.le) hW_nonneg)
  · exact (mul_le_mul (div_le_div_of_nonneg_right hlp_hi hpk.le) hW_hi hW_nonneg
      (div_nonneg (hlp_nonneg.trans hlp_hi) hpk.le)).trans h_chi

private theorem cb11_2_1 :
    0.3202637 ≤ Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) ∧
      Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) ≤ 0.3221126 :=
  bohman_coeff_bounds11 (u_lo := 2.74566) (u_hi := 2.74567) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_2 :
    0.1301484 ≤ Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) ∧
      Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) ≤ 0.1303161 :=
  bohman_coeff_bounds11 (u_lo := 2.34974) (u_hi := 2.34975) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_3 :
    0.0457082 ≤ Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) ∧
      Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) ≤ 0.0457198 :=
  bohman_coeff_bounds11 (u_lo := 1.95381) (u_hi := 1.95382) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_4 :
    0.0135108 ≤ Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) ∧
      Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) ≤ 0.0135117 :=
  bohman_coeff_bounds11 (u_lo := 1.55789) (u_hi := 1.5579) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_5 :
    0.0031416 ≤ Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) ∧
      Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) ≤ 0.0031419 :=
  bohman_coeff_bounds11 (u_lo := 1.16196) (u_hi := 1.16197) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_6 :
    0.0004868 ≤ Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) ∧
      Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) ≤ 0.0004871 :=
  bohman_coeff_bounds11 (u_lo := 0.76604) (u_hi := 0.76605) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_2_7 :
    0.0000287 ≤ Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) ∧
      Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) ≤ 0.0000289 :=
  bohman_coeff_bounds11 (u_lo := 0.37011) (u_hi := 0.37012) (by norm_num) (by norm_num) (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_3_1 :
    0.3049577 ≤ Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) ∧
      Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) ≤ 0.3057004 :=
  bohman_coeff_bounds11 (u_lo := 2.51406) (u_hi := 2.51407) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_3_2 :
    0.0596865 ≤ Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) ∧
      Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) ≤ 0.0596979 :=
  bohman_coeff_bounds11 (u_lo := 1.88654) (u_hi := 1.88655) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_3_3 :
    0.0073251 ≤ Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) ∧
      Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) ≤ 0.0073255 :=
  bohman_coeff_bounds11 (u_lo := 1.25901) (u_hi := 1.25902) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_3_4 :
    0.0003481 ≤ Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) ∧
      Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) ≤ 0.0003483 :=
  bohman_coeff_bounds11 (u_lo := 0.63148) (u_hi := 0.63149) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_3_5 :
    0 ≤ Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) ∧
      Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) ≤ 0.0000002 :=
  bohman_coeff_bounds11 (u_lo := 0.00396) (u_hi := 0.00397) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_5_1 :
    0.2193798 ≤ Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) ∧
      Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) ≤ 0.2195494 :=
  bohman_coeff_bounds11 (u_lo := 2.22228) (u_hi := 2.22229) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_5_2 :
    0.0126954 ≤ Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) ∧
      Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) ≤ 0.0126959 :=
  bohman_coeff_bounds11 (u_lo := 1.30297) (u_hi := 1.30298) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_5_3 :
    0.000076 ≤ Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) ∧
      Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) ≤ 0.0000762 :=
  bohman_coeff_bounds11 (u_lo := 0.38366) (u_hi := 0.38367) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_7_1 :
    0.1588986 ≤ Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) ∧
      Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) ≤ 0.1589541 :=
  bohman_coeff_bounds11 (u_lo := 2.03009) (u_hi := 2.0301) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_7_2 :
    0.0029985 ≤ Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) ∧
      Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) ≤ 0.0029989 :=
  bohman_coeff_bounds11 (u_lo := 0.91858) (u_hi := 0.9186) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_11_1 :
    0.0925414 ≤ Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) ∧
      Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) ≤ 0.0925522 :=
  bohman_coeff_bounds11 (u_lo := 1.77191) (u_hi := 1.77192) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_11_2 :
    0.0001346 ≤ Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) ∧
      Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) ≤ 0.0001348 :=
  bohman_coeff_bounds11 (u_lo := 0.40224) (u_hi := 0.40225) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_13_1 :
    0.0735564 ≤ Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) ∧
      Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) ≤ 0.0735624 :=
  bohman_coeff_bounds11 (u_lo := 1.67649) (u_hi := 1.6765) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_13_2 :
    0.0000151 ≤ Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) ∧
      Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) ≤ 0.0000153 :=
  bohman_coeff_bounds11 (u_lo := 0.2114) (u_hi := 0.21141) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_17_1 :
    0.0491482 ≤ Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) ∧
      Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) ≤ 0.0491506 :=
  bohman_coeff_bounds11 (u_lo := 1.52326) (u_hi := 1.52327) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_19_1 :
    0.0410428 ≤ Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) ∧
      Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) ≤ 0.0410445 :=
  bohman_coeff_bounds11 (u_lo := 1.45973) (u_hi := 1.45974) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_23_1 :
    0.0295446 ≤ Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) ∧
      Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) ≤ 0.0295457 :=
  bohman_coeff_bounds11 (u_lo := 1.3506) (u_hi := 1.35061) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_29_1 :
    0.0191371 ≤ Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) ∧
      Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) ≤ 0.0191378 :=
  bohman_coeff_bounds11 (u_lo := 1.21819) (u_hi := 1.2182) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_31_1 :
    0.0167565 ≤ Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) ∧
      Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) ≤ 0.0167571 :=
  bohman_coeff_bounds11 (u_lo := 1.1801) (u_hi := 1.18011) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_37_1 :
    0.0115563 ≤ Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) ∧
      Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) ≤ 0.0115568 :=
  bohman_coeff_bounds11 (u_lo := 1.07904) (u_hi := 1.07905) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_41_1 :
    0.0091861 ≤ Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) ∧
      Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) ≤ 0.0091866 :=
  bohman_coeff_bounds11 (u_lo := 1.0204) (u_hi := 1.02041) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_43_1 :
    0.0082266 ≤ Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) ∧
      Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) ≤ 0.0082272 :=
  bohman_coeff_bounds11 (u_lo := 0.99319) (u_hi := 0.99321) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_47_1 :
    0.0066485 ≤ Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) ∧
      Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) ≤ 0.0066489 :=
  bohman_coeff_bounds11 (u_lo := 0.94239) (u_hi := 0.9424) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_53_1 :
    0.0049082 ≤ Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) ∧
      Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) ≤ 0.0049085 :=
  bohman_coeff_bounds11 (u_lo := 0.87376) (u_hi := 0.87377) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_59_1 :
    0.0036795 ≤ Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) ∧
      Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) ≤ 0.0036799 :=
  bohman_coeff_bounds11 (u_lo := 0.8125) (u_hi := 0.81251) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_61_1 :
    0.003352 ≤ Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) ∧
      Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) ≤ 0.0033524 :=
  bohman_coeff_bounds11 (u_lo := 0.79346) (u_hi := 0.79347) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_67_1 :
    0.002552 ≤ Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) ∧
      Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) ≤ 0.0025523 :=
  bohman_coeff_bounds11 (u_lo := 0.73987) (u_hi := 0.73988) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_71_1 :
    0.0021384 ≤ Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) ∧
      Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) ≤ 0.0021387 :=
  bohman_coeff_bounds11 (u_lo := 0.70675) (u_hi := 0.70676) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_73_1 :
    0.0019599 ≤ Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) ∧
      Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) ≤ 0.0019602 :=
  bohman_coeff_bounds11 (u_lo := 0.69088) (u_hi := 0.69089) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_79_1 :
    0.0015153 ≤ Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) ∧
      Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) ≤ 0.0015156 :=
  bohman_coeff_bounds11 (u_lo := 0.64576) (u_hi := 0.64577) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_83_1 :
    0.0012803 ≤ Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) ∧
      Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) ≤ 0.0012805 :=
  bohman_coeff_bounds11 (u_lo := 0.61755) (u_hi := 0.61756) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_89_1 :
    0.0009975 ≤ Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) ∧
      Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) ≤ 0.0009978 :=
  bohman_coeff_bounds11 (u_lo := 0.57768) (u_hi := 0.57769) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_97_1 :
    0.0007183 ≤ Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) ∧
      Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) ≤ 0.0007185 :=
  bohman_coeff_bounds11 (u_lo := 0.52852) (u_hi := 0.52853) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_97.1 sharp_log_prime_97.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_101_1 :
    0.0006101 ≤ Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) ∧
      Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) ≤ 0.0006104 :=
  bohman_coeff_bounds11 (u_lo := 0.50544) (u_hi := 0.50545) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_101.1 sharp_log_prime_101.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_103_1 :
    0.0005624 ≤ Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) ∧
      Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) ≤ 0.0005626 :=
  bohman_coeff_bounds11 (u_lo := 0.49424) (u_hi := 0.49425) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_107_1 :
    0.0004778 ≤ Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) ∧
      Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) ≤ 0.0004781 :=
  bohman_coeff_bounds11 (u_lo := 0.47247) (u_hi := 0.47248) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_107.1 sharp_log_prime_107.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_109_1 :
    0.0004404 ≤ Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) ∧
      Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) ≤ 0.0004407 :=
  bohman_coeff_bounds11 (u_lo := 0.46189) (u_hi := 0.46191) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_109.1 sharp_log_prime_109.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_113_1 :
    0.0003741 ≤ Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) ∧
      Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) ≤ 0.0003743 :=
  bohman_coeff_bounds11 (u_lo := 0.44131) (u_hi := 0.44132) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_113.1 sharp_log_prime_113.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_127_1 :
    0.0002097 ≤ Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) ∧
      Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) ≤ 0.0002099 :=
  bohman_coeff_bounds11 (u_lo := 0.37459) (u_hi := 0.3746) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_127.1 sharp_log_prime_127.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_131_1 :
    0.0001772 ≤ Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) ∧
      Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) ≤ 0.0001774 :=
  bohman_coeff_bounds11 (u_lo := 0.35688) (u_hi := 0.35689) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_131.1 sharp_log_prime_131.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_137_1 :
    0.000137 ≤ Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) ∧
      Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) ≤ 0.0001372 :=
  bohman_coeff_bounds11 (u_lo := 0.3313) (u_hi := 0.33131) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_137.1 sharp_log_prime_137.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_139_1 :
    0.0001256 ≤ Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) ∧
      Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) ≤ 0.0001258 :=
  bohman_coeff_bounds11 (u_lo := 0.32302) (u_hi := 0.32303) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_139.1 sharp_log_prime_139.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_149_1 :
    0.0000804 ≤ Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) ∧
      Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) ≤ 0.0000806 :=
  bohman_coeff_bounds11 (u_lo := 0.28334) (u_hi := 0.28335) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_149.1 sharp_log_prime_149.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_151_1 :
    0.0000733 ≤ Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) ∧
      Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) ≤ 0.0000735 :=
  bohman_coeff_bounds11 (u_lo := 0.27572) (u_hi := 0.27573) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_151.1 sharp_log_prime_151.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_157_1 :
    0.0000552 ≤ Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) ∧
      Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) ≤ 0.0000554 :=
  bohman_coeff_bounds11 (u_lo := 0.25347) (u_hi := 0.25348) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_157.1 sharp_log_prime_157.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_163_1 :
    0.0000412 ≤ Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) ∧
      Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) ≤ 0.0000414 :=
  bohman_coeff_bounds11 (u_lo := 0.23204) (u_hi := 0.23205) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_163.1 sharp_log_prime_163.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_167_1 :
    0.0000336 ≤ Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) ∧
      Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) ≤ 0.0000338 :=
  bohman_coeff_bounds11 (u_lo := 0.2182) (u_hi := 0.21821) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_167.1 sharp_log_prime_167.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_173_1 :
    0.0000244 ≤ Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) ∧
      Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) ≤ 0.0000246 :=
  bohman_coeff_bounds11 (u_lo := 0.19803) (u_hi := 0.19805) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_173.1 sharp_log_prime_173.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_179_1 :
    0.0000174 ≤ Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) ∧
      Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) ≤ 0.0000176 :=
  bohman_coeff_bounds11 (u_lo := 0.17856) (u_hi := 0.17857) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_179.1 sharp_log_prime_179.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_181_1 :
    0.0000155 ≤ Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) ∧
      Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) ≤ 0.0000157 :=
  bohman_coeff_bounds11 (u_lo := 0.17221) (u_hi := 0.17222) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_181.1 sharp_log_prime_181.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_191_1 :
    0.0000082 ≤ Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) ∧
      Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) ≤ 0.0000084 :=
  bohman_coeff_bounds11 (u_lo := 0.1415) (u_hi := 0.14151) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_191.1 sharp_log_prime_191.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_193_1 :
    0.0000071 ≤ Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) ∧
      Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) ≤ 0.0000073 :=
  bohman_coeff_bounds11 (u_lo := 0.13555) (u_hi := 0.13556) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_193.1 sharp_log_prime_193.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_197_1 :
    0.0000053 ≤ Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) ∧
      Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) ≤ 0.0000055 :=
  bohman_coeff_bounds11 (u_lo := 0.12383) (u_hi := 0.12384) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_197.1 sharp_log_prime_197.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_199_1 :
    0.0000046 ≤ Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) ∧
      Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) ≤ 0.0000048 :=
  bohman_coeff_bounds11 (u_lo := 0.11806) (u_hi := 0.11807) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_199.1 sharp_log_prime_199.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_211_1 :
    0.0000016 ≤ Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) ∧
      Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) ≤ 0.0000018 :=
  bohman_coeff_bounds11 (u_lo := 0.08461) (u_hi := 0.08462) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_211.1 sharp_log_prime_211.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_223_1 :
    0.0000003 ≤ Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) ∧
      Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) ≤ 0.0000005 :=
  bohman_coeff_bounds11 (u_lo := 0.05302) (u_hi := 0.05303) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_223.1 sharp_log_prime_223.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_227_1 :
    0.0000001 ≤ Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) ∧
      Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) ≤ 0.0000003 :=
  bohman_coeff_bounds11 (u_lo := 0.04286) (u_hi := 0.04287) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_227.1 sharp_log_prime_227.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_229_1 :
    0.0000001 ≤ Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) ∧
      Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) ≤ 0.0000003 :=
  bohman_coeff_bounds11 (u_lo := 0.03785) (u_hi := 0.03786) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_229.1 sharp_log_prime_229.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_233_1 :
    0 ≤ Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) ∧
      Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) ≤ 0.0000002 :=
  bohman_coeff_bounds11 (u_lo := 0.02796) (u_hi := 0.02797) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_233.1 sharp_log_prime_233.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_239_1 :
    0 ≤ Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) ∧
      Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) ≤ 0.0000002 :=
  bohman_coeff_bounds11 (u_lo := 0.01344) (u_hi := 0.01345) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_239.1 sharp_log_prime_239.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
private theorem cb11_241_1 :
    0 ≤ Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) ∧
      Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) ≤ 0.0000002 :=
  bohman_coeff_bounds11 (u_lo := 0.00868) (u_hi := 0.00869) (by norm_num) (by norm_num) (by norm_num) sharp_log_prime_241.1 sharp_log_prime_241.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)

/-- Exact Bohman prime-power trigonometric form at `L = 11/2` (`N = 245`). -/
def bohmanPhaseForm11 (θ : ℕ → ℝ) : ℝ :=
  Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) * Real.cos (θ 2) +
  Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) * Real.cos (2 * θ 2) +
  Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) * Real.cos (3 * θ 2) +
  Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) * Real.cos (4 * θ 2) +
  Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) * Real.cos (5 * θ 2) +
  Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) * Real.cos (6 * θ 2) +
  Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) * Real.cos (7 * θ 2) +
  Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) * Real.cos (θ 3) +
  Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) * Real.cos (2 * θ 3) +
  Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) * Real.cos (3 * θ 3) +
  Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) * Real.cos (4 * θ 3) +
  Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) * Real.cos (5 * θ 3) +
  Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) * Real.cos (θ 5) +
  Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) * Real.cos (2 * θ 5) +
  Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) * Real.cos (3 * θ 5) +
  Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) * Real.cos (θ 7) +
  Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) * Real.cos (2 * θ 7) +
  Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) * Real.cos (θ 11) +
  Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) * Real.cos (2 * θ 11) +
  Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) * Real.cos (θ 13) +
  Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) * Real.cos (2 * θ 13) +
  Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) * Real.cos (θ 17) +
  Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) * Real.cos (θ 19) +
  Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) * Real.cos (θ 23) +
  Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) * Real.cos (θ 29) +
  Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) * Real.cos (θ 31) +
  Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) * Real.cos (θ 37) +
  Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) * Real.cos (θ 41) +
  Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) * Real.cos (θ 43) +
  Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) * Real.cos (θ 47) +
  Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) * Real.cos (θ 53) +
  Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) * Real.cos (θ 59) +
  Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) * Real.cos (θ 61) +
  Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) * Real.cos (θ 67) +
  Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) * Real.cos (θ 71) +
  Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) * Real.cos (θ 73) +
  Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) * Real.cos (θ 79) +
  Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) * Real.cos (θ 83) +
  Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) * Real.cos (θ 89) +
  Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) * Real.cos (θ 97) +
  Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) * Real.cos (θ 101) +
  Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) * Real.cos (θ 103) +
  Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) * Real.cos (θ 107) +
  Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) * Real.cos (θ 109) +
  Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) * Real.cos (θ 113) +
  Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) * Real.cos (θ 127) +
  Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) * Real.cos (θ 131) +
  Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) * Real.cos (θ 137) +
  Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) * Real.cos (θ 139) +
  Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) * Real.cos (θ 149) +
  Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) * Real.cos (θ 151) +
  Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) * Real.cos (θ 157) +
  Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) * Real.cos (θ 163) +
  Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) * Real.cos (θ 167) +
  Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) * Real.cos (θ 173) +
  Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) * Real.cos (θ 179) +
  Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) * Real.cos (θ 181) +
  Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) * Real.cos (θ 191) +
  Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) * Real.cos (θ 193) +
  Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) * Real.cos (θ 197) +
  Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) * Real.cos (θ 199) +
  Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) * Real.cos (θ 211) +
  Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) * Real.cos (θ 223) +
  Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) * Real.cos (θ 227) +
  Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) * Real.cos (θ 229) +
  Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) * Real.cos (θ 233) +
  Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) * Real.cos (θ 239) +
  Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) * Real.cos (θ 241)

private theorem Λ_zero_mul11 {n a b : ℕ} (heq : n = a * b) (hc : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : vonMangoldt n = 0 :=
  heq ▸ GaloisForLFunctions.BezoutValuationIncidence.vonMangoldt_mul_eq_zero_of_coprime hc ha hb

private theorem Λ_prime_pow11 {n p k : ℕ} (heq : n = p ^ k) (hp : p.Prime) (hk : k ≠ 0) :
    vonMangoldt n = Real.log p := by
  rw [heq, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem bohman11_block0 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt n / n * bohmanFn (11 / 2) (Real.log n) * Real.cos (γ * Real.log n) =
      Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) * Real.cos (γ * Real.log 2) +
      Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) * Real.cos (γ * Real.log 3) +
      Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) * Real.cos (2 * (γ * Real.log 2)) +
      Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) * Real.cos (γ * Real.log 5) +
      Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) * Real.cos (γ * Real.log 7) +
      Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) * Real.cos (3 * (γ * Real.log 2)) +
      Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) * Real.cos (2 * (γ * Real.log 3)) +
      Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) * Real.cos (γ * Real.log 11) +
      Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) * Real.cos (γ * Real.log 13) +
      Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) * Real.cos (4 * (γ * Real.log 2)) +
      Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) * Real.cos (γ * Real.log 17) +
      Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) * Real.cos (γ * Real.log 19) +
      Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) * Real.cos (γ * Real.log 23) +
      Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) * Real.cos (2 * (γ * Real.log 5)) +
      Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) * Real.cos (3 * (γ * Real.log 3)) +
      Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) * Real.cos (γ * Real.log 29) := by
  have z0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
  have z1 : vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have z6 : vonMangoldt 6 = 0 := Λ_zero_mul11 (a := 2) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z10 : vonMangoldt 10 = 0 := Λ_zero_mul11 (a := 2) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z12 : vonMangoldt 12 = 0 := Λ_zero_mul11 (a := 4) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z14 : vonMangoldt 14 = 0 := Λ_zero_mul11 (a := 2) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z15 : vonMangoldt 15 = 0 := Λ_zero_mul11 (a := 3) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z18 : vonMangoldt 18 = 0 := Λ_zero_mul11 (a := 2) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z20 : vonMangoldt 20 = 0 := Λ_zero_mul11 (a := 4) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z21 : vonMangoldt 21 = 0 := Λ_zero_mul11 (a := 3) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z22 : vonMangoldt 22 = 0 := Λ_zero_mul11 (a := 2) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z24 : vonMangoldt 24 = 0 := Λ_zero_mul11 (a := 8) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z26 : vonMangoldt 26 = 0 := Λ_zero_mul11 (a := 2) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z28 : vonMangoldt 28 = 0 := Λ_zero_mul11 (a := 4) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have p2 : vonMangoldt 2 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 1) rfl (by norm_num) (by norm_num)
  have p3 : vonMangoldt 3 = Real.log 3 := Λ_prime_pow11 (p := 3) (k := 1) rfl (by norm_num) (by norm_num)
  have p4 : vonMangoldt 4 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 2) rfl (by norm_num) (by norm_num)
  have p5 : vonMangoldt 5 = Real.log 5 := Λ_prime_pow11 (p := 5) (k := 1) rfl (by norm_num) (by norm_num)
  have p7 : vonMangoldt 7 = Real.log 7 := Λ_prime_pow11 (p := 7) (k := 1) rfl (by norm_num) (by norm_num)
  have p8 : vonMangoldt 8 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 3) rfl (by norm_num) (by norm_num)
  have p9 : vonMangoldt 9 = Real.log 3 := Λ_prime_pow11 (p := 3) (k := 2) rfl (by norm_num) (by norm_num)
  have p11 : vonMangoldt 11 = Real.log 11 := Λ_prime_pow11 (p := 11) (k := 1) rfl (by norm_num) (by norm_num)
  have p13 : vonMangoldt 13 = Real.log 13 := Λ_prime_pow11 (p := 13) (k := 1) rfl (by norm_num) (by norm_num)
  have p16 : vonMangoldt 16 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 4) rfl (by norm_num) (by norm_num)
  have p17 : vonMangoldt 17 = Real.log 17 := Λ_prime_pow11 (p := 17) (k := 1) rfl (by norm_num) (by norm_num)
  have p19 : vonMangoldt 19 = Real.log 19 := Λ_prime_pow11 (p := 19) (k := 1) rfl (by norm_num) (by norm_num)
  have p23 : vonMangoldt 23 = Real.log 23 := Λ_prime_pow11 (p := 23) (k := 1) rfl (by norm_num) (by norm_num)
  have p25 : vonMangoldt 25 = Real.log 5 := Λ_prime_pow11 (p := 5) (k := 2) rfl (by norm_num) (by norm_num)
  have p27 : vonMangoldt 27 = Real.log 3 := Λ_prime_pow11 (p := 3) (k := 3) rfl (by norm_num) (by norm_num)
  have p29 : vonMangoldt 29 = Real.log 29 := Λ_prime_pow11 (p := 29) (k := 1) rfl (by norm_num) (by norm_num)
  have l4 : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l9 : Real.log 9 = 2 * Real.log 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l16 : Real.log 16 = 4 * Real.log 2 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have l25 : Real.log 25 = 2 * Real.log 5 := by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l27 : Real.log 27 = 3 * Real.log 3 := by rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, z0, z1, p2, p3, p4, p5, z6, p7, p8, p9, z10, p11, z12, p13, z14, z15, p16, p17, z18, p19, z20, z21, z22, p23, z24, p25, z26, p27, z28, p29, zero_div, zero_mul, zero_add, add_zero, one_mul, l4, l8, l9, l16, l25, l27]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman11_block1 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (30 + n) / ((30 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((30 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((30 + n : ℕ) : ℝ)) =
      Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) * Real.cos (γ * Real.log 31) +
      Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) * Real.cos (5 * (γ * Real.log 2)) +
      Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) * Real.cos (γ * Real.log 37) +
      Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) * Real.cos (γ * Real.log 41) +
      Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) * Real.cos (γ * Real.log 43) +
      Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) * Real.cos (γ * Real.log 47) +
      Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) * Real.cos (2 * (γ * Real.log 7)) +
      Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) * Real.cos (γ * Real.log 53) +
      Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) * Real.cos (γ * Real.log 59) := by
  have z30 : vonMangoldt 30 = 0 := Λ_zero_mul11 (a := 2) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z33 : vonMangoldt 33 = 0 := Λ_zero_mul11 (a := 3) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z34 : vonMangoldt 34 = 0 := Λ_zero_mul11 (a := 2) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z35 : vonMangoldt 35 = 0 := Λ_zero_mul11 (a := 5) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z36 : vonMangoldt 36 = 0 := Λ_zero_mul11 (a := 4) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z38 : vonMangoldt 38 = 0 := Λ_zero_mul11 (a := 2) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z39 : vonMangoldt 39 = 0 := Λ_zero_mul11 (a := 3) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z40 : vonMangoldt 40 = 0 := Λ_zero_mul11 (a := 8) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z42 : vonMangoldt 42 = 0 := Λ_zero_mul11 (a := 2) (b := 21) rfl (by norm_num) (by norm_num) (by norm_num)
  have z44 : vonMangoldt 44 = 0 := Λ_zero_mul11 (a := 4) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z45 : vonMangoldt 45 = 0 := Λ_zero_mul11 (a := 9) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z46 : vonMangoldt 46 = 0 := Λ_zero_mul11 (a := 2) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z48 : vonMangoldt 48 = 0 := Λ_zero_mul11 (a := 16) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z50 : vonMangoldt 50 = 0 := Λ_zero_mul11 (a := 2) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z51 : vonMangoldt 51 = 0 := Λ_zero_mul11 (a := 3) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z52 : vonMangoldt 52 = 0 := Λ_zero_mul11 (a := 4) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z54 : vonMangoldt 54 = 0 := Λ_zero_mul11 (a := 2) (b := 27) rfl (by norm_num) (by norm_num) (by norm_num)
  have z55 : vonMangoldt 55 = 0 := Λ_zero_mul11 (a := 5) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z56 : vonMangoldt 56 = 0 := Λ_zero_mul11 (a := 8) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z57 : vonMangoldt 57 = 0 := Λ_zero_mul11 (a := 3) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z58 : vonMangoldt 58 = 0 := Λ_zero_mul11 (a := 2) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have p31 : vonMangoldt 31 = Real.log 31 := Λ_prime_pow11 (p := 31) (k := 1) rfl (by norm_num) (by norm_num)
  have p32 : vonMangoldt 32 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 5) rfl (by norm_num) (by norm_num)
  have p37 : vonMangoldt 37 = Real.log 37 := Λ_prime_pow11 (p := 37) (k := 1) rfl (by norm_num) (by norm_num)
  have p41 : vonMangoldt 41 = Real.log 41 := Λ_prime_pow11 (p := 41) (k := 1) rfl (by norm_num) (by norm_num)
  have p43 : vonMangoldt 43 = Real.log 43 := Λ_prime_pow11 (p := 43) (k := 1) rfl (by norm_num) (by norm_num)
  have p47 : vonMangoldt 47 = Real.log 47 := Λ_prime_pow11 (p := 47) (k := 1) rfl (by norm_num) (by norm_num)
  have p49 : vonMangoldt 49 = Real.log 7 := Λ_prime_pow11 (p := 7) (k := 2) rfl (by norm_num) (by norm_num)
  have p53 : vonMangoldt 53 = Real.log 53 := Λ_prime_pow11 (p := 53) (k := 1) rfl (by norm_num) (by norm_num)
  have p59 : vonMangoldt 59 = Real.log 59 := Λ_prime_pow11 (p := 59) (k := 1) rfl (by norm_num) (by norm_num)
  have l32 : Real.log 32 = 5 * Real.log 2 := by rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have l49 : Real.log 49 = 2 * Real.log 7 := by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z30, p31, p32, z33, z34, z35, z36, p37, z38, z39, z40, p41, z42, p43, z44, z45, z46, p47, z48, p49, z50, z51, z52, p53, z54, z55, z56, z57, z58, p59, zero_div, zero_mul, zero_add, add_zero, one_mul, l32, l49]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman11_block2 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (60 + n) / ((60 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((60 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((60 + n : ℕ) : ℝ)) =
      Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) * Real.cos (γ * Real.log 61) +
      Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) * Real.cos (6 * (γ * Real.log 2)) +
      Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) * Real.cos (γ * Real.log 67) +
      Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) * Real.cos (γ * Real.log 71) +
      Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) * Real.cos (γ * Real.log 73) +
      Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) * Real.cos (γ * Real.log 79) +
      Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) * Real.cos (4 * (γ * Real.log 3)) +
      Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) * Real.cos (γ * Real.log 83) +
      Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) * Real.cos (γ * Real.log 89) := by
  have z60 : vonMangoldt 60 = 0 := Λ_zero_mul11 (a := 4) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z62 : vonMangoldt 62 = 0 := Λ_zero_mul11 (a := 2) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z63 : vonMangoldt 63 = 0 := Λ_zero_mul11 (a := 9) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z65 : vonMangoldt 65 = 0 := Λ_zero_mul11 (a := 5) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z66 : vonMangoldt 66 = 0 := Λ_zero_mul11 (a := 2) (b := 33) rfl (by norm_num) (by norm_num) (by norm_num)
  have z68 : vonMangoldt 68 = 0 := Λ_zero_mul11 (a := 4) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z69 : vonMangoldt 69 = 0 := Λ_zero_mul11 (a := 3) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z70 : vonMangoldt 70 = 0 := Λ_zero_mul11 (a := 2) (b := 35) rfl (by norm_num) (by norm_num) (by norm_num)
  have z72 : vonMangoldt 72 = 0 := Λ_zero_mul11 (a := 8) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z74 : vonMangoldt 74 = 0 := Λ_zero_mul11 (a := 2) (b := 37) rfl (by norm_num) (by norm_num) (by norm_num)
  have z75 : vonMangoldt 75 = 0 := Λ_zero_mul11 (a := 3) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z76 : vonMangoldt 76 = 0 := Λ_zero_mul11 (a := 4) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z77 : vonMangoldt 77 = 0 := Λ_zero_mul11 (a := 7) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z78 : vonMangoldt 78 = 0 := Λ_zero_mul11 (a := 2) (b := 39) rfl (by norm_num) (by norm_num) (by norm_num)
  have z80 : vonMangoldt 80 = 0 := Λ_zero_mul11 (a := 16) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z82 : vonMangoldt 82 = 0 := Λ_zero_mul11 (a := 2) (b := 41) rfl (by norm_num) (by norm_num) (by norm_num)
  have z84 : vonMangoldt 84 = 0 := Λ_zero_mul11 (a := 4) (b := 21) rfl (by norm_num) (by norm_num) (by norm_num)
  have z85 : vonMangoldt 85 = 0 := Λ_zero_mul11 (a := 5) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z86 : vonMangoldt 86 = 0 := Λ_zero_mul11 (a := 2) (b := 43) rfl (by norm_num) (by norm_num) (by norm_num)
  have z87 : vonMangoldt 87 = 0 := Λ_zero_mul11 (a := 3) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z88 : vonMangoldt 88 = 0 := Λ_zero_mul11 (a := 8) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have p61 : vonMangoldt 61 = Real.log 61 := Λ_prime_pow11 (p := 61) (k := 1) rfl (by norm_num) (by norm_num)
  have p64 : vonMangoldt 64 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 6) rfl (by norm_num) (by norm_num)
  have p67 : vonMangoldt 67 = Real.log 67 := Λ_prime_pow11 (p := 67) (k := 1) rfl (by norm_num) (by norm_num)
  have p71 : vonMangoldt 71 = Real.log 71 := Λ_prime_pow11 (p := 71) (k := 1) rfl (by norm_num) (by norm_num)
  have p73 : vonMangoldt 73 = Real.log 73 := Λ_prime_pow11 (p := 73) (k := 1) rfl (by norm_num) (by norm_num)
  have p79 : vonMangoldt 79 = Real.log 79 := Λ_prime_pow11 (p := 79) (k := 1) rfl (by norm_num) (by norm_num)
  have p81 : vonMangoldt 81 = Real.log 3 := Λ_prime_pow11 (p := 3) (k := 4) rfl (by norm_num) (by norm_num)
  have p83 : vonMangoldt 83 = Real.log 83 := Λ_prime_pow11 (p := 83) (k := 1) rfl (by norm_num) (by norm_num)
  have p89 : vonMangoldt 89 = Real.log 89 := Λ_prime_pow11 (p := 89) (k := 1) rfl (by norm_num) (by norm_num)
  have l64 : Real.log 64 = 6 * Real.log 2 := by rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have l81 : Real.log 81 = 4 * Real.log 3 := by rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z60, p61, z62, z63, p64, z65, z66, p67, z68, z69, z70, p71, z72, p73, z74, z75, z76, z77, z78, p79, z80, p81, z82, p83, z84, z85, z86, z87, z88, p89, zero_div, zero_mul, zero_add, add_zero, one_mul, l64, l81]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman11_block3 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (90 + n) / ((90 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((90 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((90 + n : ℕ) : ℝ)) =
      Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) * Real.cos (γ * Real.log 97) +
      Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) * Real.cos (γ * Real.log 101) +
      Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) * Real.cos (γ * Real.log 103) +
      Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) * Real.cos (γ * Real.log 107) +
      Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) * Real.cos (γ * Real.log 109) +
      Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) * Real.cos (γ * Real.log 113) := by
  have z90 : vonMangoldt 90 = 0 := Λ_zero_mul11 (a := 2) (b := 45) rfl (by norm_num) (by norm_num) (by norm_num)
  have z91 : vonMangoldt 91 = 0 := Λ_zero_mul11 (a := 7) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z92 : vonMangoldt 92 = 0 := Λ_zero_mul11 (a := 4) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z93 : vonMangoldt 93 = 0 := Λ_zero_mul11 (a := 3) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z94 : vonMangoldt 94 = 0 := Λ_zero_mul11 (a := 2) (b := 47) rfl (by norm_num) (by norm_num) (by norm_num)
  have z95 : vonMangoldt 95 = 0 := Λ_zero_mul11 (a := 5) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z96 : vonMangoldt 96 = 0 := Λ_zero_mul11 (a := 32) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z98 : vonMangoldt 98 = 0 := Λ_zero_mul11 (a := 2) (b := 49) rfl (by norm_num) (by norm_num) (by norm_num)
  have z99 : vonMangoldt 99 = 0 := Λ_zero_mul11 (a := 9) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z100 : vonMangoldt 100 = 0 := Λ_zero_mul11 (a := 4) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z102 : vonMangoldt 102 = 0 := Λ_zero_mul11 (a := 2) (b := 51) rfl (by norm_num) (by norm_num) (by norm_num)
  have z104 : vonMangoldt 104 = 0 := Λ_zero_mul11 (a := 8) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z105 : vonMangoldt 105 = 0 := Λ_zero_mul11 (a := 3) (b := 35) rfl (by norm_num) (by norm_num) (by norm_num)
  have z106 : vonMangoldt 106 = 0 := Λ_zero_mul11 (a := 2) (b := 53) rfl (by norm_num) (by norm_num) (by norm_num)
  have z108 : vonMangoldt 108 = 0 := Λ_zero_mul11 (a := 4) (b := 27) rfl (by norm_num) (by norm_num) (by norm_num)
  have z110 : vonMangoldt 110 = 0 := Λ_zero_mul11 (a := 2) (b := 55) rfl (by norm_num) (by norm_num) (by norm_num)
  have z111 : vonMangoldt 111 = 0 := Λ_zero_mul11 (a := 3) (b := 37) rfl (by norm_num) (by norm_num) (by norm_num)
  have z112 : vonMangoldt 112 = 0 := Λ_zero_mul11 (a := 16) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z114 : vonMangoldt 114 = 0 := Λ_zero_mul11 (a := 2) (b := 57) rfl (by norm_num) (by norm_num) (by norm_num)
  have z115 : vonMangoldt 115 = 0 := Λ_zero_mul11 (a := 5) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z116 : vonMangoldt 116 = 0 := Λ_zero_mul11 (a := 4) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z117 : vonMangoldt 117 = 0 := Λ_zero_mul11 (a := 9) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z118 : vonMangoldt 118 = 0 := Λ_zero_mul11 (a := 2) (b := 59) rfl (by norm_num) (by norm_num) (by norm_num)
  have z119 : vonMangoldt 119 = 0 := Λ_zero_mul11 (a := 7) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have p97 : vonMangoldt 97 = Real.log 97 := Λ_prime_pow11 (p := 97) (k := 1) rfl (by norm_num) (by norm_num)
  have p101 : vonMangoldt 101 = Real.log 101 := Λ_prime_pow11 (p := 101) (k := 1) rfl (by norm_num) (by norm_num)
  have p103 : vonMangoldt 103 = Real.log 103 := Λ_prime_pow11 (p := 103) (k := 1) rfl (by norm_num) (by norm_num)
  have p107 : vonMangoldt 107 = Real.log 107 := Λ_prime_pow11 (p := 107) (k := 1) rfl (by norm_num) (by norm_num)
  have p109 : vonMangoldt 109 = Real.log 109 := Λ_prime_pow11 (p := 109) (k := 1) rfl (by norm_num) (by norm_num)
  have p113 : vonMangoldt 113 = Real.log 113 := Λ_prime_pow11 (p := 113) (k := 1) rfl (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z90, z91, z92, z93, z94, z95, z96, p97, z98, z99, z100, p101, z102, p103, z104, z105, z106, p107, z108, p109, z110, z111, z112, p113, z114, z115, z116, z117, z118, z119, zero_div, zero_mul, zero_add, add_zero, one_mul]

private theorem bohman11_block4 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (120 + n) / ((120 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((120 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((120 + n : ℕ) : ℝ)) =
      Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) * Real.cos (2 * (γ * Real.log 11)) +
      Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) * Real.cos (3 * (γ * Real.log 5)) +
      Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) * Real.cos (γ * Real.log 127) +
      Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) * Real.cos (7 * (γ * Real.log 2)) +
      Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) * Real.cos (γ * Real.log 131) +
      Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) * Real.cos (γ * Real.log 137) +
      Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) * Real.cos (γ * Real.log 139) +
      Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) * Real.cos (γ * Real.log 149) := by
  have z120 : vonMangoldt 120 = 0 := Λ_zero_mul11 (a := 8) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z122 : vonMangoldt 122 = 0 := Λ_zero_mul11 (a := 2) (b := 61) rfl (by norm_num) (by norm_num) (by norm_num)
  have z123 : vonMangoldt 123 = 0 := Λ_zero_mul11 (a := 3) (b := 41) rfl (by norm_num) (by norm_num) (by norm_num)
  have z124 : vonMangoldt 124 = 0 := Λ_zero_mul11 (a := 4) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z126 : vonMangoldt 126 = 0 := Λ_zero_mul11 (a := 2) (b := 63) rfl (by norm_num) (by norm_num) (by norm_num)
  have z129 : vonMangoldt 129 = 0 := Λ_zero_mul11 (a := 3) (b := 43) rfl (by norm_num) (by norm_num) (by norm_num)
  have z130 : vonMangoldt 130 = 0 := Λ_zero_mul11 (a := 2) (b := 65) rfl (by norm_num) (by norm_num) (by norm_num)
  have z132 : vonMangoldt 132 = 0 := Λ_zero_mul11 (a := 4) (b := 33) rfl (by norm_num) (by norm_num) (by norm_num)
  have z133 : vonMangoldt 133 = 0 := Λ_zero_mul11 (a := 7) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z134 : vonMangoldt 134 = 0 := Λ_zero_mul11 (a := 2) (b := 67) rfl (by norm_num) (by norm_num) (by norm_num)
  have z135 : vonMangoldt 135 = 0 := Λ_zero_mul11 (a := 27) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z136 : vonMangoldt 136 = 0 := Λ_zero_mul11 (a := 8) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z138 : vonMangoldt 138 = 0 := Λ_zero_mul11 (a := 2) (b := 69) rfl (by norm_num) (by norm_num) (by norm_num)
  have z140 : vonMangoldt 140 = 0 := Λ_zero_mul11 (a := 4) (b := 35) rfl (by norm_num) (by norm_num) (by norm_num)
  have z141 : vonMangoldt 141 = 0 := Λ_zero_mul11 (a := 3) (b := 47) rfl (by norm_num) (by norm_num) (by norm_num)
  have z142 : vonMangoldt 142 = 0 := Λ_zero_mul11 (a := 2) (b := 71) rfl (by norm_num) (by norm_num) (by norm_num)
  have z143 : vonMangoldt 143 = 0 := Λ_zero_mul11 (a := 11) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z144 : vonMangoldt 144 = 0 := Λ_zero_mul11 (a := 16) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z145 : vonMangoldt 145 = 0 := Λ_zero_mul11 (a := 5) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z146 : vonMangoldt 146 = 0 := Λ_zero_mul11 (a := 2) (b := 73) rfl (by norm_num) (by norm_num) (by norm_num)
  have z147 : vonMangoldt 147 = 0 := Λ_zero_mul11 (a := 3) (b := 49) rfl (by norm_num) (by norm_num) (by norm_num)
  have z148 : vonMangoldt 148 = 0 := Λ_zero_mul11 (a := 4) (b := 37) rfl (by norm_num) (by norm_num) (by norm_num)
  have p121 : vonMangoldt 121 = Real.log 11 := Λ_prime_pow11 (p := 11) (k := 2) rfl (by norm_num) (by norm_num)
  have p125 : vonMangoldt 125 = Real.log 5 := Λ_prime_pow11 (p := 5) (k := 3) rfl (by norm_num) (by norm_num)
  have p127 : vonMangoldt 127 = Real.log 127 := Λ_prime_pow11 (p := 127) (k := 1) rfl (by norm_num) (by norm_num)
  have p128 : vonMangoldt 128 = Real.log 2 := Λ_prime_pow11 (p := 2) (k := 7) rfl (by norm_num) (by norm_num)
  have p131 : vonMangoldt 131 = Real.log 131 := Λ_prime_pow11 (p := 131) (k := 1) rfl (by norm_num) (by norm_num)
  have p137 : vonMangoldt 137 = Real.log 137 := Λ_prime_pow11 (p := 137) (k := 1) rfl (by norm_num) (by norm_num)
  have p139 : vonMangoldt 139 = Real.log 139 := Λ_prime_pow11 (p := 139) (k := 1) rfl (by norm_num) (by norm_num)
  have p149 : vonMangoldt 149 = Real.log 149 := Λ_prime_pow11 (p := 149) (k := 1) rfl (by norm_num) (by norm_num)
  have l121 : Real.log 121 = 2 * Real.log 11 := by rw [show (121 : ℝ) = 11 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l125 : Real.log 125 = 3 * Real.log 5 := by rw [show (125 : ℝ) = 5 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l128 : Real.log 128 = 7 * Real.log 2 := by rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z120, p121, z122, z123, z124, p125, z126, p127, p128, z129, z130, p131, z132, z133, z134, z135, z136, p137, z138, p139, z140, z141, z142, z143, z144, z145, z146, z147, z148, p149, zero_div, zero_mul, zero_add, add_zero, one_mul, l121, l125, l128]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman11_block5 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (150 + n) / ((150 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((150 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((150 + n : ℕ) : ℝ)) =
      Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) * Real.cos (γ * Real.log 151) +
      Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) * Real.cos (γ * Real.log 157) +
      Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) * Real.cos (γ * Real.log 163) +
      Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) * Real.cos (γ * Real.log 167) +
      Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) * Real.cos (2 * (γ * Real.log 13)) +
      Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) * Real.cos (γ * Real.log 173) +
      Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) * Real.cos (γ * Real.log 179) := by
  have z150 : vonMangoldt 150 = 0 := Λ_zero_mul11 (a := 2) (b := 75) rfl (by norm_num) (by norm_num) (by norm_num)
  have z152 : vonMangoldt 152 = 0 := Λ_zero_mul11 (a := 8) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z153 : vonMangoldt 153 = 0 := Λ_zero_mul11 (a := 9) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z154 : vonMangoldt 154 = 0 := Λ_zero_mul11 (a := 2) (b := 77) rfl (by norm_num) (by norm_num) (by norm_num)
  have z155 : vonMangoldt 155 = 0 := Λ_zero_mul11 (a := 5) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z156 : vonMangoldt 156 = 0 := Λ_zero_mul11 (a := 4) (b := 39) rfl (by norm_num) (by norm_num) (by norm_num)
  have z158 : vonMangoldt 158 = 0 := Λ_zero_mul11 (a := 2) (b := 79) rfl (by norm_num) (by norm_num) (by norm_num)
  have z159 : vonMangoldt 159 = 0 := Λ_zero_mul11 (a := 3) (b := 53) rfl (by norm_num) (by norm_num) (by norm_num)
  have z160 : vonMangoldt 160 = 0 := Λ_zero_mul11 (a := 32) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z161 : vonMangoldt 161 = 0 := Λ_zero_mul11 (a := 7) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z162 : vonMangoldt 162 = 0 := Λ_zero_mul11 (a := 2) (b := 81) rfl (by norm_num) (by norm_num) (by norm_num)
  have z164 : vonMangoldt 164 = 0 := Λ_zero_mul11 (a := 4) (b := 41) rfl (by norm_num) (by norm_num) (by norm_num)
  have z165 : vonMangoldt 165 = 0 := Λ_zero_mul11 (a := 3) (b := 55) rfl (by norm_num) (by norm_num) (by norm_num)
  have z166 : vonMangoldt 166 = 0 := Λ_zero_mul11 (a := 2) (b := 83) rfl (by norm_num) (by norm_num) (by norm_num)
  have z168 : vonMangoldt 168 = 0 := Λ_zero_mul11 (a := 8) (b := 21) rfl (by norm_num) (by norm_num) (by norm_num)
  have z170 : vonMangoldt 170 = 0 := Λ_zero_mul11 (a := 2) (b := 85) rfl (by norm_num) (by norm_num) (by norm_num)
  have z171 : vonMangoldt 171 = 0 := Λ_zero_mul11 (a := 9) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z172 : vonMangoldt 172 = 0 := Λ_zero_mul11 (a := 4) (b := 43) rfl (by norm_num) (by norm_num) (by norm_num)
  have z174 : vonMangoldt 174 = 0 := Λ_zero_mul11 (a := 2) (b := 87) rfl (by norm_num) (by norm_num) (by norm_num)
  have z175 : vonMangoldt 175 = 0 := Λ_zero_mul11 (a := 25) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z176 : vonMangoldt 176 = 0 := Λ_zero_mul11 (a := 16) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z177 : vonMangoldt 177 = 0 := Λ_zero_mul11 (a := 3) (b := 59) rfl (by norm_num) (by norm_num) (by norm_num)
  have z178 : vonMangoldt 178 = 0 := Λ_zero_mul11 (a := 2) (b := 89) rfl (by norm_num) (by norm_num) (by norm_num)
  have p151 : vonMangoldt 151 = Real.log 151 := Λ_prime_pow11 (p := 151) (k := 1) rfl (by norm_num) (by norm_num)
  have p157 : vonMangoldt 157 = Real.log 157 := Λ_prime_pow11 (p := 157) (k := 1) rfl (by norm_num) (by norm_num)
  have p163 : vonMangoldt 163 = Real.log 163 := Λ_prime_pow11 (p := 163) (k := 1) rfl (by norm_num) (by norm_num)
  have p167 : vonMangoldt 167 = Real.log 167 := Λ_prime_pow11 (p := 167) (k := 1) rfl (by norm_num) (by norm_num)
  have p169 : vonMangoldt 169 = Real.log 13 := Λ_prime_pow11 (p := 13) (k := 2) rfl (by norm_num) (by norm_num)
  have p173 : vonMangoldt 173 = Real.log 173 := Λ_prime_pow11 (p := 173) (k := 1) rfl (by norm_num) (by norm_num)
  have p179 : vonMangoldt 179 = Real.log 179 := Λ_prime_pow11 (p := 179) (k := 1) rfl (by norm_num) (by norm_num)
  have l169 : Real.log 169 = 2 * Real.log 13 := by rw [show (169 : ℝ) = 13 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z150, p151, z152, z153, z154, z155, z156, p157, z158, z159, z160, z161, z162, p163, z164, z165, z166, p167, z168, p169, z170, z171, z172, p173, z174, z175, z176, z177, z178, p179, zero_div, zero_mul, zero_add, add_zero, one_mul, l169]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman11_block6 (γ : ℝ) :
    ∑ n ∈ Finset.range 30, vonMangoldt (180 + n) / ((180 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((180 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((180 + n : ℕ) : ℝ)) =
      Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) * Real.cos (γ * Real.log 181) +
      Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) * Real.cos (γ * Real.log 191) +
      Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) * Real.cos (γ * Real.log 193) +
      Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) * Real.cos (γ * Real.log 197) +
      Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) * Real.cos (γ * Real.log 199) := by
  have z180 : vonMangoldt 180 = 0 := Λ_zero_mul11 (a := 4) (b := 45) rfl (by norm_num) (by norm_num) (by norm_num)
  have z182 : vonMangoldt 182 = 0 := Λ_zero_mul11 (a := 2) (b := 91) rfl (by norm_num) (by norm_num) (by norm_num)
  have z183 : vonMangoldt 183 = 0 := Λ_zero_mul11 (a := 3) (b := 61) rfl (by norm_num) (by norm_num) (by norm_num)
  have z184 : vonMangoldt 184 = 0 := Λ_zero_mul11 (a := 8) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z185 : vonMangoldt 185 = 0 := Λ_zero_mul11 (a := 5) (b := 37) rfl (by norm_num) (by norm_num) (by norm_num)
  have z186 : vonMangoldt 186 = 0 := Λ_zero_mul11 (a := 2) (b := 93) rfl (by norm_num) (by norm_num) (by norm_num)
  have z187 : vonMangoldt 187 = 0 := Λ_zero_mul11 (a := 11) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z188 : vonMangoldt 188 = 0 := Λ_zero_mul11 (a := 4) (b := 47) rfl (by norm_num) (by norm_num) (by norm_num)
  have z189 : vonMangoldt 189 = 0 := Λ_zero_mul11 (a := 27) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z190 : vonMangoldt 190 = 0 := Λ_zero_mul11 (a := 2) (b := 95) rfl (by norm_num) (by norm_num) (by norm_num)
  have z192 : vonMangoldt 192 = 0 := Λ_zero_mul11 (a := 64) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z194 : vonMangoldt 194 = 0 := Λ_zero_mul11 (a := 2) (b := 97) rfl (by norm_num) (by norm_num) (by norm_num)
  have z195 : vonMangoldt 195 = 0 := Λ_zero_mul11 (a := 3) (b := 65) rfl (by norm_num) (by norm_num) (by norm_num)
  have z196 : vonMangoldt 196 = 0 := Λ_zero_mul11 (a := 4) (b := 49) rfl (by norm_num) (by norm_num) (by norm_num)
  have z198 : vonMangoldt 198 = 0 := Λ_zero_mul11 (a := 2) (b := 99) rfl (by norm_num) (by norm_num) (by norm_num)
  have z200 : vonMangoldt 200 = 0 := Λ_zero_mul11 (a := 8) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z201 : vonMangoldt 201 = 0 := Λ_zero_mul11 (a := 3) (b := 67) rfl (by norm_num) (by norm_num) (by norm_num)
  have z202 : vonMangoldt 202 = 0 := Λ_zero_mul11 (a := 2) (b := 101) rfl (by norm_num) (by norm_num) (by norm_num)
  have z203 : vonMangoldt 203 = 0 := Λ_zero_mul11 (a := 7) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z204 : vonMangoldt 204 = 0 := Λ_zero_mul11 (a := 4) (b := 51) rfl (by norm_num) (by norm_num) (by norm_num)
  have z205 : vonMangoldt 205 = 0 := Λ_zero_mul11 (a := 5) (b := 41) rfl (by norm_num) (by norm_num) (by norm_num)
  have z206 : vonMangoldt 206 = 0 := Λ_zero_mul11 (a := 2) (b := 103) rfl (by norm_num) (by norm_num) (by norm_num)
  have z207 : vonMangoldt 207 = 0 := Λ_zero_mul11 (a := 9) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z208 : vonMangoldt 208 = 0 := Λ_zero_mul11 (a := 16) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z209 : vonMangoldt 209 = 0 := Λ_zero_mul11 (a := 11) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have p181 : vonMangoldt 181 = Real.log 181 := Λ_prime_pow11 (p := 181) (k := 1) rfl (by norm_num) (by norm_num)
  have p191 : vonMangoldt 191 = Real.log 191 := Λ_prime_pow11 (p := 191) (k := 1) rfl (by norm_num) (by norm_num)
  have p193 : vonMangoldt 193 = Real.log 193 := Λ_prime_pow11 (p := 193) (k := 1) rfl (by norm_num) (by norm_num)
  have p197 : vonMangoldt 197 = Real.log 197 := Λ_prime_pow11 (p := 197) (k := 1) rfl (by norm_num) (by norm_num)
  have p199 : vonMangoldt 199 = Real.log 199 := Λ_prime_pow11 (p := 199) (k := 1) rfl (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z180, p181, z182, z183, z184, z185, z186, z187, z188, z189, z190, p191, z192, p193, z194, z195, z196, p197, z198, p199, z200, z201, z202, z203, z204, z205, z206, z207, z208, z209, zero_div, zero_mul, zero_add, add_zero, one_mul]

private theorem bohman11_block7 (γ : ℝ) :
    ∑ n ∈ Finset.range 35, vonMangoldt (210 + n) / ((210 + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((210 + n : ℕ) : ℝ)) * Real.cos (γ * Real.log ((210 + n : ℕ) : ℝ)) =
      Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) * Real.cos (γ * Real.log 211) +
      Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) * Real.cos (γ * Real.log 223) +
      Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) * Real.cos (γ * Real.log 227) +
      Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) * Real.cos (γ * Real.log 229) +
      Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) * Real.cos (γ * Real.log 233) +
      Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) * Real.cos (γ * Real.log 239) +
      Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) * Real.cos (γ * Real.log 241) +
      Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) * Real.cos (5 * (γ * Real.log 3)) := by
  have z210 : vonMangoldt 210 = 0 := Λ_zero_mul11 (a := 2) (b := 105) rfl (by norm_num) (by norm_num) (by norm_num)
  have z212 : vonMangoldt 212 = 0 := Λ_zero_mul11 (a := 4) (b := 53) rfl (by norm_num) (by norm_num) (by norm_num)
  have z213 : vonMangoldt 213 = 0 := Λ_zero_mul11 (a := 3) (b := 71) rfl (by norm_num) (by norm_num) (by norm_num)
  have z214 : vonMangoldt 214 = 0 := Λ_zero_mul11 (a := 2) (b := 107) rfl (by norm_num) (by norm_num) (by norm_num)
  have z215 : vonMangoldt 215 = 0 := Λ_zero_mul11 (a := 5) (b := 43) rfl (by norm_num) (by norm_num) (by norm_num)
  have z216 : vonMangoldt 216 = 0 := Λ_zero_mul11 (a := 8) (b := 27) rfl (by norm_num) (by norm_num) (by norm_num)
  have z217 : vonMangoldt 217 = 0 := Λ_zero_mul11 (a := 7) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z218 : vonMangoldt 218 = 0 := Λ_zero_mul11 (a := 2) (b := 109) rfl (by norm_num) (by norm_num) (by norm_num)
  have z219 : vonMangoldt 219 = 0 := Λ_zero_mul11 (a := 3) (b := 73) rfl (by norm_num) (by norm_num) (by norm_num)
  have z220 : vonMangoldt 220 = 0 := Λ_zero_mul11 (a := 4) (b := 55) rfl (by norm_num) (by norm_num) (by norm_num)
  have z221 : vonMangoldt 221 = 0 := Λ_zero_mul11 (a := 13) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z222 : vonMangoldt 222 = 0 := Λ_zero_mul11 (a := 2) (b := 111) rfl (by norm_num) (by norm_num) (by norm_num)
  have z224 : vonMangoldt 224 = 0 := Λ_zero_mul11 (a := 32) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z225 : vonMangoldt 225 = 0 := Λ_zero_mul11 (a := 9) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z226 : vonMangoldt 226 = 0 := Λ_zero_mul11 (a := 2) (b := 113) rfl (by norm_num) (by norm_num) (by norm_num)
  have z228 : vonMangoldt 228 = 0 := Λ_zero_mul11 (a := 4) (b := 57) rfl (by norm_num) (by norm_num) (by norm_num)
  have z230 : vonMangoldt 230 = 0 := Λ_zero_mul11 (a := 2) (b := 115) rfl (by norm_num) (by norm_num) (by norm_num)
  have z231 : vonMangoldt 231 = 0 := Λ_zero_mul11 (a := 3) (b := 77) rfl (by norm_num) (by norm_num) (by norm_num)
  have z232 : vonMangoldt 232 = 0 := Λ_zero_mul11 (a := 8) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z234 : vonMangoldt 234 = 0 := Λ_zero_mul11 (a := 2) (b := 117) rfl (by norm_num) (by norm_num) (by norm_num)
  have z235 : vonMangoldt 235 = 0 := Λ_zero_mul11 (a := 5) (b := 47) rfl (by norm_num) (by norm_num) (by norm_num)
  have z236 : vonMangoldt 236 = 0 := Λ_zero_mul11 (a := 4) (b := 59) rfl (by norm_num) (by norm_num) (by norm_num)
  have z237 : vonMangoldt 237 = 0 := Λ_zero_mul11 (a := 3) (b := 79) rfl (by norm_num) (by norm_num) (by norm_num)
  have z238 : vonMangoldt 238 = 0 := Λ_zero_mul11 (a := 2) (b := 119) rfl (by norm_num) (by norm_num) (by norm_num)
  have z240 : vonMangoldt 240 = 0 := Λ_zero_mul11 (a := 16) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z242 : vonMangoldt 242 = 0 := Λ_zero_mul11 (a := 2) (b := 121) rfl (by norm_num) (by norm_num) (by norm_num)
  have z244 : vonMangoldt 244 = 0 := Λ_zero_mul11 (a := 4) (b := 61) rfl (by norm_num) (by norm_num) (by norm_num)
  have p211 : vonMangoldt 211 = Real.log 211 := Λ_prime_pow11 (p := 211) (k := 1) rfl (by norm_num) (by norm_num)
  have p223 : vonMangoldt 223 = Real.log 223 := Λ_prime_pow11 (p := 223) (k := 1) rfl (by norm_num) (by norm_num)
  have p227 : vonMangoldt 227 = Real.log 227 := Λ_prime_pow11 (p := 227) (k := 1) rfl (by norm_num) (by norm_num)
  have p229 : vonMangoldt 229 = Real.log 229 := Λ_prime_pow11 (p := 229) (k := 1) rfl (by norm_num) (by norm_num)
  have p233 : vonMangoldt 233 = Real.log 233 := Λ_prime_pow11 (p := 233) (k := 1) rfl (by norm_num) (by norm_num)
  have p239 : vonMangoldt 239 = Real.log 239 := Λ_prime_pow11 (p := 239) (k := 1) rfl (by norm_num) (by norm_num)
  have p241 : vonMangoldt 241 = Real.log 241 := Λ_prime_pow11 (p := 241) (k := 1) rfl (by norm_num) (by norm_num)
  have p243 : vonMangoldt 243 = Real.log 3 := Λ_prime_pow11 (p := 3) (k := 5) rfl (by norm_num) (by norm_num)
  have l243 : Real.log 243 = 5 * Real.log 3 := by rw [show (243 : ℝ) = 3 ^ 5 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, z210, p211, z212, z213, z214, z215, z216, z217, z218, z219, z220, z221, z222, p223, z224, z225, z226, p227, z228, p229, z230, z231, z232, p233, z234, z235, z236, z237, z238, p239, z240, p241, z242, p243, z244, zero_div, zero_mul, zero_add, add_zero, one_mul, l243]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

theorem bohman11_prime_sum_eq_phaseForm (γ : ℝ) :
    (∑ n ∈ Finset.range 245,
      vonMangoldt n / n * bohmanFn (11 / 2) (Real.log n) * Real.cos (γ * Real.log n)) =
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) := by
  have hs : ∀ a b : ℕ,
      (∑ n ∈ Finset.range (a + b),
        vonMangoldt n / (n : ℝ) * bohmanFn (11 / 2) (Real.log (n : ℝ)) * Real.cos (γ * Real.log (n : ℝ))) =
      (∑ n ∈ Finset.range a,
        vonMangoldt n / (n : ℝ) * bohmanFn (11 / 2) (Real.log (n : ℝ)) * Real.cos (γ * Real.log (n : ℝ))) +
      (∑ n ∈ Finset.range b,
        vonMangoldt (a + n) / ((a + n : ℕ) : ℝ) * bohmanFn (11 / 2) (Real.log ((a + n : ℕ) : ℝ)) *
          Real.cos (γ * Real.log ((a + n : ℕ) : ℝ))) := fun a b => Finset.sum_range_add _ a b
  rw [show (245 : ℕ) = 210 + 35 by rfl, hs 210 35,
    show (210 : ℕ) = 180 + 30 by rfl, hs 180 30,
    show (180 : ℕ) = 150 + 30 by rfl, hs 150 30,
    show (150 : ℕ) = 120 + 30 by rfl, hs 120 30,
    show (120 : ℕ) = 90 + 30 by rfl, hs 90 30,
    show (90 : ℕ) = 60 + 30 by rfl, hs 60 30,
    show (60 : ℕ) = 30 + 30 by rfl, hs 30 30,
    bohman11_block0, bohman11_block1, bohman11_block2, bohman11_block3,
    bohman11_block4, bohman11_block5, bohman11_block6, bohman11_block7]
  unfold bohmanPhaseForm11
  simp only [Nat.cast_ofNat]
  ring

/-! ## Degree-7 Chebyshev monotonicity and nonnegative prime-excess decomposition -/

def chebPoly7 (A B C D E G H u : ℝ) : ℝ :=
  A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
    D * (8 * u ^ 4 - 8 * u ^ 2 + 1) + E * (16 * u ^ 5 - 20 * u ^ 3 + 5 * u) +
    G * (32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 1) +
    H * (64 * u ^ 7 - 112 * u ^ 5 + 56 * u ^ 3 - 7 * u)

private theorem hasDerivAt_chebPoly7 (A B C D E G H u : ℝ) :
    HasDerivAt (chebPoly7 A B C D E G H)
      (A + 4 * B * u + C * (12 * u ^ 2 - 3) + D * (32 * u ^ 3 - 16 * u) +
        E * (80 * u ^ 4 - 60 * u ^ 2 + 5) + G * (192 * u ^ 5 - 192 * u ^ 3 + 36 * u) +
        H * (448 * u ^ 6 - 560 * u ^ 4 + 168 * u ^ 2 - 7)) u := by
  unfold chebPoly7
  have d1 := (hasDerivAt_id u).const_mul A
  have d2 := (((hasDerivAt_pow 2 u).const_mul 2).sub (hasDerivAt_const u 1)).const_mul B
  have d3 := (((hasDerivAt_pow 3 u).const_mul 4).sub ((hasDerivAt_id u).const_mul 3)).const_mul C
  have d4 := ((((hasDerivAt_pow 4 u).const_mul 8).sub
    ((hasDerivAt_pow 2 u).const_mul 8)).add (hasDerivAt_const u 1)).const_mul D
  have d5 := ((((hasDerivAt_pow 5 u).const_mul 16).sub
    ((hasDerivAt_pow 3 u).const_mul 20)).add ((hasDerivAt_id u).const_mul 5)).const_mul E
  have d6 := (((((hasDerivAt_pow 6 u).const_mul 32).sub
    ((hasDerivAt_pow 4 u).const_mul 48)).add ((hasDerivAt_pow 2 u).const_mul 18)).sub
    (hasDerivAt_const u 1)).const_mul G
  have d7 := (((((hasDerivAt_pow 7 u).const_mul 64).sub
    ((hasDerivAt_pow 5 u).const_mul 112)).add ((hasDerivAt_pow 3 u).const_mul 56)).sub
    ((hasDerivAt_id u).const_mul 7)).const_mul H
  exact ((((((d1.add d2).add d3).add d4).add d5).add d6).add d7).congr_deriv (by norm_num; ring)

private theorem monotoneOn_chebPoly7_of_sos {A B C D E G H G_hi H_hi : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hG0 : 0 ≤ G) (hG : G ≤ G_hi) (hH0 : 0 ≤ H) (hH : H ≤ H_hi)
    (hq2 : 0 < 12 * C - (224 / 5) * D + 44 * E)
    (hdisc : (4 * B - (752 / 25) * D) ^ 2 ≤
      4 * (12 * C - (224 / 5) * D + 44 * E) *
        (A - 3 * C - (32 / 25) * D - (144 / 5) * E - 36 * G_hi - 14 * H_hi)) :
    MonotoneOn (chebPoly7 A B C D E G H) (Icc (-1) 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1) 1)
    (fun u _ => (hasDerivAt_chebPoly7 A B C D E G H u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_chebPoly7 A B C D E G H u).hasDerivWithinAt)
    fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := interior_subset hu
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
  have hg_lb : -(36 * G_hi) ≤ G * (192 * u ^ 5 - 192 * u ^ 3 + 36 * u) := by
    have hid : 192 * u ^ 5 - 192 * u ^ 3 + 36 * u + 36 =
        12 * (u + 1) * ((4 * u - 3) ^ 2 * ((u + 1 / 4) ^ 2 + 1 / 8) + 21 / 16) := by ring
    have hnn : 0 ≤ 12 * (u + 1) * ((4 * u - 3) ^ 2 * ((u + 1 / 4) ^ 2 + 1 / 8) + 21 / 16) :=
      mul_nonneg (by linarith only [hu0])
        (add_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (by norm_num))) (by norm_num))
    have hge : (-36 : ℝ) ≤ 192 * u ^ 5 - 192 * u ^ 3 + 36 * u := by linarith only [hid, hnn]
    nlinarith only [hge, hG0, hG]
  have hh_lb : -(14 * H_hi) ≤ H * (448 * u ^ 6 - 560 * u ^ 4 + 168 * u ^ 2 - 7) := by
    have hid : 448 * u ^ 6 - 560 * u ^ 4 + 168 * u ^ 2 - 7 + 14 =
        7 * (8 * u ^ 3 - 5 * u) ^ 2 + 7 * (1 - u ^ 2) := by ring
    have hnn : 0 ≤ 7 * (8 * u ^ 3 - 5 * u) ^ 2 + 7 * (1 - u ^ 2) :=
      add_nonneg (by positivity) (by linarith only [hu2])
    have hge : (-14 : ℝ) ≤ 448 * u ^ 6 - 560 * u ^ 4 + 168 * u ^ 2 - 7 := by linarith only [hid, hnn]
    nlinarith only [hge, hH0, hH]
  have hd_cub : 0 ≤ 32 * D * (u + 1) * (u + 1 / 5) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith only [hu0])) (sq_nonneg _)
  have he_quart : 0 ≤ 80 * E * (u ^ 2 - 13 / 20) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  set q2 : ℝ := 12 * C - (224 / 5) * D + 44 * E
  set q1 : ℝ := 4 * B - (752 / 25) * D
  set q0 : ℝ := A - 3 * C - (32 / 25) * D - (144 / 5) * E - 36 * G_hi - 14 * H_hi
  have hquad : 0 ≤ q2 * u ^ 2 + q1 * u + q0 := by
    have h4 : 0 ≤ 4 * q2 * (q2 * u ^ 2 + q1 * u + q0) := by
      nlinarith only [sq_nonneg (2 * q2 * u + q1), hdisc]
    exact nonneg_of_mul_nonneg_right h4 (by positivity)
  have hdecomp : A + 4 * B * u + C * (12 * u ^ 2 - 3) + D * (32 * u ^ 3 - 16 * u) +
      E * (80 * u ^ 4 - 60 * u ^ 2 + 5) - 36 * G_hi - 14 * H_hi =
      (q2 * u ^ 2 + q1 * u + q0) + 32 * D * (u + 1) * (u + 1 / 5) ^ 2 +
        80 * E * (u ^ 2 - 13 / 20) ^ 2 := by
    dsimp only [q2, q1, q0]; ring
  linarith only [hdecomp, hquad, hd_cub, he_quart, hg_lb, hh_lb]

private theorem monotoneOn_chebPoly5_of_linear {A B C D E : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hlin : 4 * B + 3 * C + 16 * D + (25 / 4) * E ≤ A) :
    MonotoneOn (chebPoly7 A B C D E 0 0) (Icc (-1) 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1) 1)
    (fun u _ => (hasDerivAt_chebPoly7 A B C D E 0 0 u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_chebPoly7 A B C D E 0 0 u).hasDerivWithinAt)
    fun u hu => ?_
  obtain ⟨hu0, _⟩ := interior_subset hu
  have hd_lb : -(16 * D) ≤ D * (32 * u ^ 3 - 16 * u) := by
    have hid : 32 * u ^ 3 - 16 * u + 16 = 16 * (u + 1) * (u ^ 2 + (u - 1) ^ 2) := by ring
    have hnn : 0 ≤ 16 * (u + 1) * (u ^ 2 + (u - 1) ^ 2) :=
      mul_nonneg (by linarith only [hu0]) (add_nonneg (sq_nonneg u) (sq_nonneg (u - 1)))
    nlinarith only [hid, hnn, hD]
  have he_lb : -((25 / 4) * E) ≤ E * (80 * u ^ 4 - 60 * u ^ 2 + 5) := by
    have hid : 80 * u ^ 4 - 60 * u ^ 2 + 5 + 25 / 4 = 5 * (4 * u ^ 2 - 3 / 2) ^ 2 := by ring
    have hge : -(25 / 4 : ℝ) ≤ 80 * u ^ 4 - 60 * u ^ 2 + 5 := by
      nlinarith only [hid, sq_nonneg (4 * u ^ 2 - 3 / 2)]
    nlinarith only [hge, hE]
  nlinarith only [hu0, hB, hC, sq_nonneg u, hd_lb, he_lb, hlin]

private theorem weighted_sign_lb11 {c_lo c_hi c t : ℝ} (hlo : c_lo ≤ c) (hhi : c ≤ c_hi) :
    c_lo * max t 0 + c_hi * min t 0 ≤ c * t := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, min_eq_right ht]; nlinarith only [hlo, ht]
  · rw [max_eq_right ht, min_eq_left ht]; nlinarith only [hhi, ht]

private theorem cos_chebyshev_seven (θ : ℝ) :
    let u := Real.cos θ
    Real.cos (2 * θ) = 2 * u ^ 2 - 1 ∧
      Real.cos (3 * θ) = 4 * u ^ 3 - 3 * u ∧
      Real.cos (4 * θ) = 8 * u ^ 4 - 8 * u ^ 2 + 1 ∧
      Real.cos (5 * θ) = 16 * u ^ 5 - 20 * u ^ 3 + 5 * u ∧
      Real.cos (6 * θ) = 32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 1 ∧
      Real.cos (7 * θ) = 64 * u ^ 7 - 112 * u ^ 5 + 56 * u ^ 3 - 7 * u := by
  dsimp only
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have h3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := Real.cos_three_mul θ
  have hrec : ∀ k : ℝ, Real.cos ((k + 1) * θ) =
      2 * Real.cos θ * Real.cos (k * θ) - Real.cos ((k - 1) * θ) := fun k => by
    have ha := Real.cos_add (k * θ) θ
    have hs := Real.cos_sub (k * θ) θ
    rw [show k * θ + θ = (k + 1) * θ by ring] at ha
    rw [show k * θ - θ = (k - 1) * θ by ring] at hs
    linarith only [ha, hs]
  have h4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    have hr := hrec 3; norm_num at hr; rw [hr, h3, h2]; ring
  have h5 : Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
    have hr := hrec 4; norm_num at hr; rw [hr, h4, h3]; ring
  have h6 : Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
    have hr := hrec 5; norm_num at hr; rw [hr, h5, h4]; ring
  have h7 : Real.cos (7 * θ) = 64 * Real.cos θ ^ 7 - 112 * Real.cos θ ^ 5 + 56 * Real.cos θ ^ 3 - 7 * Real.cos θ := by
    have hr := hrec 6; norm_num at hr; rw [hr, h6, h5]; ring
  exact ⟨h2, h3, h4, h5, h6, h7⟩

private def bohmanTerm11_2 (θ : ℝ) : ℝ :=
  Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) * Real.cos θ +
    Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) * Real.cos (2 * θ) +
    Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) * Real.cos (3 * θ) +
    Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) * Real.cos (4 * θ) +
    Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) * Real.cos (5 * θ) +
    Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) * Real.cos (6 * θ) +
    Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) * Real.cos (7 * θ)

private def bohmanTerm11_3 (θ : ℝ) : ℝ :=
  Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) * Real.cos θ +
    Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) * Real.cos (2 * θ) +
    Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) * Real.cos (3 * θ) +
    Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) * Real.cos (4 * θ) +
    Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) * Real.cos (5 * θ)

private def bohmanTerm11_5 (θ : ℝ) : ℝ :=
  Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) * Real.cos θ +
    Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) * Real.cos (2 * θ) +
    Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) * Real.cos (3 * θ)

private def bohmanTerm11_7 (θ : ℝ) : ℝ :=
  Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) * Real.cos θ +
    Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) * Real.cos (2 * θ)

private def bohmanTerm11_11 (θ : ℝ) : ℝ :=
  Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) * Real.cos θ +
    Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) * Real.cos (2 * θ)

private def bohmanTerm11_13 (θ : ℝ) : ℝ :=
  Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) * Real.cos θ +
    Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) * Real.cos (2 * θ)

def bohmanExcess11_2 (θ : ℝ) : ℝ := bohmanTerm11_2 θ - ((-0.2268572))
def bohmanExcess11_3 (θ : ℝ) : ℝ := bohmanTerm11_3 θ - ((-0.2529915))
def bohmanExcess11_5 (θ : ℝ) : ℝ := bohmanTerm11_5 θ - ((-0.2069302))
def bohmanExcess11_7 (θ : ℝ) : ℝ := bohmanTerm11_7 θ - ((-0.1559556))
def bohmanExcess11_11 (θ : ℝ) : ℝ := bohmanTerm11_11 θ - ((-0.0924176))
def bohmanExcess11_13 (θ : ℝ) : ℝ := bohmanTerm11_13 θ - ((-0.0735473))
def bohmanExcess11_17 (θ : ℝ) : ℝ := Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) * Real.cos θ + 0.0491506
def bohmanExcess11_19 (θ : ℝ) : ℝ := Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) * Real.cos θ + 0.0410445
def bohmanExcess11_23 (θ : ℝ) : ℝ := Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) * Real.cos θ + 0.0295457
def bohmanExcess11_29 (θ : ℝ) : ℝ := Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) * Real.cos θ + 0.0191378
def bohmanExcess11_31 (θ : ℝ) : ℝ := Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) * Real.cos θ + 0.0167571
def bohmanExcess11_37 (θ : ℝ) : ℝ := Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) * Real.cos θ + 0.0115568
def bohmanExcess11_41 (θ : ℝ) : ℝ := Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) * Real.cos θ + 0.0091866
def bohmanExcess11_43 (θ : ℝ) : ℝ := Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) * Real.cos θ + 0.0082272
def bohmanExcess11_47 (θ : ℝ) : ℝ := Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) * Real.cos θ + 0.0066489
def bohmanExcess11_53 (θ : ℝ) : ℝ := Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) * Real.cos θ + 0.0049085
def bohmanExcess11_59 (θ : ℝ) : ℝ := Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) * Real.cos θ + 0.0036799
def bohmanExcess11_61 (θ : ℝ) : ℝ := Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) * Real.cos θ + 0.0033524
def bohmanExcess11_67 (θ : ℝ) : ℝ := Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) * Real.cos θ + 0.0025523
def bohmanExcess11_71 (θ : ℝ) : ℝ := Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) * Real.cos θ + 0.0021387
def bohmanExcess11_73 (θ : ℝ) : ℝ := Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) * Real.cos θ + 0.0019602
def bohmanExcess11_79 (θ : ℝ) : ℝ := Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) * Real.cos θ + 0.0015156
def bohmanExcess11_83 (θ : ℝ) : ℝ := Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) * Real.cos θ + 0.0012805
def bohmanExcess11_89 (θ : ℝ) : ℝ := Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) * Real.cos θ + 0.0009978
def bohmanExcess11_97 (θ : ℝ) : ℝ := Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) * Real.cos θ + 0.0007185
def bohmanExcess11_101 (θ : ℝ) : ℝ := Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) * Real.cos θ + 0.0006104
def bohmanExcess11_103 (θ : ℝ) : ℝ := Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) * Real.cos θ + 0.0005626
def bohmanExcess11_107 (θ : ℝ) : ℝ := Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) * Real.cos θ + 0.0004781
def bohmanExcess11_109 (θ : ℝ) : ℝ := Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) * Real.cos θ + 0.0004407

private theorem monotoneOn_bohman11_2 :
    MonotoneOn (chebPoly7
      (Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2))
      (Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2))
      (Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2))
      (Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2))
      (Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2))
      (Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2))
      (Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2))) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_2_1; obtain ⟨b2l, b2u⟩ := cb11_2_2; obtain ⟨b3l, b3u⟩ := cb11_2_3
  obtain ⟨b4l, b4u⟩ := cb11_2_4; obtain ⟨b5l, b5u⟩ := cb11_2_5; obtain ⟨b6l, b6u⟩ := cb11_2_6
  obtain ⟨b7l, b7u⟩ := cb11_2_7
  refine monotoneOn_chebPoly7_of_sos (G_hi := 0.0004871) (H_hi := 0.0000289)
    (by linarith only [b4l]) (by linarith only [b5l]) (by linarith only [b6l]) b6u
    (by linarith only [b7l]) b7u (by linarith only [b3l, b4u, b5l]) ?_
  set q1 := 4 * (Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2)) -
    (752 / 25) * (Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2))
  set q2 := 12 * (Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2)) -
    (224 / 5) * (Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2)) +
    44 * (Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2))
  set q0 := Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) -
    3 * (Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2)) -
    (32 / 25) * (Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2)) -
    (144 / 5) * (Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2)) -
    36 * 0.0004871 - 14 * 0.0000289
  have hq1_0 : 0 ≤ q1 := by dsimp only [q1]; linarith only [b2l, b4u]
  have hq1_hi : q1 ≤ 0.114861 := by dsimp only [q1]; linarith only [b2u, b4l]
  have hq2_lo : (0.081404 : ℝ) ≤ q2 := by dsimp only [q2]; linarith only [b3l, b4u, b5l]
  have hq0_lo : (0.057382 : ℝ) ≤ q0 := by dsimp only [q0]; linarith only [b1l, b3u, b4u, b5u]
  have hsq := pow_le_pow_left₀ hq1_0 hq1_hi 2
  have hm := mul_le_mul hq2_lo hq0_lo (by norm_num) (by linarith only [hq2_lo])
  norm_num at hsq hm ⊢
  linarith only [hsq, hm]

private theorem monotoneOn_bohman11_3 :
    MonotoneOn (chebPoly7 (Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3)) (Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3)) (Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3)) (Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3)) (Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3)) 0 0) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_3_1; obtain ⟨b2l, b2u⟩ := cb11_3_2; obtain ⟨b3l, b3u⟩ := cb11_3_3; obtain ⟨b4l, b4u⟩ := cb11_3_4; obtain ⟨b5l, b5u⟩ := cb11_3_5
  exact monotoneOn_chebPoly5_of_linear (by linarith only [b2l]) (by linarith only [b3l]) (by linarith only [b4l]) (by linarith only [b5l]) (by linarith only [b1l, b2u, b3u, b4u, b5u])

private theorem monotoneOn_bohman11_5 :
    MonotoneOn (chebPoly7 (Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5)) (Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5)) (Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5)) 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_5_1; obtain ⟨b2l, b2u⟩ := cb11_5_2; obtain ⟨b3l, b3u⟩ := cb11_5_3
  exact monotoneOn_chebPoly5_of_linear (by linarith only [b2l]) (by linarith only [b3l]) le_rfl le_rfl (by linarith only [b1l, b2u, b3u])

private theorem monotoneOn_bohman11_7 :
    MonotoneOn (chebPoly7 (Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7)) (Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7)) 0 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_7_1; obtain ⟨b2l, b2u⟩ := cb11_7_2
  exact monotoneOn_chebPoly5_of_linear (by linarith only [b2l]) le_rfl le_rfl le_rfl (by linarith only [b1l, b2u])

private theorem monotoneOn_bohman11_11 :
    MonotoneOn (chebPoly7 (Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11)) (Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11)) 0 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_11_1; obtain ⟨b2l, b2u⟩ := cb11_11_2
  exact monotoneOn_chebPoly5_of_linear (by linarith only [b2l]) le_rfl le_rfl le_rfl (by linarith only [b1l, b2u])

private theorem monotoneOn_bohman11_13 :
    MonotoneOn (chebPoly7 (Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13)) (Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13)) 0 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨b1l, -⟩ := cb11_13_1; obtain ⟨b2l, b2u⟩ := cb11_13_2
  exact monotoneOn_chebPoly5_of_linear (by linarith only [b2l]) le_rfl le_rfl le_rfl (by linarith only [b1l, b2u])

private theorem bohmanExcess11_2_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.3202637 * max u_lo 0 + 0.3221126 * min u_lo 0) +
      (0.1301484 * max (2 * u_lo ^ 2 - 1) 0 + 0.1303161 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.0457082 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0457198 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) +
      (0.0135108 * max (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0 + 0.0135117 * min (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0) +
      (0.0031416 * max (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0 + 0.0031419 * min (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0) +
      (0.0004868 * max (32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1) 0 + 0.0004871 * min (32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1) 0) +
      (0.0000287 * max (64 * u_lo ^ 7 - 112 * u_lo ^ 5 + 56 * u_lo ^ 3 - 7 * u_lo) 0 + 0.0000289 * min (64 * u_lo ^ 7 - 112 * u_lo ^ 5 + 56 * u_lo ^ 3 - 7 * u_lo) 0) - ((-0.2268572))) :
    g ≤ bohmanExcess11_2 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_2_1; obtain ⟨b2l, b2u⟩ := cb11_2_2; obtain ⟨b3l, b3u⟩ := cb11_2_3; obtain ⟨b4l, b4u⟩ := cb11_2_4; obtain ⟨b5l, b5u⟩ := cb11_2_5; obtain ⟨b6l, b6u⟩ := cb11_2_6; obtain ⟨b7l, b7u⟩ := cb11_2_7
  obtain ⟨c2, c3, c4, c5, c6, c7⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_2 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2)) (Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2)) (Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2)) (Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2)) (Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2)) (Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2)) (Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2)) (Real.cos θ) = bohmanTerm11_2 θ := by
    unfold chebPoly7 bohmanTerm11_2; rw [c2, c3, c4, c5, c6, c7]
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  have w3 := weighted_sign_lb11 b3l b3u (t := (4 * u_lo ^ 3 - 3 * u_lo))
  have w4 := weighted_sign_lb11 b4l b4u (t := (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1))
  have w5 := weighted_sign_lb11 b5l b5u (t := (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo))
  have w6 := weighted_sign_lb11 b6l b6u (t := (32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1))
  have w7 := weighted_sign_lb11 b7l b7u (t := (64 * u_lo ^ 7 - 112 * u_lo ^ 5 + 56 * u_lo ^ 3 - 7 * u_lo))
  unfold bohmanExcess11_2
  linarith only [hg, w1, w2, w3, w4, w5, w6, w7, hmono]

private theorem bohmanExcess11_3_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.3049577 * max u_lo 0 + 0.3057004 * min u_lo 0) +
      (0.0596865 * max (2 * u_lo ^ 2 - 1) 0 + 0.0596979 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.0073251 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0073255 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) +
      (0.0003481 * max (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0 + 0.0003483 * min (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0) +
      (0 * max (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0 + 0.0000002 * min (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0) - ((-0.2529915))) :
    g ≤ bohmanExcess11_3 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_3_1; obtain ⟨b2l, b2u⟩ := cb11_3_2; obtain ⟨b3l, b3u⟩ := cb11_3_3; obtain ⟨b4l, b4u⟩ := cb11_3_4; obtain ⟨b5l, b5u⟩ := cb11_3_5
  obtain ⟨c2, c3, c4, c5, -, -⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_3 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3)) (Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3)) (Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3)) (Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3)) (Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3)) 0 0 (Real.cos θ) = bohmanTerm11_3 θ := by
    unfold chebPoly7 bohmanTerm11_3; rw [c2, c3, c4, c5]; ring
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  have w3 := weighted_sign_lb11 b3l b3u (t := (4 * u_lo ^ 3 - 3 * u_lo))
  have w4 := weighted_sign_lb11 b4l b4u (t := (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1))
  have w5 := weighted_sign_lb11 b5l b5u (t := (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo))
  unfold bohmanExcess11_3
  linarith only [hg, w1, w2, w3, w4, w5, hmono]

private theorem bohmanExcess11_5_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.2193798 * max u_lo 0 + 0.2195494 * min u_lo 0) +
      (0.0126954 * max (2 * u_lo ^ 2 - 1) 0 + 0.0126959 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.000076 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0000762 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) - ((-0.2069302))) :
    g ≤ bohmanExcess11_5 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_5_1; obtain ⟨b2l, b2u⟩ := cb11_5_2; obtain ⟨b3l, b3u⟩ := cb11_5_3
  obtain ⟨c2, c3, -, -, -, -⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_5 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5)) (Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5)) (Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5)) 0 0 0 0 (Real.cos θ) = bohmanTerm11_5 θ := by
    unfold chebPoly7 bohmanTerm11_5; rw [c2, c3]; ring
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  have w3 := weighted_sign_lb11 b3l b3u (t := (4 * u_lo ^ 3 - 3 * u_lo))
  unfold bohmanExcess11_5
  linarith only [hg, w1, w2, w3, hmono]

private theorem bohmanExcess11_7_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.1588986 * max u_lo 0 + 0.1589541 * min u_lo 0) +
      (0.0029985 * max (2 * u_lo ^ 2 - 1) 0 + 0.0029989 * min (2 * u_lo ^ 2 - 1) 0) - ((-0.1559556))) :
    g ≤ bohmanExcess11_7 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_7_1; obtain ⟨b2l, b2u⟩ := cb11_7_2
  obtain ⟨c2, -, -, -, -, -⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_7 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7)) (Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7)) 0 0 0 0 0 (Real.cos θ) = bohmanTerm11_7 θ := by
    unfold chebPoly7 bohmanTerm11_7; rw [c2]; ring
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  unfold bohmanExcess11_7
  linarith only [hg, w1, w2, hmono]

private theorem bohmanExcess11_11_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.0925414 * max u_lo 0 + 0.0925522 * min u_lo 0) +
      (0.0001346 * max (2 * u_lo ^ 2 - 1) 0 + 0.0001348 * min (2 * u_lo ^ 2 - 1) 0) - ((-0.0924176))) :
    g ≤ bohmanExcess11_11 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_11_1; obtain ⟨b2l, b2u⟩ := cb11_11_2
  obtain ⟨c2, -, -, -, -, -⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_11 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11)) (Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11)) 0 0 0 0 0 (Real.cos θ) = bohmanTerm11_11 θ := by
    unfold chebPoly7 bohmanTerm11_11; rw [c2]; ring
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  unfold bohmanExcess11_11
  linarith only [hg, w1, w2, hmono]

private theorem bohmanExcess11_13_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.0735564 * max u_lo 0 + 0.0735624 * min u_lo 0) +
      (0.0000151 * max (2 * u_lo ^ 2 - 1) 0 + 0.0000153 * min (2 * u_lo ^ 2 - 1) 0) - ((-0.0735473))) :
    g ≤ bohmanExcess11_13 θ := by
  obtain ⟨b1l, b1u⟩ := cb11_13_1; obtain ⟨b2l, b2u⟩ := cb11_13_2
  obtain ⟨c2, -, -, -, -, -⟩ := cos_chebyshev_seven θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman11_13 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly7 (Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13)) (Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13)) 0 0 0 0 0 (Real.cos θ) = bohmanTerm11_13 θ := by
    unfold chebPoly7 bohmanTerm11_13; rw [c2]; ring
  rw [hterm] at hmono
  unfold chebPoly7 at hmono
  have w1 := weighted_sign_lb11 b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb11 b2l b2u (t := (2 * u_lo ^ 2 - 1))
  unfold bohmanExcess11_13
  linarith only [hg, w1, w2, hmono]

private theorem linear_excess_ge11 {c c_lo c_hi u_lo g θ : ℝ}
    (hclo0 : 0 ≤ c_lo) (hlo : c_lo ≤ c) (hhi : c ≤ c_hi)
    (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ) (hg : g ≤ c_lo * (1 + u_lo)) :
    g ≤ c * Real.cos θ + c_hi := by
  have h1 : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have h2 : c_lo * (1 + Real.cos θ) ≤ c * Real.cos θ + c_hi := by
    have : c * Real.cos θ + c_hi - c_lo * (1 + Real.cos θ) =
        (c - c_lo) * (1 + Real.cos θ) + (c_hi - c) := by ring
    nlinarith only [this, hlo, hhi, h1]
  have h3 : c_lo * (1 + u_lo) ≤ c_lo * (1 + Real.cos θ) :=
    mul_le_mul_of_nonneg_left (by linarith only [hu]) hclo0
  exact hg.trans (h3.trans h2)

private theorem neg_ub_le_mul_cos11 {c ub θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ ub) :
    -ub ≤ c * Real.cos θ := by
  have := Real.neg_one_le_cos θ; nlinarith only [this, hc0, hc]

private theorem bohmanExcess11_17_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0491482 * (1 + u_lo)) : g ≤ bohmanExcess11_17 θ := by
  obtain ⟨bl, bu⟩ := cb11_17_1
  unfold bohmanExcess11_17
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_19_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0410428 * (1 + u_lo)) : g ≤ bohmanExcess11_19 θ := by
  obtain ⟨bl, bu⟩ := cb11_19_1
  unfold bohmanExcess11_19
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_23_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0295446 * (1 + u_lo)) : g ≤ bohmanExcess11_23 θ := by
  obtain ⟨bl, bu⟩ := cb11_23_1
  unfold bohmanExcess11_23
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_29_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0191371 * (1 + u_lo)) : g ≤ bohmanExcess11_29 θ := by
  obtain ⟨bl, bu⟩ := cb11_29_1
  unfold bohmanExcess11_29
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_31_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0167565 * (1 + u_lo)) : g ≤ bohmanExcess11_31 θ := by
  obtain ⟨bl, bu⟩ := cb11_31_1
  unfold bohmanExcess11_31
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_37_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0115563 * (1 + u_lo)) : g ≤ bohmanExcess11_37 θ := by
  obtain ⟨bl, bu⟩ := cb11_37_1
  unfold bohmanExcess11_37
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_41_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0091861 * (1 + u_lo)) : g ≤ bohmanExcess11_41 θ := by
  obtain ⟨bl, bu⟩ := cb11_41_1
  unfold bohmanExcess11_41
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_43_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0082266 * (1 + u_lo)) : g ≤ bohmanExcess11_43 θ := by
  obtain ⟨bl, bu⟩ := cb11_43_1
  unfold bohmanExcess11_43
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_47_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0066485 * (1 + u_lo)) : g ≤ bohmanExcess11_47 θ := by
  obtain ⟨bl, bu⟩ := cb11_47_1
  unfold bohmanExcess11_47
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_53_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0049082 * (1 + u_lo)) : g ≤ bohmanExcess11_53 θ := by
  obtain ⟨bl, bu⟩ := cb11_53_1
  unfold bohmanExcess11_53
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_59_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0036795 * (1 + u_lo)) : g ≤ bohmanExcess11_59 θ := by
  obtain ⟨bl, bu⟩ := cb11_59_1
  unfold bohmanExcess11_59
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_61_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.003352 * (1 + u_lo)) : g ≤ bohmanExcess11_61 θ := by
  obtain ⟨bl, bu⟩ := cb11_61_1
  unfold bohmanExcess11_61
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_67_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.002552 * (1 + u_lo)) : g ≤ bohmanExcess11_67 θ := by
  obtain ⟨bl, bu⟩ := cb11_67_1
  unfold bohmanExcess11_67
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_71_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0021384 * (1 + u_lo)) : g ≤ bohmanExcess11_71 θ := by
  obtain ⟨bl, bu⟩ := cb11_71_1
  unfold bohmanExcess11_71
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_73_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0019599 * (1 + u_lo)) : g ≤ bohmanExcess11_73 θ := by
  obtain ⟨bl, bu⟩ := cb11_73_1
  unfold bohmanExcess11_73
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_79_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0015153 * (1 + u_lo)) : g ≤ bohmanExcess11_79 θ := by
  obtain ⟨bl, bu⟩ := cb11_79_1
  unfold bohmanExcess11_79
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_83_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0012803 * (1 + u_lo)) : g ≤ bohmanExcess11_83 θ := by
  obtain ⟨bl, bu⟩ := cb11_83_1
  unfold bohmanExcess11_83
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_89_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0009975 * (1 + u_lo)) : g ≤ bohmanExcess11_89 θ := by
  obtain ⟨bl, bu⟩ := cb11_89_1
  unfold bohmanExcess11_89
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_97_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0007183 * (1 + u_lo)) : g ≤ bohmanExcess11_97 θ := by
  obtain ⟨bl, bu⟩ := cb11_97_1
  unfold bohmanExcess11_97
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_101_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0006101 * (1 + u_lo)) : g ≤ bohmanExcess11_101 θ := by
  obtain ⟨bl, bu⟩ := cb11_101_1
  unfold bohmanExcess11_101
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_103_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0005624 * (1 + u_lo)) : g ≤ bohmanExcess11_103 θ := by
  obtain ⟨bl, bu⟩ := cb11_103_1
  unfold bohmanExcess11_103
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_107_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0004778 * (1 + u_lo)) : g ≤ bohmanExcess11_107 θ := by
  obtain ⟨bl, bu⟩ := cb11_107_1
  unfold bohmanExcess11_107
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg
private theorem bohmanExcess11_109_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0004404 * (1 + u_lo)) : g ≤ bohmanExcess11_109 θ := by
  obtain ⟨bl, bu⟩ := cb11_109_1
  unfold bohmanExcess11_109
  exact linear_excess_ge11 (by norm_num) bl bu hu0 hu hg

theorem bohmanPhaseForm11_ge_sum_excess (θ : ℕ → ℝ) :
    (-1.226548) + (bohmanExcess11_2 (θ 2) + bohmanExcess11_3 (θ 3) + bohmanExcess11_5 (θ 5) + bohmanExcess11_7 (θ 7) + bohmanExcess11_11 (θ 11) + bohmanExcess11_13 (θ 13) + bohmanExcess11_17 (θ 17) + bohmanExcess11_19 (θ 19) + bohmanExcess11_23 (θ 23) + bohmanExcess11_29 (θ 29) + bohmanExcess11_31 (θ 31) + bohmanExcess11_37 (θ 37) + bohmanExcess11_41 (θ 41) + bohmanExcess11_43 (θ 43) + bohmanExcess11_47 (θ 47) + bohmanExcess11_53 (θ 53) + bohmanExcess11_59 (θ 59) + bohmanExcess11_61 (θ 61) + bohmanExcess11_67 (θ 67) + bohmanExcess11_71 (θ 71) + bohmanExcess11_73 (θ 73) + bohmanExcess11_79 (θ 79) + bohmanExcess11_83 (θ 83) + bohmanExcess11_89 (θ 89) + bohmanExcess11_97 (θ 97) + bohmanExcess11_101 (θ 101) + bohmanExcess11_103 (θ 103) + bohmanExcess11_107 (θ 107) + bohmanExcess11_109 (θ 109)) ≤ bohmanPhaseForm11 θ := by
  have s113 := neg_ub_le_mul_cos11 (θ := θ 113) (by linarith only [cb11_113_1.1]) cb11_113_1.2
  have s127 := neg_ub_le_mul_cos11 (θ := θ 127) (by linarith only [cb11_127_1.1]) cb11_127_1.2
  have s131 := neg_ub_le_mul_cos11 (θ := θ 131) (by linarith only [cb11_131_1.1]) cb11_131_1.2
  have s137 := neg_ub_le_mul_cos11 (θ := θ 137) (by linarith only [cb11_137_1.1]) cb11_137_1.2
  have s139 := neg_ub_le_mul_cos11 (θ := θ 139) (by linarith only [cb11_139_1.1]) cb11_139_1.2
  have s149 := neg_ub_le_mul_cos11 (θ := θ 149) (by linarith only [cb11_149_1.1]) cb11_149_1.2
  have s151 := neg_ub_le_mul_cos11 (θ := θ 151) (by linarith only [cb11_151_1.1]) cb11_151_1.2
  have s157 := neg_ub_le_mul_cos11 (θ := θ 157) (by linarith only [cb11_157_1.1]) cb11_157_1.2
  have s163 := neg_ub_le_mul_cos11 (θ := θ 163) (by linarith only [cb11_163_1.1]) cb11_163_1.2
  have s167 := neg_ub_le_mul_cos11 (θ := θ 167) (by linarith only [cb11_167_1.1]) cb11_167_1.2
  have s173 := neg_ub_le_mul_cos11 (θ := θ 173) (by linarith only [cb11_173_1.1]) cb11_173_1.2
  have s179 := neg_ub_le_mul_cos11 (θ := θ 179) (by linarith only [cb11_179_1.1]) cb11_179_1.2
  have s181 := neg_ub_le_mul_cos11 (θ := θ 181) (by linarith only [cb11_181_1.1]) cb11_181_1.2
  have s191 := neg_ub_le_mul_cos11 (θ := θ 191) (by linarith only [cb11_191_1.1]) cb11_191_1.2
  have s193 := neg_ub_le_mul_cos11 (θ := θ 193) (by linarith only [cb11_193_1.1]) cb11_193_1.2
  have s197 := neg_ub_le_mul_cos11 (θ := θ 197) (by linarith only [cb11_197_1.1]) cb11_197_1.2
  have s199 := neg_ub_le_mul_cos11 (θ := θ 199) (by linarith only [cb11_199_1.1]) cb11_199_1.2
  have s211 := neg_ub_le_mul_cos11 (θ := θ 211) (by linarith only [cb11_211_1.1]) cb11_211_1.2
  have s223 := neg_ub_le_mul_cos11 (θ := θ 223) (by linarith only [cb11_223_1.1]) cb11_223_1.2
  have s227 := neg_ub_le_mul_cos11 (θ := θ 227) (by linarith only [cb11_227_1.1]) cb11_227_1.2
  have s229 := neg_ub_le_mul_cos11 (θ := θ 229) (by linarith only [cb11_229_1.1]) cb11_229_1.2
  have s233 := neg_ub_le_mul_cos11 (θ := θ 233) (by linarith only [cb11_233_1.1]) cb11_233_1.2
  have s239 := neg_ub_le_mul_cos11 (θ := θ 239) (by linarith only [cb11_239_1.1]) cb11_239_1.2
  have s241 := neg_ub_le_mul_cos11 (θ := θ 241) (by linarith only [cb11_241_1.1]) cb11_241_1.2
  have hpas1 : (-0.0013515) ≤ Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) * Real.cos (θ 113) + Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) * Real.cos (θ 127) + Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) * Real.cos (θ 131) + Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) * Real.cos (θ 137) + Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) * Real.cos (θ 139) + Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) * Real.cos (θ 149) + Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) * Real.cos (θ 151) + Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) * Real.cos (θ 157) + Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) * Real.cos (θ 163) + Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) * Real.cos (θ 167) + Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) * Real.cos (θ 173) + Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) * Real.cos (θ 179) := by linarith only [s113, s127, s131, s137, s139, s149, s151, s157, s163, s167, s173, s179]
  have hpas2 : (-0.0000452) ≤ Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) * Real.cos (θ 181) + Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) * Real.cos (θ 191) + Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) * Real.cos (θ 193) + Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) * Real.cos (θ 197) + Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) * Real.cos (θ 199) + Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) * Real.cos (θ 211) + Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) * Real.cos (θ 223) + Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) * Real.cos (θ 227) + Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) * Real.cos (θ 229) + Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) * Real.cos (θ 233) + Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) * Real.cos (θ 239) + Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) * Real.cos (θ 241) := by linarith only [s181, s191, s193, s197, s199, s211, s223, s227, s229, s233, s239, s241]
  unfold bohmanPhaseForm11 bohmanExcess11_2 bohmanExcess11_3 bohmanExcess11_5 bohmanExcess11_7 bohmanExcess11_11 bohmanExcess11_13 bohmanExcess11_17 bohmanExcess11_19 bohmanExcess11_23 bohmanExcess11_29 bohmanExcess11_31 bohmanExcess11_37 bohmanExcess11_41 bohmanExcess11_43 bohmanExcess11_47 bohmanExcess11_53 bohmanExcess11_59 bohmanExcess11_61 bohmanExcess11_67 bohmanExcess11_71 bohmanExcess11_73 bohmanExcess11_79 bohmanExcess11_83 bohmanExcess11_89 bohmanExcess11_97 bohmanExcess11_101 bohmanExcess11_103 bohmanExcess11_107 bohmanExcess11_109 bohmanTerm11_2 bohmanTerm11_3 bohmanTerm11_5 bohmanTerm11_7 bohmanTerm11_11 bohmanTerm11_13
  linarith only [hpas1, hpas2]

private theorem bohmanPhaseForm11_coupled_ge_sum_excess (γ : ℝ) :
    (-1.226548) + (bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109)) ≤
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) := by
  simpa only [Nat.cast_ofNat] using bohmanPhaseForm11_ge_sum_excess (fun p => γ * Real.log (p : ℝ))

private theorem bohmanExcess11_2_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) :=
  bohmanExcess11_2_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_3_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) :=
  bohmanExcess11_3_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_5_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) :=
  bohmanExcess11_5_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_7_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) :=
  bohmanExcess11_7_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_11_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_11 (γ * Real.log 11) :=
  bohmanExcess11_11_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_13_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_13 (γ * Real.log 13) :=
  bohmanExcess11_13_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_17_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_17 (γ * Real.log 17) :=
  bohmanExcess11_17_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_19_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_19 (γ * Real.log 19) :=
  bohmanExcess11_19_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_23_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_23 (γ * Real.log 23) :=
  bohmanExcess11_23_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_29_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_29 (γ * Real.log 29) :=
  bohmanExcess11_29_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_31_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_31 (γ * Real.log 31) :=
  bohmanExcess11_31_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_37_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_37 (γ * Real.log 37) :=
  bohmanExcess11_37_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_41_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_41 (γ * Real.log 41) :=
  bohmanExcess11_41_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_43_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_43 (γ * Real.log 43) :=
  bohmanExcess11_43_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_47_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_47 (γ * Real.log 47) :=
  bohmanExcess11_47_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_53_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_53 (γ * Real.log 53) :=
  bohmanExcess11_53_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_59_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_59 (γ * Real.log 59) :=
  bohmanExcess11_59_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_61_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_61 (γ * Real.log 61) :=
  bohmanExcess11_61_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_67_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_67 (γ * Real.log 67) :=
  bohmanExcess11_67_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_71_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_71 (γ * Real.log 71) :=
  bohmanExcess11_71_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_73_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_73 (γ * Real.log 73) :=
  bohmanExcess11_73_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_79_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_79 (γ * Real.log 79) :=
  bohmanExcess11_79_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_83_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_83 (γ * Real.log 83) :=
  bohmanExcess11_83_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_89_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_89 (γ * Real.log 89) :=
  bohmanExcess11_89_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_97_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_97 (γ * Real.log 97) :=
  bohmanExcess11_97_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_101_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_101 (γ * Real.log 101) :=
  bohmanExcess11_101_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_103_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_103 (γ * Real.log 103) :=
  bohmanExcess11_103_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_107_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_107 (γ * Real.log 107) :=
  bohmanExcess11_107_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
private theorem bohmanExcess11_109_nonneg (γ : ℝ) : 0 ≤ bohmanExcess11_109 (γ * Real.log 109) :=
  bohmanExcess11_109_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)

private theorem exp_eleven_bounds : (244 : ℝ) ^ 2 ≤ Real.exp 11 ∧ Real.exp 11 ≤ (245 : ℝ) ^ 2 := by
  have he11 : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he11]
  exact ⟨(by norm_num : (244 : ℝ) ^ 2 ≤ 2.7182818283 ^ 11).trans
      (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 11),
    (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11).trans (by norm_num)⟩

private theorem eleven_halves_le_log {n : ℕ} (hn : 245 ≤ n) : (11 / 2 : ℝ) ≤ Real.log n := by
  have hn' : (245 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  rw [Real.le_log_iff_exp_le hn0]
  have hsq : Real.exp (11 / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (11 / 2) = 11 by norm_num]
    exact exp_eleven_bounds.2.trans (pow_le_pow_left₀ (by norm_num) hn' 2)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hn0.le (by norm_num : 2 ≠ 0)).mp hsq

private theorem exp_neg_eleven_quarters_bounds :
    (0.063927 : ℝ) ≤ Real.exp (-(11 / 2 / 2)) ∧
      Real.exp (-(11 / 2 / 2)) ≤ 0.063928 := by
  have he11 : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  have he11_lo : (2.7182818283 : ℝ) ^ 11 ≤ Real.exp 11 := by
    rw [he11]; exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 11
  have he11_hi : Real.exp 11 ≤ (2.7182818286 : ℝ) ^ 11 := by
    rw [he11]; exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 11
  have he4 : Real.exp (-(11 / 2 / 2)) ^ 4 = (Real.exp 11)⁻¹ := by
    rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * -(11 / 2 / 2) = -11 by norm_num, Real.exp_neg]
  have hlo4 : (0.063927 : ℝ) ^ 4 ≤ Real.exp (-(11 / 2 / 2)) ^ 4 := by
    rw [he4, le_inv_comm₀ (by norm_num) (Real.exp_pos 11)]
    exact he11_hi.trans (by norm_num)
  have hhi4 : Real.exp (-(11 / 2 / 2)) ^ 4 ≤ (0.063928 : ℝ) ^ 4 := by
    rw [he4, inv_le_comm₀ (Real.exp_pos 11) (by norm_num)]
    exact (by norm_num : (0.063928 ^ 4 : ℝ)⁻¹ ≤ 2.7182818283 ^ 11).trans he11_lo
  exact ⟨(pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 4 ≠ 0)).mp hlo4,
    (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 4 ≠ 0)).mp hhi4⟩

private theorem le_log_of_two_pow_le11 {p : ℝ} {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']; linarith only [hl]

private theorem log_le_of_pow_le_two_pow11 {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']; linarith only [hl]

private theorem log_pi_lb_sharp11 : (1.144498 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 :=
    (by norm_num : (2 : ℝ) ^ 71 ≤ 3.14159265 ^ 43).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [pi_bounds_d10_11.1]) 43)
  have h := le_log_of_two_pow_le11 (p := Real.pi) (k := 43) (m := 71) (by norm_num) hpow
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢; linarith only [h, hl2]

private theorem bohman11_budget_left_bounds :
    (2.495515 : ℝ) ≤ 4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) /
          ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ∧
      4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) /
          ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤ 2.495517 := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10_11
  obtain ⟨he_lo, he_hi⟩ := exp_neg_eleven_quarters_bounds
  have hπ2_lo : 3.1415926535 ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hπ_lo.le 2
  have hπ2_hi : Real.pi ^ 2 ≤ 3.1415926536 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hπ_hi.le 2
  have hden_lo : (11 / 2 : ℝ) ^ 2 + 4 * 3.1415926535 ^ 2 ≤ (11 / 2) ^ 2 + 4 * Real.pi ^ 2 := by
    linarith only [hπ2_lo]
  have hden_hi : (11 / 2 : ℝ) ^ 2 + 4 * Real.pi ^ 2 ≤ (11 / 2) ^ 2 + 4 * 3.1415926536 ^ 2 := by
    linarith only [hπ2_hi]
  have ht1_lo : 4 * (11 / 2 : ℝ) ^ 2 / ((11 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) ≤
      4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_hi
  have ht1_hi : 4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ≤
      4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * 3.1415926535 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden_lo
  have hnum_lo : 64 * 3.1415926535 ^ 2 * (11 / 2) * (1 + 0.063927) ≤
      64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) :=
    mul_le_mul (by linarith only [hπ2_lo]) (by linarith only [he_lo]) (by norm_num) (by positivity)
  have hnum_hi : 64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) ≤
      64 * 3.1415926536 ^ 2 * (11 / 2) * (1 + 0.063928) :=
    mul_le_mul (by linarith only [hπ2_hi]) (by linarith only [he_hi]) (by positivity) (by norm_num)
  have ht2_lo : 64 * 3.1415926535 ^ 2 * (11 / 2) * (1 + 0.063927) /
        ((11 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) ^ 2 ≤
      64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) /
        ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) hden_hi 2)).trans
      (div_le_div_of_nonneg_right hnum_lo (by positivity))
  have ht2_hi : 64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) /
        ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤
      64 * 3.1415926536 ^ 2 * (11 / 2) * (1 + 0.063928) /
        ((11 / 2) ^ 2 + 4 * 3.1415926535 ^ 2) ^ 2 :=
    (div_le_div_of_nonneg_right hnum_hi (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) hden_lo 2))
  exact ⟨(by norm_num : (2.495515 : ℝ) ≤ _).trans (add_le_add ht1_lo ht2_lo),
    (add_le_add ht1_hi ht2_hi).trans (by norm_num)⟩

private theorem bohman11_arch_lt_smooth {γ g_lo g_hi M logM4_hi ub : ℝ} {a2 b c d : ℕ}
    (hg0 : 0 < g_lo) (hlo : g_lo ≤ γ) (hhi : γ ≤ g_hi) (hM : 0 < M)
    (hM_eq : M / 4 = (2 : ℝ) ^ a2 * (3 : ℝ) ^ b * (5 : ℝ) ^ c * (7 : ℝ) ^ d)
    (hlogM : (a2 : ℝ) * 0.6931471808 + (b : ℝ) * 1.0986129 +
      (c : ℝ) * 1.609438 + (d : ℝ) * 1.9459107 ≤ logM4_hi)
    (hub : 1 / 4 * (logM4_hi + (9 + g_hi ^ 2 - M) / M) - 1.144498 / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * g_lo ^ 2) + 1200 / ((11 / 2) ^ 3 * g_lo ^ 4) < ub) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) < ub := by
  have hl2b := Real.log_two_lt_d9.le
  have hl3b := sharp_log_prime_3.2
  have hl5b := sharp_log_prime_5.2
  have hl7b := sharp_log_prime_7.2
  have hlogM4 : Real.log (M / 4) ≤ logM4_hi := by
    rw [hM_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    have m2 := mul_le_mul_of_nonneg_left hl2b (Nat.cast_nonneg a2)
    have m3 := mul_le_mul_of_nonneg_left hl3b (Nat.cast_nonneg b)
    have m5 := mul_le_mul_of_nonneg_left hl5b (Nat.cast_nonneg c)
    have m7 := mul_le_mul_of_nonneg_left hl7b (Nat.cast_nonneg d)
    linarith only [m2, m3, m5, m7, hlogM]
  have hγ_le : 9 / 4 + γ ^ 2 / 4 ≤ (9 + g_hi ^ 2) / 4 := by
    have := pow_le_pow_left₀ (hg0.le.trans hlo) hhi 2; linarith
  have hsplit : (9 + g_hi ^ 2) / 4 = (M / 4) * ((9 + g_hi ^ 2) / M) := by field_simp [hM.ne']
  have hpos_ghi : 0 < 9 + g_hi ^ 2 := by positivity
  have hlog_tot : Real.log (9 / 4 + γ ^ 2 / 4) ≤ logM4_hi + (9 + g_hi ^ 2 - M) / M := by
    calc Real.log (9 / 4 + γ ^ 2 / 4)
        ≤ Real.log ((9 + g_hi ^ 2) / 4) := Real.log_le_log (by positivity) hγ_le
      _ = Real.log (M / 4) + Real.log ((9 + g_hi ^ 2) / M) := by
          rw [hsplit, Real.log_mul (by positivity) (by positivity)]
      _ ≤ logM4_hi + ((9 + g_hi ^ 2) / M - 1) :=
          add_le_add hlogM4 (Real.log_le_sub_one_of_pos (div_pos hpos_ghi hM))
      _ = logM4_hi + (9 + g_hi ^ 2 - M) / M := by field_simp [hM.ne']
  have hπ := log_pi_lb_sharp11
  have ht1 : 18 / ((11 / 2 : ℝ) ^ 2 * γ ^ 2) ≤ 18 / ((11 / 2) ^ 2 * g_lo ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0.le hlo 2) (by norm_num))
  have ht2 : 1200 / ((11 / 2 : ℝ) ^ 3 * γ ^ 4) ≤ 1200 / ((11 / 2) ^ 3 * g_lo ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0.le hlo 4) (by norm_num))
  linarith only [hlog_tot, hπ, ht1, ht2, hub]

/-! ## 41-interval coupled prime-phase exclusion across `(150, 184]` -/

private theorem bohman11_interval_0 {γ : ℝ} (hlo : 150 ≤ γ) (hhi : γ ≤ 150.328125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 150) (g_hi := 150.328125) (M := 22680) (logM4_hi := 8.6429475) (ub := 1.58854) (a2 := 1) (b := 4) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.2172) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.7897) 26 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13722 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.2172)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.6098 ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 0.9149) 75 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04756 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := 0.6098) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6883) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.3298) 57 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0287 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.6883)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.5371 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.0038) 82 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02575 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := 0.5371) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.6738) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.31) 61 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02397 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.6738)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.6474) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.2748) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01732 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.6474)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.7433 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.7327) 92 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01159 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.7433) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.2605 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.3072) 90 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01036 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := 0.2605) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.2101 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 1.3591) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00593 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.2101) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.5626) ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 2.1682) 89 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00401 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := (-0.5626)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.9561) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.8422) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00265 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.9561)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.7823) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.4689) 86 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00251 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.7823)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.0875 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 150) (g_hi := 150.328125) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 1.4831) 102 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00232 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.0875) (by norm_num) hu_12 (by norm_num)
  have hgain_tot : 0.31989 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_71 (γ * Real.log 71) := (by norm_num : (0.31989 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_1 {γ : ℝ} (hlo : 150.328125 ≤ γ) (hhi : γ ≤ 150.484375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 150.328125) (g_hi := 150.484375) (M := 22680) (logM4_hi := 8.6429475) (ub := 1.589058) (a2 := 1) (b := 4) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.3808) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.9614) 26 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10094 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.3808)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.2236 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.3452) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06013 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := 0.2236) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.8229 ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 0.6042) 75 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.05385 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := 0.8229) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.0303 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.5404) 82 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01726 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := 0.0303) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.87 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 0.5155) 90 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01538 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := 0.87) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.5819 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.9497) 89 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01453 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.5819) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9376) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.7852) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00919 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9376)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.8447 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.5647) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00905 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.8447) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9063) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.7044) 57 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00862 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.9063)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.8647) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.6148) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00856 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.8647)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.2342 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.3343) 92 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0082 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.2342) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.909) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.7107) 61 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00668 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.909)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.8352 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.5822) 102 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00392 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.8352) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.9204) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 2.7389) 81 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00152 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.9204)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.1705) ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 1.7421) 106 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00106 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := (-0.1705)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.7622 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.704) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00099 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.7622) (by norm_num) hu_15 (by norm_num)
  have hu_16 : (-0.5818) ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 150.328125) (g_hi := 150.484375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 2.1916) 103 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00081 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := (-0.5818)) (by norm_num) hu_16 (by norm_num)
  have hgain_tot : 0.32069 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_73 (γ * Real.log 73) := (by norm_num : (0.32069 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_2 {γ : ℝ} (hlo : 150.484375 ≤ γ) (hhi : γ ≤ 150.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 150.484375) (g_hi := 150.625) (M := 22680) (logM4_hi := 8.6429475) (ub := 1.589525) (a2 := 1) (b := 4) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_11_nonneg γ) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.6196 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 0.9025) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.0796 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := 0.6196) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5186) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.1159) 26 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.07397 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.5186)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.5017 ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.0452) 75 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04436 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := 0.5017) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7898) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.4811) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03115 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.7898)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9325 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.3694) 89 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01775 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.9325) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8052) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5065) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0127 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.8052)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.5024 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.0444) 90 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01235 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := 0.5024) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.4373) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.0233) 82 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00942 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.4373)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.5989) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 2.2128) 81 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00767 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.5989)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9581) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.8491) 39 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00714 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9581)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.4329 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 1.123) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00703 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.4329) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.3003) ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.8757) 92 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00465 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := (-0.3003)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.3794 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 1.1816) 102 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00294 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.3794) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.0495 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.5212) 103 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00205 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.0495) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.496 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 1.0517) 106 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00191 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.496) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.2869) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 1.8617) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00181 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.2869)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : (-0.5447) ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 2.1467) 98 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00167 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := (-0.5447)) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.782 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.6728) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.001 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.782) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.8631 ≤ Real.cos (γ * Real.log 107) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 107) (lp_lo := 4.6728282) (lp_hi := 4.6728307) (x_hi := 0.5293) 112 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_107.1 sharp_log_prime_107.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00089 ≤ bohmanExcess11_107 (γ * Real.log 107) := bohmanExcess11_107_ge (u_lo := 0.8631) (by norm_num) hu_18 (by norm_num)
  have hu_19 : (-0.5894) ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 150.484375) (g_hi := 150.625) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 2.201) 105 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.00062 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := (-0.5894)) (by norm_num) hu_19 (by norm_num)
  have hgain_tot : 0.32068 ≤ bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_79 (γ * Real.log 79) := (by norm_num : (0.32068 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_3 {γ : ℝ} (hlo : 150.625 ≤ γ) (hhi : γ ≤ 150.84375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 150.625) (g_hi := 150.84375) (M := 22680) (logM4_hi := 8.6429475) (ub := 1.590252) (a2 := 1) (b := 4) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_11_nonneg γ) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.8756 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 0.5041) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09218 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := 0.8756) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5946) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.2075) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06056 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.5946)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7072) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3562) 26 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04164 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.7072)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.1597) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.7311) 75 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02482 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.1597)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8687) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.6228) 39 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02267 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.8687)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.7436) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.409) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01725 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.7436)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.1678) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.7393) 81 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01592 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.1678)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.5685 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.966) 89 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.0144 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.5685) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.8572) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.6002) 71 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00586 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8572)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.2921) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.8672) 90 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00582 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.2921)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.0026) ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 1.5733) 98 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00366 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := (-0.0026)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.2958 ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 1.2704) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.0033 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := 0.2958) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.6075 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 0.9178) 103 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00315 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.6075) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.4086) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 1.9916) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.0029 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.4086)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.8591 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 0.5372) 106 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00238 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.8591) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.0158) ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.5865) 105 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00149 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := (-0.0158)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : (-0.9338) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.7745) 82 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.0011 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.9338)) (by norm_num) hu_16 (by norm_num)
  have hu_17 : (-0.517) ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 2.1141) 102 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00103 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := (-0.517)) (by norm_num) hu_17 (by norm_num)
  have hu_18 : (-0.9219) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.7428) 87 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.0009 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.9219)) (by norm_num) hu_18 (by norm_num)
  have hu_19 : 0.4078 ≤ Real.cos (γ * Real.log 107) := cos_mul_ge_of_even_shift11 (g_lo := 150.625) (g_hi := 150.84375) (lp := Real.log 107) (lp_lo := 4.6728282) (lp_hi := 4.6728307) (x_hi := 1.1507) 112 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_107.1 sharp_log_prime_107.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.00067 ≤ bohmanExcess11_107 (γ * Real.log 107) := bohmanExcess11_107_ge (u_lo := 0.4078) (by norm_num) hu_19 (by norm_num)
  have hgain_tot : 0.3217 ≤ bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_107 (γ * Real.log 107) := (by norm_num : (0.3217 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_4 {γ : ℝ} (hlo : 150.84375 ≤ γ) (hhi : γ ≤ 151.484375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 150.84375) (g_hi := 151.484375) (M := 23040) (logM4_hi := 8.6586941) (ub := 1.592369) (a2 := 7) (b := 2) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.2095) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.7818) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11991 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.2095)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6442) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.2707) 39 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0634 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.6442)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3528) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.9313) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0318 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.3528)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.4039 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.155) 81 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02686 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.4039) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.634) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.2574) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0261 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.634)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.3759) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 1.9561) 71 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02561 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.3759)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8824) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.6512) 62 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00864 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.8824)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9117) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.7174) 58 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00812 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.9117)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.3729) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.9529) 87 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00724 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.3729)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.3528) ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 1.9313) 98 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00238 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := (-0.3528)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.3571) ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.9359) 99 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00215 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := (-0.3571)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.0692 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 1.5015) 108 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00106 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.0692) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.6984) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 150.84375) (g_hi := 151.484375) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 2.3438) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00076 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.6984)) (by norm_num) hu_12 (by norm_num)
  have hgain_tot : 0.32403 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_67 (γ * Real.log 67) := (by norm_num : (0.32403 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_5 {γ : ℝ} (hlo : 151.484375 ≤ γ) (hhi : γ ≤ 153.125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 151.484375) (g_hi := 153.125) (M := 23520) (logM4_hi := 8.6793139) (ub := 1.597753) (a2 := 3) (b := 1) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.1688 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 151.484375) (g_hi := 153.125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.4011) 39 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.23195 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := 0.1688) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2402) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 151.484375) (g_hi := 153.125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8133) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06927 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.2402)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.8856) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 151.484375) (g_hi := 153.125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.658) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01689 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.8856)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9259) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 151.484375) (g_hi := 153.125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.7532) 58 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00681 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.9259)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8575) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 151.484375) (g_hi := 153.125) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.6007) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00421 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8575)) (by norm_num) hu_4 (by norm_num)
  have hgain_tot : 0.32913 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_23 (γ * Real.log 23) := (by norm_num : (0.32913 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_6 {γ : ℝ} (hlo : 153.125 ≤ γ) (hhi : γ ≤ 155.953125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 153.125) (g_hi := 155.953125) (M := 24300) (logM4_hi := 8.7119405) (ub := 1.606899) (a2 := 0) (b := 5) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.2824 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 153.125) (g_hi := 155.953125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.2845) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.18188 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.2824) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1153) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 153.125) (g_hi := 155.953125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.6863) 27 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.16243 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.1153)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.34431 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) := (by norm_num : (0.34431 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_7 {γ : ℝ} (hlo : 155.953125 ≤ γ) (hhi : γ ≤ 157) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 155.953125) (g_hi := 157) (M := 24696) (logM4_hi := 8.7281051) (ub := 1.610242) (a2 := 1) (b := 2) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.2146 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 155.953125) (g_hi := 157) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.3545) 40 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24243 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := 0.2146) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4254) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 155.953125) (g_hi := 157) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0101) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04631 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.4254)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5155) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 155.953125) (g_hi := 157) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.1123) 64 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03561 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.5155)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.5759) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 155.953125) (g_hi := 157) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.1844) 78 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01252 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.5759)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9544) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 155.953125) (g_hi := 157) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.8364) 27 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0059 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.9544)) (by norm_num) hu_4 (by norm_num)
  have hgain_tot : 0.34277 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_3 (γ * Real.log 3) := (by norm_num : (0.34277 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_8 {γ : ℝ} (hlo : 157 ≤ γ) (hhi : γ ≤ 157.703125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 157) (g_hi := 157.703125) (M := 25000) (logM4_hi := 8.7403372) (ub := 1.612477) (a2 := 1) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.395 ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.1647) 60 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.12887 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := 0.395) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.2752 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.2919) 71 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06267 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := 0.2752) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.716) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.3687) 49 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04222 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.716)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7929) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.4861) 40 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03614 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.7929)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.3454 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.2181) 86 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02254 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := 0.3454) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.7217) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.3769) 64 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02045 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.7217)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.7998) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.4975) 17 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01309 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.7998)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.2617 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.306) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01159 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.2617) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.8952) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.679) 74 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.0043 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8952)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.1892) ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 157) (g_hi := 157.703125) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.7611) 103 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00271 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := (-0.1892)) (by norm_num) hu_9 (by norm_num)
  have hgain_tot : 0.34458 ≤ bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_61 (γ * Real.log 61) := (by norm_num : (0.34458 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_9 {γ : ℝ} (hlo : 157.703125 ≤ γ) (hhi : γ ≤ 158.375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 157.703125) (g_hi := 158.375) (M := 25088) (logM4_hi := 8.7438517) (ub := 1.614599) (a2 := 7) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_5_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.5398 ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.0005) 49 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24047 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := 0.5398) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.1994 ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 1.37) 74 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04922 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := 0.1994) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3182) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.8946) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02014 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.3182)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8933) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.6748) 28 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01412 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.8933)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8594) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.6044) 71 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00691 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.8594)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9343) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.7758) 60 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00604 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.9343)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.679) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.317) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.0037 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.679)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.658) ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 2.2888) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00227 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := (-0.658)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.5815) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 2.1913) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00205 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.5815)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.3845) ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 157.703125) (g_hi := 158.375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.9654) 108 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.0012 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := (-0.3845)) (by norm_num) hu_9 (by norm_num)
  have hgain_tot : 0.34612 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_73 (γ * Real.log 73) := (by norm_num : (0.34612 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_10 {γ : ℝ} (hlo : 158.375 ≤ γ) (hhi : γ ≤ 159.046875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 158.375) (g_hi := 159.046875) (M := 25200) (logM4_hi := 8.7483069) (ub := 1.616717) (a2 := 2) (b := 2) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.0443) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.6151) 49 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14592 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.0443)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3578) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.9366) 28 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.10575 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.3578)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5752) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.1835) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03122 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.5752)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.0832 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.4874) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02072 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.0832) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9112) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.716) 41 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01524 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9112)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.2627 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.3049) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01038 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := 0.2627) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.6806) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.3192) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00943 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.6806)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.1814 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 1.3883) 103 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00434 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.1814) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.8222) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.5357) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00205 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.8222)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.791) ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 2.483) 94 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00191 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := (-0.791)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.9356) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 158.375) (g_hi := 159.046875) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.7795) 87 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00107 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.9356)) (by norm_num) hu_10 (by norm_num)
  have hgain_tot : 0.34803 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_31 (γ * Real.log 31) := (by norm_num : (0.34803 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_11 {γ : ℝ} (hlo : 159.046875 ≤ γ) (hhi : γ ≤ 161.359375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 159.046875) (g_hi := 161.359375) (M := 25920) (logM4_hi := 8.7764784) (ub := 1.623932) (a2 := 4) (b := 4) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.2263 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 159.046875) (g_hi := 161.359375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.3425) 28 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.26399 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := 0.2263) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4941) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 159.046875) (g_hi := 161.359375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.0875) 41 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.09202 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.4941)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.35601 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) := (by norm_num : (0.35601 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_12 {γ : ℝ} (hlo : 161.359375 ≤ γ) (hhi : γ ≤ 162.546875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 161.359375) (g_hi := 162.546875) (M := 26460) (logM4_hi := 8.7970981) (ub := 1.627594) (a2 := 0) (b := 3) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.3137 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.2517) 18 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.19247 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.3137) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5412) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.1426) 50 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06868 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.5412)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.2831) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.8578) 73 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03523 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.2831)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6161) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.2345) 66 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02822 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.6161)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8805) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.6471) 28 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01589 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.8805)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8746) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.6348) 62 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01154 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.8746)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.7438) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 161.359375) (g_hi := 162.546875) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.4094) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01051 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.7438)) (by norm_num) hu_6 (by norm_num)
  have hgain_tot : 0.36254 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_19 (γ * Real.log 19) := (by norm_num : (0.36254 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_13 {γ : ℝ} (hlo : 162.546875 ≤ γ) (hhi : γ ≤ 164.5625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 162.546875) (g_hi := 164.5625) (M := 27000) (logM4_hi := 8.8172999) (ub := 1.633755) (a2 := 1) (b := 3) (c := 3) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.5662 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 162.546875) (g_hi := 164.5625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 0.9688) 18 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.3078 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.5662) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.655) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 162.546875) (g_hi := 164.5625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.2848) 42 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06138 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.655)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.36918 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) := (by norm_num : (0.36918 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_14 {γ : ℝ} (hlo : 164.5625 ≤ γ) (hhi : γ ≤ 165.953125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 164.5625) (g_hi := 165.953125) (M := 27648) (logM4_hi := 8.8410162) (ub := 1.63796) (a2 := 8) (b := 3) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.148 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 164.5625) (g_hi := 165.953125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.4222) 29 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.23817 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := 0.148) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3542) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 164.5625) (g_hi := 165.953125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9328) 18 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05448 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3542)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.503) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 164.5625) (g_hi := 165.953125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.0978) 63 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04579 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.503)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7939) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 164.5625) (g_hi := 165.953125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.4877) 51 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03054 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.7939)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8962) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 164.5625) (g_hi := 165.953125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.6811) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00119 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.8962)) (by norm_num) hu_4 (by norm_num)
  have hgain_tot : 0.37017 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_37 (γ * Real.log 37) := (by norm_num : (0.37017 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_15 {γ : ℝ} (hlo : 165.953125 ≤ γ) (hhi : γ ≤ 167.125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 165.953125) (g_hi := 167.125) (M := 28000) (logM4_hi := 8.8536663) (ub := 1.641476) (a2 := 3) (b := 0) (c := 3) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_5_nonneg γ)) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.1763 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.3935) 29 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24731 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := 0.1763) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0249) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.5956) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0717 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.0249)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4172) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.0011) 78 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02391 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.4172)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6377) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.2622) 75 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0178 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.6377)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.5351) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.1354) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00779 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.5351)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8104) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 165.953125) (g_hi := 167.125) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.5154) 83 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0056 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8104)) (by norm_num) hu_5 (by norm_num)
  have hgain_tot : 0.37411 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_23 (γ * Real.log 23) := (by norm_num : (0.37411 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_16 {γ : ℝ} (hlo : 167.125 ≤ γ) (hhi : γ ≤ 168.75) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 167.125) (g_hi := 168.75) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.646317) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_3_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.1543 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 167.125) (g_hi := 168.75) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.4158) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.22865 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := 0.1543) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0761) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 167.125) (g_hi := 168.75) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.6469) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.14089 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.0761)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.8138) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 167.125) (g_hi := 168.75) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.5212) 64 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01714 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.8138)) (by norm_num) hu_2 (by norm_num)
  have hgain_tot : 0.38668 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) := (by norm_num : (0.38668 : ℝ) ≤ _).trans (add_le_add (add_le_add hg_0 hg_1) hg_2)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_17 {γ : ℝ} (hlo : 168.75 ≤ γ) (hhi : γ ≤ 169.171875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 168.75) (g_hi := 169.171875) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.64756) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.7616 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 0.7049) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.12957 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.7616) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5004) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.0948) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0908 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.5004)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.2061) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.7783) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03901 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.2061)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.1732) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 1.7448) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03393 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.1732)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.7817) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.4679) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03236 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.7817)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.7456) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.4121) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0171 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.7456)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.1728 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.3971) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01355 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := 0.1728) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.083) ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.6538) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00842 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := (-0.083)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.1169) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.6879) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00726 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.1169)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.8819) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.6501) 84 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00348 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8819)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.2519 ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 1.3161) 113 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00319 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := 0.2519) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.677) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 168.75) (g_hi := 169.171875) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 2.3143) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00158 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.677)) (by norm_num) hu_11 (by norm_num)
  have hgain_tot : 0.38025 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_53 (γ * Real.log 53) := (by norm_num : (0.38025 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_18 {γ : ℝ} (hlo : 169.171875 ≤ γ) (hhi : γ ≤ 169.28125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.171875) (g_hi := 169.28125) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.647882) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_23_nonneg γ) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.791 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 0.6583) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13173 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.791) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6444) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.2709) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06336 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.6444)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5218) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.1197) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03634 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.5218)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4947) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.0882) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02483 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.4947)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.476) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.0668) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0215 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.476)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.9492 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.3199) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0179 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.9492) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8778) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.6414) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01626 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.8778)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.896) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.6807) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01534 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.896)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.5206) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 2.1183) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00917 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.5206)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.2196) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.7921) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00901 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.2196)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.8024 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.6394) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00884 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.8024) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.925) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.7508) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.0069 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.925)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.223 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 1.3459) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.0045 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.223) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.5043) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.0993) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00407 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.5043)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.5176) ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 2.1148) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.0032 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := (-0.5176)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.9466 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 0.3282) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00249 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.9466) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.1294 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 1.441) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00241 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.1294) (by norm_num) hu_16 (by norm_num)
  have hu_17 : (-0.2037) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 169.171875) (g_hi := 169.28125) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 1.7759) 113 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00203 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.2037)) (by norm_num) hu_17 (by norm_num)
  have hgain_tot : 0.37988 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_67 (γ * Real.log 67) := (by norm_num : (0.37988 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_19 {γ : ℝ} (hlo : 169.28125 ≤ γ) (hhi : γ ≤ 169.34375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.28125) (g_hi := 169.34375) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.648067) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_23_nonneg γ) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.6832 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 0.8186) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.1238 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.6832) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.7179) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.3714) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04975 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.7179)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4556) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0438) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04306 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.4556)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8139) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.5213) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02538 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.8139)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.7944) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.4885) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01892 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.7944)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.6401) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.2653) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01768 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.6401)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.8514 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.552) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.017 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.8514) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.1783) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.75) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01572 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.1783)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.629) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.2509) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.01522 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.629)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.979 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.2051) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00971 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.979) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.9435) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.8023) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00832 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9435)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.4323) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.0178) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00656 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.4323)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.6216 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.8999) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00596 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.6216) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.1226) ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.6937) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00583 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := (-0.1226)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.0308 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.5399) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00345 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.0308) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.5613 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.9748) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00333 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.5613) (by norm_num) hu_15 (by norm_num)
  have hu_16 : (-0.6916) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.3344) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00253 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.6916)) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.8229 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 0.6043) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00233 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.8229) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.9115 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.4237) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.0019 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9115) (by norm_num) hu_18 (by norm_num)
  have hu_19 : (-0.4511) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 2.0387) 113 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.0014 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.4511)) (by norm_num) hu_19 (by norm_num)
  have hu_20 : (-0.1787) ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.7504) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_20 : 0.00124 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := (-0.1787)) (by norm_num) hu_20 (by norm_num)
  have hu_21 : 0.6778 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 169.28125) (g_hi := 169.34375) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.826) 125 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_21 : 0.00094 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.6778) (by norm_num) hu_21 (by norm_num)
  have hgain_tot : 0.38003 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_103 (γ * Real.log 103) := (by norm_num : (0.38003 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19) hg_20) hg_21)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_20 {γ : ℝ} (hlo : 169.34375 ≤ γ) (hhi : γ ≤ 169.375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.34375) (g_hi := 169.375) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.648159) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_23_nonneg γ) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.6225 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 0.8988) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11933 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.6225) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4167) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0005) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04726 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.4167)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.752) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.4217) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04353 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.752)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.772) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.4526) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0316 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.772)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.6947) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.3386) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02811 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.6947)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.0312 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.5395) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01973 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.0312) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.785 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.6681) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01639 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.785) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7055) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.3538) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01447 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.7055)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.6977) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.3429) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.0124 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.6977)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9859 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.1678) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00974 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.9859) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.1175 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.453) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00742 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.1175) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.799 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.6451) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00661 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.799) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9621) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.8631) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00557 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9621)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.5311) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.1306) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00541 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.5311)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.2838 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.283) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.0043 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.2838) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.7594 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.7083) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00376 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.7594) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.7368 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 0.7424) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00222 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.7368) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.9897 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.34375) (g_hi := 169.375) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.1431) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00198 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9897) (by norm_num) hu_17 (by norm_num)
  have hgain_tot : 0.37983 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) := (by norm_num : (0.37983 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_21 {γ : ℝ} (hlo : 169.375 ≤ γ) (hhi : γ ≤ 169.40625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.375) (g_hi := 169.40625) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.648251) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_23_nonneg γ) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.5579 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 0.9789) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11457 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.5579) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3969) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9789) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04949 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3969)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7842) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.472) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03771 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.7842)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7498) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.4183) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03499 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.7498)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.6389) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.2637) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03326 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.6389)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.136 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.4343) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02173 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.136) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.708 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.7841) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01568 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.708) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7654) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.4423) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01153 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.7654)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.7607) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.4349) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00982 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.7607)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9576 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.2919) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.0096 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.9576) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.2358 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.3327) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00821 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.2358) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.8689 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.5177) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00687 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.8689) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.4043 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.1545) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.0047 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.4043) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.6232) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.2435) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00435 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.6232)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.8391 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.5751) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00393 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.8391) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.9772) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.9239) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00335 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9772)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.6367 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 0.8805) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00209 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.6367) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.9904 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.138) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00198 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9904) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.2279 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.3408) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00186 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.2279) (by norm_num) hu_18 (by norm_num)
  have hu_19 : (-0.9065) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.7048) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.00156 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.9065)) (by norm_num) hu_19 (by norm_num)
  have hu_20 : (-0.8409) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.5694) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_20 : 0.0013 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.8409)) (by norm_num) hu_20 (by norm_num)
  have hu_21 : 0.9243 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 169.375) (g_hi := 169.40625) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.3915) 125 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_21 : 0.00108 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.9243) (by norm_num) hu_21 (by norm_num)
  have hgain_tot : 0.37966 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_103 (γ * Real.log 103) := (by norm_num : (0.37966 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19) hg_20) hg_21)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_22 {γ : ℝ} (hlo : 169.40625 ≤ γ) (hhi : γ ≤ 169.4375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.40625) (g_hi := 169.4375) (M := 28672) (logM4_hi := 8.8773826) (ub := 1.648344) (a2 := 10) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (bohmanExcess11_101_nonneg γ) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4896 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.0591) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10955 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.4896) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3769) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9572) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05179 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3769)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5795) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.1888) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03873 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.5795)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7266) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.384) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03858 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.7266)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8145) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5223) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03227 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.8145)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.2393 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.3291) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02371 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.2393) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.6214 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.9002) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01489 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.6214) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.9147 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.416) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00939 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.9147) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.3507 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.2124) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00898 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.3507) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.8194) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.5309) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00887 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.8194)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.8171) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.5269) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0075 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8171)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.9248 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.3902) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00708 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9248) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.5182 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.026) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00508 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.5182) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.9039 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.4419) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00407 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9039) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.7073) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.3563) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00338 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.7073)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.8558) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.5975) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00241 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.8558)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.3584 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.2042) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00205 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.3584) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.9615 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.2783) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00195 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9615) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.5245 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 1.0186) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00195 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.5245) (by norm_num) hu_18 (by norm_num)
  have hu_19 : (-0.9888) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.9848) 52 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.00164 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9888)) (by norm_num) hu_19 (by norm_num)
  have hu_20 : (-0.4335) ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 2.0191) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_20 : 0.00111 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := (-0.4335)) (by norm_num) hu_20 (by norm_num)
  have hu_21 : 0.9697 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.2467) 125 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_21 : 0.0011 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.9697) (by norm_num) hu_21 (by norm_num)
  have hu_22 : 0.9971 ≤ Real.cos (γ * Real.log 107) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 107) (lp_lo := 4.6728282) (lp_hi := 4.6728307) (x_hi := 0.0752) 126 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_107.1 sharp_log_prime_107.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_22 : 0.00095 ≤ bohmanExcess11_107 (γ * Real.log 107) := bohmanExcess11_107_ge (u_lo := 0.9971) (by norm_num) hu_22 (by norm_num)
  have hu_23 : (-0.9714) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.8986) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_23 : 0.00084 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.9714)) (by norm_num) hu_23 (by norm_num)
  have hu_24 : (-0.8988) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.687) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_24 : 0.00083 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.8988)) (by norm_num) hu_24 (by norm_num)
  have hu_25 : (-0.7594) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 2.4329) 113 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_25 : 0.00061 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.7594)) (by norm_num) hu_25 (by norm_num)
  have hu_26 : (-0.6635) ≤ Real.cos (γ * Real.log 97) := cos_mul_ge_of_even_shift11 (g_lo := 169.40625) (g_hi := 169.4375) (lp := Real.log 97) (lp_lo := 4.5747066) (lp_hi := 4.5747121) (x_hi := 2.2961) 123 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_97.1 sharp_log_prime_97.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_26 : 0.00024 ≤ bohmanExcess11_97 (γ * Real.log 97) := bohmanExcess11_97_ge (u_lo := (-0.6635)) (by norm_num) hu_26 (by norm_num)
  have hgain_tot : 0.37955 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_97 (γ * Real.log 97) := (by norm_num : (0.37955 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19) hg_20) hg_21) hg_22) hg_23) hg_24) hg_25) hg_26)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_23 {γ : ℝ} (hlo : 169.4375 ≤ γ) (hhi : γ ≤ 169.453125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.4375) (g_hi := 169.453125) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.64839) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4543 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.0992) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10695 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.4543) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3567) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9355) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05418 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3567)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5168) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.1138) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04452 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.5168)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7025) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3496) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04239 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.7025)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8289) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5475) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02971 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.8289)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.3399 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.2239) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02564 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.3399) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.5749 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 0.9582) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01446 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.5749) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.4606 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.0921) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00971 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.4606) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.8879 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.478) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00926 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.8879) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.844) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.5751) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00766 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.844)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.9656 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.2628) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00723 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9656) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.8428) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.5729) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00645 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8428)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.6234 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.8976) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00544 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.6234) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.9527 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.3087) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00417 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9527) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.7954) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.4902) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00342 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.7954)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.746) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.4127) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00293 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.746)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.4821 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.0677) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00224 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.4821) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.9399 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.3484) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00193 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9399) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.4645 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.4375) (g_hi := 169.453125) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 1.0877) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00187 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.4645) (by norm_num) hu_18 (by norm_num)
  have hgain_tot : 0.38016 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_83 (γ * Real.log 83) := (by norm_num : (0.38016 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_24 {γ : ℝ} (hlo : 169.453125 ≤ γ) (hhi : γ ≤ 169.46875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.453125) (g_hi := 169.46875) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.648436) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4183 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.1392) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.1043 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.4183) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3466) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9247) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0554 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3466)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4844) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.0764) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04751 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.4844)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6903) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3325) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04434 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.6903)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8427) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5726) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02726 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.8427)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.3889 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.1713) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02657 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.3889) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.5266 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.0162) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01402 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.5266) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.5131 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 1.0319) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01005 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.5131) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.8577 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.54) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00911 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.8577) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9802 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.1991) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00728 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9802) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.867) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.6194) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00653 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.867)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.6724 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.8333) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.0056 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.6724) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.8667) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.6189) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00547 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8667)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.9708 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.2421) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00421 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9708) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.7617) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.4365) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00399 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.7617)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.7824) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.4691) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00251 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.7824)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.5408 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.9994) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00233 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.5408) (by norm_num) hu_16 (by norm_num)
  have hu_17 : (-0.9253) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.7516) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.0022 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.9253)) (by norm_num) hu_17 (by norm_num)
  have hu_18 : 0.9136 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.453125) (g_hi := 169.46875) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.4185) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.0019 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.9136) (by norm_num) hu_18 (by norm_num)
  have hgain_tot : 0.38058 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_89 (γ * Real.log 89) := (by norm_num : (0.38058 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_25 {γ : ℝ} (hlo : 169.46875 ≤ γ) (hhi : γ ≤ 169.484375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.46875) (g_hi := 169.484375) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.648482) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.3815 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.1793) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10159 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.3815) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3365) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9139) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05663 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3365)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4513) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.0389) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.05056 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.4513)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6777) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3153) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04638 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.6777)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.4369 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.1186) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02749 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.4369) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.856) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5978) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0249 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.856)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.4763 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.0743) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01356 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.4763) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.5638 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.9718) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01039 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.5638) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.8241 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.6021) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00895 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.8241) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9908 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.1354) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00732 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9908) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.7185 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.7691) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00576 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.7185) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.8883) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.6637) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00548 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.8883)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.7259) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.3829) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00459 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.7259)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.8888) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.6649) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00456 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.8888)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.9846 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.1755) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00424 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9846) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.9056) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.7027) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00278 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.9056)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.5968 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.9312) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00241 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.5968) (by norm_num) hu_16 (by norm_num)
  have hu_17 : (-0.8164) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.46875) (g_hi := 169.484375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.5256) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00212 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.8164)) (by norm_num) hu_17 (by norm_num)
  have hgain_tot : 0.37971 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_37 (γ * Real.log 37) := (by norm_num : (0.37971 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_26 {γ : ℝ} (hlo : 169.484375 ≤ γ) (hhi : γ ≤ 169.515625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.484375) (g_hi := 169.515625) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.648574) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.3062 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.2595) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09605 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.3062) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3263) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9031) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05789 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3263)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4175) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.0014) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.05368 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.4175)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.665) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.2981) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04846 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.665)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.4836 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.066) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02839 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.4836) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.881) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.6481) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.02051 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.881)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.3713 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.1903) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01259 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.3713) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.6124 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.9116) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01072 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.6124) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7477 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.7262) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00857 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.7477) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9974 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.0717) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00734 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9974) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.7616 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.7049) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0059 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.7616) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.6879) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.3292) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00522 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.6879)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.994 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.1089) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00426 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.994) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.9256) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.7522) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00365 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.9256)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.8836) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.6537) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00343 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8836)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.9273) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.7569) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00298 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.9273)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.6502 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.8629) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.0025 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.6502) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.8086 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.629) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.0018 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.8086) (by norm_num) hu_17 (by norm_num)
  have hu_18 : (-0.1129) ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.6839) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00173 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := (-0.1129)) (by norm_num) hu_18 (by norm_num)
  have hu_19 : 0.2055 ≤ Real.cos (γ * Real.log 83) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 83) (lp_lo := 4.4188382) (lp_hi := 4.4188418) (x_hi := 1.3638) 119 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_83.1 sharp_log_prime_83.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_19 : 0.00154 ≤ bohmanExcess11_83 (γ * Real.log 83) := bohmanExcess11_83_ge (u_lo := 0.2055) (by norm_num) hu_19 (by norm_num)
  have hu_20 : (-0.8763) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.6384) 97 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_20 : 0.00142 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.8763)) (by norm_num) hu_20 (by norm_num)
  have hu_21 : 0.966 ≤ Real.cos (γ * Real.log 103) := cos_mul_ge_of_even_shift11 (g_lo := 169.484375) (g_hi := 169.515625) (lp := Real.log 103) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (x_hi := 0.2612) 125 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_103.1 sharp_log_prime_103.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_21 : 0.0011 ≤ bohmanExcess11_103 (γ * Real.log 103) := bohmanExcess11_103_ge (u_lo := 0.966) (by norm_num) hu_21 (by norm_num)
  have hgain_tot : 0.37973 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_103 (γ * Real.log 103) := (by norm_num : (0.37973 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18) hg_19) hg_20) hg_21)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_27 {γ : ℝ} (hlo : 169.515625 ≤ γ) (hhi : γ ≤ 169.546875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.515625) (g_hi := 169.546875) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.648666) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.2291 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.3396) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09038 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.2291) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3057) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8814) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0605 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.3057)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3483) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.9265) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.06007 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.3483)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6389) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.2638) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.05279 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.6389)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.5728 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 0.9608) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03009 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.5728) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9037) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.6984) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01654 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9037)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.2613 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.3064) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01158 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.2613) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.7029 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.7913) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01132 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.7029) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.6598 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 0.8502) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00814 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.6598) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9831 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.1836) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00729 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9831) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.6061) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.2219) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0066 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.6061)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.8384 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.5764) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00616 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.8384) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.8334) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.5557) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00492 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8334)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.9875 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.1581) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00425 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9875) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.7476 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.7263) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00264 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.7476) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.9557) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.8407) 76 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00217 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.9557)) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.0209 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.5498) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.002 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.0209) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.7184 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.7692) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00171 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.7184) (by norm_num) hu_17 (by norm_num)
  have hu_18 : (-0.9581) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.515625) (g_hi := 169.546875) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.849) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_18 : 0.00171 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.9581)) (by norm_num) hu_18 (by norm_num)
  have hgain_tot : 0.38086 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_19 (γ * Real.log 19) := (by norm_num : (0.38086 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17) hg_18)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_28 {γ : ℝ} (hlo : 169.546875 ≤ γ) (hhi : γ ≤ 169.59375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.546875) (g_hi := 169.59375) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.648804) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_7_nonneg γ) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.1106 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.4599) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.08166 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.1106) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2772) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.8516) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06664 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.2772)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.285) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8597) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.06318 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.285)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6122) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.2295) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.05731 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.6122)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.6557 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 0.8556) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03168 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.6557) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.7832 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.671) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01185 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.7832) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9336) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.7738) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01135 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9336)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.0902 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.4804) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01001 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := 0.0902) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.5175) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.1146) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00808 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.5175)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.5094 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 1.0363) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.0074 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.5094) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.9305 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.3748) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0071 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.9305) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.7753) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.4577) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00663 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.7753)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.9013 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.4479) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00637 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.9013) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.9366 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.3579) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00414 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.9366) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.831 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.5898) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00277 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.831) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.1544 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.4157) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00226 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.1544) (by norm_num) hu_15 (by norm_num)
  have hu_16 : 0.5573 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.546875) (g_hi := 169.59375) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 0.9796) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00155 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.5573) (by norm_num) hu_16 (by norm_num)
  have hgain_tot : 0.37998 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_89 (γ * Real.log 89) := (by norm_num : (0.37998 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_29 {γ : ℝ} (hlo : 169.59375 ≤ γ) (hhi : γ ≤ 169.6875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.59375) (g_hi := 169.6875) (M := 28800) (logM4_hi := 8.8818378) (ub := 1.64908) (a2 := 5) (b := 2) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_17_nonneg γ) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.1677) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.7392) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07676 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.1677)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2537) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8272) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0674 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.2537)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5706) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.178) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.06456 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.5706)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.1292) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.7003) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.06402 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.1292)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.7663 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 0.6977) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0338 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.7663) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.882 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.4905) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01251 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.882) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.3736) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.9536) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01049 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.3736)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.6743) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.3107) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00962 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.6743)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.255) ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 41) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (x_hi := 1.8286) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_41.1 sharp_log_prime_41.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00684 ≤ bohmanExcess11_41 (γ * Real.log 41) := bohmanExcess11_41_ge (u_lo := (-0.255)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.9676 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 0.2552) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00659 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.9676) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.7268 ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 0.757) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00635 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := 0.7268) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.1614 ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 1.4086) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.0057 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := 0.1614) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9774) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.9247) 43 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00384 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9774)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : 0.7264 ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 0.7576) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00369 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := 0.7264) (by norm_num) hu_13 (by norm_num)
  have hu_14 : 0.9267 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 0.385) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00291 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.9267) (by norm_num) hu_14 (by norm_num)
  have hu_15 : 0.3487 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.2146) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00264 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.3487) (by norm_num) hu_15 (by norm_num)
  have hu_16 : (-0.9904) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.9951) 53 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_16 : 0.00141 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9904)) (by norm_num) hu_16 (by norm_num)
  have hu_17 : 0.1695 ≤ Real.cos (γ * Real.log 89) := cos_mul_ge_of_even_shift11 (g_lo := 169.59375) (g_hi := 169.6875) (lp := Real.log 89) (lp_lo := 4.4886359) (lp_hi := 4.4886377) (x_hi := 1.4004) 121 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_89.1 sharp_log_prime_89.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_17 : 0.00116 ≤ bohmanExcess11_89 (γ * Real.log 89) := bohmanExcess11_89_ge (u_lo := 0.1695) (by norm_num) hu_17 (by norm_num)
  have hgain_tot : 0.38029 ≤ bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_89 (γ * Real.log 89) := (by norm_num : (0.38029 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15) hg_16) hg_17)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_30 {γ : ℝ} (hlo : 169.6875 ≤ γ) (hhi : γ ≤ 169.9375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.6875) (g_hi := 169.9375) (M := 28812) (logM4_hi := 8.8822557) (ub := 1.649817) (a2 := 0) (b := 1) (c := 0) (d := 4) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.0563 ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.5144) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09749 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := 0.0563) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4832) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.075) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.08061 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.4832)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.1904) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.7623) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.07649 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.1904)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.8959 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 0.4603) 91 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03628 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := 0.8959) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.6968) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.3416) 69 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02228 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.6968)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.4314) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.0168) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01679 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.4314)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.0609) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.6317) 93 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.01573 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.0609)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.6722 ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 0.8335) 104 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.01111 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := 0.6722) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9469) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.8127) 53 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00782 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9469)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.4008 ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 1.1583) 111 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00469 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := 0.4008) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.6877 ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 0.8124) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0033 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := 0.6877) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.2042) ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 1.7764) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00292 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := (-0.2042)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.438 ≤ Real.cos (γ * Real.log 79) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 79) (lp_lo := 4.3694478) (lp_hi := 4.369448) (x_hi := 1.1174) 118 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_79.1 sharp_log_prime_79.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00217 ≤ bohmanExcess11_79 (γ * Real.log 79) := bohmanExcess11_79_ge (u_lo := 0.438) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.2498) ≤ Real.cos (γ * Real.log 71) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 71) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (x_hi := 1.8232) 115 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_71.1 sharp_log_prime_71.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.0016 ≤ bohmanExcess11_71 (γ * Real.log 71) := bohmanExcess11_71_ge (u_lo := (-0.2498)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.7383) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 2.4011) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00128 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.7383)) (by norm_num) hu_14 (by norm_num)
  have hu_15 : (-0.8851) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 169.6875) (g_hi := 169.9375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.6568) 102 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_15 : 0.00094 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.8851)) (by norm_num) hu_15 (by norm_num)
  have hgain_tot : 0.3815 ≤ bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_43 (γ * Real.log 43) := (by norm_num : (0.3815 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14) hg_15)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_31 {γ : ℝ} (hlo : 169.9375 ≤ γ) (hhi : γ ≤ 171.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 169.9375) (g_hi := 171.140625) (M := 29400) (logM4_hi := 8.9024575) (ub := 1.653344) (a2 := 1) (b := 1) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_13_nonneg γ) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.2275) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.8003) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13479 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.2275)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0183) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.589) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.10594 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.0183)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3892) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.9705) 65 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0563 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.3892)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.6857) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.3262) 53 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04678 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.6857)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.693) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.3363) 77 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01508 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.693)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.6547) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.2844) 80 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01417 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.6547)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8246) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.54) 85 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00518 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8246)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.607) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.223) 98 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00454 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.607)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9839) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 169.9375) (g_hi := 171.140625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.9565) 44 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00273 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.9839)) (by norm_num) hu_8 (by norm_num)
  have hgain_tot : 0.38551 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_5 (γ * Real.log 5) := (by norm_num : (0.38551 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_32 {γ : ℝ} (hlo : 171.140625 ≤ γ) (hhi : γ ≤ 173.5625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 171.140625) (g_hi := 173.5625) (M := 30240) (logM4_hi := 8.930629) (ub := 1.660368) (a2 := 3) (b := 3) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.6026 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 171.140625) (g_hi := 173.5625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 0.924) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.33015 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.6026) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5744) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 171.140625) (g_hi := 173.5625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.1826) 30 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.06389 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.5744)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.39404 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) := (by norm_num : (0.39404 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_33 {γ : ℝ} (hlo : 173.5625 ≤ γ) (hhi : γ ≤ 174.4375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 173.5625) (g_hi := 174.4375) (M := 30240) (logM4_hi := 8.930629) (ub := 1.662885) (a2 := 3) (b := 3) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_5_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.0152 ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.5555) 54 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15537 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := 0.0152) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0402 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.5305) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.11781 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.0402) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.2505 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.3175) 71 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.09195 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.2505) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.0281) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.5988) 100 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01123 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.0281)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.5167) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.1137) 95 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00809 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.5167)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.7595) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.4331) 87 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0071 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.7595)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.4672) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 173.5625) (g_hi := 174.4375) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 2.0569) 110 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00261 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.4672)) (by norm_num) hu_6 (by norm_num)
  have hgain_tot : 0.39416 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_53 (γ * Real.log 53) := (by norm_num : (0.39416 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_34 {γ : ℝ} (hlo : 174.4375 ≤ γ) (hhi : γ ≤ 175.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 174.4375) (g_hi := 175.140625) (M := 30720) (logM4_hi := 8.9463756) (ub := 1.66489) (a2 := 9) (b := 1) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.0545 ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.5162) 54 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.16163 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := 0.0545) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4137) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.9972) 45 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.10782 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.4137)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4324) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0179) 19 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04554 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.4324)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.03) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 1.6008) 82 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.03981 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.03)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.5501) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 2.1532) 79 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.02211 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.5501)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9004) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.6907) 67 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00916 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.9004)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8106) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.5156) 87 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00559 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.8106)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.4313) ≤ Real.cos (γ * Real.log 47) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 47) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (x_hi := 2.0167) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_47.1 sharp_log_prime_47.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00378 ≤ bohmanExcess11_47 (γ * Real.log 47) := bohmanExcess11_47_ge (u_lo := (-0.4313)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.1062) ≤ Real.cos (γ * Real.log 67) := cos_mul_ge_of_even_shift11 (g_lo := 174.4375) (g_hi := 175.140625) (lp := Real.log 67) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (x_hi := 1.6771) 117 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_67.1 sharp_log_prime_67.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00228 ≤ bohmanExcess11_67 (γ * Real.log 67) := bohmanExcess11_67_ge (u_lo := (-0.1062)) (by norm_num) hu_8 (by norm_num)
  have hgain_tot : 0.39772 ≤ bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_67 (γ * Real.log 67) := (by norm_num : (0.39772 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_35 {γ : ℝ} (hlo : 175.140625 ≤ γ) (hhi : γ ≤ 176.375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 175.140625) (g_hi := 176.375) (M := 31104) (logM4_hi := 8.9588005) (ub := 1.668401) (a2 := 5) (b := 5) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4344 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 175.140625) (g_hi := 176.375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.1214) 45 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.29425 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := 0.4344) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3754) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 175.140625) (g_hi := 176.375) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 1.9556) 67 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05757 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.3754)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.715) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 175.140625) (g_hi := 176.375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3673) 31 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04041 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.715)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.647) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift11 (g_lo := 175.140625) (g_hi := 176.375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.2743) 101 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_37.1 sharp_log_prime_37.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00407 ≤ bohmanExcess11_37 (γ * Real.log 37) := bohmanExcess11_37_ge (u_lo := (-0.647)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.7916) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift11 (g_lo := 175.140625) (g_hi := 176.375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.4839) 96 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_31.1 sharp_log_prime_31.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00349 ≤ bohmanExcess11_31 (γ * Real.log 31) := bohmanExcess11_31_ge (u_lo := (-0.7916)) (by norm_num) hu_4 (by norm_num)
  have hgain_tot : 0.39979 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_31 (γ * Real.log 31) := (by norm_num : (0.39979 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_36 {γ : ℝ} (hlo : 176.375 ≤ γ) (hhi : γ ≤ 178.25) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 176.375) (g_hi := 178.25) (M := 31752) (logM4_hi := 8.9794202) (ub := 1.673686) (a2 := 1) (b := 4) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_5_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4982 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 176.375) (g_hi := 178.25) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.0492) 31 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.36736 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := 0.4982) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.714) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 176.375) (g_hi := 178.25) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.3658) 55 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04252 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.714)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.40988 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_7 (γ * Real.log 7) := (by norm_num : (0.40988 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_37 {γ : ℝ} (hlo : 178.25 ≤ γ) (hhi : γ ≤ 179.015625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 178.25) (g_hi := 179.015625) (M := 32000) (logM4_hi := 8.9871971) (ub := 1.675828) (a2 := 6) (b := 0) (c := 3) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_17_nonneg γ) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : (-0.3141) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.8903) 31 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11514 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.3141)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5427) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.1444) 46 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.08263 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.5427)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.0999 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 1.4707) 73 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.08088 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := 0.0999) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4201) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 11) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (x_hi := 2.0043) 68 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_11.1 sharp_log_prime_11.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.05344 ≤ bohmanExcess11_11 (γ * Real.log 11) := bohmanExcess11_11_ge (u_lo := (-0.4201)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.5139) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.1104) 20 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.03711 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.5139)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.5042) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.0992) 89 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_23.1 sharp_log_prime_23.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01464 ≤ bohmanExcess11_23 (γ * Real.log 23) := bohmanExcess11_23_ge (u_lo := (-0.5042)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9334) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.7734) 55 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_7.1 sharp_log_prime_7.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00981 ≤ bohmanExcess11_7 (γ * Real.log 7) := bohmanExcess11_7_ge (u_lo := (-0.9334)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.2924) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.8675) 107 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_43.1 sharp_log_prime_43.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00582 ≤ bohmanExcess11_43 (γ * Real.log 43) := bohmanExcess11_43_ge (u_lo := (-0.2924)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.442) ≤ Real.cos (γ * Real.log 59) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 59) (lp_lo := 4.0775372) (lp_hi := 4.0775382) (x_hi := 2.0286) 116 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_59.1 sharp_log_prime_59.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00205 ≤ bohmanExcess11_59 (γ * Real.log 59) := bohmanExcess11_59_ge (u_lo := (-0.442)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.6632) ≤ Real.cos (γ * Real.log 53) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 53) (lp_lo := 3.9702913) (lp_hi := 3.9702938) (x_hi := 2.2957) 113 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_53.1 sharp_log_prime_53.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00165 ≤ bohmanExcess11_53 (γ * Real.log 53) := bohmanExcess11_53_ge (u_lo := (-0.6632)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.2023) ≤ Real.cos (γ * Real.log 73) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 73) (lp_lo := 4.290459) (lp_hi := 4.2904607) (x_hi := 1.7744) 122 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_73.1 sharp_log_prime_73.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00156 ≤ bohmanExcess11_73 (γ * Real.log 73) := bohmanExcess11_73_ge (u_lo := (-0.2023)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.7166) ≤ Real.cos (γ * Real.log 61) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 61) (lp_lo := 4.1108736) (lp_hi := 4.1108746) (x_hi := 2.3696) 117 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_61.1 sharp_log_prime_61.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00094 ≤ bohmanExcess11_61 (γ * Real.log 61) := bohmanExcess11_61_ge (u_lo := (-0.7166)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9809) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 19) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (x_hi := 2.9415) 84 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_19.1 sharp_log_prime_19.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00078 ≤ bohmanExcess11_19 (γ * Real.log 19) := bohmanExcess11_19_ge (u_lo := (-0.9809)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.5314) ≤ Real.cos (γ * Real.log 97) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 97) (lp_lo := 4.5747066) (lp_hi := 4.5747121) (x_hi := 2.131) 130 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_97.1 sharp_log_prime_97.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00033 ≤ bohmanExcess11_97 (γ * Real.log 97) := bohmanExcess11_97_ge (u_lo := (-0.5314)) (by norm_num) hu_13 (by norm_num)
  have hu_14 : (-0.9855) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift11 (g_lo := 178.25) (g_hi := 179.015625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 2.9655) 96 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_29.1 sharp_log_prime_29.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_14 : 0.00027 ≤ bohmanExcess11_29 (γ * Real.log 29) := bohmanExcess11_29_ge (u_lo := (-0.9855)) (by norm_num) hu_14 (by norm_num)
  have hgain_tot : 0.40705 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_29 (γ * Real.log 29) := (by norm_num : (0.40705 : ℝ) ≤ _).trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hg_0 hg_1) hg_2) hg_3) hg_4) hg_5) hg_6) hg_7) hg_8) hg_9) hg_10) hg_11) hg_12) hg_13) hg_14)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_38 {γ : ℝ} (hlo : 179.015625 ≤ γ) (hhi : γ ≤ 180.328125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 179.015625) (g_hi := 180.328125) (M := 32400) (logM4_hi := 8.999622) (ub := 1.679481) (a2 := 2) (b := 4) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_3_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.3617 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 179.015625) (g_hi := 180.328125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.2006) 46 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.27683 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := 0.3617) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.009) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 179.015625) (g_hi := 180.328125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.5797) 20 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.10777 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := (-0.009)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3891) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift11 (g_lo := 179.015625) (g_hi := 180.328125) (lp := Real.log 17) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (x_hi := 1.9704) 81 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_17.1 sharp_log_prime_17.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03002 ≤ bohmanExcess11_17 (γ * Real.log 17) := bohmanExcess11_17_ge (u_lo := (-0.3891)) (by norm_num) hu_2 (by norm_num)
  have hgain_tot : 0.41462 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_17 (γ * Real.log 17) := (by norm_num : (0.41462 : ℝ) ≤ _).trans (add_le_add (add_le_add hg_0 hg_1) hg_2)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_39 {γ : ℝ} (hlo : 180.328125 ≤ γ) (hhi : γ ≤ 182.40625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 180.328125) (g_hi := 182.40625) (M := 33600) (logM4_hi := 9.0359884) (ub := 1.685218) (a2 := 4) (b := 1) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_5 (γ * Real.log 5) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_5_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.7173 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift11 (g_lo := 180.328125) (g_hi := 182.40625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 0.7708) 20 (by norm_num) hlo hhi (by norm_num) Real.log_two_gt_d9.le Real.log_two_lt_d9.le (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.41358 ≤ bohmanExcess11_2 (γ * Real.log 2) := bohmanExcess11_2_ge (u_lo := 0.7173) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9829) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 180.328125) (g_hi := 182.40625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.9514) 32 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00219 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := (-0.9829)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9735) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift11 (g_lo := 180.328125) (g_hi := 182.40625) (lp := Real.log 13) (lp_lo := 2.5649481) (lp_hi := 2.56495) (x_hi := 2.9073) 74 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_13.1 sharp_log_prime_13.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00194 ≤ bohmanExcess11_13 (γ * Real.log 13) := bohmanExcess11_13_ge (u_lo := (-0.9735)) (by norm_num) hu_2 (by norm_num)
  have hgain_tot : 0.41771 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_13 (γ * Real.log 13) := (by norm_num : (0.41771 : ℝ) ≤ _).trans (add_le_add (add_le_add hg_0 hg_1) hg_2)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_interval_40 {γ : ℝ} (hlo : 182.40625 ≤ γ) (hhi : γ ≤ 184) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  have harch := bohman11_arch_lt_smooth (g_lo := 182.40625) (g_hi := 184) (M := 34020) (logM4_hi := 9.0484132) (ub := 1.689558) (a2 := 0) (b := 5) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm11_coupled_ge_sum_excess γ
  have hnn_rest : 0 ≤ bohmanExcess11_2 (γ * Real.log 2) + bohmanExcess11_7 (γ * Real.log 7) + bohmanExcess11_11 (γ * Real.log 11) + bohmanExcess11_13 (γ * Real.log 13) + bohmanExcess11_17 (γ * Real.log 17) + bohmanExcess11_19 (γ * Real.log 19) + bohmanExcess11_23 (γ * Real.log 23) + bohmanExcess11_29 (γ * Real.log 29) + bohmanExcess11_31 (γ * Real.log 31) + bohmanExcess11_37 (γ * Real.log 37) + bohmanExcess11_41 (γ * Real.log 41) + bohmanExcess11_43 (γ * Real.log 43) + bohmanExcess11_47 (γ * Real.log 47) + bohmanExcess11_53 (γ * Real.log 53) + bohmanExcess11_59 (γ * Real.log 59) + bohmanExcess11_61 (γ * Real.log 61) + bohmanExcess11_67 (γ * Real.log 67) + bohmanExcess11_71 (γ * Real.log 71) + bohmanExcess11_73 (γ * Real.log 73) + bohmanExcess11_79 (γ * Real.log 79) + bohmanExcess11_83 (γ * Real.log 83) + bohmanExcess11_89 (γ * Real.log 89) + bohmanExcess11_97 (γ * Real.log 97) + bohmanExcess11_101 (γ * Real.log 101) + bohmanExcess11_103 (γ * Real.log 103) + bohmanExcess11_107 (γ * Real.log 107) + bohmanExcess11_109 (γ * Real.log 109) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (bohmanExcess11_2_nonneg γ) (bohmanExcess11_7_nonneg γ)) (bohmanExcess11_11_nonneg γ)) (bohmanExcess11_13_nonneg γ)) (bohmanExcess11_17_nonneg γ)) (bohmanExcess11_19_nonneg γ)) (bohmanExcess11_23_nonneg γ)) (bohmanExcess11_29_nonneg γ)) (bohmanExcess11_31_nonneg γ)) (bohmanExcess11_37_nonneg γ)) (bohmanExcess11_41_nonneg γ)) (bohmanExcess11_43_nonneg γ)) (bohmanExcess11_47_nonneg γ)) (bohmanExcess11_53_nonneg γ)) (bohmanExcess11_59_nonneg γ)) (bohmanExcess11_61_nonneg γ)) (bohmanExcess11_67_nonneg γ)) (bohmanExcess11_71_nonneg γ)) (bohmanExcess11_73_nonneg γ)) (bohmanExcess11_79_nonneg γ)) (bohmanExcess11_83_nonneg γ)) (bohmanExcess11_89_nonneg γ)) (bohmanExcess11_97_nonneg γ)) (bohmanExcess11_101_nonneg γ)) (bohmanExcess11_103_nonneg γ)) (bohmanExcess11_107_nonneg γ)) (bohmanExcess11_109_nonneg γ))
  have hu_0 : 0.4686 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift11 (g_lo := 182.40625) (g_hi := 184) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.083) 32 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.355 ≤ bohmanExcess11_3 (γ * Real.log 3) := bohmanExcess11_3_ge (u_lo := 0.4686) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1668) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift11 (g_lo := 182.40625) (g_hi := 184) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.7383) 47 (by norm_num) hlo hhi (by norm_num) sharp_log_prime_5.1 sharp_log_prime_5.2 (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.15835 ≤ bohmanExcess11_5 (γ * Real.log 5) := bohmanExcess11_5_ge (u_lo := (-0.1668)) (by norm_num) hu_1 (by norm_num)
  have hgain_tot : 0.51335 ≤ bohmanExcess11_3 (γ * Real.log 3) + bohmanExcess11_5 (γ * Real.log 5) := (by norm_num : (0.51335 : ℝ) ≤ _).trans (add_le_add hg_0 hg_1)
  linarith only [harch, hmaster, hnn_rest, hgain_tot]

private theorem bohman11_coupled_lt_on_band {γ : ℝ} (hlo : 150 ≤ γ) (hhi : γ ≤ 184) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((11 / 2) ^ 2 * γ ^ 2) + 1200 / ((11 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm11 (fun p => γ * Real.log (p : ℝ)) < 2.495515 := by
  rcases le_or_gt γ 150.328125 with h0 | h0
  · exact bohman11_interval_0 hlo h0
  rcases le_or_gt γ 150.484375 with h1 | h1
  · exact bohman11_interval_1 h0.le h1
  rcases le_or_gt γ 150.625 with h2 | h2
  · exact bohman11_interval_2 h1.le h2
  rcases le_or_gt γ 150.84375 with h3 | h3
  · exact bohman11_interval_3 h2.le h3
  rcases le_or_gt γ 151.484375 with h4 | h4
  · exact bohman11_interval_4 h3.le h4
  rcases le_or_gt γ 153.125 with h5 | h5
  · exact bohman11_interval_5 h4.le h5
  rcases le_or_gt γ 155.953125 with h6 | h6
  · exact bohman11_interval_6 h5.le h6
  rcases le_or_gt γ 157 with h7 | h7
  · exact bohman11_interval_7 h6.le h7
  rcases le_or_gt γ 157.703125 with h8 | h8
  · exact bohman11_interval_8 h7.le h8
  rcases le_or_gt γ 158.375 with h9 | h9
  · exact bohman11_interval_9 h8.le h9
  rcases le_or_gt γ 159.046875 with h10 | h10
  · exact bohman11_interval_10 h9.le h10
  rcases le_or_gt γ 161.359375 with h11 | h11
  · exact bohman11_interval_11 h10.le h11
  rcases le_or_gt γ 162.546875 with h12 | h12
  · exact bohman11_interval_12 h11.le h12
  rcases le_or_gt γ 164.5625 with h13 | h13
  · exact bohman11_interval_13 h12.le h13
  rcases le_or_gt γ 165.953125 with h14 | h14
  · exact bohman11_interval_14 h13.le h14
  rcases le_or_gt γ 167.125 with h15 | h15
  · exact bohman11_interval_15 h14.le h15
  rcases le_or_gt γ 168.75 with h16 | h16
  · exact bohman11_interval_16 h15.le h16
  rcases le_or_gt γ 169.171875 with h17 | h17
  · exact bohman11_interval_17 h16.le h17
  rcases le_or_gt γ 169.28125 with h18 | h18
  · exact bohman11_interval_18 h17.le h18
  rcases le_or_gt γ 169.34375 with h19 | h19
  · exact bohman11_interval_19 h18.le h19
  rcases le_or_gt γ 169.375 with h20 | h20
  · exact bohman11_interval_20 h19.le h20
  rcases le_or_gt γ 169.40625 with h21 | h21
  · exact bohman11_interval_21 h20.le h21
  rcases le_or_gt γ 169.4375 with h22 | h22
  · exact bohman11_interval_22 h21.le h22
  rcases le_or_gt γ 169.453125 with h23 | h23
  · exact bohman11_interval_23 h22.le h23
  rcases le_or_gt γ 169.46875 with h24 | h24
  · exact bohman11_interval_24 h23.le h24
  rcases le_or_gt γ 169.484375 with h25 | h25
  · exact bohman11_interval_25 h24.le h25
  rcases le_or_gt γ 169.515625 with h26 | h26
  · exact bohman11_interval_26 h25.le h26
  rcases le_or_gt γ 169.546875 with h27 | h27
  · exact bohman11_interval_27 h26.le h27
  rcases le_or_gt γ 169.59375 with h28 | h28
  · exact bohman11_interval_28 h27.le h28
  rcases le_or_gt γ 169.6875 with h29 | h29
  · exact bohman11_interval_29 h28.le h29
  rcases le_or_gt γ 169.9375 with h30 | h30
  · exact bohman11_interval_30 h29.le h30
  rcases le_or_gt γ 171.140625 with h31 | h31
  · exact bohman11_interval_31 h30.le h31
  rcases le_or_gt γ 173.5625 with h32 | h32
  · exact bohman11_interval_32 h31.le h32
  rcases le_or_gt γ 174.4375 with h33 | h33
  · exact bohman11_interval_33 h32.le h33
  rcases le_or_gt γ 175.140625 with h34 | h34
  · exact bohman11_interval_34 h33.le h34
  rcases le_or_gt γ 176.375 with h35 | h35
  · exact bohman11_interval_35 h34.le h35
  rcases le_or_gt γ 178.25 with h36 | h36
  · exact bohman11_interval_36 h35.le h36
  rcases le_or_gt γ 179.015625 with h37 | h37
  · exact bohman11_interval_37 h36.le h37
  rcases le_or_gt γ 180.328125 with h38 | h38
  · exact bohman11_interval_38 h37.le h38
  rcases le_or_gt γ 182.40625 with h39 | h39
  · exact bohman11_interval_39 h38.le h39
  exact bohman11_interval_40 h39.le hhi

/-- **The Riemann hypothesis through height `184` via bandwidth-`11/2` prime-phase-coupled Bohman analysis.**
Every zero of `ξ` in the critical strip with `0 < Im ρ ≤ 184` lies on `Re ρ = 1/2`, proved without
locating any zero or computing any value of `ζ`. -/
theorem rhVerifiedThrough_oneHundredEightyFour : RHVerifiedThrough 184 := by
  intro ρ hzero hre0 hre1 him0 him184
  rcases le_or_gt ρ.im 150 with hle | hgt
  · exact rhVerifiedThrough_oneHundredFifty hzero hre0 hre1 him0 hle
  · by_contra hoff
    let rhoSupport : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy := by
      have hpos := xi_divisor_pos_on_support rhoSupport
      have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by omega
      exact ⟨rhoSupport, ⟨0, hn⟩⟩
    have hqre : (q.1 : ℂ).re ≠ 1 / 2 := hoff
    have hqim : (q.1 : ℂ).im = ρ.im := rfl
    have hLγ : 4 * Real.pi < (11 / 2) * ρ.im := by
      have := Real.pi_lt_four; linarith only [this, hgt]
    have hb := bohman_budget_at_edge (L := 11 / 2) (N := 245) (by norm_num)
      (fun _ hn => eleven_halves_le_log hn) q hqre hqim (by linarith only [hgt]) hLγ
    rw [bohman11_prime_sum_eq_phaseForm] at hb
    have hleft := bohman11_budget_left_bounds.1
    have hstrict := bohman11_coupled_lt_on_band hgt.le him184
    linarith only [hb, hleft, hstrict]

/-! ## Exact coupled real-height saturation at `γ = 185` (`L = 11/2`) -/

private theorem mul_cos_le_ub11 {c ub θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ ub) :
    c * Real.cos θ ≤ ub := by
    have := Real.cos_le_one θ; nlinarith only [this, hc0, hc]

private theorem bohman11_sat185_chunk0 :
    Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) * Real.cos ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ)) +
      Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) * Real.cos (2 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) * Real.cos (3 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) * Real.cos (4 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) * Real.cos (5 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) * Real.cos (6 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) * Real.cos (7 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) +
      Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) * Real.cos ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ)) +
      Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) * Real.cos (2 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) +
      Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) * Real.cos (3 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ (-0.4025537) := by
  have hcu_0 : Real.cos ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ)) ≤ (-0.84) := by rw [show ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ)) = 185 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.5732) 20 (by norm_num) (by simpa only [Nat.cast_ofNat] using Real.log_two_gt_d9.le) (by simpa only [Nat.cast_ofNat] using Real.log_two_lt_d9.le) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_0 : Real.log 2 / 2 * bohmanFn (11 / 2) (1 * Real.log 2) * Real.cos ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ)) ≤ (-0.26902) := by nlinarith only [cb11_2_1.1, hcu_0]
  have hcu_1 : Real.cos (2 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.4123 := by rw [show (2 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 370 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 370) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.9956) 40 (by norm_num) (by simpa only [Nat.cast_ofNat] using Real.log_two_gt_d9.le) (by simpa only [Nat.cast_ofNat] using Real.log_two_lt_d9.le) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_1 : Real.log 2 / 4 * bohmanFn (11 / 2) (2 * Real.log 2) * Real.cos (2 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.053731 := by nlinarith only [cb11_2_2.1, cb11_2_2.2, hcu_1]
  have hcu_2 : Real.cos (3 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.1482 := by rw [show (3 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 555 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 555) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.7194) 61 (by norm_num) (by simpa only [Nat.cast_ofNat] using Real.log_two_gt_d9.le) (by simpa only [Nat.cast_ofNat] using Real.log_two_lt_d9.le) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_2 : Real.log 2 / 8 * bohmanFn (11 / 2) (3 * Real.log 2) * Real.cos (3 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.006777 := by nlinarith only [cb11_2_3.1, cb11_2_3.2, hcu_2]
  have hcu_3 : Real.cos (4 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.6602) := by rw [show (4 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 740 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 740) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.8495) 81 (by norm_num) (by simpa only [Nat.cast_ofNat] using Real.log_two_gt_d9.le) (by simpa only [Nat.cast_ofNat] using Real.log_two_lt_d9.le) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_3 : Real.log 2 / 16 * bohmanFn (11 / 2) (4 * Real.log 2) * Real.cos (4 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.008918) := by nlinarith only [cb11_2_4.1, hcu_3]
  have ht_4 : Real.log 2 / 32 * bohmanFn (11 / 2) (5 * Real.log 2) * Real.cos (5 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.0031419 := mul_cos_le_ub11 (by linarith only [cb11_2_5.1]) cb11_2_5.2
  have hcu_5 : Real.cos (6 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.9561) := by rw [show (6 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 1110 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 1110) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.297) 122 (by norm_num) (by simpa only [Nat.cast_ofNat] using Real.log_two_gt_d9.le) (by simpa only [Nat.cast_ofNat] using Real.log_two_lt_d9.le) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_5 : Real.log 2 / 64 * bohmanFn (11 / 2) (6 * Real.log 2) * Real.cos (6 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.000464) := by nlinarith only [cb11_2_6.1, hcu_5]
  have ht_6 : Real.log 2 / 128 * bohmanFn (11 / 2) (7 * Real.log 2) * Real.cos (7 * ((185 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.0000289 := mul_cos_le_ub11 (by linarith only [cb11_2_7.1]) cb11_2_7.2
  have hcu_7 : Real.cos ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ)) ≤ (-0.573) := by rw [show ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ)) = 185 * Real.log ((3 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((3 : ℕ) : ℝ)) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (s_hi := 0.9604) 32 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_3.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_3.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_7 : Real.log 3 / 3 * bohmanFn (11 / 2) (1 * Real.log 3) * Real.cos ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ)) ≤ (-0.174739) := by nlinarith only [cb11_3_1.1, hcu_7]
  have hcu_8 : Real.cos (2 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ (-0.3421) := by rw [show (2 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) = 370 * Real.log ((3 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 370) (lp := Real.log ((3 : ℕ) : ℝ)) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (s_hi := 1.2215) 64 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_3.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_3.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_8 : Real.log 3 / 9 * bohmanFn (11 / 2) (2 * Real.log 3) * Real.cos (2 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ (-0.020417) := by nlinarith only [cb11_3_2.1, hcu_8]
  have ht_9 : Real.log 3 / 27 * bohmanFn (11 / 2) (3 * Real.log 3) * Real.cos (3 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ 0.0073255 := mul_cos_le_ub11 (by linarith only [cb11_3_3.1]) cb11_3_3.2
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_0 ht_1) ht_2) ht_3) ht_4) ht_5) ht_6) ht_7) ht_8) ht_9).trans (by norm_num)

private theorem bohman11_sat185_chunk1 :
    Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) * Real.cos (4 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) +
      Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) * Real.cos (5 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) +
      Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) * Real.cos ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ)) +
      Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) * Real.cos (2 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) +
      Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) * Real.cos (3 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) +
      Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) * Real.cos ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ)) +
      Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) * Real.cos (2 * ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ))) +
      Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) * Real.cos ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ)) +
      Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) * Real.cos (2 * ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ))) +
      Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) * Real.cos ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ)) ≤ (-0.3576355) := by
  have ht_10 : Real.log 3 / 81 * bohmanFn (11 / 2) (4 * Real.log 3) * Real.cos (4 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ 0.0003483 := mul_cos_le_ub11 (by linarith only [cb11_3_4.1]) cb11_3_4.2
  have ht_11 : Real.log 3 / 243 * bohmanFn (11 / 2) (5 * Real.log 3) * Real.cos (5 * ((185 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ 0.0000002 := mul_cos_le_ub11 (by linarith only [cb11_3_5.1]) cb11_3_5.2
  have hcu_12 : Real.cos ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ)) ≤ (-0.7612) := by rw [show ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ)) = 185 * Real.log ((5 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((5 : ℕ) : ℝ)) (lp_lo := 1.6094379) (lp_hi := 1.609438) (s_hi := 0.7054) 47 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_5.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_5.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_12 : Real.log 5 / 5 * bohmanFn (11 / 2) (1 * Real.log 5) * Real.cos ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ)) ≤ (-0.16699) := by nlinarith only [cb11_5_1.1, hcu_12]
  have hcu_13 : Real.cos (2 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) ≤ 0.1599 := by rw [show (2 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) = 370 * Real.log ((5 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 370) (lp := Real.log ((5 : ℕ) : ℝ)) (lp_lo := 1.6094379) (lp_hi := 1.609438) (s_hi := 1.7312) 94 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_5.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_5.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_13 : Real.log 5 / 25 * bohmanFn (11 / 2) (2 * Real.log 5) * Real.cos (2 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) ≤ 0.002032 := by nlinarith only [cb11_5_2.1, cb11_5_2.2, hcu_13]
  have ht_14 : Real.log 5 / 125 * bohmanFn (11 / 2) (3 * Real.log 5) * Real.cos (3 * ((185 : ℝ) * Real.log ((5 : ℕ) : ℝ))) ≤ 0.0000762 := mul_cos_le_ub11 (by linarith only [cb11_5_3.1]) cb11_5_3.2
  have hcu_15 : Real.cos ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ)) ≤ (-0.2767) := by rw [show ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ)) = 185 * Real.log ((7 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((7 : ℕ) : ℝ)) (lp_lo := 1.945908) (lp_hi := 1.9459107) (s_hi := 1.2903) 57 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_7.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_7.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_15 : Real.log 7 / 7 * bohmanFn (11 / 2) (1 * Real.log 7) * Real.cos ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ)) ≤ (-0.043966) := by nlinarith only [cb11_7_1.1, hcu_15]
  have hcu_16 : Real.cos (2 * ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ))) ≤ (-0.8458) := by rw [show (2 * ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ))) = 370 * Real.log ((7 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 370) (lp := Real.log ((7 : ℕ) : ℝ)) (lp_lo := 1.945908) (lp_hi := 1.9459107) (s_hi := 0.5624) 114 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_7.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_7.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_16 : Real.log 7 / 49 * bohmanFn (11 / 2) (2 * Real.log 7) * Real.cos (2 * ((185 : ℝ) * Real.log ((7 : ℕ) : ℝ))) ≤ (-0.002535) := by nlinarith only [cb11_7_2.1, hcu_16]
  have hcu_17 : Real.cos ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ)) ≤ (-0.7982) := by rw [show ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ)) = 185 * Real.log ((11 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((11 : ℕ) : ℝ)) (lp_lo := 2.3978951) (lp_hi := 2.3978957) (s_hi := 0.6463) 70 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_11.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_11.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_17 : Real.log 11 / 11 * bohmanFn (11 / 2) (1 * Real.log 11) * Real.cos ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ)) ≤ (-0.073865) := by nlinarith only [cb11_11_1.1, hcu_17]
  have ht_18 : Real.log 11 / 121 * bohmanFn (11 / 2) (2 * Real.log 11) * Real.cos (2 * ((185 : ℝ) * Real.log ((11 : ℕ) : ℝ))) ≤ 0.0001348 := mul_cos_le_ub11 (by linarith only [cb11_11_2.1]) cb11_11_2.2
  have hcu_19 : Real.cos ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ)) ≤ (-0.9907) := by rw [show ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ)) = 185 * Real.log ((13 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((13 : ℕ) : ℝ)) (lp_lo := 2.5649481) (lp_hi := 2.56495) (s_hi := 0.1354) 75 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_13.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_13.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_19 : Real.log 13 / 13 * bohmanFn (11 / 2) (1 * Real.log 13) * Real.cos ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ)) ≤ (-0.072871) := by nlinarith only [cb11_13_1.1, hcu_19]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_10 ht_11) ht_12) ht_13) ht_14) ht_15) ht_16) ht_17) ht_18) ht_19).trans (by norm_num)

private theorem bohman11_sat185_chunk2 :
    Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) * Real.cos (2 * ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ))) +
      Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) * Real.cos ((185 : ℝ) * Real.log ((17 : ℕ) : ℝ)) +
      Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) * Real.cos ((185 : ℝ) * Real.log ((19 : ℕ) : ℝ)) +
      Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) * Real.cos ((185 : ℝ) * Real.log ((23 : ℕ) : ℝ)) +
      Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) * Real.cos ((185 : ℝ) * Real.log ((29 : ℕ) : ℝ)) +
      Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) * Real.cos ((185 : ℝ) * Real.log ((31 : ℕ) : ℝ)) +
      Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) * Real.cos ((185 : ℝ) * Real.log ((37 : ℕ) : ℝ)) +
      Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) * Real.cos ((185 : ℝ) * Real.log ((41 : ℕ) : ℝ)) +
      Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) * Real.cos ((185 : ℝ) * Real.log ((43 : ℕ) : ℝ)) +
      Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) * Real.cos ((185 : ℝ) * Real.log ((47 : ℕ) : ℝ)) ≤ (-0.0593567) := by
  have ht_20 : Real.log 13 / 169 * bohmanFn (11 / 2) (2 * Real.log 13) * Real.cos (2 * ((185 : ℝ) * Real.log ((13 : ℕ) : ℝ))) ≤ 0.0000153 := mul_cos_le_ub11 (by linarith only [cb11_13_2.1]) cb11_13_2.2
  have hcu_21 : Real.cos ((185 : ℝ) * Real.log ((17 : ℕ) : ℝ)) ≤ (-0.8766) := by rw [show ((185 : ℝ) * Real.log ((17 : ℕ) : ℝ)) = 185 * Real.log ((17 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((17 : ℕ) : ℝ)) (lp_lo := 2.8332129) (lp_hi := 2.8332146) (s_hi := 0.5017) 83 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_17.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_17.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_21 : Real.log 17 / 17 * bohmanFn (11 / 2) (1 * Real.log 17) * Real.cos ((185 : ℝ) * Real.log ((17 : ℕ) : ℝ)) ≤ (-0.043082) := by nlinarith only [cb11_17_1.1, hcu_21]
  have hcu_22 : Real.cos ((185 : ℝ) * Real.log ((19 : ℕ) : ℝ)) ≤ (-0.3379) := by rw [show ((185 : ℝ) * Real.log ((19 : ℕ) : ℝ)) = 185 * Real.log ((19 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((19 : ℕ) : ℝ)) (lp_lo := 2.9444389) (lp_hi := 2.9444391) (s_hi := 1.2259) 86 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_19.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_19.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_22 : Real.log 19 / 19 * bohmanFn (11 / 2) (1 * Real.log 19) * Real.cos ((185 : ℝ) * Real.log ((19 : ℕ) : ℝ)) ≤ (-0.013867) := by nlinarith only [cb11_19_1.1, hcu_22]
  have hcu_23 : Real.cos ((185 : ℝ) * Real.log ((23 : ℕ) : ℝ)) ≤ (-0.428) := by rw [show ((185 : ℝ) * Real.log ((23 : ℕ) : ℝ)) = 185 * Real.log ((23 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((23 : ℕ) : ℝ)) (lp_lo := 3.135494) (lp_hi := 3.1354949) (s_hi := 1.1284) 92 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_23.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_23.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_23 : Real.log 23 / 23 * bohmanFn (11 / 2) (1 * Real.log 23) * Real.cos ((185 : ℝ) * Real.log ((23 : ℕ) : ℝ)) ≤ (-0.012644) := by nlinarith only [cb11_23_1.1, hcu_23]
  have hcu_24 : Real.cos ((185 : ℝ) * Real.log ((29 : ℕ) : ℝ)) ≤ 0.6106 := by rw [show ((185 : ℝ) * Real.log ((29 : ℕ) : ℝ)) = 185 * Real.log ((29 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((29 : ℕ) : ℝ)) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (s_hi := 2.2274) 99 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_29.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_29.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_24 : Real.log 29 / 29 * bohmanFn (11 / 2) (1 * Real.log 29) * Real.cos ((185 : ℝ) * Real.log ((29 : ℕ) : ℝ)) ≤ 0.011687 := by nlinarith only [cb11_29_1.1, cb11_29_1.2, hcu_24]
  have hcu_25 : Real.cos ((185 : ℝ) * Real.log ((31 : ℕ) : ℝ)) ≤ 0.7742 := by rw [show ((185 : ℝ) * Real.log ((31 : ℕ) : ℝ)) = 185 * Real.log ((31 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((31 : ℕ) : ℝ)) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (s_hi := 2.4558) 101 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_31.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_31.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_25 : Real.log 31 / 31 * bohmanFn (11 / 2) (1 * Real.log 31) * Real.cos ((185 : ℝ) * Real.log ((31 : ℕ) : ℝ)) ≤ 0.012975 := by nlinarith only [cb11_31_1.1, cb11_31_1.2, hcu_25]
  have hcu_26 : Real.cos ((185 : ℝ) * Real.log ((37 : ℕ) : ℝ)) ≤ (-0.4178) := by rw [show ((185 : ℝ) * Real.log ((37 : ℕ) : ℝ)) = 185 * Real.log ((37 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((37 : ℕ) : ℝ)) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (s_hi := 1.1396) 106 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_37.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_37.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_26 : Real.log 37 / 37 * bohmanFn (11 / 2) (1 * Real.log 37) * Real.cos ((185 : ℝ) * Real.log ((37 : ℕ) : ℝ)) ≤ (-0.004827) := by nlinarith only [cb11_37_1.1, hcu_26]
  have hcu_27 : Real.cos ((185 : ℝ) * Real.log ((41 : ℕ) : ℝ)) ≤ (-0.5414) := by rw [show ((185 : ℝ) * Real.log ((41 : ℕ) : ℝ)) = 185 * Real.log ((41 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((41 : ℕ) : ℝ)) (lp_lo := 3.7135697) (lp_hi := 3.7135733) (s_hi := 0.9985) 109 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_41.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_41.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_27 : Real.log 41 / 41 * bohmanFn (11 / 2) (1 * Real.log 41) * Real.cos ((185 : ℝ) * Real.log ((41 : ℕ) : ℝ)) ≤ (-0.004972) := by nlinarith only [cb11_41_1.1, hcu_27]
  have hcu_28 : Real.cos ((185 : ℝ) * Real.log ((43 : ℕ) : ℝ)) ≤ (-0.0402) := by rw [show ((185 : ℝ) * Real.log ((43 : ℕ) : ℝ)) = 185 * Real.log ((43 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((43 : ℕ) : ℝ)) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (s_hi := 1.5304) 110 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_43.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_43.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_28 : Real.log 43 / 43 * bohmanFn (11 / 2) (1 * Real.log 43) * Real.cos ((185 : ℝ) * Real.log ((43 : ℕ) : ℝ)) ≤ (-0.000329) := by nlinarith only [cb11_43_1.1, hcu_28]
  have hcu_29 : Real.cos ((185 : ℝ) * Real.log ((47 : ℕ) : ℝ)) ≤ (-0.6489) := by rw [show ((185 : ℝ) * Real.log ((47 : ℕ) : ℝ)) = 185 * Real.log ((47 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((47 : ℕ) : ℝ)) (lp_lo := 3.8501474) (lp_hi := 3.8501483) (s_hi := 0.8644) 113 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_47.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_47.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_29 : Real.log 47 / 47 * bohmanFn (11 / 2) (1 * Real.log 47) * Real.cos ((185 : ℝ) * Real.log ((47 : ℕ) : ℝ)) ≤ (-0.004313) := by nlinarith only [cb11_47_1.1, hcu_29]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_20 ht_21) ht_22) ht_23) ht_24) ht_25) ht_26) ht_27) ht_28) ht_29).trans (by norm_num)

private theorem bohman11_sat185_chunk3 :
    Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) * Real.cos ((185 : ℝ) * Real.log ((53 : ℕ) : ℝ)) +
      Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) * Real.cos ((185 : ℝ) * Real.log ((59 : ℕ) : ℝ)) +
      Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) * Real.cos ((185 : ℝ) * Real.log ((61 : ℕ) : ℝ)) +
      Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) * Real.cos ((185 : ℝ) * Real.log ((67 : ℕ) : ℝ)) +
      Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) * Real.cos ((185 : ℝ) * Real.log ((71 : ℕ) : ℝ)) +
      Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) * Real.cos ((185 : ℝ) * Real.log ((73 : ℕ) : ℝ)) +
      Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) * Real.cos ((185 : ℝ) * Real.log ((79 : ℕ) : ℝ)) +
      Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) * Real.cos ((185 : ℝ) * Real.log ((83 : ℕ) : ℝ)) +
      Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) * Real.cos ((185 : ℝ) * Real.log ((89 : ℕ) : ℝ)) +
      Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) * Real.cos ((185 : ℝ) * Real.log ((97 : ℕ) : ℝ)) ≤ 0.0108881 := by
  have ht_30 : Real.log 53 / 53 * bohmanFn (11 / 2) (1 * Real.log 53) * Real.cos ((185 : ℝ) * Real.log ((53 : ℕ) : ℝ)) ≤ 0.0049085 := mul_cos_le_ub11 (by linarith only [cb11_53_1.1]) cb11_53_1.2
  have ht_31 : Real.log 59 / 59 * bohmanFn (11 / 2) (1 * Real.log 59) * Real.cos ((185 : ℝ) * Real.log ((59 : ℕ) : ℝ)) ≤ 0.0036799 := mul_cos_le_ub11 (by linarith only [cb11_59_1.1]) cb11_59_1.2
  have ht_32 : Real.log 61 / 61 * bohmanFn (11 / 2) (1 * Real.log 61) * Real.cos ((185 : ℝ) * Real.log ((61 : ℕ) : ℝ)) ≤ 0.0033524 := mul_cos_le_ub11 (by linarith only [cb11_61_1.1]) cb11_61_1.2
  have hcu_33 : Real.cos ((185 : ℝ) * Real.log ((67 : ℕ) : ℝ)) ≤ 0.3187 := by rw [show ((185 : ℝ) * Real.log ((67 : ℕ) : ℝ)) = 185 * Real.log ((67 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((67 : ℕ) : ℝ)) (lp_lo := 4.2046904) (lp_hi := 4.2046933) (s_hi := 1.895) 123 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_67.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_67.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_33 : Real.log 67 / 67 * bohmanFn (11 / 2) (1 * Real.log 67) * Real.cos ((185 : ℝ) * Real.log ((67 : ℕ) : ℝ)) ≤ 0.000815 := by nlinarith only [cb11_67_1.1, cb11_67_1.2, hcu_33]
  have hcu_34 : Real.cos ((185 : ℝ) * Real.log ((71 : ℕ) : ℝ)) ≤ (-0.9983) := by rw [show ((185 : ℝ) * Real.log ((71 : ℕ) : ℝ)) = 185 * Real.log ((71 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((71 : ℕ) : ℝ)) (lp_lo := 4.2626794) (lp_hi := 4.2626812) (s_hi := 0.0564) 125 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_71.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_71.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_34 : Real.log 71 / 71 * bohmanFn (11 / 2) (1 * Real.log 71) * Real.cos ((185 : ℝ) * Real.log ((71 : ℕ) : ℝ)) ≤ (-0.002133) := by nlinarith only [cb11_71_1.1, hcu_34]
  have hcu_35 : Real.cos ((185 : ℝ) * Real.log ((73 : ℕ) : ℝ)) ≤ (-0.4639) := by rw [show ((185 : ℝ) * Real.log ((73 : ℕ) : ℝ)) = 185 * Real.log ((73 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((73 : ℕ) : ℝ)) (lp_lo := 4.290459) (lp_hi := 4.2904607) (s_hi := 1.0882) 126 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_73.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_73.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_35 : Real.log 73 / 73 * bohmanFn (11 / 2) (1 * Real.log 73) * Real.cos ((185 : ℝ) * Real.log ((73 : ℕ) : ℝ)) ≤ (-0.000908) := by nlinarith only [cb11_73_1.1, hcu_35]
  have hcu_36 : Real.cos ((185 : ℝ) * Real.log ((79 : ℕ) : ℝ)) ≤ (-0.5744) := by rw [show ((185 : ℝ) * Real.log ((79 : ℕ) : ℝ)) = 185 * Real.log ((79 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((79 : ℕ) : ℝ)) (lp_lo := 4.3694478) (lp_hi := 4.369448) (s_hi := 0.9587) 128 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_79.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_79.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_36 : Real.log 79 / 79 * bohmanFn (11 / 2) (1 * Real.log 79) * Real.cos ((185 : ℝ) * Real.log ((79 : ℕ) : ℝ)) ≤ (-0.000869) := by nlinarith only [cb11_79_1.1, hcu_36]
  have ht_37 : Real.log 83 / 83 * bohmanFn (11 / 2) (1 * Real.log 83) * Real.cos ((185 : ℝ) * Real.log ((83 : ℕ) : ℝ)) ≤ 0.0012805 := mul_cos_le_ub11 (by linarith only [cb11_83_1.1]) cb11_83_1.2
  have ht_38 : Real.log 89 / 89 * bohmanFn (11 / 2) (1 * Real.log 89) * Real.cos ((185 : ℝ) * Real.log ((89 : ℕ) : ℝ)) ≤ 0.0009978 := mul_cos_le_ub11 (by linarith only [cb11_89_1.1]) cb11_89_1.2
  have hcu_39 : Real.cos ((185 : ℝ) * Real.log ((97 : ℕ) : ℝ)) ≤ (-0.3308) := by rw [show ((185 : ℝ) * Real.log ((97 : ℕ) : ℝ)) = 185 * Real.log ((97 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((97 : ℕ) : ℝ)) (lp_lo := 4.5747066) (lp_hi := 4.5747121) (s_hi := 1.2335) 134 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_97.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_97.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_39 : Real.log 97 / 97 * bohmanFn (11 / 2) (1 * Real.log 97) * Real.cos ((185 : ℝ) * Real.log ((97 : ℕ) : ℝ)) ≤ (-0.000236) := by nlinarith only [cb11_97_1.1, hcu_39]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_30 ht_31) ht_32) ht_33) ht_34) ht_35) ht_36) ht_37) ht_38) ht_39).trans (by norm_num)

private theorem bohman11_sat185_chunk4 :
    Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) * Real.cos ((185 : ℝ) * Real.log ((101 : ℕ) : ℝ)) +
      Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) * Real.cos ((185 : ℝ) * Real.log ((103 : ℕ) : ℝ)) +
      Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) * Real.cos ((185 : ℝ) * Real.log ((107 : ℕ) : ℝ)) +
      Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) * Real.cos ((185 : ℝ) * Real.log ((109 : ℕ) : ℝ)) +
      Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) * Real.cos ((185 : ℝ) * Real.log ((113 : ℕ) : ℝ)) +
      Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) * Real.cos ((185 : ℝ) * Real.log ((127 : ℕ) : ℝ)) +
      Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) * Real.cos ((185 : ℝ) * Real.log ((131 : ℕ) : ℝ)) +
      Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) * Real.cos ((185 : ℝ) * Real.log ((137 : ℕ) : ℝ)) +
      Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) * Real.cos ((185 : ℝ) * Real.log ((139 : ℕ) : ℝ)) +
      Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) * Real.cos ((185 : ℝ) * Real.log ((149 : ℕ) : ℝ)) ≤ 0.0020884 := by
  have ht_40 : Real.log 101 / 101 * bohmanFn (11 / 2) (1 * Real.log 101) * Real.cos ((185 : ℝ) * Real.log ((101 : ℕ) : ℝ)) ≤ 0.0006104 := mul_cos_le_ub11 (by linarith only [cb11_101_1.1]) cb11_101_1.2
  have hcu_41 : Real.cos ((185 : ℝ) * Real.log ((103 : ℕ) : ℝ)) ≤ (-0.9734) := by rw [show ((185 : ℝ) * Real.log ((103 : ℕ) : ℝ)) = 185 * Real.log ((103 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift11 (c := 185) (lp := Real.log ((103 : ℕ) : ℝ)) (lp_lo := 4.6347266) (lp_hi := 4.6347303) (s_hi := 0.2305) 136 (by norm_num) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_103.1) (by simpa only [Nat.cast_ofNat] using sharp_log_prime_103.2) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_41 : Real.log 103 / 103 * bohmanFn (11 / 2) (1 * Real.log 103) * Real.cos ((185 : ℝ) * Real.log ((103 : ℕ) : ℝ)) ≤ (-0.000546) := by nlinarith only [cb11_103_1.1, hcu_41]
  have ht_42 : Real.log 107 / 107 * bohmanFn (11 / 2) (1 * Real.log 107) * Real.cos ((185 : ℝ) * Real.log ((107 : ℕ) : ℝ)) ≤ 0.0004781 := mul_cos_le_ub11 (by linarith only [cb11_107_1.1]) cb11_107_1.2
  have ht_43 : Real.log 109 / 109 * bohmanFn (11 / 2) (1 * Real.log 109) * Real.cos ((185 : ℝ) * Real.log ((109 : ℕ) : ℝ)) ≤ 0.0004407 := mul_cos_le_ub11 (by linarith only [cb11_109_1.1]) cb11_109_1.2
  have ht_44 : Real.log 113 / 113 * bohmanFn (11 / 2) (1 * Real.log 113) * Real.cos ((185 : ℝ) * Real.log ((113 : ℕ) : ℝ)) ≤ 0.0003743 := mul_cos_le_ub11 (by linarith only [cb11_113_1.1]) cb11_113_1.2
  have ht_45 : Real.log 127 / 127 * bohmanFn (11 / 2) (1 * Real.log 127) * Real.cos ((185 : ℝ) * Real.log ((127 : ℕ) : ℝ)) ≤ 0.0002099 := mul_cos_le_ub11 (by linarith only [cb11_127_1.1]) cb11_127_1.2
  have ht_46 : Real.log 131 / 131 * bohmanFn (11 / 2) (1 * Real.log 131) * Real.cos ((185 : ℝ) * Real.log ((131 : ℕ) : ℝ)) ≤ 0.0001774 := mul_cos_le_ub11 (by linarith only [cb11_131_1.1]) cb11_131_1.2
  have ht_47 : Real.log 137 / 137 * bohmanFn (11 / 2) (1 * Real.log 137) * Real.cos ((185 : ℝ) * Real.log ((137 : ℕ) : ℝ)) ≤ 0.0001372 := mul_cos_le_ub11 (by linarith only [cb11_137_1.1]) cb11_137_1.2
  have ht_48 : Real.log 139 / 139 * bohmanFn (11 / 2) (1 * Real.log 139) * Real.cos ((185 : ℝ) * Real.log ((139 : ℕ) : ℝ)) ≤ 0.0001258 := mul_cos_le_ub11 (by linarith only [cb11_139_1.1]) cb11_139_1.2
  have ht_49 : Real.log 149 / 149 * bohmanFn (11 / 2) (1 * Real.log 149) * Real.cos ((185 : ℝ) * Real.log ((149 : ℕ) : ℝ)) ≤ 0.0000806 := mul_cos_le_ub11 (by linarith only [cb11_149_1.1]) cb11_149_1.2
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_40 ht_41) ht_42) ht_43) ht_44) ht_45) ht_46) ht_47) ht_48) ht_49).trans (by norm_num)

private theorem bohman11_sat185_chunk5 :
    Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) * Real.cos ((185 : ℝ) * Real.log ((151 : ℕ) : ℝ)) +
      Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) * Real.cos ((185 : ℝ) * Real.log ((157 : ℕ) : ℝ)) +
      Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) * Real.cos ((185 : ℝ) * Real.log ((163 : ℕ) : ℝ)) +
      Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) * Real.cos ((185 : ℝ) * Real.log ((167 : ℕ) : ℝ)) +
      Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) * Real.cos ((185 : ℝ) * Real.log ((173 : ℕ) : ℝ)) +
      Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) * Real.cos ((185 : ℝ) * Real.log ((179 : ℕ) : ℝ)) +
      Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) * Real.cos ((185 : ℝ) * Real.log ((181 : ℕ) : ℝ)) +
      Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) * Real.cos ((185 : ℝ) * Real.log ((191 : ℕ) : ℝ)) +
      Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) * Real.cos ((185 : ℝ) * Real.log ((193 : ℕ) : ℝ)) +
      Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) * Real.cos ((185 : ℝ) * Real.log ((197 : ℕ) : ℝ)) ≤ 0.0002832 := by
  have ht_50 : Real.log 151 / 151 * bohmanFn (11 / 2) (1 * Real.log 151) * Real.cos ((185 : ℝ) * Real.log ((151 : ℕ) : ℝ)) ≤ 0.0000735 := mul_cos_le_ub11 (by linarith only [cb11_151_1.1]) cb11_151_1.2
  have ht_51 : Real.log 157 / 157 * bohmanFn (11 / 2) (1 * Real.log 157) * Real.cos ((185 : ℝ) * Real.log ((157 : ℕ) : ℝ)) ≤ 0.0000554 := mul_cos_le_ub11 (by linarith only [cb11_157_1.1]) cb11_157_1.2
  have ht_52 : Real.log 163 / 163 * bohmanFn (11 / 2) (1 * Real.log 163) * Real.cos ((185 : ℝ) * Real.log ((163 : ℕ) : ℝ)) ≤ 0.0000414 := mul_cos_le_ub11 (by linarith only [cb11_163_1.1]) cb11_163_1.2
  have ht_53 : Real.log 167 / 167 * bohmanFn (11 / 2) (1 * Real.log 167) * Real.cos ((185 : ℝ) * Real.log ((167 : ℕ) : ℝ)) ≤ 0.0000338 := mul_cos_le_ub11 (by linarith only [cb11_167_1.1]) cb11_167_1.2
  have ht_54 : Real.log 173 / 173 * bohmanFn (11 / 2) (1 * Real.log 173) * Real.cos ((185 : ℝ) * Real.log ((173 : ℕ) : ℝ)) ≤ 0.0000246 := mul_cos_le_ub11 (by linarith only [cb11_173_1.1]) cb11_173_1.2
  have ht_55 : Real.log 179 / 179 * bohmanFn (11 / 2) (1 * Real.log 179) * Real.cos ((185 : ℝ) * Real.log ((179 : ℕ) : ℝ)) ≤ 0.0000176 := mul_cos_le_ub11 (by linarith only [cb11_179_1.1]) cb11_179_1.2
  have ht_56 : Real.log 181 / 181 * bohmanFn (11 / 2) (1 * Real.log 181) * Real.cos ((185 : ℝ) * Real.log ((181 : ℕ) : ℝ)) ≤ 0.0000157 := mul_cos_le_ub11 (by linarith only [cb11_181_1.1]) cb11_181_1.2
  have ht_57 : Real.log 191 / 191 * bohmanFn (11 / 2) (1 * Real.log 191) * Real.cos ((185 : ℝ) * Real.log ((191 : ℕ) : ℝ)) ≤ 0.0000084 := mul_cos_le_ub11 (by linarith only [cb11_191_1.1]) cb11_191_1.2
  have ht_58 : Real.log 193 / 193 * bohmanFn (11 / 2) (1 * Real.log 193) * Real.cos ((185 : ℝ) * Real.log ((193 : ℕ) : ℝ)) ≤ 0.0000073 := mul_cos_le_ub11 (by linarith only [cb11_193_1.1]) cb11_193_1.2
  have ht_59 : Real.log 197 / 197 * bohmanFn (11 / 2) (1 * Real.log 197) * Real.cos ((185 : ℝ) * Real.log ((197 : ℕ) : ℝ)) ≤ 0.0000055 := mul_cos_le_ub11 (by linarith only [cb11_197_1.1]) cb11_197_1.2
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_50 ht_51) ht_52) ht_53) ht_54) ht_55) ht_56) ht_57) ht_58) ht_59).trans (by norm_num)

private theorem bohman11_sat185_chunk6 :
    Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) * Real.cos ((185 : ℝ) * Real.log ((199 : ℕ) : ℝ)) +
      Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) * Real.cos ((185 : ℝ) * Real.log ((211 : ℕ) : ℝ)) +
      Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) * Real.cos ((185 : ℝ) * Real.log ((223 : ℕ) : ℝ)) +
      Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) * Real.cos ((185 : ℝ) * Real.log ((227 : ℕ) : ℝ)) +
      Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) * Real.cos ((185 : ℝ) * Real.log ((229 : ℕ) : ℝ)) +
      Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) * Real.cos ((185 : ℝ) * Real.log ((233 : ℕ) : ℝ)) +
      Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) * Real.cos ((185 : ℝ) * Real.log ((239 : ℕ) : ℝ)) +
      Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) * Real.cos ((185 : ℝ) * Real.log ((241 : ℕ) : ℝ)) ≤ 0.0000083 := by
  have ht_60 : Real.log 199 / 199 * bohmanFn (11 / 2) (1 * Real.log 199) * Real.cos ((185 : ℝ) * Real.log ((199 : ℕ) : ℝ)) ≤ 0.0000048 := mul_cos_le_ub11 (by linarith only [cb11_199_1.1]) cb11_199_1.2
  have ht_61 : Real.log 211 / 211 * bohmanFn (11 / 2) (1 * Real.log 211) * Real.cos ((185 : ℝ) * Real.log ((211 : ℕ) : ℝ)) ≤ 0.0000018 := mul_cos_le_ub11 (by linarith only [cb11_211_1.1]) cb11_211_1.2
  have ht_62 : Real.log 223 / 223 * bohmanFn (11 / 2) (1 * Real.log 223) * Real.cos ((185 : ℝ) * Real.log ((223 : ℕ) : ℝ)) ≤ 0.0000005 := mul_cos_le_ub11 (by linarith only [cb11_223_1.1]) cb11_223_1.2
  have ht_63 : Real.log 227 / 227 * bohmanFn (11 / 2) (1 * Real.log 227) * Real.cos ((185 : ℝ) * Real.log ((227 : ℕ) : ℝ)) ≤ 0.0000003 := mul_cos_le_ub11 (by linarith only [cb11_227_1.1]) cb11_227_1.2
  have ht_64 : Real.log 229 / 229 * bohmanFn (11 / 2) (1 * Real.log 229) * Real.cos ((185 : ℝ) * Real.log ((229 : ℕ) : ℝ)) ≤ 0.0000003 := mul_cos_le_ub11 (by linarith only [cb11_229_1.1]) cb11_229_1.2
  have ht_65 : Real.log 233 / 233 * bohmanFn (11 / 2) (1 * Real.log 233) * Real.cos ((185 : ℝ) * Real.log ((233 : ℕ) : ℝ)) ≤ 0.0000002 := mul_cos_le_ub11 (by linarith only [cb11_233_1.1]) cb11_233_1.2
  have ht_66 : Real.log 239 / 239 * bohmanFn (11 / 2) (1 * Real.log 239) * Real.cos ((185 : ℝ) * Real.log ((239 : ℕ) : ℝ)) ≤ 0.0000002 := mul_cos_le_ub11 (by linarith only [cb11_239_1.1]) cb11_239_1.2
  have ht_67 : Real.log 241 / 241 * bohmanFn (11 / 2) (1 * Real.log 241) * Real.cos ((185 : ℝ) * Real.log ((241 : ℕ) : ℝ)) ≤ 0.0000002 := mul_cos_le_ub11 (by linarith only [cb11_241_1.1]) cb11_241_1.2
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht_60 ht_61) ht_62) ht_63) ht_64) ht_65) ht_66) ht_67).trans (by norm_num)

/-- **Exact coupled real-height saturation at `γ = 185` (`L = 11/2`).**
Evaluating at the coupled real height `γ = 185` strictly reverses the `L = 11/2` Bohman
explicit-formula inequality even without the positive `O(1/1215 + 1/γ²)` archimedean terms,
proving `184` is the exact integer ceiling of the coupled `L = 11/2` Bohman test. -/
theorem bohman_eleven_halves_coupled_saturates_at_oneHundredEightyFive :
    4 * (11 / 2) ^ 2 / ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (11 / 2) * (1 + Real.exp (-(11 / 2 / 2))) /
          ((11 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 <
      1 / 4 * Real.log (9 / 4 + 185 ^ 2 / 4) - Real.log Real.pi / 2 -
        ∑ n ∈ Finset.range 245,
          vonMangoldt n / n * bohmanFn (11 / 2) (Real.log n) * Real.cos (185 * Real.log n) := by
  rw [bohman11_prime_sum_eq_phaseForm]
  have hleft_ub := bohman11_budget_left_bounds.2
  have hlog_rev : (0 : ℝ) * 0.6931471803 + (5 : ℝ) * 1.0986121 +
      (1 : ℝ) * 1.6094379 + (1 : ℝ) * 1.945908 +
      (214 / 34234 : ℝ) ≤ Real.log (9 / 4 + (185 : ℝ) ^ 2 / 4) := by
    obtain ⟨hM_lo, -⟩ := log_smooth_bounds11 (M := 8505) (a2 := 0) (b3 := 5) (c5 := 1) (d7 := 1) (by norm_num) sharp_log_prime_3.1 sharp_log_prime_3.2 sharp_log_prime_5.1 sharp_log_prime_5.2 sharp_log_prime_7.1 sharp_log_prime_7.2
    have heq : (9 / 4 + (185 : ℝ) ^ 2 / 4) = (8505 : ℝ) * (34234 / 34020) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num)]
    have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 34020 / 34234 by norm_num)
    have hinv_eq : Real.log (34234 / 34020 : ℝ) = -Real.log (34020 / 34234) := by
      rw [← Real.log_inv]; norm_num
    rw [hinv_eq]; norm_num at hinv ⊢; linarith only [hM_lo, hinv]
  have hlog_pi_ub : Real.log Real.pi ≤ 38 / 23 * 0.6931471808 := by
    have hpow : Real.pi ^ 23 ≤ (2 : ℝ) ^ 38 :=
      (pow_le_pow_left₀ Real.pi_pos.le pi_bounds_d10_11.2.le 23).trans (by norm_num)
    have h := log_le_of_pow_le_two_pow11 Real.pi_pos (k := 23) (m := 38) (by norm_num) hpow
    have hl2b := Real.log_two_lt_d9.le
    norm_num at h ⊢; linarith only [h, hl2b]
  have hsum_rev : bohmanPhaseForm11 (fun p => (185 : ℝ) * Real.log (p : ℝ)) ≤ (-0.8062779) := by
    unfold bohmanPhaseForm11
    linarith only [bohman11_sat185_chunk0, bohman11_sat185_chunk1, bohman11_sat185_chunk2, bohman11_sat185_chunk3, bohman11_sat185_chunk4, bohman11_sat185_chunk5, bohman11_sat185_chunk6]
  linarith only [hleft_ub, hlog_rev, hlog_pi_ub, hsum_rev]

/-! ## Upgraded Pólya frequency, slice, Li, and Jensen rungs at height `184` -/

/-- At verified height `184`, the Taylor coefficients of `ξ` at the centre form a `PF_551` sequence
(upgraded from `PF_449` at height `150`). -/
theorem xi_centre_pfSeq_fiveHundredFiftyOne :
    PFSeq 551 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_rhVerifiedThrough (T := 184) (by norm_num)
    rhVerifiedThrough_oneHundredEightyFour (by norm_num) (by norm_num)

/-- Every Taylor coefficient of `ξ(1/2 + x + i t) ξ(1/2 - x + i t)` is nonnegative on `|t| ≤ 367/2`
(upgraded from `|t| ≤ 299/2` at height `150`). -/
theorem xiSliceCoeff_nonneg_of_abs_le_threeHundredSixtySeven_halves {t : ℝ} (ht : |t| ≤ 367 / 2)
    (n : ℕ) : 0 ≤ xiSliceCoeff t n :=
  xiSliceCoeff_nonneg_of_rhVerifiedThrough (T := 184) (t := t) (by linarith only [ht])
    rhVerifiedThrough_oneHundredEightyFour n

/-- The Li coefficients satisfy `Re(2 λ_n) ≥ 0` for all `n ≤ 864` (upgraded from `n ≤ 705` at
height `150`). -/
theorem re_xiLiPaired_nonneg_of_le_eightHundredSixtyFour {n : ℕ} (hn : n ≤ 864) :
    0 ≤ (xiLiPaired n).re := by
  have hn' : (n : ℝ) ≤ 864 := by exact_mod_cast hn
  exact re_xiLiPaired_nonneg_of_rhVerifiedThrough (T := 184) (by norm_num)
    rhVerifiedThrough_oneHundredEightyFour (by linarith only [hn'])

/-- Exact largest Jensen degree paid by width `8999/24000` at coupled Bohman verified height `184`. -/
theorem jensen_sector_at_oneHundredEightyFour_iff (d : ℕ) :
    ((d : ℝ) - 1) * (8999 / 24000 : ℝ) ^ 2 ≤ 184 ^ 2 ↔ d ≤ 240808 := by
  constructor
  · intro h
    by_contra! hd
    have hn : 240809 ≤ d := by omega
    have h' : (240809 : ℝ) ≤ d := by exact_mod_cast hn
    norm_num at h ⊢
    linarith
  · intro h
    have h' : (d : ℝ) ≤ 240808 := by exact_mod_cast h
    norm_num
    linarith

/-- Unshifted `Ξ` Jensen polynomials have only real zeros through degree `240,808` (upgraded from
`160,036` at height `150`). -/
theorem jensenNonrealCount_eq_zero_through_240808 (d : Fin 240809) :
    jensenNonrealCount d.val = 0 := by
  apply jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width (T := 184) (by norm_num)
    rhVerifiedThrough_oneHundredEightyFour
  have h := (jensen_sector_at_oneHundredEightyFour_iff d).2 (by omega)
  rcases le_or_gt ((d.val : ℝ) - 1) 0 with hd | hd
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg _)).trans (sq_nonneg _)
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ _root_.GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
        zetaZeroWidth_le_8999_div_24000 2) hd.le).trans h

/-- All positive-integer Euler root filters preserve real-rootedness of `xiJensenReal` through
degree `240,808` (upgraded from `160,036`). -/
theorem weightedXiJensen_splits_through_240808 (w : List ℕ) (d : Fin 240809) :
    (eulerWord w (xiJensenReal d.val)).Splits := by
  have h := weightedXiJensen_nonreal_le w d
  rw [jensenNonrealCount_eq_zero_through_240808 d, nonrealRootCount] at h
  have hc := Polynomial.card_roots' (eulerWord w (xiJensenReal d))
  rw [splits_iff_card_roots]
  omega

#print axioms rhVerifiedThrough_oneHundredEightyFour
#print axioms bohman_eleven_halves_coupled_saturates_at_oneHundredEightyFive
#print axioms xi_centre_pfSeq_fiveHundredFiftyOne
#print axioms xiSliceCoeff_nonneg_of_abs_le_threeHundredSixtySeven_halves
#print axioms re_xiLiPaired_nonneg_of_le_eightHundredSixtyFour
#print axioms jensenNonrealCount_eq_zero_through_240808
#print axioms weightedXiJensen_splits_through_240808

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
