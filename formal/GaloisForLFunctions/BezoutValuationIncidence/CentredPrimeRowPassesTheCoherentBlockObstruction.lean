import GaloisForLFunctions.BezoutValuationIncidence.BlockEquidistributionSufficesForCrossScaleDispersion
import GaloisForLFunctions.RHTower.PrimeShortIntervalsHuxleyAsymptotic

/-!
# The centred prime row passes the coherent-block obstruction below the quadratic horizon

The Type-II no-go of the pronic prime Gram (`CoherentPrimeBlocksAndTheTypeIIWindowNoGo`) stops
every `ℓ²` coefficient class at the cross-scale exponent `θ = 1`; its replacement hypothesis is
block equidistribution of the large-scale row at the scale `H = o(P/log² P)` of the small moduli
(`BlockEquidistributionSufficesForCrossScaleDispersion`). This module shows that the **actual
centred prime row** `c'(n) = Λ(n) − 1` on a window `[A, A + KH) ⊆ [Q, 2Q]` satisfies that
hypothesis unconditionally, through Huxley's prime number theorem in short intervals, in the
whole regime `P^{1+δ} ≤ Q ≤ P^{12/7 − δ}`, that is at every cross-scale exponent
`θ = 2 log P/log Q` with `7/6 < θ < 2`.

* `eventually_abs_psi_window_sub_le`: Huxley's theorem uniformly in the window length,
  `|ψ(x + h) − ψ(x) − h| ≤ ε h` for every `x^α ≤ h ≤ x/2`, `7/12 < α < 1`, and all large `x`.
  The two-sided window bounds of `ChebyshevShortWindowUpperBound` and
  `ChebyshevShortWindowLowerBound` hold for every `h`; their zero sums are monotone in the
  parameter, and `c x²/(h·(h/M)) ≤ cM x^{2(1−α)}`, whose weighted zero sum tends to `0` below
  the exponent `5/12` by the `12/5` zero-density theorem.
* `abs_sum_centredPrimeRow_block_le`: a block `[a, a + H)` of the centred prime row has
  `|Σ (Λ(n) − 1)/n²| ≤ (H/a²)(ε + 6H/a)`: the leading part is the short-interval count
  `ψ(a − 1 + H) − ψ(a − 1) − H`, the rest the variation of `1/n²` across the block.
* `one_div_twelve_le_abs_vonMangoldt_sub_one`: `|Λ(n) − 1| ≥ 1/12` for every `n` (`Λ(n)` is `0`,
  `log 2 ≤ 11/12` or `≥ log 3 ≥ 13/12`), so the row has mass `S₀ ≥ KH/(48Q²)` and the block
  discrepancy satisfies `Δ_H ≤ 96 ε S₀`.
* `exists_abs_rowBilinear_centredPrimeRow_le`: for every row `c` on `(P, 2P]`, every window at
  scale `Q` with blocks of length `(2Q)^α ≤ H ≤ 4Q^α` and horizon `N`, once
  `H h_N²/2 + 1/8 ≤ εP` and `3P ≤ 2εQ`,

  `|B + m R' + β H'| ≤ 16 ε S₀ Σ_d |c(d)| d`:

  the cross-scale remainder is `16ε` times the rank-two remainder bound `2K_c S₀`.

Below the quadratic horizon the coherent blocks therefore obstruct only sign-blind coefficient
classes: the prime row itself, read against any small-scale row, has cross-scale dispersion of
rank-two quality at every exponent `θ < 2`. What remains for the receiver is the balanced regime
`Q ≍ P`, where the cubic tail `Σ_d |c(d)| d² Σ_n |c'(n)|/n³` is itself of rank-two size.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Huxley's theorem uniformly in the window length -/

/-- The weighted zero sum is monotone in its parameter. -/
theorem zeroShortWeight_le_of_param_le {x Y Y' : ℝ} (hx : 0 ≤ x) (hYY : Y ≤ Y') (ρ : ℂ) :
    zeroShortWeight x Y ρ ≤ zeroShortWeight x Y' ρ := by
  unfold zeroShortWeight
  refine mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) (Real.rpow_nonneg hx _)
  exact div_le_div_of_nonneg_right hYY (by positivity)

/-- `c x²/(h (h/M)) ≤ c M x^{2(1−α)}` when `x^α ≤ h`. -/
theorem param_le_of_rpow_le {x h M c α : ℝ} (hx : 0 < x) (hM : 0 < M) (hc : 0 ≤ c)
    (hh : x ^ α ≤ h) :
    c * x ^ 2 / (h * (h / M)) ≤ c * M * x ^ (2 * (1 - α)) := by
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hh0 : 0 < h := lt_of_lt_of_le hxα hh
  have hx2 : x ^ (2 * (1 - α)) = x ^ 2 / (x ^ α * x ^ α) := by
    rw [show 2 * (1 - α) = (2 : ℝ) - (α + α) by ring, Real.rpow_sub hx, Real.rpow_add hx,
      Real.rpow_two]
  have hrew : c * x ^ 2 / (h * (h / M)) = c * M * (x ^ 2 / (h * h)) := by
    rw [← mul_div_assoc, div_div_eq_mul_div]; ring
  rw [hx2, hrew]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul hh hh hxα.le hh0.le)

/-- **Huxley's theorem uniformly in the window length.** For `7/12 < α < 1` and `ε > 0`, for all
large `x` and every `x^α ≤ h ≤ x/2`: `|ψ(x + h) − ψ(x) − h| ≤ ε h`. -/
theorem eventually_abs_psi_window_sub_le {α ε : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x ^ α ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h := by
  obtain ⟨M, hM8, hM4⟩ : ∃ M : ℕ, 8 / ε ≤ M ∧ 4 ≤ M := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max (8 / ε) 4)
    exact ⟨M, (le_max_left _ _).trans hM, by exact_mod_cast (le_max_right _ _).trans hM⟩
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM4
  have hM0 : (0 : ℝ) < M := by linarith
  have hMε : 2 / (M : ℝ) ≤ ε / 4 := by
    rw [div_le_iff₀ hM0]
    rw [div_le_iff₀ hε] at hM8
    linarith
  have hu : 0 < 1 - α := by linarith
  have hu' : 1 - α < 5 / 12 := by linarith
  have hzero := tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 8 * M) hu hu'
    (by linarith)
  have hz := hzero.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 32 by positivity))
  filter_upwards [hz, eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (16 * M / ε)]
    with x hzx hx4 hxM
  intro h hh1 hh2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hxα1 : 1 ≤ x ^ α := Real.one_le_rpow hx1 (by linarith)
  have hh0 : 0 < h := lt_of_lt_of_le hxα hh1
  have hh1' : 1 ≤ h := hxα1.trans hh1
  have hh' : 0 < h / M := div_pos hh0 hM0
  have h2h' : 2 * (h / M) ≤ h := by
    rw [← mul_div_assoc, div_le_iff₀ hM0]; nlinarith
  -- the two explicit error terms are at most `(ε/4) h`
  have hE1 : 2 * (h / M) ≤ ε / 4 * h := by
    have : 2 * (h / M) = h * (2 / M) := by ring
    rw [this]
    calc h * (2 / M) ≤ h * (ε / 4) := mul_le_mul_of_nonneg_left hMε hh0.le
      _ = ε / 4 * h := by ring
  have hE2 : 4 / (x * (h / M)) ≤ ε / 4 * h := by
    have hxM' : 16 * M ≤ ε * x := by rw [div_le_iff₀ hε] at hxM; linarith
    have hhh : 1 ≤ h * h := by nlinarith
    have heq : ε / 4 * h * (x * (h / M)) = ε * x * (h * h) / (4 * M) := by
      field_simp
    rw [div_le_iff₀ (by positivity), heq, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hhh (by positivity : (0 : ℝ) ≤ ε * x)]
  -- both zero sums are dominated by the one with parameter `8 M x^{2(1−α)}`
  have hS : ∀ c : ℝ, 0 ≤ c → c ≤ 8 →
      ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ 2 / (h * (h / M))) (q.1 : ℂ) ≤ ε / 32 := by
    intro c hc hc8
    refine le_trans ?_ hzx.le
    refine Summable.tsum_le_tsum (fun q => zeroShortWeight_le_of_param_le hx0.le ?_ _)
      (summable_zeroShortWeight hx1 (by positivity)) (summable_zeroShortWeight hx1 (by positivity))
    calc c * x ^ 2 / (h * (h / M)) ≤ c * M * x ^ (2 * (1 - α)) :=
          param_le_of_rpow_le hx0 hM0 hc hh1
      _ ≤ 8 * M * x ^ (2 * (1 - α)) := by
          have hp := Real.rpow_nonneg hx0.le (2 * (1 - α))
          have : c * M ≤ 8 * M := mul_le_mul_of_nonneg_right hc8 hM0.le
          exact mul_le_mul_of_nonneg_right this hp
  have hup := psi_window_le_add_zeroShortWeight hx4 hh' h2h' hh2
  have hlo := psi_window_ge_sub_zeroShortWeight (by linarith : (2 : ℝ) ≤ x) hh' h2h' (by linarith)
  have hS4 := mul_le_mul_of_nonneg_left (hS 4 (by norm_num) (by norm_num))
    (by positivity : (0 : ℝ) ≤ 8 * h)
  have hS8 := mul_le_mul_of_nonneg_left (hS 8 (by norm_num) (by norm_num))
    (by positivity : (0 : ℝ) ≤ 2 * h)
  rw [abs_le]
  constructor <;> nlinarith

/-! ## §2. One block of the centred prime row -/

/-- The sum of `Λ` over `[a, a + H)` is a difference of `ψ` at `a − 1 + H` and `a − 1`. -/
theorem sum_Ico_vonMangoldt_eq_psi_sub {a H : ℕ} (ha : 1 ≤ a) :
    ∑ n ∈ Ico a (a + H), vonMangoldt n =
      Chebyshev.psi (((a - 1 : ℕ) : ℝ) + H) - Chebyshev.psi ((a - 1 : ℕ) : ℝ) := by
  have h1 : (((a - 1 : ℕ) : ℝ) + H) = ((a - 1 + H : ℕ) : ℝ) := by push_cast; ring
  rw [h1]
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, Nat.floor_natCast,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (a - 1)) (Nat.le_add_right (a - 1) H),
    add_sub_cancel_left]
  congr 1
  ext n
  simp only [mem_Ioc, mem_Ico]
  omega

/-- `1/a² − 1/n² ≤ 2H/a³` for `a ≤ n < a + H`. -/
theorem inv_sq_sub_inv_sq_le {a n H : ℕ} (ha : 1 ≤ a) (han : a ≤ n) (hnH : n < a + H) :
    1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2 ≤ 2 * H / (a : ℝ) ^ 3 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have hnHR : (n : ℝ) ≤ a + H := by exact_mod_cast hnH.le
  have ha0 : (0 : ℝ) < a := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have h3 : ((n : ℝ) ^ 2 - a ^ 2) * a ≤ 2 * H * n ^ 2 := by
    have e : ((n : ℝ) ^ 2 - a ^ 2) * a = ((n - a) * (n + a)) * a := by ring
    rw [e]
    have hHR : (n : ℝ) - a ≤ H := by linarith
    calc ((n : ℝ) - a) * (n + a) * a ≤ H * (2 * n) * n :=
          mul_le_mul (mul_le_mul hHR (by linarith) (by positivity) (by positivity)) hanR ha0.le
            (by positivity)
      _ = 2 * H * n ^ 2 := by ring
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg (a : ℝ))]

/-- **A block of the centred prime row.** If the short-interval count on `[a, a + H)` has error
`≤ εH` and is at most `2H`, then `|Σ_{a ≤ n < a+H} (Λ(n) − 1)/n²| ≤ (H/a²)(ε + 6H/a)`. -/
theorem abs_sum_centredPrimeRow_block_le {a H : ℕ} (ha : 1 ≤ a) {ε : ℝ}
    (hψ : |Chebyshev.psi (((a - 1 : ℕ) : ℝ) + H) - Chebyshev.psi ((a - 1 : ℕ) : ℝ) - H| ≤ ε * H)
    (hψ2 : Chebyshev.psi (((a - 1 : ℕ) : ℝ) + H) - Chebyshev.psi ((a - 1 : ℕ) : ℝ) ≤ 2 * H) :
    |∑ n ∈ Ico a (a + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤
      (H : ℝ) / (a : ℝ) ^ 2 * (ε + 6 * H / a) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hsum := sum_Ico_vonMangoldt_eq_psi_sub (H := H) ha
  have hsplit : ∑ n ∈ Ico a (a + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2 =
      (∑ n ∈ Ico a (a + H), (vonMangoldt n - 1)) / (a : ℝ) ^ 2 -
        ∑ n ∈ Ico a (a + H), (vonMangoldt n - 1) * (1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2) := by
    rw [sum_div, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  have hcard : ∑ n ∈ Ico a (a + H), (1 : ℝ) = H := by
    rw [sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one]
  have hfirst : |(∑ n ∈ Ico a (a + H), (vonMangoldt n - 1)) / (a : ℝ) ^ 2| ≤
      ε * H / (a : ℝ) ^ 2 := by
    rw [sum_sub_distrib, hcard, hsum, abs_div, abs_of_pos (pow_pos ha0 2)]
    exact div_le_div_of_nonneg_right hψ (pow_pos ha0 2).le
  have hsecond : |∑ n ∈ Ico a (a + H), (vonMangoldt n - 1) * (1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2)| ≤
      6 * H ^ 2 / (a : ℝ) ^ 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ n ∈ Ico a (a + H),
        |(vonMangoldt n - 1) * (1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2)| ≤
          (vonMangoldt n + 1) * (2 * H / (a : ℝ) ^ 3) := by
      intro n hn
      rw [mem_Ico] at hn
      have hanR : (a : ℝ) ≤ n := by exact_mod_cast hn.1
      have hdiff : 0 ≤ 1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2 := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by positivity) (by gcongr)
      rw [abs_mul, abs_of_nonneg hdiff]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have h1 : |vonMangoldt n - 1| ≤ vonMangoldt n + 1 := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul h1 (inv_sq_sub_inv_sq_le ha hn.1 hn.2) hdiff (by linarith)
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul, sum_add_distrib, hcard, hsum]
    have h0 : (0 : ℝ) ≤ 2 * H / (a : ℝ) ^ 3 := by positivity
    calc (Chebyshev.psi (((a - 1 : ℕ) : ℝ) + H) - Chebyshev.psi ((a - 1 : ℕ) : ℝ) + H) *
          (2 * H / (a : ℝ) ^ 3)
        ≤ (2 * H + H) * (2 * H / (a : ℝ) ^ 3) := by gcongr
      _ = 6 * H ^ 2 / (a : ℝ) ^ 3 := by ring
  rw [hsplit]
  calc |(∑ n ∈ Ico a (a + H), (vonMangoldt n - 1)) / (a : ℝ) ^ 2 -
        ∑ n ∈ Ico a (a + H), (vonMangoldt n - 1) * (1 / (a : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2)|
      ≤ ε * H / (a : ℝ) ^ 2 + 6 * H ^ 2 / (a : ℝ) ^ 3 :=
        (abs_sub _ _).trans (add_le_add hfirst hsecond)
    _ = (H : ℝ) / (a : ℝ) ^ 2 * (ε + 6 * H / a) := by
        field_simp

/-! ## §3. The mass of the centred prime row -/

/-- `|Λ(n) − 1| ≥ 1/12` for every `n`: `Λ(n)` is `0`, `log 2 ≤ 11/12`, or `log p ≥ log 3 ≥ 13/12`. -/
theorem one_div_twelve_le_abs_vonMangoldt_sub_one (n : ℕ) : 1 / 12 ≤ |vonMangoldt n - 1| := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  split_ifs with hpp
  · have hp : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
    have h2 : 2 ≤ n.minFac := hp.two_le
    rcases Nat.lt_or_ge n.minFac 3 with h3 | h3
    · have h2' : n.minFac = 2 := by omega
      rw [h2', Nat.cast_ofNat]
      have := Real.log_two_lt_d9
      exact le_abs.mpr (Or.inr (by linarith))
    · have hp3 : (3 : ℝ) ≤ n.minFac := by exact_mod_cast h3
      have hlog3 : (13 : ℝ) / 12 ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 12) ≤ 1 / (1 - 1 / 12) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
        have h3 : Real.exp (13 / 12) = Real.exp 1 * Real.exp (1 / 12) := by
          rw [← Real.exp_add]; norm_num
        rw [h3]
        calc Real.exp 1 * Real.exp (1 / 12) ≤ 2.7182818286 * (1 / (1 - 1 / 12)) :=
              mul_le_mul h1.le h2 (Real.exp_pos _).le (by norm_num)
          _ ≤ 3 := by norm_num
      have : (13 : ℝ) / 12 ≤ Real.log n.minFac :=
        hlog3.trans (Real.log_le_log (by norm_num) hp3)
      exact le_abs.mpr (Or.inl (by linarith))
  · norm_num

/-! ## §4. The centred prime row on a window and its cross-scale remainder -/

/-- The centred prime row `Λ(n) − 1` on the window `[A, A + KH)`. -/
def centredPrimeRow (A H K : ℕ) (n : ℕ) : ℝ :=
  if n ∈ Ico A (A + K * H) then vonMangoldt n - 1 else 0

theorem centredPrimeRow_support {A H K n : ℕ} (h : centredPrimeRow A H K n ≠ 0) :
    n ∈ Ico A (A + K * H) := by
  by_contra hn
  exact h (by simp [centredPrimeRow, hn])

theorem centredPrimeRow_of_mem {A H K n : ℕ} (h : n ∈ Ico A (A + K * H)) :
    centredPrimeRow A H K n = vonMangoldt n - 1 := by
  simp [centredPrimeRow, h]

/-- The blocks of the window lie in the window. -/
theorem Ico_block_subset {A H K m : ℕ} (hm : m < K) :
    Ico (A + m * H) (A + m * H + H) ⊆ Ico A (A + K * H) := by
  have h1 : m * H + H ≤ K * H := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right H hm
  intro n hn
  rw [mem_Ico] at hn ⊢
  omega

/-- **The block discrepancy of the centred prime row.** If every block satisfies
`|Σ_{block} (Λ(n) − 1)/n²| ≤ 2εH/Q²`, then `Δ_H ≤ 2εKH/Q²`. -/
theorem blockDiscrepancy_centredPrimeRow_le {A H K Q : ℕ} {ε : ℝ}
    (hblock : ∀ m < K, |∑ n ∈ Ico (A + m * H) (A + m * H + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤
      2 * ε * H / (Q : ℝ) ^ 2) :
    blockDiscrepancy (centredPrimeRow A H K) A H K ≤ 2 * ε * K * H / (Q : ℝ) ^ 2 := by
  unfold blockDiscrepancy
  have hrw : ∀ m ∈ range K,
      ∑ n ∈ Ico (A + m * H) (A + m * H + H), centredPrimeRow A H K n / (n : ℝ) ^ 2 =
        ∑ n ∈ Ico (A + m * H) (A + m * H + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2 := by
    intro m hm
    refine sum_congr rfl fun n hn => ?_
    rw [centredPrimeRow_of_mem (Ico_block_subset (mem_range.mp hm) hn)]
  calc ∑ m ∈ range K, |∑ n ∈ Ico (A + m * H) (A + m * H + H),
          centredPrimeRow A H K n / (n : ℝ) ^ 2|
      = ∑ m ∈ range K, |∑ n ∈ Ico (A + m * H) (A + m * H + H),
          (vonMangoldt n - 1) / (n : ℝ) ^ 2| :=
        sum_congr rfl fun m hm => by rw [hrw m hm]
    _ ≤ ∑ m ∈ range K, 2 * ε * H / (Q : ℝ) ^ 2 :=
        sum_le_sum fun m hm => hblock m (mem_range.mp hm)
    _ = 2 * ε * K * H / (Q : ℝ) ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **The mass of the centred prime row.** On a window `[A, A + KH) ⊆ [1, N]` with `A + KH ≤ 2Q`,
`S₀ = Σ_{n ≤ N} |c'(n)|/n² ≥ KH/(48 Q²)`. -/
theorem mass_centredPrimeRow_ge {N A H K Q : ℕ} (hQ : 1 ≤ Q) (hA : Q ≤ A) (hAK : A + K * H ≤ 2 * Q)
    (hN : 2 * Q ≤ N) :
    (K : ℝ) * H / (48 * (Q : ℝ) ^ 2) ≤ ∑ n ∈ Icc 1 N, |centredPrimeRow A H K n| / (n : ℝ) ^ 2 := by
  have hsub : Ico A (A + K * H) ⊆ Icc 1 N := by
    intro n hn
    rw [mem_Ico] at hn
    rw [mem_Icc]
    omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc (K : ℝ) * H / (48 * (Q : ℝ) ^ 2)
      = ∑ n ∈ Ico A (A + K * H), (1 / 12) / (2 * (Q : ℝ)) ^ 2 := by
        rw [sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
        push_cast
        field_simp
        ring
    _ ≤ ∑ n ∈ Ico A (A + K * H), |centredPrimeRow A H K n| / (n : ℝ) ^ 2 := by
        refine sum_le_sum fun n hn => ?_
        rw [centredPrimeRow_of_mem hn]
        rw [mem_Ico] at hn
        have hn2 : (n : ℝ) ≤ 2 * Q := by exact_mod_cast (hn.2.le.trans hAK)
        have hn0 : (0 : ℝ) < n := by
          have : 1 ≤ n := le_trans hQ (hA.trans hn.1)
          exact_mod_cast this
        calc (1 / 12 : ℝ) / (2 * (Q : ℝ)) ^ 2 ≤ (1 / 12) / (n : ℝ) ^ 2 :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
          _ ≤ |vonMangoldt n - 1| / (n : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right (one_div_twelve_le_abs_vonMangoldt_sub_one n)
                (by positivity)
    _ ≤ ∑ n ∈ Icc 1 N, |centredPrimeRow A H K n| / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity

/-- One block of the window satisfies the short-interval prime number theorem with error `ε` once
`Q ≥ 100`, `Q − 1 ≥ X₀`, `(2Q)^α ≤ H` and `25H ≤ εQ`: then
`|Σ_{block} (Λ(n) − 1)/n²| ≤ 2εH/Q²`. -/
theorem abs_sum_block_le_of_window {α ε X₀ : ℝ} (hα0 : 0 ≤ α) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX₀ : ∀ b : ℝ, X₀ ≤ b → ∀ h : ℝ, b ^ α ≤ h → h ≤ b / 2 →
      |Chebyshev.psi (b + h) - Chebyshev.psi b - h| ≤ ε * h)
    {A H K Q : ℕ} (hA : Q ≤ A) (hAK : A + K * H ≤ 2 * Q) (hHnat : 1 ≤ H)
    (hq100 : (100 : ℝ) ≤ Q) (hqX : X₀ + 1 ≤ Q) (hH1 : (2 * (Q : ℝ)) ^ α ≤ H)
    (hHQ : 25 * (H : ℝ) ≤ ε * Q) {m : ℕ} (hm : m < K) :
    |∑ n ∈ Ico (A + m * H) (A + m * H + H), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤
      2 * ε * H / (Q : ℝ) ^ 2 := by
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, a = A + m * H := ⟨_, rfl⟩
  rw [← hadef]
  have hQ0 : (0 : ℝ) < Q := by linarith
  have h1 : m * H + H ≤ K * H := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right H hm
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) ≤ Q := by linarith
    have hQ1 : 1 ≤ Q := by exact_mod_cast this
    omega
  have haQ : Q ≤ a := by omega
  have haQR : (Q : ℝ) ≤ a := by exact_mod_cast haQ
  have ha2Q : a + H ≤ 2 * Q := by omega
  have ha2QR : (a : ℝ) + H ≤ 2 * Q := by exact_mod_cast ha2Q
  have hx : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha1, Nat.cast_one]
  have hH1' : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  have hxX : X₀ ≤ ((a - 1 : ℕ) : ℝ) := by rw [hx]; linarith
  have hxα : ((a - 1 : ℕ) : ℝ) ^ α ≤ H := by
    refine le_trans ?_ hH1
    exact Real.rpow_le_rpow (by rw [hx]; linarith) (by rw [hx]; linarith) hα0
  have hxh : (H : ℝ) ≤ ((a - 1 : ℕ) : ℝ) / 2 := by
    rw [hx]
    have : 25 * (H : ℝ) ≤ Q := by nlinarith
    linarith
  have hψ := hX₀ _ hxX H hxα hxh
  have hψ2 : Chebyshev.psi (((a - 1 : ℕ) : ℝ) + H) - Chebyshev.psi ((a - 1 : ℕ) : ℝ) ≤ 2 * H := by
    have := (abs_le.mp hψ).2
    nlinarith
  refine (abs_sum_centredPrimeRow_block_le ha1 hψ hψ2).trans ?_
  have haR0 : (0 : ℝ) < a := by linarith
  have h6 : 6 * (H : ℝ) / a ≤ ε := by
    rw [div_le_iff₀ haR0]
    nlinarith
  calc (H : ℝ) / (a : ℝ) ^ 2 * (ε + 6 * H / a) ≤ (H : ℝ) / (Q : ℝ) ^ 2 * (ε + ε) := by
        gcongr
    _ = 2 * ε * H / (Q : ℝ) ^ 2 := by ring

/-- The inverse-square mass `Σ_{n ≤ N} |c'(n)|/n²` of a row. -/
def rowInverseSquareMass (N : ℕ) (c' : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2

/-- The linear weight `Σ_{d ≤ N} |c(d)| d` of a row. -/
def rowLinearWeight (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ d ∈ Icc 1 N, |c d| * d

theorem rowInverseSquareMass_nonneg (N : ℕ) (c' : ℕ → ℝ) : 0 ≤ rowInverseSquareMass N c' :=
  sum_nonneg fun n _ => by positivity

theorem rowLinearWeight_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ rowLinearWeight N c :=
  sum_nonneg fun d _ => by positivity

/-- A row on `(P, 2P]`: `P Σ|c| ≤ Σ|c| d`. -/
theorem mul_sum_abs_le_rowLinearWeight {N P : ℕ} {c : ℕ → ℝ}
    (hc : ∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) :
    (P : ℝ) * ∑ d ∈ Icc 1 N, |c d| ≤ rowLinearWeight N c := by
  unfold rowLinearWeight
  rw [mul_sum]
  refine sum_le_sum fun d _ => ?_
  by_cases hd : c d = 0
  · simp [hd]
  · have hdR : (P : ℝ) ≤ d := by exact_mod_cast (hc d hd).1.le
    exact mul_comm (P : ℝ) |c d| ▸ mul_le_mul_of_nonneg_left hdR (abs_nonneg _)

/-- A row on `(P, 2P]`: `Σ|c| d² ≤ 2P Σ|c| d`. -/
theorem sum_abs_mul_sq_le_rowLinearWeight {N P : ℕ} {c : ℕ → ℝ}
    (hc : ∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) :
    ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤ 2 * P * rowLinearWeight N c := by
  unfold rowLinearWeight
  rw [mul_sum]
  refine sum_le_sum fun d _ => ?_
  by_cases hd : c d = 0
  · simp [hd]
  · have hdR : (d : ℝ) ≤ 2 * P := by exact_mod_cast (hc d hd).2
    have h0 : 0 ≤ |c d| * (d : ℝ) := by positivity
    calc |c d| * (d : ℝ) ^ 2 = |c d| * d * d := by ring
      _ ≤ |c d| * d * (2 * P) := mul_le_mul_of_nonneg_left hdR h0
      _ = 2 * P * (|c d| * d) := by ring

/-- A row supported above `Q`: `Q Σ|c'|/n³ ≤ Σ|c'|/n²`. -/
theorem mul_sum_abs_div_cube_le_rowInverseSquareMass {N Q : ℕ} {c' : ℕ → ℝ}
    (hc' : ∀ n, c' n ≠ 0 → Q ≤ n) :
    (Q : ℝ) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 ≤ rowInverseSquareMass N c' := by
  unfold rowInverseSquareMass
  rw [mul_sum]
  refine sum_le_sum fun n _ => ?_
  by_cases hn : c' n = 0
  · simp [hn]
  · rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast hc' n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h
    have heq : (Q : ℝ) * (|c' n| / (n : ℝ) ^ 3) = |c' n| / (n : ℝ) ^ 2 * (Q / n) := by
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hn0).mpr hnQ)

/-- The real-number assembly of the three terms of the block bound. -/
theorem assembly_le {X Δ S₀ Sc Sa Sq Sk h H P Q ε : ℝ} (hε : 0 < ε) (hS₀ : 0 ≤ S₀) (hSc : 0 ≤ Sc)
    (hΔ0 : 0 ≤ Δ) (hSa : 0 ≤ Sa) (hSk : 0 ≤ Sk)
    (hmain : X ≤ Real.pi ^ 2 / 72 * Δ * Sc + ((H * h ^ 2 / 2 + 1 / 8) * S₀) * Sa +
      (3 / 4 * Sq) * Sk)
    (hΔ : Δ ≤ 96 * ε * S₀) (hterm2 : H * h ^ 2 / 2 + 1 / 8 ≤ ε * P) (hS1 : P * Sa ≤ Sc)
    (hS2 : Sq ≤ 2 * P * Sc) (hS3 : Q * Sk ≤ S₀) (hterm3 : 3 * P ≤ 2 * ε * Q) :
    X ≤ 16 * ε * S₀ * Sc := by
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hT1 : Real.pi ^ 2 / 72 * Δ * Sc ≤ 14 * ε * S₀ * Sc := by
    have h1 : Δ * Sc ≤ 96 * ε * S₀ * Sc := mul_le_mul_of_nonneg_right hΔ hSc
    have h2 : 0 ≤ Δ * Sc := mul_nonneg hΔ0 hSc
    have h3 : Real.pi ^ 2 / 72 * (Δ * Sc) ≤ 10 / 72 * (96 * ε * S₀ * Sc) :=
      mul_le_mul (by linarith) h1 h2 (by norm_num)
    have h4 : 0 ≤ ε * S₀ * Sc := by positivity
    calc Real.pi ^ 2 / 72 * Δ * Sc = Real.pi ^ 2 / 72 * (Δ * Sc) := by ring
      _ ≤ 10 / 72 * (96 * ε * S₀ * Sc) := h3
      _ ≤ 14 * ε * S₀ * Sc := by linarith
  have hT2 : ((H * h ^ 2 / 2 + 1 / 8) * S₀) * Sa ≤ ε * S₀ * Sc := by
    calc ((H * h ^ 2 / 2 + 1 / 8) * S₀) * Sa ≤ ((ε * P) * S₀) * Sa :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hterm2 hS₀) hSa
      _ = ε * S₀ * (P * Sa) := by ring
      _ ≤ ε * S₀ * Sc := mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hT3 : (3 / 4 * Sq) * Sk ≤ ε * S₀ * Sc := by
    have h1 : 3 * P * Sk ≤ 2 * ε * S₀ := by
      calc 3 * P * Sk ≤ 2 * ε * Q * Sk := mul_le_mul_of_nonneg_right hterm3 hSk
        _ = 2 * ε * (Q * Sk) := by ring
        _ ≤ 2 * ε * S₀ := mul_le_mul_of_nonneg_left hS3 (by positivity)
    calc (3 / 4 * Sq) * Sk ≤ (3 / 4 * (2 * P * Sc)) * Sk :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS2 (by norm_num)) hSk
      _ = 1 / 2 * Sc * (3 * P * Sk) := by ring
      _ ≤ 1 / 2 * Sc * (2 * ε * S₀) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε * S₀ * Sc := by ring
  linarith

/-- **The centred prime row passes the coherent-block obstruction.** For `7/12 < α < 1` and
`0 < ε ≤ 1` there is a scale `Q₀` such that for every window `[A, A + KH) ⊆ [Q, 2Q]` with
`Q ≥ Q₀`, blocks of length `(2Q)^α ≤ H ≤ 4Q^α`, horizon `N ≥ 2Q`, and every row `c` on `(P, 2P]`
with `H h_N²/2 + 1/8 ≤ εP` and `3P ≤ 2εQ`,

`|B + m R' + β H'| ≤ 16 ε S₀ Σ_d |c(d)| d`,

`S₀ = Σ_n |c'(n)|/n²` the inverse-square mass of the centred prime row: the cross-scale remainder
is `16ε` times the rank-two remainder bound. -/
theorem exists_abs_rowBilinear_centredPrimeRow_le {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ Q₀ : ℕ, ∀ {N A H K P Q : ℕ} {c : ℕ → ℝ}, Q₀ ≤ Q → Q ≤ A → A + K * H ≤ 2 * Q →
      2 * Q ≤ N → 1 ≤ P → (2 * (Q : ℝ)) ^ α ≤ H → (H : ℝ) ≤ 4 * (Q : ℝ) ^ α →
      (∀ d, c d ≠ 0 → P < d ∧ d ≤ 2 * P) →
      (H : ℝ) * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8 ≤ ε * P →
      3 * (P : ℝ) ≤ 2 * ε * Q →
      |rowBilinear N c (centredPrimeRow A H K) +
          rowMean N c * vonMangoldtReadout N (centredPrimeRow A H K) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeRow A H K)| ≤
        16 * ε * rowInverseSquareMass N (centredPrimeRow A H K) * rowLinearWeight N c := by
  -- the thresholds in `Q`: the uniform window theorem and `100 Q^α ≤ ε Q`
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_abs_psi_window_sub_le hα hα1 hε)
  have hev : ∀ᶠ q : ℝ in atTop, 100 / ε ≤ q ^ (1 - α) ∧ 100 ≤ q ∧ X₀ + 1 ≤ q :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - α)).eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and (eventually_ge_atTop _))
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨Q₀, ?_⟩
  intro N A H K P Q c hQ hA hAK hN hP hH1 hH2 hc hterm2 hterm3
  obtain ⟨hq1, hq100, hqX⟩ := hQ₀ Q hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : 1 ≤ Q := by exact_mod_cast (show (1 : ℝ) ≤ Q by linarith)
  have hQα : (Q : ℝ) ^ α * (Q : ℝ) ^ (1 - α) = Q := by
    rw [← Real.rpow_add hQ0, show α + (1 - α) = (1 : ℝ) by ring, Real.rpow_one]
  have hQα0 : 0 < (Q : ℝ) ^ α := Real.rpow_pos_of_pos hQ0 α
  -- `100 Q^α ≤ ε Q`, hence `25 H ≤ εQ`
  have h100 : 100 * (Q : ℝ) ^ α ≤ ε * Q := by
    rw [div_le_iff₀ hε] at hq1
    calc 100 * (Q : ℝ) ^ α ≤ (Q : ℝ) ^ (1 - α) * ε * (Q : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hq1 hQα0.le
      _ = ε * Q := by
          rw [mul_comm ((Q : ℝ) ^ (1 - α)) ε, mul_assoc, mul_comm ((Q : ℝ) ^ (1 - α)), hQα]
  have hHQ : 25 * (H : ℝ) ≤ ε * Q := by linarith
  have hHnat : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := le_trans (Real.one_le_rpow (by linarith) (by linarith)) hH1
    exact_mod_cast this
  -- the block discrepancy and the mass
  have hΔ := blockDiscrepancy_centredPrimeRow_le (A := A) (H := H) (K := K) (Q := Q) (ε := ε)
    fun m hm => abs_sum_block_le_of_window (by linarith) hε hε1 hX₀ hA hAK hHnat hq100 hqX hH1
      hHQ hm
  have hS₀ := mass_centredPrimeRow_ge (N := N) hQ1 hA hAK hN
  have hKH : 2 * ε * K * H / (Q : ℝ) ^ 2 ≤ 96 * ε * rowInverseSquareMass N (centredPrimeRow A H K) := by
    have h48 : (K : ℝ) * H / (48 * (Q : ℝ) ^ 2) = (K : ℝ) * H / (Q : ℝ) ^ 2 / 48 := by
      rw [div_div, mul_comm 48]
    rw [h48, div_le_iff₀ (by norm_num)] at hS₀
    have : 0 ≤ (K : ℝ) * H / (Q : ℝ) ^ 2 := by positivity
    calc 2 * ε * K * H / (Q : ℝ) ^ 2 = 2 * ε * ((K : ℝ) * H / (Q : ℝ) ^ 2) := by ring
      _ ≤ 2 * ε * (48 * rowInverseSquareMass N (centredPrimeRow A H K)) :=
          mul_le_mul_of_nonneg_left (by unfold rowInverseSquareMass; linarith) (by positivity)
      _ = 96 * ε * rowInverseSquareMass N (centredPrimeRow A H K) := by ring
  -- the three terms of the block bound
  have hmain := abs_rowBilinear_add_mean_add_beta_le_block (N := N) (A := A) (H := H) (K := K)
    (c := c) (c' := centredPrimeRow A H K) (by omega) (by omega) fun n => centredPrimeRow_support
  have hS1 := mul_sum_abs_le_rowLinearWeight (N := N) hc
  have hS2 := sum_abs_mul_sq_le_rowLinearWeight (N := N) hc
  have hS3 := mul_sum_abs_div_cube_le_rowInverseSquareMass (N := N) (Q := Q)
    (c' := centredPrimeRow A H K) fun n hn => hA.trans (mem_Ico.mp (centredPrimeRow_support hn)).1
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  refine assembly_le hε (rowInverseSquareMass_nonneg _ _) (rowLinearWeight_nonneg _ _)
    (sum_nonneg fun m _ => abs_nonneg _) (sum_nonneg fun d _ => abs_nonneg _)
    (sum_nonneg fun n _ => by positivity) ?_ (hΔ.trans hKH) hterm2 hS1 hS2 hS3 hterm3
  exact hmain

end

end GaloisForLFunctions.BezoutValuationIncidence
