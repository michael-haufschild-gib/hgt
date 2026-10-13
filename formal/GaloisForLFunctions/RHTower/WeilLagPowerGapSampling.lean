import GaloisForLFunctions.RHTower.WeilLagTwoSidedMeshSampling
import GaloisForLFunctions.RHTower.PrimeLagLandauPowerSaving
import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowthLower

/-!
# Lag sampling with power-saving gaps decides the Riemann hypothesis

Let `a_n = Φ(log n)` be the integer lags and `E(n) = √n a_n` the lag bracket. Write
`F(d) = ψ(d) − d` for the Chebyshev error.

**Exact slope law.** The normalised bracket `Q(d) = (E(d) − S(d) + log 2π)/d`, with `S` the
trivial-zero series, equals `1 − ψ(d)/d + Σ_{m ≤ d} Λ(m)/m − log d + γ`. One step gives

`Q(d + 1) − Q(d) = F(d)/(d(d + 1)) + (1/(d + 1) − log(1 + 1/d))`  (`lagBracketSlope_succ_sub`).

The second term lies in `[−1/(d(d + 1)), 0]`. So the bracket moves along the ray through the origin
up to the Chebyshev error on the window. If `|F| ≤ B` on `[k, n)` with `k ≤ n ≤ 2k`, then
`|E(n) − (n/k) E(k)| ≤ 2(n − k)B/k + 20` (`abs_lagBracket_sub_ratio_mul_le`). With Chebyshev's bound
`B ≍ n`, this is the square-root Lipschitz law of `WeilLagTwoSidedMeshSampling`.

**Bootstrap.** Let `A ⊆ ℕ` meet every window `[n − K n^{1 − δ}, n]` for large `n`, with `δ > 0`.
Given `|F(x)| ≤ C x^β`, every large `n` has a sample `k ∈ A` with
`|a_n − (√n/√k) a_k| ≤ D + D n^{β − ½ − δ}` (`exists_abs_integerLag_sub_le_rpow_of_powerGaps`).
Let the lags along `A` be bounded above (or below).
* Chebyshev's bound `β = 1` gives `a_n ≤ D + D n^{½ − δ}` (or the mirror lower bound).
* A one-sided bound with exponent `e ∈ [0, ½)` gives `Re ρ ≤ ½ + e` for every zero: from above
  by the power-saving prime-lag Landau argument (`xiZeroHalfPlaneBound_of_integerLag_le_rpow`),
  from below by the lower growth criterion (`xiZeroHalfPlaneBound_of_neg_rpow_le_integerLag`).
* The generalized von Koch bound then gives `β = ½ + e + δ/2`, hence the exponent `e − δ/2`.

After `⌈1/δ⌉` rounds the exponent is negative (`exists_neg_of_halfPlane_bootstrap`), the lags are
bounded, and the integer lag criterion gives RH. So RH holds iff the lags along `A` are bounded
above, and iff they are bounded below (`riemannHypothesis_iff_integerLag_bddAbove_of_powerGaps`,
`riemannHypothesis_iff_integerLag_bddBelow_of_powerGaps`).

**Perfect powers.** The `m`-th powers have gaps at most `m 2^{m − 1} n^{1 − 1/m}`
(`exists_pow_le_sub_le_rpow`). So for every `m ≥ 1`, RH holds iff the lags `a_{j^m}` are bounded
above, and iff they are bounded below (`riemannHypothesis_iff_integerLag_pow_bddAbove`,
`riemannHypothesis_iff_integerLag_pow_bddBelow`).

**Adaptive sampling.** The sampling set may be the level set `{k : a_k ≤ M}` itself. So RH holds iff
for some `δ > 0` and `M` every window `[n − n^{1 − δ}, n]` contains a dip `a_k ≤ M`
(`riemannHypothesis_iff_exists_powerWindow_integerLag_le`), and likewise for rises. Without RH,
for every `δ > 0` the lag has persistent excursions above every level, and below every level, on
whole windows of length `n^{1 − δ}` (`exists_persistent_integerLag_gt_of_not_riemannHypothesis`,
`exists_persistent_integerLag_lt_of_not_riemannHypothesis`). The square-root Lipschitz law alone
gives this only for windows of length `O(√n)`. This extends the quadratic-mesh threshold
`O(n^{3/4})` of `WeilLagTwoSidedMeshSampling` to every power-saving gap. Single-base progressions
`b^m` have gaps `≍ n`. There one round gains nothing, and the zero-side configurations of
`WeilLagSingleBaseWolffConfiguration` show that the progression alone cannot decide RH.
-/

open Real Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The exact slope law -/

/-- The normalised bracket `Q(d) = (E(d) − S(d) + log 2π)/d`. -/
def lagBracketSlope (d : ℕ) : ℝ :=
  (lagBracket d - trivialZeroSeriesReal d + Real.log (2 * Real.pi)) / d

/-- **One step of the slope law.** -/
theorem lagBracketSlope_succ_sub {d : ℕ} (hd : 1 ≤ d) :
    lagBracketSlope (d + 1) - lagBracketSlope d =
      (Chebyshev.psi d - d) / ((d : ℝ) * (d + 1)) +
        (1 / ((d : ℝ) + 1) - Real.log (((d : ℝ) + 1) / d)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hψ : Chebyshev.psi ((d : ℝ) + 1) = Chebyshev.psi d + vonMangoldt (d + 1) := by
    have h := psi_sub_psi_eq (Nat.le_succ d)
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
    push_cast at h
    linarith
  have hM : mertensSum (d + 1) = mertensSum d + vonMangoldt (d + 1) / ((d : ℝ) + 1) := by
    have h := mertensSum_sub_eq (Nat.le_succ d)
    rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
    push_cast at h
    linarith
  have hlog : Real.log (((d : ℝ) + 1) / d) = Real.log ((d : ℝ) + 1) - Real.log d :=
    Real.log_div (by positivity) hd0.ne'
  unfold lagBracketSlope lagBracket
  push_cast
  rw [hψ, hM, hlog]
  field_simp
  ring

theorem lagBracketSlope_sub_eq_sum {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    lagBracketSlope n - lagBracketSlope k =
      ∑ d ∈ Finset.Ico k n, ((Chebyshev.psi d - d) / ((d : ℝ) * (d + 1)) +
        (1 / ((d : ℝ) + 1) - Real.log (((d : ℝ) + 1) / d))) := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [Finset.sum_Ico_succ_top hkn, ← ih, ← lagBracketSlope_succ_sub (le_trans hk hkn)]
    ring

/-- `1/(d + 1) − log(1 + 1/d)` lies in `[−1/(d(d + 1)), 0]`. -/
theorem abs_inv_succ_sub_log_le {d : ℕ} (hd : 1 ≤ d) :
    |1 / ((d : ℝ) + 1) - Real.log (((d : ℝ) + 1) / d)| ≤ 1 / ((d : ℝ) * (d + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hup : Real.log (((d : ℝ) + 1) / d) ≤ 1 / d := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((d : ℝ) + 1) / d by positivity)
    have e : ((d : ℝ) + 1) / d - 1 = 1 / d := by field_simp; ring
    linarith
  have hlow : 1 / ((d : ℝ) + 1) ≤ Real.log (((d : ℝ) + 1) / d) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d : ℝ) / (d + 1) by positivity)
    have e1 : (d : ℝ) / (d + 1) - 1 = -(1 / ((d : ℝ) + 1)) := by field_simp; ring
    have e2 : Real.log ((d : ℝ) / (d + 1)) = -Real.log (((d : ℝ) + 1) / d) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have e : 1 / (d : ℝ) - 1 / ((d : ℝ) + 1) = 1 / ((d : ℝ) * (d + 1)) := by field_simp; ring
  rw [abs_le]
  constructor <;> linarith

/-- **Window transport of the bracket.** If `|ψ(d) − d| ≤ B` for `k ≤ d < n` and
`k ≤ n ≤ 2k`, then `|E(n) − (n/k) E(k)| ≤ 2(n − k)B/k + 20`. -/
theorem abs_lagBracket_sub_ratio_mul_le {k n : ℕ} {B : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn2k : n ≤ 2 * k) (hB0 : 0 ≤ B)
    (hB : ∀ d : ℕ, k ≤ d → d < n → |Chebyshev.psi d - d| ≤ B) :
    |lagBracket n - ((n : ℝ) / k) * lagBracket k| ≤ 2 * ((n : ℝ) - k) * B / k + 20 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn2k' : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
  have hn0 : (0 : ℝ) < n := by linarith
  -- the slope moves by at most `(n − k)(B + 1)/k²`
  have hsum : |lagBracketSlope n - lagBracketSlope k| ≤
      ((n : ℝ) - k) * ((B + 1) / (k : ℝ) ^ 2) := by
    rw [lagBracketSlope_sub_eq_sum hk hkn]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Finset.Ico k n,
        |(Chebyshev.psi d - d) / ((d : ℝ) * (d + 1)) +
          (1 / ((d : ℝ) + 1) - Real.log (((d : ℝ) + 1) / d))| ≤ (B + 1) / (k : ℝ) ^ 2 := by
      intro d hd
      obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
      have hd1 : 1 ≤ d := le_trans hk hkd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
      have hden : (k : ℝ) ^ 2 ≤ (d : ℝ) * (d + 1) := by nlinarith
      have h1 : |(Chebyshev.psi d - d) / ((d : ℝ) * (d + 1))| ≤ B / ((d : ℝ) * (d + 1)) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) * (d + 1))]
        exact div_le_div_of_nonneg_right (hB d hkd hdn) (by positivity)
      have h2 := abs_inv_succ_sub_log_le hd1
      calc _ ≤ B / ((d : ℝ) * (d + 1)) + 1 / ((d : ℝ) * (d + 1)) :=
            (abs_add_le _ _).trans (add_le_add h1 h2)
        _ = (B + 1) / ((d : ℝ) * (d + 1)) := by ring
        _ ≤ (B + 1) / (k : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity) hden
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hkn]
  -- `E(j) = j Q(j) + S(j) − log 2π`
  have hE : ∀ j : ℕ, 1 ≤ j →
      lagBracket j = j * lagBracketSlope j + trivialZeroSeriesReal j - Real.log (2 * Real.pi) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    unfold lagBracketSlope
    field_simp
    ring
  have hS : ∀ j : ℕ, 1 ≤ j → |trivialZeroSeriesReal j - Real.log (2 * Real.pi)| ≤ 6 := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have h0 := trivialZeroSeriesReal_nonneg hj1
    have h1 := trivialZeroSeriesReal_le_one hj1
    have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
      have := Real.pi_lt_d2
      linarith
    have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [abs_le]; constructor <;> linarith
  have hdecomp : lagBracket n - ((n : ℝ) / k) * lagBracket k =
      n * (lagBracketSlope n - lagBracketSlope k) +
        (trivialZeroSeriesReal n - Real.log (2 * Real.pi)) -
          ((n : ℝ) / k) * (trivialZeroSeriesReal k - Real.log (2 * Real.pi)) := by
    rw [hE n (le_trans hk hkn), hE k hk]
    field_simp
    ring
  rw [hdecomp]
  have hratio : (n : ℝ) / k ≤ 2 := by rw [div_le_iff₀ hk0]; linarith
  have hratio0 : 0 ≤ (n : ℝ) / k := by positivity
  have hA : |(n : ℝ) * (lagBracketSlope n - lagBracketSlope k)| ≤
      2 * ((n : ℝ) - k) * B / k + 2 := by
    rw [abs_mul, abs_of_pos hn0]
    have hnk0 : 0 ≤ (n : ℝ) - k := by linarith
    calc (n : ℝ) * |lagBracketSlope n - lagBracketSlope k|
        ≤ n * (((n : ℝ) - k) * ((B + 1) / (k : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum hn0.le
      _ = ((n : ℝ) / k) * (((n : ℝ) - k) * (B + 1) / k) := by field_simp
      _ ≤ 2 * (((n : ℝ) - k) * (B + 1) / k) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = 2 * ((n : ℝ) - k) * B / k + 2 * (((n : ℝ) - k) / k) := by ring
      _ ≤ 2 * ((n : ℝ) - k) * B / k + 2 := by
          have : ((n : ℝ) - k) / k ≤ 1 := by rw [div_le_iff₀ hk0]; linarith
          linarith
  have hB2 : |((n : ℝ) / k) * (trivialZeroSeriesReal k - Real.log (2 * Real.pi))| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg hratio0]
    nlinarith [hS k hk, abs_nonneg (trivialZeroSeriesReal k - Real.log (2 * Real.pi))]
  have hB1 := hS n (le_trans hk hkn)
  have t1 := abs_sub ((n : ℝ) * (lagBracketSlope n - lagBracketSlope k) +
    (trivialZeroSeriesReal n - Real.log (2 * Real.pi)))
    (((n : ℝ) / k) * (trivialZeroSeriesReal k - Real.log (2 * Real.pi)))
  have t2 := abs_add_le ((n : ℝ) * (lagBracketSlope n - lagBracketSlope k))
    (trivialZeroSeriesReal n - Real.log (2 * Real.pi))
  linarith

/-- `√n/√k ≤ 2` for `0 < k` and `n ≤ 4k`. -/
theorem sqrt_div_sqrt_le_two_of_le_two_mul {k n : ℕ} (hk : 0 < k) (hn2k : n ≤ 2 * k) :
    Real.sqrt n / Real.sqrt k ≤ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn2k' : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hk0)]
  have : Real.sqrt n ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt (by linarith)
  rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this

/-- **Window transport of the lags.** If `2 ≤ k ≤ n ≤ 2k` and `|ψ(d) − d| ≤ B` for `k ≤ d < n`, then
`|a_n − (√n/√k) a_k| ≤ (2(n − k)B/k + 20)/√n`. -/
theorem abs_integerLag_sub_ratio_mul_le {k n : ℕ} {B : ℝ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hn2k : n ≤ 2 * k) (hB0 : 0 ≤ B)
    (hB : ∀ d : ℕ, k ≤ d → d < n → |Chebyshev.psi d - d| ≤ B) :
    |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤
      (2 * ((n : ℝ) - k) * B / k + 20) / Real.sqrt n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hid : integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k =
      (lagBracket n - ((n : ℝ) / k) * lagBracket k) / Real.sqrt n := by
    rw [integerLag_eq_lagBracket hk, integerLag_eq_lagBracket (le_trans hk hkn)]
    have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
    have hkk : (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hk0.le).symm
    rw [show ((n : ℝ) / k) = (Real.sqrt n * Real.sqrt n) / (Real.sqrt k * Real.sqrt k) by
      rw [← hnn, ← hkk]]
    field_simp
  rw [hid, abs_div, abs_of_pos hsn]
  exact div_le_div_of_nonneg_right
    (abs_lagBracket_sub_ratio_mul_le (by omega) hkn hn2k hB0 hB) hsn.le

/-! ## One round of the bootstrap -/

/-- **Power-gap transport.** Let `A` meet every window `[n − K n^{1 − δ}, n]` for `n ≥ N₀`, and let
`|ψ(N) − N| ≤ C N^β`. Then every large `n` has a sample `k ∈ A` with `√n/√k ≤ 2` and
`|a_n − (√n/√k) a_k| ≤ D + D n^{β − ½ − δ}`. -/
theorem exists_abs_integerLag_sub_le_rpow_of_powerGaps {A : Set ℕ} {K δ C β : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧
      Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤
        D + D * (n : ℝ) ^ (β - 1 / 2 - δ) := by
  -- eventually `K n^{−δ} ≤ ½`
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨20 + 4 * K * C, by positivity, max N₀ (max N₂ 4), fun n hn => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hKn := hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  obtain ⟨k, hkA, hkn, hgapn⟩ := hgap n (le_trans (le_max_left _ _) hn)
  -- `K n^{1 − δ} = (K n^{−δ}) n ≤ n/2`
  have hsplit : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
    rw [show (1 : ℝ) - δ = -δ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hhalf : K * (n : ℝ) ^ (1 - δ) ≤ n / 2 := by
    rw [hsplit, ← mul_assoc]
    nlinarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn2k' : (n : ℝ) ≤ 2 * k := by linarith
  have hn2k : n ≤ 2 * k := by exact_mod_cast hn2k'
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨k, hkA, hk2, sqrt_div_sqrt_le_two_of_le_two_mul (by omega) hn2k, ?_⟩
  -- the Chebyshev error on the window is at most `C n^β`
  have hB : ∀ d : ℕ, k ≤ d → d < n → |Chebyshev.psi d - d| ≤ C * (n : ℝ) ^ β := by
    intro d hkd hdn
    have hd1 : 1 ≤ d := by omega
    refine (hψ d hd1).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdn.le) hβ
  have hw := abs_integerLag_sub_ratio_mul_le hk2 hkn hn2k (by positivity) hB
  -- the error term
  set y : ℝ := (n : ℝ) ^ (β - 1 / 2 - δ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hsn : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hkey : (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β = y * ((n : ℝ) * Real.sqrt n) := by
    rw [hy, hsn, ← Real.rpow_add hn0, show (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) + 1 / 2) by rw [Real.rpow_add hn0, Real.rpow_one],
      ← Real.rpow_add hn0]
    ring_nf
  have herr : 2 * ((n : ℝ) - k) * (C * (n : ℝ) ^ β) / k / Real.sqrt n ≤ 4 * K * C * y := by
    rw [div_div, div_le_iff₀ (by positivity)]
    calc 2 * ((n : ℝ) - k) * (C * (n : ℝ) ^ β)
        ≤ 2 * (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ = 2 * K * C * ((n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β) := by ring
      _ = 2 * K * C * y * ((n : ℝ) * Real.sqrt n) := by rw [hkey]; ring
      _ ≤ 2 * K * C * y * ((2 * k) * Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hn2k' hsn0.le
      _ = 4 * K * C * y * (k * Real.sqrt n) := by ring
  have h20 : 20 / Real.sqrt n ≤ 20 := by
    rw [div_le_iff₀ hsn0]; nlinarith
  rw [add_div] at hw
  have hKC : 0 ≤ K * C := mul_nonneg hK hC
  have hy1 : 4 * K * C * y ≤ (20 + 4 * K * C) * y := by
    apply mul_le_mul_of_nonneg_right _ hy0; linarith
  linarith

/-! ## The Landau steps -/

/-- **Upper power-saving lag bound gives a zero half-plane.** If `a_n ≤ D + D n^e` for all large
`n`, with `0 ≤ e < ½`, every zero satisfies `Re ρ ≤ ½ + e`. -/
theorem xiZeroHalfPlaneBound_of_integerLag_le_rpow {D e : ℝ} {N₁ : ℕ} (he0 : 0 ≤ e)
    (he : e < 1 / 2) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, N₁ ≤ n → integerLag n ≤ D + D * (n : ℝ) ^ e) : XiZeroHalfPlaneBound e := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  refine re_le_half_add_of_primeLag_le_rpow' (X := N₁) (M := 2 * D) he0 he
    (fun p hp hpX => ?_) q
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hexp : Real.exp (e * Real.log p) = (p : ℝ) ^ e := by
    rw [Real.rpow_def_of_pos hp0, mul_comm]
  rw [hexp]
  have h1 : 1 ≤ (p : ℝ) ^ e := Real.one_le_rpow hp1 he0
  have := h p hpX.le
  nlinarith

/-- **Lower power-saving lag bound gives a zero half-plane.** If `a_n ≥ −(D + D n^e)` for all
large `n`, with `0 ≤ e < ½`, every zero satisfies `Re ρ ≤ ½ + e`. -/
theorem xiZeroHalfPlaneBound_of_neg_rpow_le_integerLag {D e : ℝ} {N₁ : ℕ} (he0 : 0 ≤ e)
    (he : e < 1 / 2) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, N₁ ≤ n → -(D + D * (n : ℝ) ^ e) ≤ integerLag n) : XiZeroHalfPlaneBound e := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  set L₀ : ℝ := max (Real.log 2) (Real.log ((N₁ : ℝ) + 1)) with hL₀
  have hW := lagWeightTotal_nonneg
  refine re_le_half_add_of_neg_exp_le_weilLagFunctionReal (M := 2 * D + 30 +
    Real.exp (L₀ / 2) * lagWeightTotal) he0 he (fun L hL => ?_) q
  have hE1 : 1 ≤ Real.exp (e * L) := Real.one_le_exp (by positivity)
  have hX0 : 0 ≤ Real.exp (L₀ / 2) * lagWeightTotal := by positivity
  rcases le_or_gt L₀ L with hbig | hsmall
  · have hL2 : Real.log 2 ≤ L := le_trans (le_max_left _ _) hbig
    have hLN : Real.log ((N₁ : ℝ) + 1) ≤ L := le_trans (le_max_right _ _) hbig
    have hexpN : (N₁ : ℝ) + 1 ≤ Real.exp L := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (N₁ : ℝ) + 1)]
      exact Real.exp_le_exp.mpr hLN
    set n : ℕ := ⌊Real.exp L⌋₊ with hn
    have hnN : N₁ ≤ n := Nat.le_floor (by linarith)
    have hnL : (n : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have hcmp := integerLag_sub_le_weilLagFunctionReal hL2
    have hlow := h n hnN
    have hpow : (n : ℝ) ^ e ≤ Real.exp (e * L) := by
      calc (n : ℝ) ^ e ≤ (Real.exp L) ^ e := Real.rpow_le_rpow (Nat.cast_nonneg _) hnL he0
        _ = Real.exp (e * L) := by rw [← Real.exp_mul, mul_comm]
    have hDp : D * (n : ℝ) ^ e ≤ D * Real.exp (e * L) := mul_le_mul_of_nonneg_left hpow hD
    nlinarith
  · have hab := abs_weilLagFunctionReal_le L
    rw [abs_of_nonneg hL] at hab
    have hle : Real.exp (L / 2) * lagWeightTotal ≤ Real.exp (L₀ / 2) * lagWeightTotal :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hW
    have h4 := neg_abs_le (weilLagFunctionReal L)
    nlinarith

/-- Chebyshev's function at an integer is the von Mangoldt sum over `[1, N]`. -/
theorem psi_natCast_eq_sum_Icc_one (N : ℕ) :
    Chebyshev.psi N = ∑ n ∈ Finset.Icc 1 N, vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast,
    ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
  simp [ArithmeticFunction.map_zero]
  rfl

/-! ## The bootstrap -/

/-- **The abstract half-plane bootstrap.** Let `P` be a property of exponents. Suppose `P` holds at
`½ − δ`, a negative exponent with `P` gives `P` everywhere, and `P e` with `0 ≤ e < ½` gives
`P (e − δ/2)`. Then `P` holds at some negative exponent. -/
theorem exists_neg_of_halfPlane_bootstrap {P : ℝ → Prop} {δ : ℝ} (hδ : 0 < δ)
    (h0 : P (1 / 2 - δ)) (hneg : ∀ e, e < 0 → P e → ∀ e', P e')
    (hstep : ∀ e, 0 ≤ e → e < 1 / 2 → P e → P (e - δ / 2)) : ∃ e, e < 0 ∧ P e := by
  have hiter : ∀ j : ℕ, P (1 / 2 - δ - j * (δ / 2)) := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have he' : 1 / 2 - δ - ((j + 1 : ℕ) : ℝ) * (δ / 2) = (1 / 2 - δ - j * (δ / 2)) - δ / 2 := by
        push_cast; ring
      rw [he']
      rcases lt_or_ge (1 / 2 - δ - j * (δ / 2)) 0 with hlt | hnn
      · exact hneg _ hlt ih _
      · refine hstep _ hnn ?_ ih
        have : (0 : ℝ) ≤ j * (δ / 2) := by positivity
        linarith
  refine ⟨_, ?_, hiter ⌈1 / δ⌉₊⟩
  have hc : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
  have : 1 / 2 ≤ (⌈1 / δ⌉₊ : ℝ) * (δ / 2) := by
    have h1 : (1 / δ) * (δ / 2) = 1 / 2 := by field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  linarith

/-- The von Koch round: a zero half-plane `e ∈ [0, ½)` and power gaps give the two-sided transport
at exponent `e − δ/2`. -/
theorem exists_abs_integerLag_sub_le_rpow_of_powerGaps_of_halfPlane {A : Set ℕ} {K δ e : ℝ}
    {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K) (he0 : 0 ≤ e) (he : e < 1 / 2)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hXi : XiZeroHalfPlaneBound e) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧
      Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤
        D + D * (n : ℝ) ^ (e - δ / 2) := by
  obtain ⟨C, hC0, hC⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound he0 he
    hXi (show 0 < δ / 2 by positivity)
  have hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ (1 / 2 + e + δ / 2) := by
    intro N hN
    rw [psi_natCast_eq_sum_Icc_one]
    exact hC N hN
  have ee : 1 / 2 + e + δ / 2 - 1 / 2 - δ = e - δ / 2 := by ring
  rw [← ee]
  exact exists_abs_integerLag_sub_le_rpow_of_powerGaps hδ hK hC0.le (by positivity) hgap hψ

/-- The Chebyshev round: power gaps alone give the two-sided transport at exponent `½ − δ`. -/
theorem exists_abs_integerLag_sub_le_rpow_of_powerGaps_chebyshev {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧
      Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤
        D + D * (n : ℝ) ^ (1 / 2 - δ) := by
  have hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) ^ (1 : ℝ) := by
    intro N _
    rw [Real.rpow_one]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]; constructor <;> linarith
  have ee : (1 : ℝ) - 1 / 2 - δ = 1 / 2 - δ := by ring
  rw [← ee]
  exact exists_abs_integerLag_sub_le_rpow_of_powerGaps hδ hK (by norm_num) (by norm_num) hgap hψ

/-- The upper bootstrap level: `a_n ≤ D + D n^e` for all large `n`. -/
def powerGapUpperLevel (e : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → integerLag n ≤ D + D * (n : ℝ) ^ e

/-- The lower bootstrap level: `a_n ≥ −(D + D n^e)` for all large `n`. -/
def powerGapLowerLevel (e : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → -(D + D * (n : ℝ) ^ e) ≤ integerLag n

theorem powerGapUpperLevel_of_transport {A : Set ℕ} {M e : ℝ}
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M)
    (h : ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧
      Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤ D + D * (n : ℝ) ^ e) :
    powerGapUpperLevel e := by
  obtain ⟨D, hD, N₁, h⟩ := h
  refine ⟨2 * max M 0 + D, by positivity, N₁, fun n hn => ?_⟩
  obtain ⟨k, hkA, hk2, hr, habs⟩ := h n hn
  have hr0 : 0 ≤ Real.sqrt n / Real.sqrt k := by positivity
  have hak : integerLag k ≤ max M 0 := (hA k hkA hk2).trans (le_max_left _ _)
  have h1 : (Real.sqrt n / Real.sqrt k) * integerLag k ≤ 2 * max M 0 :=
    (mul_le_mul_of_nonneg_left hak hr0).trans
      (mul_le_mul_of_nonneg_right hr (le_max_right _ _))
  have h2 := (abs_le.mp habs).2
  have h3 : D * (n : ℝ) ^ e ≤ (2 * max M 0 + D) * (n : ℝ) ^ e :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right M 0]) (by positivity)
  linarith

theorem powerGapLowerLevel_of_transport {A : Set ℕ} {M e : ℝ}
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k)
    (h : ∃ D : ℝ, 0 ≤ D ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧
      Real.sqrt n / Real.sqrt k ≤ 2 ∧
      |integerLag n - (Real.sqrt n / Real.sqrt k) * integerLag k| ≤ D + D * (n : ℝ) ^ e) :
    powerGapLowerLevel e := by
  obtain ⟨D, hD, N₁, h⟩ := h
  refine ⟨2 * max (-M) 0 + D, by positivity, N₁, fun n hn => ?_⟩
  obtain ⟨k, hkA, hk2, hr, habs⟩ := h n hn
  have hr0 : 0 ≤ Real.sqrt n / Real.sqrt k := by positivity
  have hak : -max (-M) 0 ≤ integerLag k := by
    have := hA k hkA hk2; have := le_max_left (-M) 0; linarith
  have h1 : -(2 * max (-M) 0) ≤ (Real.sqrt n / Real.sqrt k) * integerLag k := by
    have h1a : (Real.sqrt n / Real.sqrt k) * (-max (-M) 0) ≤
        (Real.sqrt n / Real.sqrt k) * integerLag k := mul_le_mul_of_nonneg_left hak hr0
    have h1b : (Real.sqrt n / Real.sqrt k) * max (-M) 0 ≤ 2 * max (-M) 0 :=
      mul_le_mul_of_nonneg_right hr (le_max_right _ _)
    linarith
  have h2 := (abs_le.mp habs).1
  have h3 : D * (n : ℝ) ^ e ≤ (2 * max (-M) 0 + D) * (n : ℝ) ^ e :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right (-M) 0]) (by positivity)
  linarith

/-- An eventual upper bound for the lags is a bound for all `n ≥ 2`. -/
theorem integerLag_bddAbove_of_eventually_le {M : ℝ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → integerLag n ≤ M) : ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M' := by
  classical
  set B : ℝ := (Finset.range (N + 2)).sup' ⟨0, by simp⟩ fun n => integerLag n
  refine ⟨max B M, fun n _ => ?_⟩
  rcases lt_or_ge n N with hlt | hge
  · exact le_max_of_le_left (Finset.le_sup' (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · exact le_max_of_le_right (h n hge)

/-- An eventual lower bound for the lags is a bound for all `n ≥ 2`. -/
theorem integerLag_bddBelow_of_eventually_le {M : ℝ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → M ≤ integerLag n) : ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → M' ≤ integerLag n := by
  classical
  set B : ℝ := (Finset.range (N + 2)).inf' ⟨0, by simp⟩ fun n => integerLag n
  refine ⟨min B M, fun n _ => ?_⟩
  rcases lt_or_ge n N with hlt | hge
  · exact min_le_of_left_le (Finset.inf'_le (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · exact min_le_of_right_le (h n hge)

/-- **Power-gap lag sampling from above gives RH.** If `A` meets every window
`[n − K n^{1 − δ}, n]` for large `n`, with `δ > 0`, and the lags along `A` are bounded above, then
RH holds. -/
theorem riemannHypothesis_of_powerGaps_integerLag_le {A : Set ℕ} {M K δ : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M) : RiemannHypothesis := by
  obtain ⟨e, he, D, hD, N₁, h⟩ := exists_neg_of_halfPlane_bootstrap (P := powerGapUpperLevel) hδ
    (powerGapUpperLevel_of_transport hA (exists_abs_integerLag_sub_le_rpow_of_powerGaps_chebyshev
      hδ hK hgap))
    (fun e he ⟨D, hD, N₁, h⟩ e' => ⟨2 * D, by positivity, max N₁ 1, fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hn1 he.le
      have h0 : 0 ≤ (n : ℝ) ^ e' := by positivity
      have := h n (le_trans (le_max_left _ _) hn)
      nlinarith⟩)
    (fun e he0 he hP => powerGapUpperLevel_of_transport hA
      (exists_abs_integerLag_sub_le_rpow_of_powerGaps_of_halfPlane hδ hK he0 he hgap
        (by obtain ⟨D, hD, N₁, h⟩ := hP
            exact xiZeroHalfPlaneBound_of_integerLag_le_rpow he0 he hD h)))
  obtain ⟨M', hM'⟩ := integerLag_bddAbove_of_eventually_le (M := 2 * D) (N := max N₁ 1)
    (fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hn1 he.le
      have := h n (le_trans (le_max_left _ _) hn)
      nlinarith)
  exact riemannHypothesis_iff_integerLag_bddAbove.mpr ⟨M', hM'⟩

/-- **Power-gap lag sampling from below gives RH.** If `A` meets every window
`[n − K n^{1 − δ}, n]` for large `n`, with `δ > 0`, and the lags along `A` are bounded below, then
RH holds. -/
theorem riemannHypothesis_of_powerGaps_le_integerLag {A : Set ℕ} {M K δ : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k) : RiemannHypothesis := by
  obtain ⟨e, he, D, hD, N₁, h⟩ := exists_neg_of_halfPlane_bootstrap (P := powerGapLowerLevel) hδ
    (powerGapLowerLevel_of_transport hA (exists_abs_integerLag_sub_le_rpow_of_powerGaps_chebyshev
      hδ hK hgap))
    (fun e he ⟨D, hD, N₁, h⟩ e' => ⟨2 * D, by positivity, max N₁ 1, fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hn1 he.le
      have h0 : 0 ≤ (n : ℝ) ^ e' := by positivity
      have := h n (le_trans (le_max_left _ _) hn)
      nlinarith⟩)
    (fun e he0 he hP => powerGapLowerLevel_of_transport hA
      (exists_abs_integerLag_sub_le_rpow_of_powerGaps_of_halfPlane hδ hK he0 he hgap
        (by obtain ⟨D, hD, N₁, h⟩ := hP
            exact xiZeroHalfPlaneBound_of_neg_rpow_le_integerLag he0 he hD h)))
  obtain ⟨M', hM'⟩ := integerLag_bddBelow_of_eventually_le (M := -(2 * D)) (N := max N₁ 1)
    (fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
      have hle := Real.rpow_le_one_of_one_le_of_nonpos hn1 he.le
      have := h n (le_trans (le_max_left _ _) hn)
      nlinarith)
  exact riemannHypothesis_iff_integerLag_bddBelow.mpr ⟨M', hM'⟩

/-- **Lag criterion with power-saving gaps, upper form.** If `A ⊆ ℕ` meets every window
`[n − K n^{1 − δ}, n]` for large `n`, with `δ > 0`, then RH holds iff the lags along `A` are bounded
above. -/
theorem riemannHypothesis_iff_integerLag_bddAbove_of_powerGaps {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_powerGaps_integerLag_le hδ hK hgap hM

/-- **Lag criterion with power-saving gaps, lower form.** If `A ⊆ ℕ` meets every window
`[n − K n^{1 − δ}, n]` for large `n`, with `δ > 0`, then RH holds iff the lags along `A` are bounded
below. -/
theorem riemannHypothesis_iff_integerLag_bddBelow_of_powerGaps {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_powerGaps_le_integerLag hδ hK hgap hM

/-! ## Perfect powers -/

/-- `(x + 1)^{m+1} ≤ x^{m+1} + (m + 1)(x + 1)^m` for `x ≥ 0`. -/
theorem add_one_pow_le_pow_add {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (x + 1) ^ (m + 1) ≤ x ^ (m + 1) + (m + 1) * (x + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmono : x ^ (m + 1) ≤ (x + 1) ^ (m + 1) := pow_le_pow_left₀ hx (by linarith) _
    have hx1 : 0 ≤ x + 1 := by linarith
    calc (x + 1) ^ (m + 1 + 1) = (x + 1) ^ (m + 1) * (x + 1) := pow_succ _ _
      _ ≤ (x ^ (m + 1) + (m + 1) * (x + 1) ^ m) * (x + 1) := mul_le_mul_of_nonneg_right ih hx1
      _ = x ^ (m + 1 + 1) + x ^ (m + 1) + (m + 1) * (x + 1) ^ (m + 1) := by ring
      _ ≤ x ^ (m + 1 + 1) + (x + 1) ^ (m + 1) + (m + 1) * (x + 1) ^ (m + 1) := by linarith
      _ = x ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1) * (x + 1) ^ (m + 1) := by push_cast; ring

/-- **The gaps of the `m`-th powers.** Every `n ≥ 1` has an `m`-th power `j^m ≤ n` with
`n − j^m ≤ m 2^{m − 1} n^{1 − 1/m}`. -/
theorem exists_pow_le_sub_le_rpow {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ∃ j : ℕ, j ^ m ≤ n ∧
      (n : ℝ) - ((j ^ m : ℕ) : ℝ) ≤ (m * 2 ^ (m - 1) : ℝ) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set r : ℝ := (n : ℝ) ^ (1 / (m : ℝ)) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hn1 (by positivity)
  have hrm : r ^ m = n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    rw [show 1 / (m : ℝ) * m = 1 by field_simp, Real.rpow_one]
  set j : ℕ := ⌊r⌋₊ with hj
  have hjr : (j : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hrj : r < j + 1 := Nat.lt_floor_add_one r
  have hjm : (j : ℝ) ^ m ≤ n := by
    rw [← hrm]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hjr m
  have hnj : (n : ℝ) < ((j : ℝ) + 1) ^ m := by
    rw [← hrm]; exact pow_lt_pow_left₀ hrj (by linarith) (by omega)
  refine ⟨j, by exact_mod_cast hjm, ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hstep := add_one_pow_le_pow_add (Nat.cast_nonneg j) m'
  have hj1 : (j : ℝ) + 1 ≤ 2 * r := by linarith
  have hpow : ((j : ℝ) + 1) ^ m' ≤ 2 ^ m' * r ^ m' := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hj1 m'
  have hrm' : r ^ m' = (n : ℝ) ^ (1 - 1 / ((m' + 1 : ℕ) : ℝ)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    field_simp
    ring
  push_cast at hstep hnj hrm' ⊢
  rw [← hrm']
  nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (m' : ℝ) + 1)]

/-- **The `m`-th powers decide RH.** For every `m ≥ 1`, RH holds iff the lags `a_{j^m}` are bounded
above. -/
theorem riemannHypothesis_iff_integerLag_pow_bddAbove {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j ^ m → integerLag (j ^ m) ≤ M := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap : ∀ n : ℕ, 1 ≤ n → ∃ k ∈ Set.range (fun j : ℕ => j ^ m), k ≤ n ∧
      (n : ℝ) - k ≤ (m * 2 ^ (m - 1) : ℝ) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hj, hgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hj, hgap⟩
  rw [riemannHypothesis_iff_integerLag_bddAbove_of_powerGaps (by positivity) (by positivity) hgap]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ hj⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k hk hk2 => ?_⟩
    obtain ⟨j, rfl⟩ := hk
    exact hM j hk2

/-- **The `m`-th powers decide RH from below.** For every `m ≥ 1`, RH holds iff the lags `a_{j^m}`
are bounded below. -/
theorem riemannHypothesis_iff_integerLag_pow_bddBelow {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j ^ m → M ≤ integerLag (j ^ m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap : ∀ n : ℕ, 1 ≤ n → ∃ k ∈ Set.range (fun j : ℕ => j ^ m), k ≤ n ∧
      (n : ℝ) - k ≤ (m * 2 ^ (m - 1) : ℝ) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hj, hgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hj, hgap⟩
  rw [riemannHypothesis_iff_integerLag_bddBelow_of_powerGaps (by positivity) (by positivity) hgap]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ hj⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k hk hk2 => ?_⟩
    obtain ⟨j, rfl⟩ := hk
    exact hM j hk2

/-! ## Adaptive sampling: persistent excursions -/

/-- **RH ⟺ the lag dips below a fixed level in every power window.** RH holds iff for some `δ > 0`
and some level `M`, every large `n` has `k ∈ [n − n^{1 − δ}, n]` with `a_k ≤ M`. The sampling set
is the adaptive set `{k : a_k ≤ M}`. -/
theorem riemannHypothesis_iff_exists_powerWindow_integerLag_le :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) ∧ integerLag k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    refine ⟨1 / 2, by norm_num, M, 2, fun n hn => ⟨n, hn, le_rfl, ?_, hM n hn⟩⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, M, N₀, h⟩
    refine riemannHypothesis_of_powerGaps_integerLag_le (A := {k | 2 ≤ k ∧ integerLag k ≤ M})
      (M := M) (K := 1) (N₀ := N₀) hδ zero_le_one (fun n hn => ?_) (fun k hk _ => hk.2)
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := h n hn
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

/-- **RH ⟺ the lag rises above a fixed level in every power window.** -/
theorem riemannHypothesis_iff_exists_powerWindow_le_integerLag :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) ∧ M ≤ integerLag k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    refine ⟨1 / 2, by norm_num, M, 2, fun n hn => ⟨n, hn, le_rfl, ?_, hM n hn⟩⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, M, N₀, h⟩
    refine riemannHypothesis_of_powerGaps_le_integerLag (A := {k | 2 ≤ k ∧ M ≤ integerLag k})
      (M := M) (K := 1) (N₀ := N₀) hδ zero_le_one (fun n hn => ?_) (fun k hk _ => hk.2)
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := h n hn
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

/-- **Persistent upper excursions without RH.** If RH fails, then for every `δ > 0` and every level
`M` there are arbitrarily large `n` with `a_k > M` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`. -/
theorem exists_persistent_integerLag_gt_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ ∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) →
      M < integerLag k := by
  by_contra hcon
  push Not at hcon
  exact hRH (riemannHypothesis_iff_exists_powerWindow_integerLag_le.mpr ⟨δ, hδ, M, N₀, hcon⟩)

/-- **Persistent lower excursions without RH.** If RH fails, then for every `δ > 0` and every level
`M` there are arbitrarily large `n` with `a_k < M` for every `k ≥ 2` in `[n − n^{1 − δ}, n]`. -/
theorem exists_persistent_integerLag_lt_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (M : ℝ) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ ∀ k : ℕ, 2 ≤ k → k ≤ n → (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) →
      integerLag k < M := by
  by_contra hcon
  push Not at hcon
  exact hRH (riemannHypothesis_iff_exists_powerWindow_le_integerLag.mpr ⟨δ, hδ, M, N₀, hcon⟩)

end

end RHTower
