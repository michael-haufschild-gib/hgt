import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SmallDampingMoebiusAndLiouvilleCancellationLaws

/-!
# Prefix stability and critical Wiener closure of Möbius and Liouville rows

Below half damping (`0 ≤ ε < 1/2`), a general paid weight `c ∈ 𝒞(K, ε)` need not have uniformly
paid dyadic rows `dyadicRow c J`: a horizon cut at the midpoint `N = 2^J` of a windowed dipole
leaves an uncancelled harmonic half-mass `τ_N = ∑_{d > N} c(d)/d` that injects a linear drift
`τ_N n` on `[1, N]`, and freezes the plain partial sum `S_N(x) = S(N)` at a spike for `x ≥ N`
(`TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping`).

This module establishes the exact structure of the Möbius and Liouville rows — and of general
damped sign and convolution rows — that excludes the dipole obstruction below half damping:

1. **Exact square-root harmonic-tail characterization of the sub-horizon dipole obstruction
   (`subHorizon_horizonRowEnergy_bounded_iff`, `subHorizon_dyadicRowEnergy_bounded_iff`).**
   For any paid weight `c` with convergent harmonic series `m = ∑_d c(d)/d`, on the sub-horizon
   `1 ≤ n ≤ N` the horizon-`N` row prefix satisfies `A_{row(c, N)}(n) = A_c(n) + τ_N n` where
   `τ_N = m − ∑_{d ≤ N} c(d)/d = ∑_{d > N} c(d)/d`. Because `(N/2) τ_N² ≤ ∑_{n ≤ N} (τ_N n)²/(n(n+1)) ≤ N τ_N²`,
   the sub-horizon row energies `E_T(row(c, N))` (`T ≤ N`) are uniformly bounded **if and only if**
   the harmonic tail obeys the square-root law `sup_{N ≥ 1} N τ_N² < ∞`.

2. **Exclusion of the sub-horizon dipole obstruction for Möbius and Liouville across the entire
   zero-width admission range `ε > Θ − 1/2`
   (`moebius_harmonicTail_sq_mul_bounded_of_zetaZeroAbscissa_sub_half_lt`,
   `subHorizon_horizonRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt`,
   `subHorizon_dyadicRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt`).**
   For `c_ε(d) = μ(d) d^{−ε}`, the harmonic tail `τ_N(ε) = ∑_{d > N} μ(d) d^{−(1+ε)}` is evaluated
   at the real point `1 + ε > 1`. By Littlewood's zero-abscissa bound `|M(x)| ≤ C_δ x^{Θ+δ}` and
   Abel summation, for **every** `ε > Θ − 1/2` (the entire admission range of the Möbius receiver),
   `|τ_N(ε)| = O(N^{Θ − 1 − ε + δ}) = o(N^{−1/2})`, so `N τ_N(ε)² → 0` and all sub-horizon row
   energies (`T ≤ N`) are uniformly bounded. Under `RiemannHypothesis`, this holds for every `ε > 0`.

3. **Prefix-stable partial-sum inheritance and full-horizon (`∀ N, T`) row bounds
   (`abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos`,
   `horizonRows_bounded_dampedSign_of_partialSum_rpow`,
   `exists_abs_weightCenteredPrefix_horizonRow_pmPowerDamped_le_all_pos`,
   `exists_horizonRow_receiver_le_on_zeroFreeBand_of_pos`,
   `horizonRows_bounded_moebius_of_half_zetaZeroAbscissa_lt`).**
   For any sign pattern `|s(d)| ≤ 1` whose partial sums satisfy `|∑_{e ≤ x} s(e)| ≤ L x` for
   `x ≥ D`, truncating `s` at any horizon `N` yields `∑_{e ≤ x} s_N(e) = S(min(x, N))`:
   - if `N ≥ D`, then `min(x, N) ≥ D` for all `x ≥ D`, so `|S_N(x)| ≤ L min(x, N) ≤ L x`;
   - if `N < D ≤ n`, `n` is above the horizon `N`, so `|A_{row(N)}(n)| ≤ ∑_{d ≤ N} d^{−ε} ≤ 3 D^{1−ε}`.
   Hence **every horizon row `horizonRow (s · d^{−ε}) N` obeys the exact same all-damping hyperbola
   bound `3 D^{1−ε} + (13/ε) L n D^{−ε}` as the full weight**, with zero loss in the constant.
   Consequently:
   - every sign pattern with `|S(x)| ≤ C (x+1)^β` (`0 ≤ β < 1`) has uniformly paid horizon rows and
     dyadic rows across all `N, J, T` for every `ε > β/2`;
   - all horizon rows and dyadic rows of `μ(d) d^{−ε}` satisfy the uniform Vinogradov–Korobov prefix
     bound `|A_{row(N)}(n)| ≤ (K/ε) n^{1−ε} exp(−√(log n)/40)` and are uniformly paid on the
     zero-free band `ε ≥ 1/2 − 1/(80 √(log T))` above any `ε₀ > 0`;
   - for every `ε > Θ/2` (and for every `ε > 1/4` under RH), all horizon rows and dyadic rows of
     `μ(d) d^{−ε}` are uniformly paid across all `N, J, T`.

4. **Exact divisor-quotient horizon-row convolution law and critical Wiener monoid closure
   (`weightCenteredPrefix_horizonRow_dirichletConv`, `pronicNorm_horizonRow_dirichletConv_le`,
   `horizonRows_bounded_dirichletConv`, `horizonRows_bounded_moebius_iff_liouville`).**
   Because `q m ≤ N ⇔ m ≤ ⌊N/q⌋`, the horizon-`N` row of a Dirichlet convolution `g ⋆ c` decomposes
   into shifted horizon-`⌊N/q⌋` rows of `c`:
   `A_{row(g⋆c, N)}(n) = ∑_{q ≤ N} g(q) A_{row(c, ⌊N/q⌋)}(⌊n/q⌋) + ∑_{q ≤ N} g(q) m_c(⌊N/q⌋) (⌊n/q⌋ − n/q)`.
   Each dilated term contracts by `q^{−1/2}` and each sawtooth has pronic norm `≤ √(2/q)`, so
   uniform horizon-row boundedness is preserved by every kernel `g ∈ CriticalWiener`. In particular,
   at **every** damping `ε > 0`, the horizon rows of `μ(d) d^{−ε}` are uniformly paid **if and only if**
   the horizon rows of `λ(d) d^{−ε}` are uniformly paid.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open _root_.RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. General horizon rows and the sub-horizon square-root harmonic-tail law -/

/-- The truncated row of `c` at arbitrary horizon `N`. -/
def horizonRow (c : ℕ → ℝ) (N : ℕ) (d : ℕ) : ℝ := if d ≤ N then c d else 0

/-- The finite harmonic mean of the horizon-`N` row. -/
def horizonRowMean (c : ℕ → ℝ) (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, horizonRow c N d / d

theorem horizonRowMean_eq (c : ℕ → ℝ) (N : ℕ) :
    horizonRowMean c N = ∑ d ∈ Icc 1 N, c d / d :=
  sum_congr rfl fun d hd => by simp [horizonRow, (mem_Icc.mp hd).2]

theorem dyadicRow_eq_horizonRow (c : ℕ → ℝ) (J : ℕ) :
    dyadicRow c J = horizonRow c (2 ^ J) := rfl

theorem dyadicRowMean_eq_horizonRowMean (c : ℕ → ℝ) (J : ℕ) :
    dyadicRowMean c J = horizonRowMean c (2 ^ J) := rfl

theorem hasSum_horizonRow_div (c : ℕ → ℝ) (N : ℕ) :
    HasSum (fun d : ℕ => horizonRow c N d / d) (horizonRowMean c N) := by
  rw [horizonRowMean]
  exact hasSum_sum_of_ne_finset_zero fun d hd => by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · have : N < d := by simp only [mem_Icc, not_and, not_le] at hd; exact hd hd0
      simp [horizonRow, not_le.mpr this]

theorem tsum_horizonRow_div (c : ℕ → ℝ) (N : ℕ) :
    ∑' d : ℕ, horizonRow c N d / d = horizonRowMean c N :=
  (hasSum_horizonRow_div c N).tsum_eq

theorem horizonRow_dampedSignWeight (s : ℕ → ℝ) (ε : ℝ) (N : ℕ) :
    horizonRow (dampedSignWeight s ε) N = dampedSignWeight (horizonRow s N) ε := by
  funext d
  simp only [horizonRow, dampedSignWeight]
  split_ifs <;> simp

theorem abs_horizonRow_le (c : ℕ → ℝ) (N d : ℕ) : |horizonRow c N d| ≤ |c d| := by
  unfold horizonRow; split_ifs <;> simp

theorem abs_horizonRowMean_le_tsum {c : ℕ → ℝ} (hc : Summable (fun d : ℕ => |c d / d|)) (N : ℕ) :
    |horizonRowMean c N| ≤ ∑' d : ℕ, |c d / d| := by
  rw [horizonRowMean_eq]
  exact (abs_sum_le_sum_abs _ _).trans (hc.sum_le_tsum _ fun _ _ => abs_nonneg _)

/-- **Uniformly bounded horizon rows pay the limit.** -/
theorem weightPronicEnergy_le_of_horizonRows_le {c : ℕ → ℝ} {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) {E : ℝ}
    (hE : ∀ N T : ℕ, weightPronicEnergy (horizonRow c N) (horizonRowMean c N) T ≤ E) (T : ℕ) :
    weightPronicEnergy c m T ≤ E :=
  weightPronicEnergy_le_of_rows_le hm (fun J T' => hE (2 ^ J) T') T

/-- **Below its horizon `N`, a row is the weight plus the harmonic-tail drift `(m − m_N) n`.** -/
theorem weightCenteredPrefix_horizonRow_of_le (c : ℕ → ℝ) (m : ℝ) {N n : ℕ} (hn : n ≤ N) :
    weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n =
      weightCenteredPrefix c m n + (m - horizonRowMean c N) * n := by
  rw [weightCenteredPrefix, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    sum_Icc_sum_divisors_eq_floor]
  have h : ∑ d ∈ Icc 1 n, horizonRow c N d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
    have : d ≤ N := (mem_Icc.mp hd).2.trans hn
    simp [horizonRow, this]
  rw [h]; ring

/-- **Beyond its horizon `N`, a row is a sawtooth sum bounded by `∑_{d ≤ N} |c(d)|`.** -/
theorem abs_weightCenteredPrefix_horizonRow_le_of_lt (c : ℕ → ℝ) {N n : ℕ} (hn : N < n) :
    |weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n| ≤ ∑ d ∈ Icc 1 N, |c d| := by
  have heq : weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n =
      ∑ d ∈ Icc 1 N, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, horizonRowMean_eq]
    have hsplit : Icc 1 n = Icc 1 N ∪ Ioc N n := by
      ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 N) (Ioc N n) := by
      rw [disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    rw [hsplit, sum_union hdisj]
    have hz : ∑ d ∈ Ioc N n, horizonRow c N d * ((n / d : ℕ) : ℝ) = 0 :=
      sum_eq_zero fun d hd => by
        have : ¬ d ≤ N := by simp only [mem_Ioc] at hd; omega
        simp [horizonRow, this]
    have hc' : ∑ d ∈ Icc 1 N, horizonRow c N d * ((n / d : ℕ) : ℝ) =
        ∑ d ∈ Icc 1 N, c d * ((n / d : ℕ) : ℝ) := sum_congr rfl fun d hd => by
      have : d ≤ N := (mem_Icc.mp hd).2
      simp [horizonRow, this]
    rw [hz, add_zero, hc', sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  rw [abs_mul]
  calc |c d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ |c d| * 1 :=
        mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1) (abs_nonneg _)
    _ = |c d| := mul_one _

/-- The pronic mass of the linear drift `n` over `Icc 1 N` is pinched between `N/2` and `N`. -/
theorem sum_Icc_linear_pronic_bounds (N : ℕ) :
    (N : ℝ) / 2 ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧
      ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ (N : ℝ) := by
  constructor
  · calc (N : ℝ) / 2 = ∑ _n ∈ Icc 1 N, (1 / 2 : ℝ) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          sum_le_sum fun n hn => by
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            nlinarith
  · calc ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
          sum_le_sum fun n hn => by
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
            rw [div_le_one (by positivity)]
            nlinarith
      _ = N := by simp

/-- **Upper sub-horizon row bound from the harmonic tail.** For `T ≤ N`,
`E_T(row(c, N)) ≤ 2 E_T(c) + 2 N (m − m_N)²`. -/
theorem weightPronicEnergy_horizonRow_le_of_le (c : ℕ → ℝ) (m : ℝ) {N T : ℕ} (hTN : T ≤ N) :
    weightPronicEnergy (horizonRow c N) (horizonRowMean c N) T ≤
      2 * weightPronicEnergy c m T + 2 * (N : ℝ) * (m - horizonRowMean c N) ^ 2 := by
  set τ := m - horizonRowMean c N
  have hterm : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
          2 * τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : n ≤ N := (mem_Icc.mp hn).2.trans hTN
    have hp : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    rw [weightCenteredPrefix_horizonRow_of_le c m hnN]
    have hsq : (weightCenteredPrefix c m n + τ * n) ^ 2 ≤
        2 * weightCenteredPrefix c m n ^ 2 + 2 * τ ^ 2 * (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (weightCenteredPrefix c m n - τ * n)]
    calc (weightCenteredPrefix c m n + τ * n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ (2 * weightCenteredPrefix c m n ^ 2 + 2 * τ ^ 2 * (n : ℝ) ^ 2) /
            ((n : ℝ) * ((n : ℝ) + 1)) := div_le_div_of_nonneg_right hsq hp.le
      _ = 2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
  rw [weightPronicEnergy, weightPronicEnergy]
  calc ∑ n ∈ Icc 1 T,
        weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, (2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
          2 * τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) := sum_le_sum hterm
    _ = 2 * ∑ n ∈ Icc 1 T, weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          2 * τ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 2 * ∑ n ∈ Icc 1 T, weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          2 * τ ^ 2 * (T : ℝ) := by
        gcongr
        exact (sum_Icc_linear_pronic_bounds T).2
    _ ≤ 2 * ∑ n ∈ Icc 1 T, weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          2 * (N : ℝ) * τ ^ 2 := by
        have hTR : (T : ℝ) ≤ N := by exact_mod_cast hTN
        nlinarith [sq_nonneg τ]

/-- **Lower harmonic-tail bound from the sub-horizon row energy.**
`(N/2) (m − m_N)² ≤ 2 E_N(row(c, N)) + 2 E_N(c)`. -/
theorem harmonicTail_sq_mul_le_of_horizonRowEnergy (c : ℕ → ℝ) (m : ℝ) (N : ℕ) :
    (N : ℝ) / 2 * (m - horizonRowMean c N) ^ 2 ≤
      2 * weightPronicEnergy (horizonRow c N) (horizonRowMean c N) N +
        2 * weightPronicEnergy c m N := by
  set τ := m - horizonRowMean c N
  have hterm : ∀ n ∈ Icc 1 N,
      τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        2 * (weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1))) +
          2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : n ≤ N := (mem_Icc.mp hn).2
    have hp : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have heq := weightCenteredPrefix_horizonRow_of_le c m hnN
    have hsq : τ ^ 2 * (n : ℝ) ^ 2 ≤
        2 * weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 +
          2 * weightCenteredPrefix c m n ^ 2 := by
      have hdiff : τ * (n : ℝ) = weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n -
          weightCenteredPrefix c m n := by linarith
      calc τ ^ 2 * (n : ℝ) ^ 2 = (τ * (n : ℝ)) ^ 2 := by ring
        _ = (weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n -
              weightCenteredPrefix c m n) ^ 2 := by rw [hdiff]
        _ ≤ 2 * weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 +
              2 * weightCenteredPrefix c m n ^ 2 := by
            nlinarith [sq_nonneg (weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n +
              weightCenteredPrefix c m n)]
    calc τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
        = (τ ^ 2 * (n : ℝ) ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) := by ring
      _ ≤ (2 * weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 +
            2 * weightCenteredPrefix c m n ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hsq hp.le
      _ = _ := by ring
  calc (N : ℝ) / 2 * τ ^ 2 = τ ^ 2 * ((N : ℝ) / 2) := by ring
    _ ≤ τ ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_linear_pronic_bounds N).1 (sq_nonneg τ)
    _ = ∑ n ∈ Icc 1 N, τ ^ 2 * ((n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by rw [mul_sum]
    _ ≤ ∑ n ∈ Icc 1 N,
          (2 * (weightCenteredPrefix (horizonRow c N) (horizonRowMean c N) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) +
            2 * (weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) := sum_le_sum hterm
    _ = 2 * weightPronicEnergy (horizonRow c N) (horizonRowMean c N) N +
          2 * weightPronicEnergy c m N := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, weightPronicEnergy, weightPronicEnergy]

/-- **Exact characterization of the sub-horizon dipole obstruction.** For any paid weight `c`, the
sub-horizon row energies `E_T(row(c, N))` (`T ≤ N`) are uniformly bounded if and only if the
harmonic tail `τ_N = ∑_{d > N} c(d)/d` obeys the square-root law `sup_N N τ_N² < ∞`. -/
theorem subHorizon_horizonRowEnergy_bounded_iff {c : ℕ → ℝ} (hcB : ReceiverBounded c) :
    (∃ B : ℝ, ∀ N T : ℕ, T ≤ N →
      weightPronicEnergy (horizonRow c N) (horizonRowMean c N) T ≤ B) ↔
      ∃ M : ℝ, ∀ N : ℕ, (N : ℝ) * (∑' d : ℕ, c d / d - horizonRowMean c N) ^ 2 ≤ M := by
  obtain ⟨E, hE⟩ := hcB
  set m := ∑' d : ℕ, c d / d
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨4 * B + 4 * E, fun N => ?_⟩
    have h1 := harmonicTail_sq_mul_le_of_horizonRowEnergy c m N
    have h2 := hB N N le_rfl
    have h3 := hE N
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨2 * E + 2 * M, fun N T hTN => ?_⟩
    have h1 := weightPronicEnergy_horizonRow_le_of_le c m hTN
    have h2 := hE T
    have h3 := hM N
    linarith

/-- **Dyadic form of the sub-horizon dipole characterization.** For any paid weight `c`, the
sub-horizon dyadic row energies `E_T(dyadicRow c J)` (`T ≤ 2^J`) are uniformly bounded if and only
if `sup_J 2^J (m − dyadicRowMean c J)² < ∞`. -/
theorem subHorizon_dyadicRowEnergy_bounded_iff {c : ℕ → ℝ} (hcB : ReceiverBounded c) :
    (∃ B : ℝ, ∀ J T : ℕ, T ≤ 2 ^ J →
      weightPronicEnergy (dyadicRow c J) (dyadicRowMean c J) T ≤ B) ↔
      ∃ M : ℝ, ∀ J : ℕ, ((2 ^ J : ℕ) : ℝ) * (∑' d : ℕ, c d / d - dyadicRowMean c J) ^ 2 ≤ M := by
  obtain ⟨E, hE⟩ := hcB
  set m := ∑' d : ℕ, c d / d
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨4 * B + 4 * E, fun J => ?_⟩
    have h1 := harmonicTail_sq_mul_le_of_horizonRowEnergy c m (2 ^ J)
    have h2 := hB J (2 ^ J) le_rfl
    have h3 := hE (2 ^ J)
    rw [← dyadicRow_eq_horizonRow, ← dyadicRowMean_eq_horizonRowMean] at h1
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨2 * E + 2 * M, fun J T hTJ => ?_⟩
    have h1 := weightPronicEnergy_horizonRow_le_of_le c m hTJ
    rw [← dyadicRow_eq_horizonRow, ← dyadicRowMean_eq_horizonRowMean] at h1
    have h2 := hE T
    have h3 := hM J
    linarith

/-! ### §2. Exclusion of the sub-horizon dipole obstruction across `ε > Θ − 1/2` -/

/-- The Mertens partial sum in real form. -/
private theorem norm_mobiusMertensPartialSum_eq' (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ = |∑ e ∈ Icc 1 N, moebiusReal e| := by
  have h : mobiusMertensPartialSum N =
      ((∑ n ∈ range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
    simp only [mobiusMertensPartialSum, mobiusComplexCoefficient, Complex.ofReal_sum,
      Complex.ofReal_intCast]
  rw [h, Complex.norm_real, Real.norm_eq_abs, sum_range_moebius_eq_sum_Icc_moebiusReal]

/-- **Square-root harmonic-tail bound under subpower partial sums.** If `|s(d)| ≤ 1` and
`|∑_{e ≤ N} s(e)| ≤ C (N + 1)^β` with `0 ≤ β ≤ 1` and `β − 1/2 ≤ ε` (`ε > 0`), then
`N (m − horizonRowMean (s · d^{−ε}) N)²` is uniformly bounded for all `N`. -/
theorem harmonicTail_sq_mul_bounded_of_partialSum_rpow {s : ℕ → ℝ} {β C ε : ℝ}
    (hs1 : ∀ d, |s d| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hC0 : 0 ≤ C) (hε0 : 0 < ε)
    (hS : ∀ N : ℕ, |∑ e ∈ Icc 1 N, s e| ≤ C * ((N : ℝ) + 1) ^ β)
    (hβε : β - 1 / 2 ≤ ε) :
    ∃ M : ℝ, ∀ N : ℕ,
      (N : ℝ) * (∑' d : ℕ, dampedSignWeight s ε d / d -
        horizonRowMean (dampedSignWeight s ε) N) ^ 2 ≤ M := by
  set c := dampedSignWeight s ε
  have hsum := summable_dampedSignWeight_div_of_abs_le_one hε0 hs1
  set K : ℝ := (2 + 1 / ε) * (2 * C)
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ 2, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hK0]
  have hN1 : 1 ≤ N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set L : ℝ := 2 * C * (N : ℝ) ^ (β - 1) with hL
  have hL0 : 0 ≤ L := by positivity
  have hSl : ∀ x : ℕ, N ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (hN1.trans hx)
    have hNx : (N : ℝ) ≤ x := by exact_mod_cast hx
    have hxβ : (x : ℝ) ^ β = (x : ℝ) ^ (β - 1) * x := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    have h2β : (2 : ℝ) ^ β ≤ 2 := by
      calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 2 := Real.rpow_one 2
    calc |∑ e ∈ Icc 1 x, s e| ≤ C * ((x : ℝ) + 1) ^ β := hS x
      _ ≤ C * (2 * (x : ℝ)) ^ β :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hβ0) hC0
      _ = C * (2 ^ β * (x : ℝ) ^ β) := by rw [Real.mul_rpow (by norm_num) hx0.le]
      _ ≤ C * (2 * (x : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2β (Real.rpow_nonneg hx0.le _)) hC0
      _ = 2 * C * ((x : ℝ) ^ (β - 1) * x) := by rw [hxβ]; ring
      _ ≤ 2 * C * ((N : ℝ) ^ (β - 1) * x) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (rpow_sub_one_le_of_le hβ1 hN0 hNx) hx0.le)
          (by positivity)
      _ = L * x := by rw [hL]; ring
  have htail_eq : ∑' d : ℕ, c d / d - horizonRowMean c N =
      ∑' i : ℕ, ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (N + 1)) := by
    have h1 := hsum.sum_add_tsum_nat_add (N + 1)
    rw [dampedSign_sum_range_succ_eq_add_Icc, dampedSignWeight] at h1
    simp only [Nat.cast_zero, div_zero, zero_add] at h1
    rw [← h1, horizonRowMean_eq, add_sub_cancel_left]
    exact tsum_congr fun i => dampedSignWeight_div hε0 _
  have ht := (abs_tsum_tail_rpow_le_of_linear hN1 hL0 hε0 hs1 hSl).2
  rw [← htail_eq] at ht
  have hpow : (N : ℝ) ^ (β - 1) * (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  have habs : |∑' d : ℕ, c d / d - horizonRowMean c N| ≤ K * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc |∑' d : ℕ, c d / d - horizonRowMean c N|
        ≤ (2 + 1 / ε) * L * (N : ℝ) ^ (-ε) := ht
      _ = K * ((N : ℝ) ^ (β - 1) * (N : ℝ) ^ (-ε)) := by simp only [K, hL]; ring
      _ ≤ K * (N : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpow hK0
  have hsq : (∑' d : ℕ, c d / d - horizonRowMean c N) ^ 2 ≤ K ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hNpow : (N : ℝ) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hN0.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hN0.ne']
  calc (N : ℝ) * (∑' d : ℕ, c d / d - horizonRowMean c N) ^ 2
      ≤ (N : ℝ) * (K ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hN0.le
    _ = K ^ 2 * ((N : ℝ) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by ring
    _ = K ^ 2 := by rw [hNpow, mul_one]

/-- **The Möbius harmonic tail obeys the square-root law across the entire zero-width admission
range `ε > Θ − 1/2`.** -/
theorem moebius_harmonicTail_sq_mul_bounded_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    ∃ M : ℝ, ∀ N : ℕ,
      (N : ℝ) * (∑' d : ℕ, pmPowerDampedRealWeight ε d / d -
        horizonRowMean (pmPowerDampedRealWeight ε) N) ^ 2 ≤ M := by
  have hΘ := half_le_zetaZeroAbscissa
  have hε0 : 0 < ε := by linarith
  rw [pmPowerDampedRealWeight_eq_dampedSignWeight]
  rcases le_or_gt (1 / 2) ε with hε_half | hε_half
  · have htriv : ∀ N : ℕ, |∑ e ∈ Icc 1 N, moebiusReal e| ≤ 1 * ((N : ℝ) + 1) ^ (1 : ℝ) := by
      intro N
      rw [one_mul, Real.rpow_one]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ e ∈ Icc 1 N, |moebiusReal e| ≤ ∑ _e ∈ Icc 1 N, (1 : ℝ) :=
            sum_le_sum fun e _ => abs_moebiusReal_le_one' e
        _ = N := by simp
        _ ≤ (N : ℝ) + 1 := by linarith
    exact harmonicTail_sq_mul_bounded_of_partialSum_rpow abs_moebiusReal_le_one' zero_le_one
      le_rfl zero_le_one hε0 htriv (by linarith)
  · set β : ℝ := (zetaZeroAbscissa + (1 / 2 + ε)) / 2
    have hβΘ : zetaZeroAbscissa < β := by dsimp [β]; linarith
    have hβ0 : 0 ≤ β := by linarith
    have hβ1 : β ≤ 1 := by dsimp [β]; linarith
    have hβε : β - 1 / 2 ≤ ε := by dsimp [β]; linarith
    obtain ⟨C, hC0, hC⟩ :=
      mobiusMertens_subpower_zetaZeroAbscissa (β - zetaZeroAbscissa) (by linarith)
    have hC' : ∀ N : ℕ, |∑ e ∈ Icc 1 N, moebiusReal e| ≤ C * ((N : ℝ) + 1) ^ β := by
      intro N
      have := hC N
      rwa [norm_mobiusMertensPartialSum_eq', add_sub_cancel] at this
    exact harmonicTail_sq_mul_bounded_of_partialSum_rpow abs_moebiusReal_le_one' hβ0 hβ1 hC0 hε0
      hC' hβε

/-- **Exclusion of the sub-horizon dipole obstruction for the Möbius row across `ε > Θ − 1/2`.**
For every damping `ε > Θ − 1/2`, the sub-horizon row energies `E_T(row(c_ε, N))` (`T ≤ N`) are
uniformly bounded across all horizons `N` and cutoffs `T ≤ N`. -/
theorem subHorizon_horizonRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    ∃ B : ℝ, ∀ N T : ℕ, T ≤ N →
      weightPronicEnergy (horizonRow (pmPowerDampedRealWeight ε) N)
        (horizonRowMean (pmPowerDampedRealWeight ε) N) T ≤ B :=
  (subHorizon_horizonRowEnergy_bounded_iff
    (receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt hε)).mpr
    (moebius_harmonicTail_sq_mul_bounded_of_zetaZeroAbscissa_sub_half_lt hε)

/-- **Dyadic form of sub-horizon dipole exclusion for the Möbius row across `ε > Θ − 1/2`.** -/
theorem subHorizon_dyadicRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt {ε : ℝ}
    (hε : zetaZeroAbscissa - 1 / 2 < ε) :
    ∃ B : ℝ, ∀ J T : ℕ, T ≤ 2 ^ J →
      weightPronicEnergy (dyadicRow (pmPowerDampedRealWeight ε) J)
        (dyadicRowMean (pmPowerDampedRealWeight ε) J) T ≤ B := by
  obtain ⟨B, hB⟩ := subHorizon_horizonRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt hε
  exact ⟨B, fun J T hTJ => hB (2 ^ J) T hTJ⟩

/-- **Under RH, the sub-horizon dipole obstruction is excluded for the Möbius row at every `ε > 0`.** -/
theorem subHorizon_horizonRowEnergy_moebius_bounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ N T : ℕ, T ≤ N →
      weightPronicEnergy (horizonRow (pmPowerDampedRealWeight ε) N)
        (horizonRowMean (pmPowerDampedRealWeight ε) N) T ≤ B := by
  have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
  exact subHorizon_horizonRowEnergy_moebius_bounded_of_zetaZeroAbscissa_sub_half_lt (by linarith)

/-! ### §3. Prefix-stable partial-sum inheritance and full-horizon row bounds -/

/-- Truncating a sign pattern at horizon `N` freezes its partial sum at `min x N`. -/
theorem sum_Icc_horizonRow_eq_min (s : ℕ → ℝ) (N x : ℕ) :
    ∑ e ∈ Icc 1 x, horizonRow s N e = ∑ e ∈ Icc 1 (min x N), s e := by
  simp only [horizonRow]
  rw [← sum_filter]
  congr 1
  ext e
  simp only [mem_filter, mem_Icc]
  omega

/-- **Prefix-stability of linear partial-sum bounds.** If `|∑_{e ≤ x} s(e)| ≤ L x` for `x ≥ D` and
`N ≥ D`, then `horizonRow s N` satisfies the exact same linear bound `|∑_{e ≤ x} s_N(e)| ≤ L x`
for all `x ≥ D`. -/
theorem abs_sum_Icc_horizonRow_le_of_linear {s : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L) {D N : ℕ}
    (hDN : D ≤ N) (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) {x : ℕ} (hx : D ≤ x) :
    |∑ e ∈ Icc 1 x, horizonRow s N e| ≤ L * x := by
  rw [sum_Icc_horizonRow_eq_min]
  have hminD : D ≤ min x N := le_min hx hDN
  have hminx : ((min x N : ℕ) : ℝ) ≤ x := by exact_mod_cast min_le_left x N
  exact (hS (min x N) hminD).trans (mul_le_mul_of_nonneg_left hminx hL)

/-- **All-damping hyperbola rate transfer for arbitrary horizon rows.** If `|s(d)| ≤ 1` and
`|∑_{e ≤ x} s(e)| ≤ L x` for `x ≥ D ≥ 1`, then for **every** horizon `N`, every `0 < ε ≤ 1/2` and
every `n ≥ D`, the horizon-`N` row of `s(d) d^{−ε}` satisfies the exact same prefix bound as the
full weight:
`|A_{row(N)}(n)| ≤ 3 D^{1−ε} + (13/ε) L n D^{−ε}`. -/
theorem abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos {s : ℕ → ℝ} {L ε : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hs1 : ∀ d, |s d| ≤ 1) {n D : ℕ} (hD : 1 ≤ D)
    (hDn : D ≤ n) (hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x) (N : ℕ) :
    |weightCenteredPrefix (horizonRow (dampedSignWeight s ε) N)
        (horizonRowMean (dampedSignWeight s ε) N) n| ≤
      3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := by
  rcases le_or_gt D N with hDN | hND
  · -- Horizon at or above the cut `D`: `horizonRow s N` inherits the linear bound beyond `D`
    have hsN1 : ∀ d, |horizonRow s N d| ≤ 1 := fun d =>
      (abs_horizonRow_le s N d).trans (hs1 d)
    have hSN : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, horizonRow s N e| ≤ L * x :=
      fun x hx => abs_sum_Icc_horizonRow_le_of_linear hL hDN hS hx
    have h := abs_weightCenteredPrefix_dampedSign_le_of_linear_pos hL hε hε2 hsN1 hD hDn hSN
    rwa [← horizonRow_dampedSignWeight, tsum_horizonRow_div] at h
  · -- Horizon below the cut `D`: `n ≥ D > N` is trans-horizon, bounded by `∑_{d ≤ N} d^{−ε} ≤ 3 D^{1−ε}`
    have hNn : N < n := lt_of_lt_of_le hND hDn
    have h1 := abs_weightCenteredPrefix_horizonRow_le_of_lt (dampedSignWeight s ε) hNn
    have h2 : ∑ d ∈ Icc 1 N, |dampedSignWeight s ε d| ≤ ∑ d ∈ Icc 1 D, (d : ℝ) ^ (-ε) := by
      calc ∑ d ∈ Icc 1 N, |dampedSignWeight s ε d|
          ≤ ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-ε) := sum_le_sum fun d _ => by
            simp only [dampedSignWeight, abs_mul,
              abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
            exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
        _ ≤ ∑ d ∈ Icc 1 D, (d : ℝ) ^ (-ε) :=
            sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hND.le)
              fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) _
    have h3 := sum_Icc_rpow_neg_le_three hε hε2 hD
    have hpos : 0 ≤ 13 / ε * L * n * (D : ℝ) ^ (-ε) := by
      have := Real.rpow_nonneg (Nat.cast_nonneg D) (-ε)
      positivity
    linarith

/-- Trivial all-damping horizon-row prefix bound (`D = 1, L = 1`): for `0 < ε ≤ 1/2`, `n ≥ 1`, and
any horizon `N`, `|A_{row(c_ε, N)}(n)| ≤ 3 + (13/ε) n`. -/
theorem abs_weightCenteredPrefix_horizonRow_pmPowerDamped_le_trivial_pos {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    |weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
        (horizonRowMean (pmPowerDampedRealWeight ε) N) n| ≤
      3 + 13 / ε * n := by
  have hS : ∀ x, 1 ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ 1 * x := fun x _ => by
    rw [one_mul]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ Icc 1 x, |moebiusReal e| ≤ ∑ _e ∈ Icc 1 x, (1 : ℝ) :=
          sum_le_sum fun e _ => abs_moebiusReal_le_one' e
      _ = x := by simp
  have h := abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos zero_le_one hε hε2
    abs_moebiusReal_le_one' le_rfl hn hS N
  rw [← pmPowerDampedRealWeight_eq_dampedSignWeight] at h
  simpa using h

/-- **General subpower partial-sum transfer to all horizon rows.** If `|s(d)| ≤ 1` and
`|∑_{e ≤ M} s(e)| ≤ C (M + 1)^β` (`0 ≤ β < 1`), then for every `ε > β/2`, all horizon rows
`horizonRow (dampedSignWeight s ε) N` have uniformly bounded receiver energy across all `N` and `T`. -/
theorem horizonRows_bounded_dampedSign_of_partialSum_rpow {s : ℕ → ℝ} {β C ε : ℝ}
    (hs1 : ∀ d, |s d| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hC0 : 0 ≤ C)
    (hS : ∀ M : ℕ, |∑ e ∈ Icc 1 M, s e| ≤ C * ((M : ℝ) + 1) ^ β)
    (hε : β / 2 < ε) :
    ∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (dampedSignWeight s ε) N)
        (horizonRowMean (dampedSignWeight s ε) N) T ≤ E := by
  have hε0 : 0 < ε := by linarith
  rcases lt_or_ge (1 / 2) ε with hgt | hε2
  · obtain ⟨E, hE⟩ := (uniformReceiverBound_iff_half_lt (K := 1) one_pos hε0).mpr hgt
    refine ⟨E, fun N T => ?_⟩
    have hcN : DampedClass 1 ε (horizonRow (dampedSignWeight s ε) N) := fun d => by
      have hd : |horizonRow (dampedSignWeight s ε) N d| ≤ |dampedSignWeight s ε d| :=
        abs_horizonRow_le _ _ _
      refine hd.trans ?_
      rw [dampedSignWeight, one_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hs1 d)
    have h := hE _ hcN T
    rwa [tsum_horizonRow_div] at h
  -- For `β/2 < ε ≤ 1/2`, every `horizonRow s N` inherits the exact same subpower partial-sum bound!
  set β' : ℝ := min ((β + 2 * ε) / 2) 1
  have hβ_le : β ≤ β' := le_min (by linarith) hβ1.le
  have hβ'2ε : β' < 2 * ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hβ'1 : β' ≤ 1 := min_le_right _ _
  have hβ'0 : 0 ≤ β' := hβ0.trans hβ_le
  have h2β : 0 < 2 - β' := by linarith
  set a : ℝ := 1 / (2 - β')
  set γ : ℝ := a * (1 - ε)
  have hγhalf : γ < 1 / 2 := by
    dsimp [γ, a]; rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2β]; linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 * γ - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  -- Notice `horizonRow s N` satisfies `|∑_{e ≤ M} horizonRow s N e| ≤ C (M + 1)^β` for every `N`
  refine ⟨(3 + 52 / ε * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2), fun N T => ?_⟩
  -- Re-use the exact prefix bound on `horizonRow s N`
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; rw [div_le_one h2β]; linarith
  have hγeq : 1 + a * (β' - 1 - ε) = γ := by dsimp [γ, a]; field_simp; ring
  have hpre : ∀ n : ℕ, 1 ≤ n →
      |weightCenteredPrefix (horizonRow (dampedSignWeight s ε) N)
          (horizonRowMean (dampedSignWeight s ε) N) n| ≤
        (3 + 52 / ε * C) * (n : ℝ) ^ γ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set y : ℝ := (n : ℝ) ^ a with hy
    have hy1 : 1 ≤ y := by
      rw [hy, ← Real.one_rpow a]
      exact Real.rpow_le_rpow zero_le_one hn1 ha0.le
    have hy0 : 0 < y := by linarith
    set D : ℕ := ⌊y⌋₊ with hD
    have hD1 : 1 ≤ D := Nat.floor_pos.mpr hy1
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
    have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
    have hyD : y / 2 ≤ D := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : (1 : ℝ) ≤ D := by exact_mod_cast hD1
      rw [← hD] at h1
      linarith
    have hyn : y ≤ n := by
      rw [hy]
      calc (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 ha1
        _ = n := Real.rpow_one _
    have hDn : D ≤ n := by exact_mod_cast hDy.trans hyn
    set L : ℝ := 2 * C * (D : ℝ) ^ (β' - 1) with hL
    have hL0 : 0 ≤ L := by positivity
    have hSl : ∀ x : ℕ, D ≤ x → |∑ e ∈ Icc 1 x, s e| ≤ L * x := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (hD1.trans hx)
      have hx0 : (0 : ℝ) < x := by exact_mod_cast (hD1.trans hx)
      have hDx : (D : ℝ) ≤ x := by exact_mod_cast hx
      have hxβ : (x : ℝ) ^ β' = (x : ℝ) ^ (β' - 1) * x := by
        rw [Real.rpow_sub_one hx0.ne']; field_simp
      have h2β' : (2 : ℝ) ^ β' ≤ 2 := by
        calc (2 : ℝ) ^ β' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ'1
          _ = 2 := Real.rpow_one 2
      have hmon_β : ((x : ℝ) + 1) ^ β ≤ ((x : ℝ) + 1) ^ β' :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hβ_le
      calc |∑ e ∈ Icc 1 x, s e| ≤ C * ((x : ℝ) + 1) ^ β := hS x
        _ ≤ C * ((x : ℝ) + 1) ^ β' := mul_le_mul_of_nonneg_left hmon_β hC0
        _ ≤ C * (2 * (x : ℝ)) ^ β' :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hβ'0) hC0
        _ = C * (2 ^ β' * (x : ℝ) ^ β') := by rw [Real.mul_rpow (by norm_num) hx0.le]
        _ ≤ C * (2 * (x : ℝ) ^ β') :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2β' (Real.rpow_nonneg hx0.le _)) hC0
        _ = 2 * C * ((x : ℝ) ^ (β' - 1) * x) := by rw [hxβ]; ring
        _ ≤ 2 * C * ((D : ℝ) ^ (β' - 1) * x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (rpow_sub_one_le_of_le hβ'1 hD0 hDx) hx0.le)
            (by positivity)
        _ = L * x := by rw [hL]; ring
    have hA := abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos hL0 hε0 hε2 hs1 hD1
      hDn hSl N
    refine hA.trans ?_
    have hT1 : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ γ := by
      calc (D : ℝ) ^ (1 - ε) ≤ y ^ (1 - ε) := Real.rpow_le_rpow hD0.le hDy (by linarith)
        _ = (n : ℝ) ^ γ := by rw [hy, ← Real.rpow_mul hn0.le]
    have hpow : (D : ℝ) ^ (β' - 1 - ε) ≤ 2 * y ^ (β' - 1 - ε) := by
      have hexp0 : 0 ≤ 1 + ε - β' := by linarith
      have hexp1 : 1 + ε - β' ≤ 1 := by
        have : ε ≤ β' := le_min (by linarith) (by linarith)
        linarith
      have h2e : (2 : ℝ) ^ (1 + ε - β') ≤ 2 := by
        calc (2 : ℝ) ^ (1 + ε - β') ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1
          _ = 2 := Real.rpow_one 2
      have hylow : y ^ (1 + ε - β') / 2 ≤ (D : ℝ) ^ (1 + ε - β') := by
        calc y ^ (1 + ε - β') / 2 ≤ y ^ (1 + ε - β') / 2 ^ (1 + ε - β') :=
              div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le _) (by positivity) h2e
          _ = (y / 2) ^ (1 + ε - β') := (Real.div_rpow hy0.le (by norm_num) _).symm
          _ ≤ (D : ℝ) ^ (1 + ε - β') := Real.rpow_le_rpow (by positivity) hyD hexp0
      rw [show β' - 1 - ε = -(1 + ε - β') by ring, Real.rpow_neg hD0.le, Real.rpow_neg hy0.le]
      calc ((D : ℝ) ^ (1 + ε - β'))⁻¹ ≤ (y ^ (1 + ε - β') / 2)⁻¹ :=
            inv_anti₀ (by positivity) hylow
        _ = 2 * (y ^ (1 + ε - β'))⁻¹ := by rw [inv_div]; ring
    have hT2 : 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε) ≤ 52 / ε * C * (n : ℝ) ^ γ := by
      have hcomb : (D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε) = (D : ℝ) ^ (β' - 1 - ε) := by
        rw [← Real.rpow_add hD0]; ring_nf
      have hyγ : (n : ℝ) * y ^ (β' - 1 - ε) = (n : ℝ) ^ γ := by
        rw [hy, ← Real.rpow_mul hn0.le, ← hγeq, Real.rpow_add hn0, Real.rpow_one]
      calc 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
          = (26 / ε * C * (n : ℝ)) * ((D : ℝ) ^ (β' - 1) * (D : ℝ) ^ (-ε)) := by rw [hL]; ring
        _ = (26 / ε * C * (n : ℝ)) * (D : ℝ) ^ (β' - 1 - ε) := by rw [hcomb]
        _ ≤ (26 / ε * C * (n : ℝ)) * (2 * y ^ (β' - 1 - ε)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 52 / ε * C * ((n : ℝ) * y ^ (β' - 1 - ε)) := by ring
        _ = 52 / ε * C * (n : ℝ) ^ γ := by rw [hyγ]
    calc 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * (n : ℝ) * (D : ℝ) ^ (-ε)
        ≤ 3 * (n : ℝ) ^ γ + 52 / ε * C * (n : ℝ) ^ γ :=
          add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num)) hT2
      _ = (3 + 52 / ε * C) * (n : ℝ) ^ γ := by ring
  rw [weightPronicEnergy]
  calc ∑ n ∈ Icc 1 T,
        weightCenteredPrefix (horizonRow (dampedSignWeight s ε) N)
          (horizonRowMean (dampedSignWeight s ε) N) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, (3 + 52 / ε * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by
        refine sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsq : weightCenteredPrefix (horizonRow (dampedSignWeight s ε) N)
            (horizonRowMean (dampedSignWeight s ε) N) n ^ 2 ≤
            ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpre n hn1) 2
        have hpow : ((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (2 * γ - 2) := by
          have h1 : ((n : ℝ) ^ γ) ^ 2 = (n : ℝ) ^ (2 * γ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
            congr 1; push_cast; ring
          have h2 : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
          rw [h1, h2, Real.rpow_sub hn0 (2 * γ) 2]
        calc weightCenteredPrefix (horizonRow (dampedSignWeight s ε) N)
              (horizonRowMean (dampedSignWeight s ε) N) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
            ≤ ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
              div_le_div_of_nonneg_right hsq (by positivity)
          _ ≤ ((3 + 52 / ε * C) * (n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
          _ = (3 + 52 / ε * C) ^ 2 * (((n : ℝ) ^ γ) ^ 2 / ((n : ℝ) * (n : ℝ))) := by
              rw [mul_pow]; ring
          _ = (3 + 52 / ε * C) ^ 2 * (n : ℝ) ^ (2 * γ - 2) := by rw [hpow]
    _ = (3 + 52 / ε * C) ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (2 * γ - 2) := by rw [mul_sum]
    _ ≤ (3 + 52 / ε * C) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * γ - 2) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)

/-- **Dyadic rows are uniformly paid under subpower partial sums for `ε > β/2`.** -/
theorem dyadicRows_bounded_dampedSign_of_partialSum_rpow {s : ℕ → ℝ} {β C ε : ℝ}
    (hs1 : ∀ d, |s d| ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hC0 : 0 ≤ C)
    (hS : ∀ M : ℕ, |∑ e ∈ Icc 1 M, s e| ≤ C * ((M : ℝ) + 1) ^ β)
    (hε : β / 2 < ε) :
    ∃ E : ℝ, ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (dampedSignWeight s ε) J)
        (dyadicRowMean (dampedSignWeight s ε) J) T ≤ E := by
  obtain ⟨E, hE⟩ := horizonRows_bounded_dampedSign_of_partialSum_rpow hs1 hβ0 hβ1 hC0 hS hε
  exact ⟨E, fun J T => hE (2 ^ J) T⟩

/-- **Full-horizon Möbius row admission above half the zero abscissa `ε > Θ/2`.** -/
theorem horizonRows_bounded_moebius_of_half_zetaZeroAbscissa_lt {ε : ℝ}
    (hε : zetaZeroAbscissa / 2 < ε) :
    ∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (pmPowerDampedRealWeight ε) N)
        (horizonRowMean (pmPowerDampedRealWeight ε) N) T ≤ E := by
  have hΘ := half_le_zetaZeroAbscissa
  have hΘ1 := zetaZeroAbscissa_le_one
  have hε0 : 0 < ε := by linarith
  rcases lt_or_ge (1 / 2) ε with hgt | hε2
  · obtain ⟨E, hE⟩ := (uniformReceiverBound_iff_half_lt (K := 1) one_pos hε0).mpr hgt
    refine ⟨E, fun N T => ?_⟩
    have hcN : DampedClass 1 ε (horizonRow (pmPowerDampedRealWeight ε) N) := fun d =>
      (abs_horizonRow_le _ _ _).trans (dampedClass_one_pmPowerDampedRealWeight ε d)
    have h := hE _ hcN T
    rwa [tsum_horizonRow_div] at h
  have hΘlt1 : zetaZeroAbscissa < 1 := by linarith
  set β : ℝ := (zetaZeroAbscissa + min (2 * ε) 1) / 2
  have hβΘ : zetaZeroAbscissa < β := by
    have : zetaZeroAbscissa < min (2 * ε) 1 := lt_min (by linarith) hΘlt1
    dsimp [β]; linarith
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β < 1 := by
    have : min (2 * ε) 1 ≤ 1 := min_le_right _ _
    dsimp [β]; linarith
  have hβ2ε : β / 2 < ε := by
    have : min (2 * ε) 1 ≤ 2 * ε := min_le_left _ _
    dsimp [β]; linarith
  obtain ⟨C, hC0, hC⟩ :=
    mobiusMertens_subpower_zetaZeroAbscissa (β - zetaZeroAbscissa) (by linarith)
  have hC' : ∀ M : ℕ, |∑ e ∈ Icc 1 M, moebiusReal e| ≤ C * ((M : ℝ) + 1) ^ β := by
    intro M
    have := hC M
    rwa [norm_mobiusMertensPartialSum_eq', add_sub_cancel] at this
  rw [pmPowerDampedRealWeight_eq_dampedSignWeight]
  exact horizonRows_bounded_dampedSign_of_partialSum_rpow abs_moebiusReal_le_one' hβ0 hβ1 hC0
    hC' hβ2ε

/-- **Dyadic Möbius rows are uniformly paid across all `J, T` for `ε > Θ/2`.** -/
theorem dyadicRows_bounded_moebius_of_half_zetaZeroAbscissa_lt {ε : ℝ}
    (hε : zetaZeroAbscissa / 2 < ε) :
    ∃ E : ℝ, ∀ J T : ℕ,
      weightPronicEnergy (dyadicRow (pmPowerDampedRealWeight ε) J)
        (dyadicRowMean (pmPowerDampedRealWeight ε) J) T ≤ E := by
  obtain ⟨E, hE⟩ := horizonRows_bounded_moebius_of_half_zetaZeroAbscissa_lt hε
  exact ⟨E, fun J T => hE (2 ^ J) T⟩

/-- **All-damping Vinogradov–Korobov prefix bound for arbitrary Möbius horizon rows.**
There exist absolute constants `K ≥ 0` and `N₁` such that for every `0 < ε ≤ 1/2`, every horizon
`N`, and every `n ≥ N₁`,
`|A_{row(c_ε, N)}(n)| ≤ (K/ε) n^{1−ε} exp(−√(log n)/40)`. -/
theorem exists_abs_weightCenteredPrefix_horizonRow_pmPowerDamped_le_all_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₁ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ N n : ℕ, N₁ ≤ n →
      |weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
          (horizonRowMean (pmPowerDampedRealWeight ε) N) n| ≤
        K / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
  obtain ⟨B, hB, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((hlog.eventually_ge_atTop 4).and (hlog.eventually_ge_atTop (9 / 4 * Real.log (N₀ + 2))))
  refine ⟨3 + 26 * B, by positivity, N₁, fun ε hε hε2 N n hn => ?_⟩
  obtain ⟨hℓ4, hℓN⟩ := hN₁ n hn
  set ℓ := Real.log n with hℓdef
  set u := Real.sqrt ℓ with hudef
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hℓdef, this, Real.log_zero] at hℓ4; linarith
  have huu : u ^ 2 = ℓ := Real.sq_sqrt (by linarith)
  have hu2 : 2 ≤ u := by
    rw [hudef, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hℓ4
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y := Real.exp (ℓ - u / 20) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = ℓ - u / 20 := Real.log_exp _
  have hkey : 4 / 9 * ℓ ≤ ℓ - u / 20 - Real.log 2 := by nlinarith
  have hN2 : (0 : ℝ) < (N₀ : ℝ) + 2 := by positivity
  have hy2 : (N₀ : ℝ) + 2 ≤ y / 2 := by
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 2) ≤ ℓ - u / 20 - Real.log 2 by
      linarith)
    rwa [Real.exp_log hN2, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  set D := ⌊y⌋₊ with hDdef
  have hDy : (D : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyD : y / 2 ≤ (D : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hDN₀ : N₀ ≤ D := by
    have : (N₀ : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ D := by linarith
    exact_mod_cast this
  have hDn : D ≤ n := by
    have hyn : y ≤ n := by
      rw [hydef, ← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by rw [← hℓdef]; linarith [Real.sqrt_nonneg ℓ])
    exact_mod_cast hDy.trans hyn
  have hlogD_le : Real.log D ≤ ℓ - u / 20 := by
    rw [← hlogy]; exact Real.log_le_log hD0 hDy
  have hlogD_ge : ℓ - u / 20 - Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by positivity) hyD
    rwa [Real.log_div hy0.ne' (by norm_num), hlogy] at h
  have hsqD : 2 / 3 * u ≤ Real.sqrt (Real.log D) := by
    have h49 : (2 / 3 * u) ^ 2 = 4 / 9 * ℓ := by rw [mul_pow, huu]; ring
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / 3 * u), h49]
    exact Real.sqrt_le_sqrt (by linarith)
  set L := B * Real.exp (-(Real.sqrt (Real.log D) / 12)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hS : ∀ x, D ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ L * x := by
    intro x hx
    have hxR : (D : ℝ) ≤ x := by exact_mod_cast hx
    have hmono : Real.exp (-(Real.sqrt (Real.log x) / 12)) ≤
        Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
      Real.exp_le_exp.mpr (by
        have := Real.sqrt_le_sqrt (Real.log_le_log hD0 hxR)
        linarith)
    calc _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log x) / 12)) := hM x (hDN₀.trans hx)
      _ ≤ B * x * Real.exp (-(Real.sqrt (Real.log D) / 12)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = L * x := by rw [hLdef]; ring
  have hhyp := abs_weightCenteredPrefix_horizonRow_dampedSign_le_of_linear_pos hL0 hε hε2
    abs_moebiusReal_le_one' hD1 hDn hS N
  rw [← pmPowerDampedRealWeight_eq_dampedSignWeight] at hhyp
  have hnpow : (n : ℝ) ^ (1 - ε) = Real.exp (ℓ * (1 - ε)) := Real.rpow_def_of_pos hn0 _
  have hshort : (D : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  have hlong : (n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12)) ≤
      2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) := by
    rw [Real.rpow_def_of_pos hD0, hnpow, ← Real.exp_log hn0, ← hℓdef, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  have h3ε : (3 : ℝ) ≤ 3 / ε := by
    rw [le_div_iff₀ hε]; linarith
  calc _ ≤ 3 * (D : ℝ) ^ (1 - ε) + 13 / ε * L * n * (D : ℝ) ^ (-ε) := hhyp
    _ = 3 * (D : ℝ) ^ (1 - ε) +
          (13 / ε * B) * ((n : ℝ) * (D : ℝ) ^ (-ε) * Real.exp (-(Real.sqrt (Real.log D) / 12))) := by
        rw [hLdef]; ring
    _ ≤ (3 / ε) * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) +
          (13 / ε * B) * (2 * ((n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40)))) := by
        refine add_le_add (mul_le_mul h3ε hshort (by positivity) (by positivity)) ?_
        exact mul_le_mul_of_nonneg_left hlong (by positivity)
    _ = (3 + 26 * B) / ε * (n : ℝ) ^ (1 - ε) * Real.exp (-(Real.sqrt (Real.log n) / 40)) := by
        rw [hudef, hℓdef]; ring

/-- **All horizon rows of the Möbius weight are uniformly paid on the Vinogradov–Korobov zero-free
band above any `ε₀ > 0`.** -/
theorem exists_horizonRow_receiver_le_on_zeroFreeBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (N T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        weightPronicEnergy (horizonRow (pmPowerDampedRealWeight ε) N)
          (horizonRowMean (pmPowerDampedRealWeight ε) N) T ≤ E := by
  obtain ⟨K, hK, N₁, hpre⟩ := exists_abs_weightCenteredPrefix_horizonRow_pmPowerDamped_le_all_pos
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 40 by norm_num)
  set S := ∑' m : ℕ, Real.exp (-(1 / 40 * Real.sqrt (Real.log m))) / m
  refine ⟨(N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 + (K / ε₀) ^ 2 * S,
    fun N T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  rw [weightPronicEnergy]
  set f := fun n : ℕ => weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
    (horizonRowMean (pmPowerDampedRealWeight ε) N) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) with hfdef
  have hsplit : ∑ n ∈ Icc 1 T, f n ≤
      ∑ n ∈ Icc 1 T with n < N₁, f n + ∑ n ∈ Icc 1 T with ¬ n < N₁, f n :=
    (sum_filter_add_sum_filter_not _ _ _).ge
  have hsmall : ∑ n ∈ Icc 1 T with n < N₁, f n ≤ (N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
    have hsub : (Icc 1 T).filter (fun n => n < N₁) ⊆ range N₁ := fun n hn => by
      simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N₁), f n ≤ (3 + 13 / ε₀ * N₁) ^ 2 := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hA := abs_weightCenteredPrefix_horizonRow_pmPowerDamped_le_trivial_pos hε hε2 hn.1.1 N
      have h13 : 13 / ε ≤ 13 / ε₀ := div_le_div_of_nonneg_left (by norm_num) hε₀ hε_ge
      have hA' : |weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
          (horizonRowMean (pmPowerDampedRealWeight ε) N) n| ≤ 3 + 13 / ε₀ * N₁ := by
        have hnN : (n : ℝ) ≤ N₁ := by exact_mod_cast hn.2.le
        have := mul_le_mul h13 hnN (Nat.cast_nonneg n) (by positivity)
        linarith
      have hA2 : weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
          (horizonRowMean (pmPowerDampedRealWeight ε) N) n ^ 2 ≤ (3 + 13 / ε₀ * N₁) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hA' 2
      simp only [hfdef]
      rw [div_le_iff₀ (by positivity)]
      exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
    calc ∑ n ∈ Icc 1 T with n < N₁, f n ≤ ∑ n ∈ Icc 1 T with n < N₁, (3 + 13 / ε₀ * (N₁ : ℝ)) ^ 2 :=
          sum_le_sum hterm
      _ = (((Icc 1 T).filter (fun n => n < N₁)).card : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N₁ : ℝ) * (3 + 13 / ε₀ * N₁) ^ 2 := by
          gcongr
          exact_mod_cast (card_le_card hsub).trans (card_range N₁).le
  have hlarge : ∑ n ∈ Icc 1 T with ¬ n < N₁, f n ≤ (K / ε₀) ^ 2 * S := by
    have hKε : K / ε ≤ K / ε₀ := div_le_div_of_nonneg_left hK hε₀ hε_ge
    have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n < N₁),
        f n ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) := by
      intro n hn
      simp only [mem_filter, mem_Icc, not_lt] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
      have hn0 : (0 : ℝ) < n := by linarith
      set ℓ := Real.log n with hℓ
      set u := Real.sqrt ℓ
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hn1
      have huu : u ^ 2 = ℓ := Real.sq_sqrt hℓ0
      have hu0 : 0 ≤ u := Real.sqrt_nonneg _
      have hA := (hpre ε hε hε2 N n hn.2).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKε (Real.rpow_nonneg hn0.le _)) (Real.exp_pos _).le)
      have hA2 : weightCenteredPrefix (horizonRow (pmPowerDampedRealWeight ε) N)
          (horizonRowMean (pmPowerDampedRealWeight ε) N) n ^ 2 ≤
          (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hbandn : (1 - 2 * ε) * ℓ ≤ u / 40 := by
        have huT : u ≤ Real.sqrt (Real.log T) := Real.sqrt_le_sqrt
          (Real.log_le_log hn0 (by exact_mod_cast hn.1.2))
        rcases (Real.sqrt_nonneg (Real.log T)).eq_or_lt with h0 | hpos
        · have hu00 : u = 0 := le_antisymm (h0 ▸ huT) hu0
          rw [← huu, hu00]; nlinarith
        · have hb : 1 - 2 * ε ≤ 2 / (80 * Real.sqrt (Real.log T)) := by
            have : 2 / (80 * Real.sqrt (Real.log T)) = 2 * (1 / (80 * Real.sqrt (Real.log T))) := by
              ring
            rw [this]; linarith
          calc (1 - 2 * ε) * ℓ = (1 - 2 * ε) * u * u := by rw [← huu]; ring
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * u * u := by gcongr
            _ ≤ 2 / (80 * Real.sqrt (Real.log T)) * Real.sqrt (Real.log T) * u := by gcongr
            _ = u / 40 := by field_simp; ring
      have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          Real.exp (-(1 / 40 * u)) / n := by
        have hnpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = Real.exp (2 * ((1 - ε) * ℓ)) := by
          rw [Real.rpow_def_of_pos hn0, ← Real.exp_nat_mul, hℓ]; congr 1; push_cast; ring
        have hex : Real.exp (-(u / 40)) ^ 2 = Real.exp (-(u / 20)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        rw [hnpow, hex, ← Real.exp_add, div_le_div_iff₀ (by positivity) hn0]
        have hnn : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
        have hnexp : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
        calc Real.exp (2 * ((1 - ε) * ℓ) + -(u / 20)) * n
            = Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) *
                Real.exp ((1 - 2 * ε) * ℓ - u / 40) := by
              rw [hnexp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 1; ring
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * (n : ℝ)) * 1 := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by linarith)
          _ ≤ Real.exp (-(1 / 40 * u)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hnn (Real.exp_pos _).le
      calc f n ≤ (K / ε₀ * (n : ℝ) ^ (1 - ε) * Real.exp (-(u / 40))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) :=
            div_le_div_of_nonneg_right hA2 (by positivity)
        _ = (K / ε₀) ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 * Real.exp (-(u / 40)) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) := by ring
        _ ≤ (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    calc ∑ n ∈ Icc 1 T with ¬ n < N₁, f n
        ≤ ∑ n ∈ Icc 1 T with ¬ n < N₁,
            (K / ε₀) ^ 2 * (Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n) :=
          sum_le_sum hterm
      _ = (K / ε₀) ^ 2 * ∑ n ∈ Icc 1 T with ¬ n < N₁,
            Real.exp (-(1 / 40 * Real.sqrt (Real.log n))) / n := by rw [mul_sum]
      _ ≤ (K / ε₀) ^ 2 * S := mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun m _ => by positivity) (sq_nonneg _)
  linarith

/-! ### §4. Exact divisor-quotient horizon-row convolution law and critical Wiener closure -/

/-- The delta kernel at modulus `q`: `δ_q(k) = 1` if `k = q` else `0`. -/
def deltaModulus (q k : ℕ) : ℝ := if k = q then 1 else 0

theorem dirichletConv_deltaModulus_apply (q : ℕ) (w : ℕ → ℝ) (d : ℕ) :
    RHTower.dirichletConv (deltaModulus q) w d = if q ∣ d ∧ d ≠ 0 then w (d / q) else 0 := by
  simp only [RHTower.dirichletConv, deltaModulus, ite_mul, one_mul, zero_mul, sum_ite_eq',
    Nat.mem_divisors]

theorem hasSum_deltaModulus_div (q : ℕ) :
    HasSum (fun k : ℕ => deltaModulus q k / k) (1 / (q : ℝ)) := by
  have h : (fun k : ℕ => deltaModulus q k / k) = fun k : ℕ => if k = q then 1 / (q : ℝ) else 0 := by
    funext k; simp only [deltaModulus]; split_ifs with hk <;> simp [hk]
  rw [h]
  exact hasSum_ite_eq q (1 / (q : ℝ))

theorem summable_abs_deltaModulus_div (q : ℕ) :
    Summable (fun k : ℕ => |deltaModulus q k / k|) := by
  refine summable_of_ne_finset_zero (s := {q}) fun k hk => ?_
  simp only [mem_singleton] at hk
  simp [deltaModulus, hk]

/-- The centred prefix of `δ_q` at mean `1/q` is the sawtooth `⌊n/q⌋ − n/q`. -/
theorem weightCenteredPrefix_deltaModulus {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    weightCenteredPrefix (deltaModulus q) (1 / (q : ℝ)) n =
      ((n / q : ℕ) : ℝ) - (n : ℝ) / q := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  have hsum : ∑ k ∈ Icc 1 n, deltaModulus q k * ((n / k : ℕ) : ℝ) = ((n / q : ℕ) : ℝ) := by
    simp only [deltaModulus, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_Icc]
    split_ifs with h
    · rfl
    · have hnq : n < q := by omega
      simp [Nat.div_eq_of_lt hnq]
  rw [hsum]; ring

/-- **Dilation of a horizon row.** For `q ≥ 1`, `δ_q ⋆ row(c, M)` has centred prefix
`A_{row(c, M)}(⌊n/q⌋) + m_c(M) (⌊n/q⌋ − n/q)` at mean `(1/q) m_c(M)`. -/
theorem weightCenteredPrefix_dirichletConv_deltaModulus {q : ℕ} (hq : 1 ≤ q) (c : ℕ → ℝ)
    (M n : ℕ) :
    weightCenteredPrefix (RHTower.dirichletConv (deltaModulus q) (horizonRow c M))
        ((1 / (q : ℝ)) * horizonRowMean c M) n =
      weightCenteredPrefix (horizonRow c M) (horizonRowMean c M) (n / q) +
        horizonRowMean c M * (((n / q : ℕ) : ℝ) - (n : ℝ) / q) := by
  rw [weightCenteredPrefix_dirichletConv, weightCenteredPrefix_deltaModulus hq]
  congr 1
  simp only [deltaModulus, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_Icc]
  split_ifs with h
  · rfl
  · have hnq : n < q := by omega
    rw [Nat.div_eq_of_lt hnq, weightCenteredPrefix_zero]

/-- **Horizon-row decomposition of a Dirichlet convolution.** Because `q m ≤ N ⇔ m ≤ ⌊N/q⌋` for
`q ≥ 1`, `horizonRow (g ⋆ c) N` decomposes on `d ≥ 1` into `∑_{q ≤ N} g(q) (δ_q ⋆ horizonRow c (N / q))`. -/
theorem horizonRow_dirichletConv_eq_of_pos (g c : ℕ → ℝ) (N : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    horizonRow (RHTower.dirichletConv g c) N d =
      ∑ q ∈ Icc 1 N, g q * RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d := by
  have hd0 : d ≠ 0 := by omega
  have hterm : ∀ q ∈ Icc 1 N,
      g q * RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d =
        if d ≤ N then (if q ∣ d then g q * c (d / q) else 0) else 0 := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    rw [dirichletConv_deltaModulus_apply]
    by_cases hqd : q ∣ d
    · rw [if_pos ⟨hqd, hd0⟩, if_pos hqd, horizonRow]
      have hiff : d / q ≤ N / q ↔ d ≤ N := by
        rw [Nat.le_div_iff_mul_le hq1, Nat.div_mul_cancel hqd]
      simp only [hiff]
      split_ifs <;> ring
    · rw [if_neg (fun h => hqd h.1), if_neg hqd, mul_zero, ite_self]
  rw [sum_congr rfl hterm]
  simp only [horizonRow]
  split_ifs with hdN
  · rw [← sum_filter]
    have hset : (Icc 1 N).filter (fun q => q ∣ d) = d.divisors := by
      ext q
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨-, h⟩; exact ⟨h, hd0⟩
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hd, (Nat.le_of_dvd hd h).trans hdN⟩, h⟩
    rw [hset, RHTower.dirichletConv]
  · simp

/-- For `1 ≤ q ≤ N`, `δ_q ⋆ horizonRow c (N / q)` vanishes outside `Icc 1 N`. -/
theorem dirichletConv_deltaModulus_horizonRow_eq_zero {q N d : ℕ} (hq : 1 ≤ q) (c : ℕ → ℝ)
    (hd : d ∉ Icc 1 N) :
    RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d = 0 := by
  rw [dirichletConv_deltaModulus_apply]
  split_ifs with h
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero h.2
    have hNd : N < d := by simp only [mem_Icc, not_and, not_le] at hd; exact hd hd1
    have hdiv : ¬ d / q ≤ N / q := by
      rw [Nat.le_div_iff_mul_le hq, Nat.div_mul_cancel h.1]
      omega
    simp [horizonRow, hdiv]
  · rfl

/-- **Mean decomposition of a horizon-row convolution.**
`m_{row(g⋆c, N)} = ∑_{q ≤ N} (g(q)/q) m_{row(c, ⌊N/q⌋)}`. -/
theorem horizonRowMean_dirichletConv_eq (g c : ℕ → ℝ) (N : ℕ) :
    horizonRowMean (RHTower.dirichletConv g c) N =
      ∑ q ∈ Icc 1 N, g q * ((1 / (q : ℝ)) * horizonRowMean c (N / q)) := by
  rw [horizonRowMean]
  have h1 : ∀ d ∈ Icc 1 N, horizonRow (RHTower.dirichletConv g c) N d / d =
      ∑ q ∈ Icc 1 N, g q * (RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d / d) := by
    intro d hd
    rw [horizonRow_dirichletConv_eq_of_pos g c N (mem_Icc.mp hd).1, sum_div]
    exact sum_congr rfl fun q _ => mul_div_assoc _ _ _
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun q hq => ?_
  rw [← mul_sum]
  congr 1
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  have hsum := hasSum_dirichletConv_div (hasSum_deltaModulus_div q)
    (hasSum_horizonRow_div c (N / q)) (summable_abs_deltaModulus_div q)
    ((hasSum_horizonRow_div (fun d => |c d|) (N / q)).summable.congr fun d => by
      simp only [horizonRow, abs_div, Nat.abs_cast]; split_ifs <;> simp)
  have hfin : HasSum
      (fun d : ℕ => RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d / d)
      (∑ d ∈ Icc 1 N, RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d / d) :=
    hasSum_sum_of_ne_finset_zero fun d hd => by
      rw [dirichletConv_deltaModulus_horizonRow_eq_zero hq1 c hd, zero_div]
  exact hfin.unique hsum

/-- **Exact prefix decomposition of a horizon-row convolution.**
`A_{row(g⋆c, N)}(n) = ∑_{q ≤ N} g(q) A_{row(c, ⌊N/q⌋)}(⌊n/q⌋) + ∑_{q ≤ N} g(q) m_c(⌊N/q⌋) (⌊n/q⌋ − n/q)`. -/
theorem weightCenteredPrefix_horizonRow_dirichletConv (g c : ℕ → ℝ) (N n : ℕ) :
    weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
        (horizonRowMean (RHTower.dirichletConv g c) N) n =
      ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix (horizonRow c (N / q))
          (horizonRowMean c (N / q)) (n / q) +
        ∑ q ∈ Icc 1 N, g q * (horizonRowMean c (N / q) * (((n / q : ℕ) : ℝ) - (n : ℝ) / q)) := by
  have hfloor : ∑ d ∈ Icc 1 n, horizonRow (RHTower.dirichletConv g c) N d * ((n / d : ℕ) : ℝ) =
      ∑ q ∈ Icc 1 N, g q * ∑ d ∈ Icc 1 n,
        RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d * ((n / d : ℕ) : ℝ) := by
    have h1 : ∀ d ∈ Icc 1 n, horizonRow (RHTower.dirichletConv g c) N d * ((n / d : ℕ) : ℝ) =
        ∑ q ∈ Icc 1 N, g q *
          (RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)) d * ((n / d : ℕ) : ℝ)) := by
      intro d hd
      rw [horizonRow_dirichletConv_eq_of_pos g c N (mem_Icc.mp hd).1, sum_mul]
      exact sum_congr rfl fun q _ => mul_assoc _ _ _
    rw [sum_congr rfl h1, sum_comm]
    exact sum_congr rfl fun q _ => (mul_sum _ _ _).symm
  have hpref : weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
      (horizonRowMean (RHTower.dirichletConv g c) N) n =
      ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix
        (RHTower.dirichletConv (deltaModulus q) (horizonRow c (N / q)))
        ((1 / (q : ℝ)) * horizonRowMean c (N / q)) n := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hfloor,
      horizonRowMean_dirichletConv_eq, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
    ring
  rw [hpref, ← sum_add_distrib]
  refine sum_congr rfl fun q hq => ?_
  rw [weightCenteredPrefix_dirichletConv_deltaModulus (mem_Icc.mp hq).1 c (N / q) n, mul_add]

/-- **Pronic norm bound for a horizon-row convolution.** If `g ∈ CriticalWiener`, `∑ |c(d)/d| < ∞`,
and all horizon rows of `c` have pronic norm `≤ B`, then every horizon row of `g ⋆ c` has pronic
norm at most `(∑_q |g(q)| q^{−1/2}) (B + √2 ∑_d |c(d)/d|)`. -/
theorem pronicNorm_horizonRow_dirichletConv_le {g c : ℕ → ℝ} (hg : CriticalWiener g)
    (hc : Summable (fun d : ℕ => |c d / d|)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ M T : ℕ, pronicNorm (weightCenteredPrefix (horizonRow c M) (horizonRowMean c M)) T ≤ B)
    (N T : ℕ) :
    pronicNorm (weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
        (horizonRowMean (RHTower.dirichletConv g c) N)) T ≤
      (∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) *
        (B + Real.sqrt 2 * ∑' d : ℕ, |c d / d|) := by
  have hW : Summable (fun q : ℕ => |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) := hg
  set G := ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  set M₀ := ∑' d : ℕ, |c d / d|
  have hM₀ : 0 ≤ M₀ := tsum_nonneg fun _ => abs_nonneg _
  have hG0 : ∀ q : ℕ, 0 ≤ |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) := fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hfin : ∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G :=
    hW.sum_le_tsum _ fun q _ => hG0 q
  have hrep : weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
      (horizonRowMean (RHTower.dirichletConv g c) N) = fun n =>
      ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix (horizonRow c (N / q))
          (horizonRowMean c (N / q)) (n / q) +
        ∑ q ∈ Icc 1 N, (g q * horizonRowMean c (N / q)) * (((n / q : ℕ) : ℝ) - (n : ℝ) / q) := by
    funext n
    rw [weightCenteredPrefix_horizonRow_dirichletConv]
    congr 1
    exact sum_congr rfl fun q _ => by ring
  rw [hrep]
  have h1 : pronicNorm (fun n => ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix (horizonRow c (N / q))
      (horizonRowMean c (N / q)) (n / q)) T ≤
      (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * B := by
    refine (pronicNorm_sum_le _ _ T).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun q hq => ?_
    rw [pronicNorm_smul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hdil := pronicNorm_dilate_le (weightCenteredPrefix (horizonRow c (N / q))
      (horizonRowMean c (N / q))) (weightCenteredPrefix_zero _ _) (mem_Icc.mp hq).1 T
    exact hdil.trans (mul_le_mul_of_nonneg_left (hB (N / q) T)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have h2 : pronicNorm (fun n => ∑ q ∈ Icc 1 N, (g q * horizonRowMean c (N / q)) *
      (((n / q : ℕ) : ℝ) - (n : ℝ) / q)) T ≤
      (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.sqrt 2 * M₀) := by
    refine (pronicNorm_sum_le _ _ T).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun q hq => ?_
    rw [pronicNorm_smul, abs_mul]
    have hsaw := pronicNorm_sawtooth_le (mem_Icc.mp hq).1 T
    have hm := abs_horizonRowMean_le_tsum hc (N / q)
    calc |g q| * |horizonRowMean c (N / q)| * pronicNorm (fun n => ((n / q : ℕ) : ℝ) - (n : ℝ) / q) T
        ≤ |g q| * M₀ * (Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm (abs_nonneg _)) hsaw
            (pronicNorm_nonneg _ T) (mul_nonneg (abs_nonneg _) hM₀)
      _ = |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.sqrt 2 * M₀) := by ring
  calc _ ≤ (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * B +
          (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.sqrt 2 * M₀) :=
        (pronicNorm_add_le _ _ T).trans (add_le_add h1 h2)
    _ = (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (B + Real.sqrt 2 * M₀) := by ring
    _ ≤ G * (B + Real.sqrt 2 * M₀) :=
        mul_le_mul_of_nonneg_right hfin (by positivity)

/-- **Critical Wiener convolutions preserve uniformly bounded horizon rows.** -/
theorem horizonRows_bounded_dirichletConv {g c : ℕ → ℝ} (hg : CriticalWiener g)
    (hc : Summable (fun d : ℕ => |c d / d|))
    (hcR : ∃ E : ℝ, ∀ N T : ℕ, weightPronicEnergy (horizonRow c N) (horizonRowMean c N) T ≤ E) :
    ∃ E' : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (RHTower.dirichletConv g c) N)
        (horizonRowMean (RHTower.dirichletConv g c) N) T ≤ E' := by
  obtain ⟨E, hE⟩ := hcR
  set G := ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  set M₀ := ∑' d : ℕ, |c d / d|
  set B := Real.sqrt (max E 0)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hB : ∀ M T : ℕ, pronicNorm (weightCenteredPrefix (horizonRow c M) (horizonRowMean c M)) T ≤ B :=
    fun M T => by
      rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
      exact Real.sqrt_le_sqrt ((hE M T).trans (le_max_left E 0))
  refine ⟨(G * (B + Real.sqrt 2 * M₀)) ^ 2, fun N T => ?_⟩
  rw [weightPronicEnergy_eq_sq_pronicNorm]
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T)
    (pronicNorm_horizonRow_dirichletConv_le hg hc hB0 hB N T) 2

/-- **The Möbius and Liouville horizon rows are uniformly paid at the exact same dampings `ε > 0`.** -/
theorem horizonRows_bounded_moebius_iff_liouville {ε : ℝ} (hε : 0 < ε) :
    (∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (pmPowerDampedRealWeight ε) N)
        (horizonRowMean (pmPowerDampedRealWeight ε) N) T ≤ E) ↔
    (∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (dampedSignWeight RHTower.liouvilleR ε) N)
        (horizonRowMean (dampedSignWeight RHTower.liouvilleR ε) N) T ≤ E) := by
  constructor
  · intro hμ
    rw [show dampedSignWeight RHTower.liouvilleR ε =
        RHTower.dirichletConv (dampedSignWeight RHTower.squareIndicatorR ε)
          (pmPowerDampedRealWeight ε) from funext (dampedLiouville_eq_dirichletConv ε)]
    exact horizonRows_bounded_dirichletConv (criticalWiener_dampedSquare hε)
      (summable_abs_pmPowerDamped_div hε) hμ
  · intro hlam
    rw [show pmPowerDampedRealWeight ε =
        RHTower.dirichletConv (dampedSignWeight squareMoebius ε)
          (dampedSignWeight RHTower.liouvilleR ε) from funext (dampedMoebius_eq_dirichletConv ε)]
    exact horizonRows_bounded_dirichletConv (criticalWiener_dampedSquareMoebius hε)
      (summable_abs_dampedLiouville_div hε) hlam

/-- **Full-horizon Liouville row admission above half the zero abscissa `ε > Θ/2`.** -/
theorem horizonRows_bounded_liouville_of_half_zetaZeroAbscissa_lt {ε : ℝ}
    (hε : zetaZeroAbscissa / 2 < ε) :
    ∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (dampedSignWeight RHTower.liouvilleR ε) N)
        (horizonRowMean (dampedSignWeight RHTower.liouvilleR ε) N) T ≤ E := by
  have hε0 : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  exact (horizonRows_bounded_moebius_iff_liouville hε0).mp
    (horizonRows_bounded_moebius_of_half_zetaZeroAbscissa_lt hε)

/-- **All horizon rows of the damped Liouville weight are uniformly paid on the Vinogradov–Korobov
zero-free band above any `ε₀ > 0`.** -/
theorem exists_liouville_horizonRow_receiver_le_on_zeroFreeBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (N T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - 1 / (80 * Real.sqrt (Real.log T)) ≤ ε →
        weightPronicEnergy (horizonRow (dampedSignWeight RHTower.liouvilleR ε) N)
          (horizonRowMean (dampedSignWeight RHTower.liouvilleR ε) N) T ≤ E := by
  obtain ⟨Eμ, hEμ⟩ := exists_horizonRow_receiver_le_on_zeroFreeBand_of_pos hε₀
  set G₀ := ∑' q : ℕ, |dampedSignWeight RHTower.squareIndicatorR ε₀ q| * (q : ℝ) ^ (-(1 / 2 : ℝ))
  set M₀ := ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε₀))
  have hG₀ : 0 ≤ G₀ := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hM₀ : 0 ≤ M₀ := tsum_nonneg fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  set B := Real.sqrt (max Eμ 0)
  refine ⟨(G₀ * (B + Real.sqrt 2 * M₀)) ^ 2, fun N T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  set g := dampedSignWeight RHTower.squareIndicatorR ε
  set c := pmPowerDampedRealWeight ε
  have hgW := criticalWiener_dampedSquare hε
  have hc := summable_abs_pmPowerDamped_div hε
  have hconv : dampedSignWeight RHTower.liouvilleR ε = RHTower.dirichletConv g c :=
    funext (dampedLiouville_eq_dirichletConv ε)
  rw [hconv, weightPronicEnergy_eq_sq_pronicNorm]
  -- Notice that at the fixed `T` and `ε` in the band, `pronicNorm` at `(M, T)` is at most `B`
  have hBM : ∀ M : ℕ, pronicNorm (weightCenteredPrefix (horizonRow c M) (horizonRowMean c M)) T ≤ B :=
    fun M => by
      rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
      exact Real.sqrt_le_sqrt ((hEμ M T ε hε_ge hε2 hband).trans (le_max_left Eμ 0))
  have hG_le : ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G₀ :=
    tsum_criticalWiener_dampedSquare_le hε₀ hε_ge
  have hM_le : ∑' d : ℕ, |c d / d| ≤ M₀ := by
    have hs0 : Summable (fun d : ℕ => (d : ℝ) ^ (-(1 + ε₀))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine Summable.tsum_le_tsum (fun d => ?_) hc hs0
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [Nat.cast_zero, div_zero, abs_zero]
      exact Real.rpow_nonneg le_rfl _
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h := dampedSignWeight_div (s := moebiusReal) hε d
    simp only [dampedSignWeight] at h
    rw [show c d = moebiusReal d * (d : ℝ) ^ (-ε) from rfl, h, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact (mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_moebiusReal_le_one' d)).trans (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith))
  have hrep : weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
      (horizonRowMean (RHTower.dirichletConv g c) N) = fun n =>
      ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix (horizonRow c (N / q))
          (horizonRowMean c (N / q)) (n / q) +
        ∑ q ∈ Icc 1 N, (g q * horizonRowMean c (N / q)) * (((n / q : ℕ) : ℝ) - (n : ℝ) / q) := by
    funext n
    rw [weightCenteredPrefix_horizonRow_dirichletConv]
    congr 1
    exact sum_congr rfl fun q _ => by ring
  have hfin : ∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G₀ :=
    (hgW.sum_le_tsum _ fun q _ => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans hG_le
  have h1 : pronicNorm (fun n => ∑ q ∈ Icc 1 N, g q * weightCenteredPrefix (horizonRow c (N / q))
      (horizonRowMean c (N / q)) (n / q)) T ≤
      (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * B := by
    refine (pronicNorm_sum_le _ _ T).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun q hq => ?_
    rw [pronicNorm_smul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hdil := pronicNorm_dilate_le (weightCenteredPrefix (horizonRow c (N / q))
      (horizonRowMean c (N / q))) (weightCenteredPrefix_zero _ _) (mem_Icc.mp hq).1 T
    exact hdil.trans (mul_le_mul_of_nonneg_left (hBM (N / q))
      (Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have h2 : pronicNorm (fun n => ∑ q ∈ Icc 1 N, (g q * horizonRowMean c (N / q)) *
      (((n / q : ℕ) : ℝ) - (n : ℝ) / q)) T ≤
      (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.sqrt 2 * M₀) := by
    refine (pronicNorm_sum_le _ _ T).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun q hq => ?_
    rw [pronicNorm_smul, abs_mul]
    have hsaw := pronicNorm_sawtooth_le (mem_Icc.mp hq).1 T
    have hm := (abs_horizonRowMean_le_tsum hc (N / q)).trans hM_le
    calc |g q| * |horizonRowMean c (N / q)| * pronicNorm (fun n => ((n / q : ℕ) : ℝ) - (n : ℝ) / q) T
        ≤ |g q| * M₀ * (Real.sqrt 2 * (q : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm (abs_nonneg _)) hsaw
            (pronicNorm_nonneg _ T) (mul_nonneg (abs_nonneg _) hM₀)
      _ = |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.sqrt 2 * M₀) := by ring
  have htot : pronicNorm (weightCenteredPrefix (horizonRow (RHTower.dirichletConv g c) N)
      (horizonRowMean (RHTower.dirichletConv g c) N)) T ≤ G₀ * (B + Real.sqrt 2 * M₀) := by
    rw [hrep]
    calc _ ≤ (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * B +
            (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.sqrt 2 * M₀) :=
          (pronicNorm_add_le _ _ T).trans (add_le_add h1 h2)
      _ = (∑ q ∈ Icc 1 N, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) * (B + Real.sqrt 2 * M₀) := by ring
      _ ≤ G₀ * (B + Real.sqrt 2 * M₀) :=
          mul_le_mul_of_nonneg_right hfin (by positivity)
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) htot 2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
