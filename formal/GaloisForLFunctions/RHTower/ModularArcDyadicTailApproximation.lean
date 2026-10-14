import GaloisForLFunctions.RHTower.ModularArcDyadicInfiniteHorizonLimit

/-!
# Shifted doubly-exponential `O((k^{2^{r₀}})⁻¹)` tail approximation and sublattice asymptotic vanishing for the infinite-horizon dyadic modular arc limit

In `ModularArcDyadicInfiniteHorizonLimit`, we proved that as the dyadic pole-cancellation depth
`R → ∞`, `arcLineDyadicTowerProfile k R ν` and `∫ arcLineDyadicTowerDeriv k R ν x · sin(c x) dx`
converge unconditionally to `arcLineInfiniteDyadicProfile k ν` and
`arcLineInfiniteDyadicSineMoment k ν`.

Because each finite level `r₀` is identically blind along the `k^{2^{r₀+1}}`-sublattice
`arcFreq (k^{2^{r₀+1}}(j+1) − 1)`, passing to the infinite-horizon limit `R → ∞` requires
quantifying the exact tail leakage from base depth `r₀` to `∞`. In this module we establish the
complete quantitative tail approximation theory:

1. **Shifted doubly-exponential comparison law (`add_le_two_pow_add`,
   `pow_two_pow_mul_two_pow_le`, `inv_cosh_log_pow_two_pow_add_le`):**
   Because `2^{r₀} + s ≤ 2^{r₀ + s}` for all `r₀, s ∈ ℕ`, for every `k ≥ 2` we have
   `k^{2^{r₀}} · 2^s ≤ k^{2^{r₀ + s}}`, and therefore
   `1 / cosh(log(k^{2^{r₀ + s}})) ≤ 2 · (k^{2^{r₀}})⁻¹ · (1/2)^s`.
2. **Shifted finite- and infinite-horizon `O((k^{2^{r₀}})⁻¹)` tail bounds
   (`abs_arcLineDyadicTowerProfile_add_sub_le`, `abs_arcLineInfiniteDyadicProfile_sub_le`,
   `abs_arcLineInfiniteDyadicSineMoment_sub_le`,
   `abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le`):**
   Combining the shifted `cosh` inequality with the depth-and-scale-uniform `L^∞` and `O(√c)`
   bounds proves that from any base depth `r₀ ∈ ℕ`, the entire infinite tail from `r₀` to `∞` is
   bounded by `O((k^{2^{r₀}})⁻¹)`:
   - `|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k r₀ ν v| ≤ 288 · ν.real univ · (k^{2^{r₀}})⁻¹`,
   - `|arcLineInfiniteDyadicSineMoment k ν (arcFreq n) − ∫ arcLineDyadicTowerDeriv k r₀ ν x · sin(arcFreq n · x) dx| ≤ 144 √(π/2) · ν.real univ · √(arcFreq n) · (k^{2^{r₀}})⁻¹`.
3. **Sublattice scale cancellation and asymptotic vanishing as `k → ∞`
   (`abs_arcLineInfiniteDyadicSineMoment_sublattice_le`,
   `abs_arcLineInfiniteDyadicSineMoment_sublattice_sub_succ_le`,
   `tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop`,
   `tendsto_arcLineInfiniteDyadicSineMoment_sublattice_atTop`):**
   - For every integer frequency `n ∈ ℕ`, both `∫ arcLineDyadicTowerDeriv k r₀ ν x · sin(arcFreq n · x) dx`
     and the infinite-horizon limit `arcLineInfiniteDyadicSineMoment k ν (arcFreq n)` converge to
     `0` as `k → ∞`.
   - Along the doubly-exponential sublattice `arcFreq (k^{2^{r₀+1}}(j+1) − 1)`, where level `r₀`
     vanishes identically and `√(arcFreq (k^{2^{r₀+1}}(j+1) − 1)) = k^{2^{r₀}} √(arcFreq j)`, the
     `k^{2^{r₀}}` growth factor is **cancelled identically** by `(k^{2^{r₀}})⁻¹` at depth `r₀`
     (giving a `(k, r₀)`-uniform bound `144 √(π/2) · ν.real univ · √(arcFreq j)`), and starting
     the tail at depth `r₀ + 1` yields `O((k^{2^{r₀}})⁻¹)` tail decay and `k → ∞` vanishing even
     along the moving `k^{2^{r₀+1}}`-sublattice!
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Shifted doubly-exponential comparison inequalities -/

/-- For all `r₀, s ∈ ℕ`, `2^{r₀} + s ≤ 2^{r₀ + s}`. -/
theorem add_le_two_pow_add (r₀ s : ℕ) : 2 ^ r₀ + s ≤ 2 ^ (r₀ + s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 : 1 ≤ 2 ^ (r₀ + s) := Nat.one_le_two_pow
    calc 2 ^ r₀ + (s + 1) = (2 ^ r₀ + s) + 1 := by omega
      _ ≤ 2 ^ (r₀ + s) + 2 ^ (r₀ + s) := Nat.add_le_add ih h1
      _ = 2 ^ (r₀ + (s + 1)) := by rw [← Nat.add_assoc, pow_succ, Nat.mul_two]

/-- For every `k ≥ 2` and `r₀, s ∈ ℕ`, `k^{2^{r₀}} · 2^s ≤ k^{2^{r₀ + s}}`. -/
theorem pow_two_pow_mul_two_pow_le {k : ℕ} (hk : 2 ≤ k) (r₀ s : ℕ) :
    k ^ (2 ^ r₀) * 2 ^ s ≤ k ^ (2 ^ (r₀ + s)) := by
  calc k ^ (2 ^ r₀) * 2 ^ s
      ≤ k ^ (2 ^ r₀) * k ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk s)
    _ = k ^ (2 ^ r₀ + s) := (Nat.pow_add k (2 ^ r₀) s).symm
    _ ≤ k ^ (2 ^ (r₀ + s)) := Nat.pow_le_pow_right (by omega) (add_le_two_pow_add r₀ s)

/-- **Shifted doubly-exponential `cosh` bound (`k ≥ 2`):**
For every `r₀, s ∈ ℕ`, `1 / cosh(log(k^{2^{r₀ + s}})) ≤ 2 · (k^{2^{r₀}})⁻¹ · (1/2)^s`. -/
theorem inv_cosh_log_pow_two_pow_add_le {k : ℕ} (hk : 2 ≤ k) (r₀ s : ℕ) :
    1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) ≤
      2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by
  have hk1 : 1 ≤ k := by omega
  have hm : 1 ≤ k ^ (2 ^ (r₀ + s)) := one_le_pow_two_pow hk1 (r₀ + s)
  have hm0 : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk1 r₀
  have hpos0 : (0 : ℝ) < (k ^ (2 ^ r₀) : ℕ) := by exact_mod_cast hm0
  have hcosh := inv_cosh_log_le hm
  have hpow : ((k ^ (2 ^ r₀) : ℕ) : ℝ) * (2 : ℝ) ^ s ≤ ((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ) := by
    exact_mod_cast pow_two_pow_mul_two_pow_le hk r₀ s
  have hinv : (((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ)⁻¹) ≤
      (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by
    have hmul_pos : (0 : ℝ) < ((k ^ (2 ^ r₀) : ℕ) : ℝ) * (2 : ℝ) ^ s := by positivity
    have h1 := inv_anti₀ hmul_pos hpow
    rw [mul_inv, ← inv_pow] at h1
    simpa only [one_div] using h1
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))
      ≤ 2 * (((k ^ (2 ^ (r₀ + s)) : ℕ) : ℝ)⁻¹) := hcosh
    _ ≤ 2 * ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s := by ring

/-! ### Shifted telescoping identities from base depth `r₀` to `r₀ + S` -/

/-- Shifted telescoping identity for `arcLineDyadicTowerProfile` from depth `r₀` to `r₀ + S`. -/
theorem arcLineDyadicTowerProfile_add_sub (k r₀ S : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineDyadicTowerProfile k (r₀ + S) ν v - arcLineDyadicTowerProfile k r₀ ν v =
      -∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          arcLineSymDyadicTowerProfile k (r₀ + s) ν v := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [← Nat.add_assoc, arcLineDyadicTowerProfile_succ_eq_sub_sym, Finset.sum_range_succ]
    linarith

/-- Shifted telescoping identity for the sine moments of `arcLineDyadicTowerDeriv` from depth `r₀` to `r₀ + S`. -/
theorem integral_arcLineDyadicTowerDeriv_add_mul_sin_sub
    {k : ℕ} (hk : 1 ≤ k) (r₀ S : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (c : ℝ) :
    (∫ x, arcLineDyadicTowerDeriv k (r₀ + S) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (c * x)) =
      -∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          ∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (c * x) := by
  induction S with
  | zero => simp
  | succ S ih =>
    have hstep := integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk (r₀ + S) ν c
    rw [← Nat.add_assoc, Finset.sum_range_succ]
    linarith

/-! ### Shifted `O((k^{2^{r₀}})⁻¹)` finite- and infinite-horizon tail bounds -/

/-- **Finite-horizon `O((k^{2^{r₀}})⁻¹)` tail bound for `arcLineDyadicTowerProfile` (`k ≥ 2`).** -/
theorem abs_arcLineDyadicTowerProfile_add_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineDyadicTowerProfile k (r₀ + S) ν v - arcLineDyadicTowerProfile k r₀ ν v| ≤
      288 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  rw [arcLineDyadicTowerProfile_add_sub, abs_neg]
  set A := 144 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
  have hA0 : 0 ≤ A := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ s ∈ Finset.range S,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
        arcLineSymDyadicTowerProfile k (r₀ + s) ν v| ≤
      A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_of_pos (by positivity)]
    have hcosh := inv_cosh_log_pow_two_pow_add_le hk r₀ s
    have hS := abs_arcLineSymDyadicTowerProfile_le_uniform hk (r₀ + s) ν v
    calc 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) *
          |arcLineSymDyadicTowerProfile k (r₀ + s) ν v|
        ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) * (72 * ν.real univ) :=
          mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
      _ = A * (1 / 2 : ℝ) ^ s := by dsimp [A]; ring
  calc |∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          arcLineSymDyadicTowerProfile k (r₀ + s) ν v|
      ≤ A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := hsum
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) hA0
    _ = 288 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by dsimp [A]; ring

/-- **Infinite-horizon `O((k^{2^{r₀}})⁻¹)` tail approximation bound for `arcLineInfiniteDyadicProfile`:**
For every `k ≥ 2`, `r₀ ∈ ℕ`, and `v ∈ ℝ`,
`|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k r₀ ν v| ≤ 288 · ν.real univ · (k^{2^{r₀}})⁻¹`. -/
theorem abs_arcLineInfiniteDyadicProfile_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k r₀ ν v| ≤
      288 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have ht : Tendsto (fun S : ℕ =>
      |arcLineDyadicTowerProfile k (S + r₀) ν v - arcLineDyadicTowerProfile k r₀ ν v|)
      atTop (𝓝 |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k r₀ ν v|) :=
    continuous_abs.tendsto _ |>.comp
      (((tendsto_arcLineDyadicTowerProfile_atTop hk ν v).comp
        (tendsto_add_atTop_nat r₀)).sub_const _)
  exact le_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S r₀] using abs_arcLineDyadicTowerProfile_add_sub_le hk r₀ S ν v)

/-- **Finite-horizon `O((k^{2^{r₀}})⁻¹)` sine-moment tail bound at any frequency `c > 0`.** -/
theorem abs_integral_arcLineDyadicTowerDeriv_add_mul_sin_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |(∫ x, arcLineDyadicTowerDeriv k (r₀ + S) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (c * x))| ≤
      288 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_add_mul_sin_sub hk1 r₀ S ν c, abs_neg]
  set A := 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
    (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
  have hA0 : 0 ≤ A := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ s ∈ Finset.range S,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (c * x)| ≤
      A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_of_pos (by positivity)]
    have hcosh := inv_cosh_log_pow_two_pow_add_le hk r₀ s
    have hS := abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_le_uniform hk (r₀ + s) ν hc
    calc 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) *
          |∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (c * x)|
        ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) *
            (72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) :=
          mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
      _ = A * (1 / 2 : ℝ) ^ s := by dsimp [A]; ring
  calc |∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          ∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (c * x)|
      ≤ A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := hsum
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) hA0
    _ = 288 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by dsimp [A]; ring

/-- **Infinite-horizon `O((k^{2^{r₀}})⁻¹)` tail approximation bound for `arcLineInfiniteDyadicSineMoment` (`c > 0`).** -/
theorem abs_arcLineInfiniteDyadicSineMoment_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |arcLineInfiniteDyadicSineMoment k ν c -
        ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (c * x)| ≤
      288 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have ht : Tendsto (fun S : ℕ =>
      |(∫ x, arcLineDyadicTowerDeriv k (S + r₀) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (c * x))|)
      atTop (𝓝 |arcLineInfiniteDyadicSineMoment k ν c -
        ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (c * x)|) :=
    continuous_abs.tendsto _ |>.comp
      (((tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop hk ν hc).comp
        (tendsto_add_atTop_nat r₀)).sub_const _)
  exact le_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S r₀] using
        abs_integral_arcLineDyadicTowerDeriv_add_mul_sin_sub_le hk r₀ S ν hc)

/-- **Halved finite-horizon `O((k^{2^{r₀}})⁻¹)` sine-moment tail bound at integer frequencies `arcFreq n`.** -/
theorem abs_integral_arcLineDyadicTowerDeriv_add_mul_sin_arcFreq_sub_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r₀ S n : ℕ) :
    |(∫ x, arcLineDyadicTowerDeriv k (r₀ + S) ν x * Real.sin (arcFreq n * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x))| ≤
      144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_add_mul_sin_sub hk1 r₀ S ν (arcFreq n), abs_neg]
  set A := 72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
    (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
  have hA0 : 0 ≤ A := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := arcFreq_pos n
    positivity
  have hsum : |∑ s ∈ Finset.range S,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (arcFreq n * x)| ≤
      A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_of_pos (by positivity)]
    have hcosh := inv_cosh_log_pow_two_pow_add_le hk r₀ s
    have hS := abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le_uniform hblind hk (r₀ + s) n
    calc 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) *
          |∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (arcFreq n * x)|
        ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) *
            (36 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) :=
          mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
      _ = A * (1 / 2 : ℝ) ^ s := by dsimp [A]; ring
  calc |∑ s ∈ Finset.range S,
        (1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          ∫ x, arcLineSymDyadicTowerDeriv k (r₀ + s) ν x * Real.sin (arcFreq n * x)|
      ≤ A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := hsum
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) hA0
    _ = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by dsimp [A]; ring

/-- **Halved infinite-horizon `O((k^{2^{r₀}})⁻¹)` tail approximation bound at integer frequencies `arcFreq n`.** -/
theorem abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r₀ n : ℕ) :
    |arcLineInfiniteDyadicSineMoment k ν (arcFreq n) -
        ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x)| ≤
      144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have hc : 0 < arcFreq n := arcFreq_pos n
  have ht : Tendsto (fun S : ℕ =>
      |(∫ x, arcLineDyadicTowerDeriv k (S + r₀) ν x * Real.sin (arcFreq n * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x))|)
      atTop (𝓝 |arcLineInfiniteDyadicSineMoment k ν (arcFreq n) -
        ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x)|) :=
    continuous_abs.tendsto _ |>.comp
      (((tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop hk ν hc).comp
        (tendsto_add_atTop_nat r₀)).sub_const _)
  exact le_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S r₀] using
        abs_integral_arcLineDyadicTowerDeriv_add_mul_sin_arcFreq_sub_le hblind hk r₀ S n)

/-! ### Sublattice scale cancellation and `k → ∞` asymptotic vanishing -/

/-- Exact square-root scaling identity on the `k^{2^{r₀+1}}`-sublattice:
`√(arcFreq (k^{2^{r₀+1}}(j+1) − 1)) = k^{2^{r₀}} · √(arcFreq j)`. -/
theorem sqrt_arcFreq_pow_two_pow_succ_mul
    {k : ℕ} (hk : 1 ≤ k) (r₀ j : ℕ) :
    Real.sqrt (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)) =
      ((k ^ (2 ^ r₀) : ℕ) : ℝ) * Real.sqrt (arcFreq j) := by
  have hm : 1 ≤ k ^ (2 ^ (r₀ + 1)) := one_le_pow_two_pow hk (r₀ + 1)
  have hm0 : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk r₀
  have hpos0 : (0 : ℝ) ≤ (k ^ (2 ^ r₀) : ℕ) := by exact_mod_cast (Nat.zero_le _)
  have hfreq : arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1) =
      (((k ^ (2 ^ r₀) : ℕ) : ℝ) ^ 2) * arcFreq j := by
    rw [Nat.mul_comm (k ^ (2 ^ (r₀ + 1))) (j + 1),
      ← arcFreq_mul_nat hm j, ← pow_two_pow_sq k r₀]
    push_cast
    ring
  rw [hfreq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos0]

/-- **Depth-and-scale-uniform `k^{2^{r₀+1}}`-sublattice bound for the infinite-horizon limit:**
Because level `r₀` vanishes identically along `arcFreq (k^{2^{r₀+1}}(j+1) − 1)` and
`√(arcFreq (k^{2^{r₀+1}}(j+1) − 1)) = k^{2^{r₀}} √(arcFreq j)`, the `k^{2^{r₀}}` growth factor
is **cancelled identically** by the `(k^{2^{r₀}})⁻¹` tail factor from base depth `r₀`, yielding
a bound completely independent of both `k` and `r₀`. -/
theorem abs_arcLineInfiniteDyadicSineMoment_sublattice_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r₀ j : ℕ) :
    |arcLineInfiniteDyadicSineMoment k ν
        (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1))| ≤
      144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk1 r₀
  have hne0 : ((k ^ (2 ^ r₀) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm0).ne'
  have hzero := integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 r₀ j
  have htail := abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le
    hblind hk r₀ (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)
  rw [hzero, sub_zero, sqrt_arcFreq_pow_two_pow_succ_mul hk1 r₀ j] at htail
  refine htail.trans_eq ?_
  calc 144 * Real.sqrt (Real.pi / 2) * ν.real univ *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ) * Real.sqrt (arcFreq j)) *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
      = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) := by ring
    _ = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) := by
        rw [mul_inv_cancel₀ hne0, mul_one]

/-- **One-step higher `O((k^{2^{r₀}})⁻¹)` tail bound on the `k^{2^{r₀+1}}`-sublattice:**
Starting the tail at depth `r₀ + 1` along `arcFreq (k^{2^{r₀+1}}(j+1) − 1)` cancels one factor of
`k^{2^{r₀}}` against `√(arcFreq (k^{2^{r₀+1}}(j+1) − 1)) = k^{2^{r₀}} √(arcFreq j)` and leaves
a net decay factor of `(k^{2^{r₀}})⁻¹`. -/
theorem abs_arcLineInfiniteDyadicSineMoment_sublattice_sub_succ_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r₀ j : ℕ) :
    |arcLineInfiniteDyadicSineMoment k ν
        (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)) -
      ∫ x, arcLineDyadicTowerDeriv k (r₀ + 1) ν x *
        Real.sin (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1) * x)| ≤
      144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk1 r₀
  have hne0 : ((k ^ (2 ^ r₀) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm0).ne'
  have htail := abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le
    hblind hk (r₀ + 1) (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)
  have hinv : (((k ^ (2 ^ (r₀ + 1)) : ℕ) : ℝ)⁻¹) =
      (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
    rw [← pow_two_pow_sq k r₀, sq, Nat.cast_mul, mul_inv]
  rw [sqrt_arcFreq_pow_two_pow_succ_mul hk1 r₀ j] at htail
  refine htail.trans_eq ?_
  rw [hinv]
  calc 144 * Real.sqrt (Real.pi / 2) * ν.real univ *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ) * Real.sqrt (arcFreq j)) *
        ((((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹))
      = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ) * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) := by ring
    _ = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
          (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
        rw [mul_inv_cancel₀ hne0, mul_one]

/-- For every `r₀ ∈ ℕ`, `(k^{2^{r₀}})⁻¹ → 0` as `k → ∞`. -/
theorem tendsto_inv_pow_two_pow_atTop (r₀ : ℕ) :
    Tendsto (fun k : ℕ => (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hle : ∀ᶠ k : ℕ in atTop, (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) ≤ (k : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
    have hpow : k ≤ k ^ (2 ^ r₀) := Nat.le_self_pow (by positivity) k
    exact inv_anti₀ hkpos (by exact_mod_cast hpow)
  exact squeeze_zero' (Eventually.of_forall fun k => by positivity) hle
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

/-- **Asymptotic `k → ∞` vanishing of every integer sine moment at any fixed dyadic depth `r₀`.** -/
theorem tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_arcFreq_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    (r₀ n : ℕ) :
    Tendsto (fun k : ℕ =>
      ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x))
      atTop (𝓝 0) := by
  have h0 := tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop hblind n
  set C := 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)
  have hdiff : Tendsto (fun k : ℕ =>
      (∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x)) -
        (∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x)))
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun k : ℕ => C * (((k ^ (2 ^ 0) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_pow_two_pow_atTop 0).const_mul C
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [Real.norm_eq_abs]
    simpa [arcLineDyadicTowerDeriv, C] using
      abs_integral_arcLineDyadicTowerDeriv_add_mul_sin_arcFreq_sub_le hblind hk 0 r₀ n
  simpa using hdiff.add h0

/-- **Asymptotic `k → ∞` vanishing of the infinite-horizon sine moment at every integer frequency `arcFreq n`.** -/
theorem tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0) (n : ℕ) :
    Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
      atTop (𝓝 0) := by
  have h0 := tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop hblind n
  set C := 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)
  have hdiff : Tendsto (fun k : ℕ =>
      arcLineInfiniteDyadicSineMoment k ν (arcFreq n) -
        ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x))
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun k : ℕ => C * (((k ^ (2 ^ 0) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_pow_two_pow_atTop 0).const_mul C
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [Real.norm_eq_abs]
    simpa [arcLineDyadicTowerDeriv, C] using
      abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le hblind hk 0 n
  simpa using hdiff.add h0

/-- **Asymptotic `k → ∞` vanishing of the infinite-horizon sine moment even along the moving `k^{2^{r₀+1}}`-sublattice!** -/
theorem tendsto_arcLineInfiniteDyadicSineMoment_sublattice_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    (r₀ j : ℕ) :
    Tendsto (fun k : ℕ =>
      arcLineInfiniteDyadicSineMoment k ν
        (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)))
      atTop (𝓝 0) := by
  have hsucc : Tendsto (fun k : ℕ =>
      ∫ x, arcLineDyadicTowerDeriv k (r₀ + 1) ν x *
        Real.sin (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1) * x))
      atTop (𝓝 0) := by
    have hbase := (continuous_abs.tendsto 0).comp
      (tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_arcFreq_atTop hblind r₀ j)
    rw [abs_zero] at hbase
    refine squeeze_zero_norm' ?_ hbase
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Real.norm_eq_abs, integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice hblind hk r₀ j,
      abs_mul, abs_neg]
    have hm : 1 ≤ k ^ (2 ^ r₀) := one_le_pow_two_pow hk r₀
    have hratio : |((k ^ (2 ^ r₀) : ℕ) : ℝ) /
        (2 * Real.cosh (Real.log ((k ^ (2 ^ r₀) : ℕ))))| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact div_two_mul_cosh_log_le_one hm
    calc |((k ^ (2 ^ r₀) : ℕ) : ℝ) / (2 * Real.cosh (Real.log ((k ^ (2 ^ r₀) : ℕ))))| *
          |∫ t, arcLineDyadicTowerDeriv k r₀ ν t * Real.sin (arcFreq j * t)|
        ≤ 1 * |∫ t, arcLineDyadicTowerDeriv k r₀ ν t * Real.sin (arcFreq j * t)| :=
          mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ = |∫ t, arcLineDyadicTowerDeriv k r₀ ν t * Real.sin (arcFreq j * t)| := one_mul _
  set C := 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j)
  have hdiff : Tendsto (fun k : ℕ =>
      arcLineInfiniteDyadicSineMoment k ν
        (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)) -
      ∫ x, arcLineDyadicTowerDeriv k (r₀ + 1) ν x *
        Real.sin (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1) * x))
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun k : ℕ => C * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_pow_two_pow_atTop r₀).const_mul C
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [Real.norm_eq_abs]
    exact abs_arcLineInfiniteDyadicSineMoment_sublattice_sub_succ_le hblind hk r₀ j
  simpa using hdiff.add hsucc

/-! ### Master unconditional dyadic tail approximation and sublattice vanishing theorem -/

/-- **Master unconditional theorem for the dyadic tail approximation and sublattice asymptotic vanishing.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that:
1. For every `k ≥ 2` and every base depth `r₀ ∈ ℕ`, the infinite-horizon limit profile and
   sine-moment functional approximate level `r₀` within `O((k^{2^{r₀}})⁻¹)`:
   - `|arcLineInfiniteDyadicProfile k ν v − arcLineDyadicTowerProfile k r₀ ν v| ≤ 288 · ν.real univ · (k^{2^{r₀}})⁻¹`,
   - `|arcLineInfiniteDyadicSineMoment k ν (arcFreq n) − ∫ arcLineDyadicTowerDeriv k r₀ ν x · sin(arcFreq n · x) dx| ≤ 144 √(π/2) · ν.real univ · √(arcFreq n) · (k^{2^{r₀}})⁻¹`;
2. Along the doubly-exponential sublattice `arcFreq (k^{2^{r₀+1}}(j+1) − 1)`, where level `r₀`
   vanishes identically, the `k^{2^{r₀}}` growth of `√c` cancels `(k^{2^{r₀}})⁻¹` identically:
   `|arcLineInfiniteDyadicSineMoment k ν (arcFreq (k^{2^{r₀+1}}(j+1) − 1))| ≤ 144 √(π/2) · ν.real univ · √(arcFreq j)`;
3. As `k → ∞`, `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` at every integer frequency
   `n ∈ ℕ`, AND `arcLineInfiniteDyadicSineMoment k ν (arcFreq (k^{2^{r₀+1}}(j+1) − 1)) → 0` even
   along the moving `k^{2^{r₀+1}}`-sublattice for every `r₀, j ∈ ℕ`. -/
theorem exists_dyadic_tailApproximation_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ r₀ : ℕ, ∀ v : ℝ,
          |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k r₀ ν v| ≤
            288 * ν.real univ * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) ∧
        (∀ r₀ n : ℕ,
          |arcLineInfiniteDyadicSineMoment k ν (arcFreq n) -
              ∫ x, arcLineDyadicTowerDeriv k r₀ ν x * Real.sin (arcFreq n * x)| ≤
            144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
              (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) ∧
        (∀ r₀ j : ℕ,
          |arcLineInfiniteDyadicSineMoment k ν
              (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1))| ≤
            144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j)) ∧
        (∀ r₀ j : ℕ,
          |arcLineInfiniteDyadicSineMoment k ν
              (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)) -
            ∫ x, arcLineDyadicTowerDeriv k (r₀ + 1) ν x *
              Real.sin (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1) * x)| ≤
            144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
              (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹))) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) ∧
      (∀ r₀ j : ℕ, Tendsto (fun k : ℕ =>
        arcLineInfiniteDyadicSineMoment k ν
          (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk => ?_,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind,
    tendsto_arcLineInfiniteDyadicSineMoment_sublattice_atTop hblind⟩
  exact ⟨fun r₀ v => abs_arcLineInfiniteDyadicProfile_sub_le hk r₀ ν v,
    fun r₀ n => abs_arcLineInfiniteDyadicSineMoment_arcFreq_sub_le hblind hk r₀ n,
    fun r₀ j => abs_arcLineInfiniteDyadicSineMoment_sublattice_le hblind hk r₀ j,
    fun r₀ j => abs_arcLineInfiniteDyadicSineMoment_sublattice_sub_succ_le hblind hk r₀ j⟩

end

end RHTower
