import GaloisForLFunctions.RHTower.ModularArcDyadicTailApproximation

/-!
# Infinite-horizon critical-line spectral convergence, Weierstrass lower bounds, and strict positivity for the dyadic modular arc tower

In `ModularArcTowerCascadeAsymptotics`, the constant-scale tower `arcLineTowerProfile k d ν` had
critical-line cosine transform
`(1 − cos(2τ log k) / cosh(log k))^d · ∫ cos(τv) arcLineAtomicProfile (log k) ν v`,
which collapses to `0` as `d → ∞` whenever `cos(2τ log k) > 0`.

In this module we prove that the **dyadic (exponent-doubling) hyperbolic tower**
`arcLineDyadicTowerProfile k R ν` completely eliminates this infinite-depth spectral collapse:

1. **Exact dyadic product factorization and telescoping identity
   (`integral_cos_mul_arcLineDyadicTowerProfile`,
   `integral_cos_mul_arcLineDyadicTowerProfile_add_sub`):**
   At dyadic depth `R`, the critical-line cosine transform factors as the product of
   `1 − cos(2τ log(k^{2^r})) / cosh(log(k^{2^r}))` over `0 ≤ r < R`, and satisfies the shifted
   telescoping law from any base depth `r₀` to `r₀ + S`.
2. **Depth-and-scale-uniform upper bound and `O((k^{2^{r₀}})⁻¹)` tail approximation
   (`abs_integral_cos_mul_arcLineDyadicTowerProfile_le_uniform`,
   `abs_integral_cos_mul_arcLineDyadicTowerProfile_add_sub_le`):**
   Across all `k ≥ 2`, `R ∈ ℕ`, and `τ ∈ ℝ`,
   `|∫ cos(τv) arcLineDyadicTowerProfile k R ν v| ≤ 9 · |∫ cos(τv) arcLineAtomicProfile (log k) ν v|`,
   and the tail from `r₀` to `r₀ + S` is bounded by `36 · (k^{2^{r₀}})⁻¹ · |∫ cos(τv) arcLineAtomicProfile (log k) ν v|`.
3. **Weierstrass lower bound and non-collapsing `3/4` floor across all depths `R ≥ 2`
   (`integral_cos_mul_arcLineDyadicTowerProfile_add_ge`,
   `three_quarters_mul_le_integral_cos_mul_arcLineDyadicTowerProfile_add_two`):**
   For every `k ≥ 2`, `r₀, S ∈ ℕ`, and `τ ∈ ℝ`,
   `(1 − 4 · (k^{2^{r₀}})⁻¹) · ∫ cos(τv) arcLineDyadicTowerProfile k r₀ ν v ≤ ∫ cos(τv) arcLineDyadicTowerProfile k (r₀ + S) ν v`.
   At `r₀ = 2` (`k^4 ≥ 16`), this gives the depth-uniform strictly positive lower bound
   `(3/4) · ∫ cos(τv) arcLineDyadicTowerProfile k 2 ν v ≤ ∫ cos(τv) arcLineDyadicTowerProfile k (2 + S) ν v`
   for all `S ∈ ℕ`.
4. **Unconditional `R → ∞` convergence, strict infinite-horizon positivity, and `k → ∞` spectral
   convergence (`tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop`,
   `arcLineInfiniteDyadicCosTransform_pos`,
   `tendsto_arcLineInfiniteDyadicCosTransform_atTop`,
   `exists_dyadic_infiniteHorizon_criticalLine_positivity_arcWitness`):**
   As `R → ∞`, the critical-line cosine transforms converge unconditionally to
   `arcLineInfiniteDyadicCosTransform k ν τ > 0`, and as `k → ∞`,
   `arcLineInfiniteDyadicCosTransform k ν τ → ∫ cos(τv) arcPoissonProfile ν v > 0` for every `τ ∈ ℝ`
   simultaneously with the `k → ∞` vanishing of `arcLineInfiniteDyadicSineMoment k ν`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Exact dyadic step, product factorization, and shifted telescoping on the critical line -/

/-- One-step critical-line cosine transform recursion for `arcLineDyadicTowerProfile`. -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_succ
    (k r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r + 1) ν v =
      (1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v :=
  integral_cos_mul_hyperbolicFilterProfile (k ^ (2 ^ r))
    (integrable_arcLineDyadicTowerProfile k r ν)
    (arcLineDyadicTowerProfile_neg k r ν) τ

/-- One-step additive difference identity for the critical-line cosine transform of `arcLineDyadicTowerProfile`. -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_succ_sub
    (k r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r + 1) ν v) -
        (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v) =
      -(Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v := by
  rw [integral_cos_mul_arcLineDyadicTowerProfile_succ]
  ring

/-- **Closed-form Euler-product factorization of the critical-line cosine transform at dyadic depth `R`.** -/
theorem integral_cos_mul_arcLineDyadicTowerProfile
    (k R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v =
      (∏ r ∈ Finset.range R,
        (1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))) *
        (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2 *
        ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  induction R with
  | zero =>
    rw [Finset.prod_range_zero, one_mul]
    exact integral_cos_mul_arcLineAtomicProfile (Real.log k) ν τ
  | succ R ih =>
    rw [integral_cos_mul_arcLineDyadicTowerProfile_succ, ih, Finset.prod_range_succ]
    ring

/-- Shifted telescoping identity for the critical-line cosine transform from base depth `r₀` to `r₀ + S`. -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_add_sub
    (k r₀ S : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v) -
        (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v) =
      -∑ s ∈ Finset.range S,
        (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + s) ν v := by
  induction S with
  | zero => simp
  | succ S ih =>
    have hstep := integral_cos_mul_arcLineDyadicTowerProfile_succ_sub k (r₀ + S) ν τ
    rw [← Nat.add_assoc, Finset.sum_range_succ]
    linarith

/-- Telescoping decomposition of the critical-line cosine transform from `r = 0` to `R`. -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_eq_atomic_sub_sum
    (k R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v =
      (∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v) -
        ∑ r ∈ Finset.range R,
          (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v := by
  have h := integral_cos_mul_arcLineDyadicTowerProfile_add_sub k 0 R ν τ
  simp only [Nat.zero_add] at h
  change (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v) -
    (∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v) = _ at h
  linarith

/-! ### Depth-and-scale-uniform upper bound and `O((k^{2^{r₀}})⁻¹)` tail bounds -/

/-- Coarse `2^r` bound on the critical-line cosine transform at dyadic level `r`. -/
theorem abs_integral_cos_mul_arcLineDyadicTowerProfile_le_two_pow
    (k r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    |∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v| ≤
      2 ^ r * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| := by
  induction r with
  | zero =>
    simp [arcLineDyadicTowerProfile]
  | succ r ih =>
    rw [integral_cos_mul_arcLineDyadicTowerProfile_succ, abs_mul]
    have hfactor : |1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))| ≤ 2 := by
      have hC := Real.cosh_pos (Real.log ((k ^ (2 ^ r) : ℕ)))
      have h1 : |Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))| ≤ 1 := by
        rw [abs_div, abs_of_pos hC, div_le_one hC]
        exact (Real.abs_cos_le_one _).trans (Real.one_le_cosh _)
      have hsub := abs_sub (1 : ℝ)
        (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))
      rw [abs_one] at hsub
      linarith
    calc |1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))| *
          |∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v|
        ≤ 2 * (2 ^ r * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|) :=
          mul_le_mul hfactor ih (abs_nonneg _) (by positivity)
      _ = 2 ^ (r + 1) * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| := by
          rw [pow_succ']; ring

/-- Geometric `(1/2)^r` Cauchy step bound for the critical-line cosine transform (`k ≥ 2`). -/
theorem abs_integral_cos_mul_arcLineDyadicTowerProfile_succ_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    |(Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v| ≤
      (4 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|) *
        (1 / 2 : ℝ) ^ r := by
  rw [abs_mul, abs_div, abs_of_pos (Real.cosh_pos _)]
  have hcos : |Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ))))| /
      Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) ≤
      1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) :=
    div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.cosh_pos _).le
  have hr := abs_integral_cos_mul_arcLineDyadicTowerProfile_le_two_pow k r ν τ
  have hratio := two_pow_div_cosh_log_pow_two_pow_le hk r
  calc |Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ))))| /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v|
      ≤ (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          (2 ^ r * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|) :=
        mul_le_mul hcos hr (abs_nonneg _) (by positivity)
    _ = ((2 : ℝ) ^ r / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| := by ring
    _ ≤ (4 * (1 / 2 : ℝ) ^ r) *
          |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ = (4 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|) *
          (1 / 2 : ℝ) ^ r := by ring

/-- **Depth-and-scale-uniform upper bound on the critical-line cosine transform (`k ≥ 2`).** -/
theorem abs_integral_cos_mul_arcLineDyadicTowerProfile_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    |∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v| ≤
      9 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| := by
  rw [integral_cos_mul_arcLineDyadicTowerProfile_eq_atomic_sub_sum]
  set B := |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|
  have hB0 : 0 ≤ B := abs_nonneg _
  have hsum : |∑ r ∈ Finset.range R,
      (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v| ≤
      (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ =>
      abs_integral_cos_mul_arcLineDyadicTowerProfile_succ_sub_le hk r ν τ
  have hgeom : (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 8 * B := by
    have h2 := sum_range_half_pow_le_two R
    nlinarith
  have hsub := abs_sub (∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v)
    (∑ r ∈ Finset.range R,
      (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v)
  linarith

/-- **Shifted finite-horizon `O((k^{2^{r₀}})⁻¹)` tail bound on the critical-line cosine transform.** -/
theorem abs_integral_cos_mul_arcLineDyadicTowerProfile_add_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    |(∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v) -
        (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v)| ≤
      36 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  rw [integral_cos_mul_arcLineDyadicTowerProfile_add_sub, abs_neg]
  set B := |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|
  set A := 18 * B * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)
  have hA0 : 0 ≤ A := by positivity
  have hsum : |∑ s ∈ Finset.range S,
      (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + s) ν v| ≤
      A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_div, abs_of_pos (Real.cosh_pos _)]
    have hcos : |Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))))| /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) ≤
        2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s :=
      (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.cosh_pos _).le).trans
        (inv_cosh_log_pow_two_pow_add_le hk r₀ s)
    have hS := abs_integral_cos_mul_arcLineDyadicTowerProfile_le_uniform hk (r₀ + s) ν τ
    calc |Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))))| /
          Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) *
          |∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + s) ν v|
        ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) * (1 / 2 : ℝ) ^ s) * (9 * B) :=
          mul_le_mul hcos hS (abs_nonneg _) (by positivity)
      _ = A * (1 / 2 : ℝ) ^ s := by dsimp [A]; ring
  calc |∑ s ∈ Finset.range S,
        (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
          Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
          ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + s) ν v|
      ≤ A * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := hsum
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) hA0
    _ = 36 * B * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by dsimp [A]; ring

/-! ### Weierstrass lower bound and non-collapsing `3/4` floor across all depths `R ≥ 2` -/

/-- **Shifted Weierstrass product lower bound on the critical-line cosine transform:**
For every `k ≥ 2`, `r₀, S ∈ ℕ`, and `τ ∈ ℝ`,
`(1 − ∑_{s < S} 1 / cosh(log(k^{2^{r₀+s}}))) · ∫ cos(τv) arcLineDyadicTowerProfile k r₀ ν v`
`≤ ∫ cos(τv) arcLineDyadicTowerProfile k (r₀ + S) ν v`. -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_add_ge_sub_sum
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    (1 - ∑ s ∈ Finset.range S,
      1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
      (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
    ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v := by
  have hpos0 : 0 ≤ ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v :=
    (integral_cos_mul_arcLineDyadicTowerProfile_pos hk r₀ ν hpd τ).le
  induction S with
  | zero => simp
  | succ S ih =>
    rw [← Nat.add_assoc, integral_cos_mul_arcLineDyadicTowerProfile_succ, Finset.sum_range_succ]
    set a := 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))
    set Ssum := ∑ s ∈ Finset.range S, 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))
    have ha0 : 0 ≤ a := by positivity
    have ha1 : 0 ≤ 1 - a := by
      dsimp [a]
      rw [sub_nonneg, div_le_one (Real.cosh_pos _)]
      exact Real.one_le_cosh _
    have hSsum0 : 0 ≤ Ssum := Finset.sum_nonneg fun s _ => by positivity
    have hfactor : 1 - a ≤ 1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ))) := by
      dsimp [a]
      gcongr
      exact Real.cos_le_one _
    have hposS : 0 ≤ ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v :=
      (integral_cos_mul_arcLineDyadicTowerProfile_pos hk (r₀ + S) ν hpd τ).le
    have hweier : 1 - (Ssum + a) ≤ (1 - a) * (1 - Ssum) := by nlinarith
    calc (1 - (Ssum + a)) * (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v)
        ≤ ((1 - a) * (1 - Ssum)) *
            (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v) :=
          mul_le_mul_of_nonneg_right hweier hpos0
      _ = (1 - a) * ((1 - Ssum) *
            (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v)) := by ring
      _ ≤ (1 - a) * (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v) :=
          mul_le_mul_of_nonneg_left ih ha1
      _ ≤ (1 - Real.cos (τ * (2 * Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))) *
            (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v) :=
          mul_le_mul_of_nonneg_right hfactor hposS

/-- **Closed-form `(1 − 4 · (k^{2^{r₀}})⁻¹)` lower bound on the critical-line cosine transform.** -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_add_ge
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    (1 - 4 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) *
      (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
    ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v := by
  have hpos0 : 0 ≤ ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v :=
    (integral_cos_mul_arcLineDyadicTowerProfile_pos hk r₀ ν hpd τ).le
  have hsum : ∑ s ∈ Finset.range S,
      1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) ≤
      4 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
    calc ∑ s ∈ Finset.range S, 1 / Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))
        ≤ ∑ s ∈ Finset.range S,
            (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) * (1 / 2 : ℝ) ^ s :=
          Finset.sum_le_sum fun s _ => inv_cosh_log_pow_two_pow_add_le hk r₀ s
      _ = (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) * ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by
          rw [Finset.mul_sum]
      _ ≤ (2 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) (by positivity)
      _ = 4 * (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by ring
  refine (mul_le_mul_of_nonneg_right (by linarith) hpos0).trans
    (integral_cos_mul_arcLineDyadicTowerProfile_add_ge_sub_sum hk r₀ S hpd τ)

/-- **Uniform `3/4` critical-line positivity floor across all dyadic depths `2 + S` (`k ≥ 2`):**
Because `k^{2^2} = k^4 ≥ 16` for all `k ≥ 2`, `1 − 4 · (k^4)⁻¹ ≥ 3/4`, so the critical-line
cosine transform at depth `2 + S` is bounded below by `(3/4)` of its value at depth `2` uniformly
across all `S ∈ ℕ`. -/
theorem three_quarters_mul_le_integral_cos_mul_arcLineDyadicTowerProfile_add_two
    {k : ℕ} (hk : 2 ≤ k) (S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    (3 / 4 : ℝ) * (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k 2 ν v) ≤
      ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (2 + S) ν v := by
  have hpos2 : 0 ≤ ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k 2 ν v :=
    (integral_cos_mul_arcLineDyadicTowerProfile_pos hk 2 ν hpd τ).le
  have h16 : (16 : ℝ) ≤ ((k ^ (2 ^ 2) : ℕ) : ℝ) := by
    have : 16 ≤ k ^ (2 ^ 2) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
    exact_mod_cast this
  have hinv : (((k ^ (2 ^ 2) : ℕ) : ℝ)⁻¹) ≤ 1 / 16 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 16) h16
    simpa only [one_div] using this
  have h34 : (3 / 4 : ℝ) ≤ 1 - 4 * (((k ^ (2 ^ 2) : ℕ) : ℝ)⁻¹) := by linarith
  exact (mul_le_mul_of_nonneg_right h34 hpos2).trans
    (integral_cos_mul_arcLineDyadicTowerProfile_add_ge hk 2 S hpd τ)

/-! ### Unconditional `R → ∞` convergence, strict infinite-horizon positivity, and `k → ∞` convergence -/

/-- The infinite-horizon critical-line cosine transform at integer scale `k`:
`P̂_{k,∞}(τ) = ∫ cos(τv) arcLineAtomicProfile (log k) ν v − ∑'_{r=0}^∞ (cos(2τ log(k^{2^r})) / cosh(log(k^{2^r}))) · ∫ cos(τv) arcLineDyadicTowerProfile k r ν v`. -/
def arcLineInfiniteDyadicCosTransform (k : ℕ) (ν : Measure ArcParam) (τ : ℝ) : ℝ :=
  (∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v) -
    ∑' r : ℕ, (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
      Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
      ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v

/-- Absolute summability of the critical-line cosine transform telescoping series (`k ≥ 2`). -/
theorem summable_cos_div_cosh_mul_integral_cos_mul_arcLineDyadicTowerProfile
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    Summable fun r : ℕ =>
      (Real.cos (τ * (2 * Real.log ((k ^ (2 ^ r) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v := by
  refine Summable.of_norm_bounded
    (summable_geometric_two.mul_left
      (4 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v|))
    fun r => ?_
  rw [Real.norm_eq_abs]
  exact abs_integral_cos_mul_arcLineDyadicTowerProfile_succ_sub_le hk r ν τ

/-- **Unconditional `R → ∞` convergence of the critical-line cosine transform to `arcLineInfiniteDyadicCosTransform k ν τ`.** -/
theorem tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    Tendsto (fun R : ℕ => ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (arcLineInfiniteDyadicCosTransform k ν τ)) := by
  refine (tendsto_const_nhds.sub
    (summable_cos_div_cosh_mul_integral_cos_mul_arcLineDyadicTowerProfile hk ν τ).hasSum.tendsto_sum_nat).congr
    fun R => (integral_cos_mul_arcLineDyadicTowerProfile_eq_atomic_sub_sum k R ν τ).symm

/-- **Infinite-horizon `O((k^{2^{r₀}})⁻¹)` tail approximation bound on the critical line.** -/
theorem abs_arcLineInfiniteDyadicCosTransform_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    |arcLineInfiniteDyadicCosTransform k ν τ -
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v| ≤
      36 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| *
        (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹) := by
  have ht : Tendsto (fun S : ℕ =>
      |(∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (S + r₀) ν v) -
        (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v)|)
      atTop (𝓝 |arcLineInfiniteDyadicCosTransform k ν τ -
        ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v|) :=
    continuous_abs.tendsto _ |>.comp
      (((tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop hk ν τ).comp
        (tendsto_add_atTop_nat r₀)).sub_const _)
  exact le_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S r₀] using
        abs_integral_cos_mul_arcLineDyadicTowerProfile_add_sub_le hk r₀ S ν τ)

/-- **Infinite-horizon `3/4` critical-line lower bound (`k ≥ 2`).** -/
theorem three_quarters_mul_le_arcLineInfiniteDyadicCosTransform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    (3 / 4 : ℝ) * (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k 2 ν v) ≤
      arcLineInfiniteDyadicCosTransform k ν τ := by
  have ht : Tendsto (fun S : ℕ =>
      ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k (S + 2) ν v)
      atTop (𝓝 (arcLineInfiniteDyadicCosTransform k ν τ)) :=
    (tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop hk ν τ).comp
      (tendsto_add_atTop_nat 2)
  exact ge_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S 2] using
        three_quarters_mul_le_integral_cos_mul_arcLineDyadicTowerProfile_add_two hk S hpd τ)

/-- **Strict infinite-horizon critical-line positivity (`k ≥ 2`, `τ ∈ ℝ`):**
Unlike the constant-scale tower (whose cosine transform collapses to `0` as `d → ∞`), the
infinite-horizon dyadic cosine transform `arcLineInfiniteDyadicCosTransform k ν τ` is **strictly
positive** for every `k ≥ 2` and every `τ ∈ ℝ`. -/
theorem arcLineInfiniteDyadicCosTransform_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < arcLineInfiniteDyadicCosTransform k ν τ := by
  have hpos2 := integral_cos_mul_arcLineDyadicTowerProfile_pos hk 2 ν hpd τ
  have hle := three_quarters_mul_le_arcLineInfiniteDyadicCosTransform hk hpd τ
  linarith

/-- **Asymptotic `k → ∞` convergence of the infinite-horizon critical-line cosine transform:**
For every `τ ∈ ℝ`, `arcLineInfiniteDyadicCosTransform k ν τ → ∫ cos(τv) arcPoissonProfile ν v`. -/
theorem tendsto_arcLineInfiniteDyadicCosTransform_atTop
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    Tendsto (fun k : ℕ => arcLineInfiniteDyadicCosTransform k ν τ)
      atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  have h0 := tendsto_integral_cos_mul_arcLineAtomicProfile_log_atTop ν τ
  have hdiff : Tendsto (fun k : ℕ =>
      arcLineInfiniteDyadicCosTransform k ν τ -
        ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v)
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun k : ℕ =>
        36 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| *
          (((k ^ (2 ^ 0) : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
      have h1 := ((continuous_abs.tendsto _).comp h0).const_mul 36
      have h2 := h1.mul (tendsto_inv_pow_two_pow_atTop 0)
      simpa using h2
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with k hk
    rw [Real.norm_eq_abs]
    simpa [arcLineDyadicTowerProfile] using
      abs_arcLineInfiniteDyadicCosTransform_sub_le hk 0 ν τ
  simpa using hdiff.add h0

/-! ### Master unconditional infinite-horizon critical-line positivity and sublattice vanishing theorem -/

/-- **Master unconditional theorem for the infinite-horizon dyadic modular arc witness.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that:
1. For every integer `k ≥ 2` and every `τ ∈ ℝ`, as the dyadic pole-cancellation depth `R → ∞`,
   `∫ cos(τv) arcLineDyadicTowerProfile k R ν v` converges unconditionally to
   `arcLineInfiniteDyadicCosTransform k ν τ`, which is **strictly positive** (`> 0`) for every
   `k ≥ 2` and `τ ∈ ℝ` (satisfying the depth-uniform lower bound
   `(3/4) ∫ cos(τv) arcLineDyadicTowerProfile k 2 ν v ≤ arcLineInfiniteDyadicCosTransform k ν τ`);
2. For every base depth `r₀ ∈ ℕ`, `arcLineInfiniteDyadicCosTransform k ν τ` approximates level `r₀`
   within `O((k^{2^{r₀}})⁻¹)`;
3. As `k → ∞`, simultaneously:
   - `arcLineInfiniteDyadicCosTransform k ν τ → ∫ cos(τv) arcPoissonProfile ν v > 0` for every `τ ∈ ℝ`,
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for every integer frequency `n ∈ ℕ`, and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq (k^{2^{r₀+1}}(j+1) − 1)) → 0` along every
     moving `k^{2^{r₀+1}}`-sublattice (`r₀, j ∈ ℕ`). -/
theorem exists_dyadic_infiniteHorizon_criticalLine_positivity_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ τ : ℝ, Tendsto (fun R : ℕ => ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v)
          atTop (𝓝 (arcLineInfiniteDyadicCosTransform k ν τ))) ∧
        (∀ τ : ℝ, 0 < arcLineInfiniteDyadicCosTransform k ν τ) ∧
        (∀ τ : ℝ, (3 / 4 : ℝ) * (∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k 2 ν v) ≤
          arcLineInfiniteDyadicCosTransform k ν τ) ∧
        (∀ r₀ : ℕ, ∀ τ : ℝ,
          |arcLineInfiniteDyadicCosTransform k ν τ -
              ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r₀ ν v| ≤
            36 * |∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v| *
              (((k ^ (2 ^ r₀) : ℕ) : ℝ)⁻¹))) ∧
      (∀ τ : ℝ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicCosTransform k ν τ)
        atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) ∧
      (∀ r₀ j : ℕ, Tendsto (fun k : ℕ =>
        arcLineInfiniteDyadicSineMoment k ν
          (arcFreq (k ^ (2 ^ (r₀ + 1)) * (j + 1) - 1)))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, hpd, fun k hk => ?_,
    tendsto_arcLineInfiniteDyadicCosTransform_atTop ν,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind,
    tendsto_arcLineInfiniteDyadicSineMoment_sublattice_atTop hblind⟩
  exact ⟨fun τ => tendsto_integral_cos_mul_arcLineDyadicTowerProfile_atTop hk ν τ,
    fun τ => arcLineInfiniteDyadicCosTransform_pos hk hpd τ,
    fun τ => three_quarters_mul_le_arcLineInfiniteDyadicCosTransform hk hpd τ,
    fun r₀ τ => abs_arcLineInfiniteDyadicCosTransform_sub_le hk r₀ ν τ⟩

end

end RHTower
