import GaloisForLFunctions.BezoutValuationIncidence.ActiveDeletedMartingaleAndShiftedEulerConvergence

/-!
# Pillar XX: Shifted-Exponent Asymptotic Density, Euler Product & Exact Active Martingale Rate (`ε → 0⁺`)

In Pillar XIX (`ActiveDeletedMartingaleAndShiftedEulerConvergence`), we established the
**Active-Deleted Martingale Identity**:
$$W_{N,c_\varepsilon}(n + 1)^2 - W_{N,c_\varepsilon}(n)^2 =
  \bigl(\tau_\varepsilon(n + 1) - Y_N(1)\bigr)\bigl(\tau_{1+\varepsilon}(n + 1) - Y_N(1)\bigr) +
  2\bigl(\tau_\varepsilon(n + 1) - Y_N(1)\bigr)\,I_{N,c_\varepsilon}(n + 1, n),$$
where $\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n) = \sum_{d \mid n} \operatorname{pmShiftedExponentSecondCoeff}\,\varepsilon\,d$,
and we proved that the relative prime deficit `pmShiftedExponentPrimeDeficit ε p` between the
local Euler factor of $\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n)$ and $1 - p^{-\varepsilon}/p$ is
uniformly $O(1/p^2)$ and satisfies $\sum_p \operatorname{pmShiftedExponentPrimeDeficit}\,\varepsilon\,p \to 0$
as $\varepsilon \to 0^+$.

In this twentieth pillar of **Bézout–Valuation Incidence Mechanics**, we establish the **exact
asymptotic Cesàro density, infinite Euler product, and small-damping rate (`ε → 0⁺`)** of both the
active-deleted shifted-exponent product $\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n)$ and the
active sawtooth martingale contribution $\tau_\varepsilon(n)\bigl(\tau_{1+\varepsilon}(n) - \tau_\varepsilon(n)\bigr)$:

## Core Main Theorems (100% Unconditional)

1. **Asymptotic Density, Euler Product & Universal Sandwich of `pmShiftedExponentSecondDensity`
   (`abs_pmShiftedExponentSecondCoeff_le`, `summable_pmShiftedExponentSecondCoeff_div`,
   `pmShiftedExponentSecondDensity_hasProd`, `tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean`,
   `pmPowerDampedSecondDensity_le_pmShiftedExponentSecondDensity`,
   `pmShiftedExponentSecondDensity_le_density`)**:
   For every $\varepsilon > 0$:
   - $\lim_{x \to \infty} \frac{1}{x} \sum_{n=1}^{\lfloor x \rfloor} \tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n) =
     \operatorname{pmShiftedExponentSecondDensity}\,\varepsilon =
     \prod_{p} \left(1 - \frac{\operatorname{pmShiftedExponentSecondWeight}\,\varepsilon\,p}{p}\right)$,
   - and the three fundamental densities obey the universal sandwich:
     $$\operatorname{pmPowerDampedSecondDensity}\,\varepsilon \le
       \operatorname{pmShiftedExponentSecondDensity}\,\varepsilon \le
       (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}.$$

2. **Exact Unit Small-Damping Limit of `pmShiftedExponentDensityRatio` & Rate `1` of the Active-Deleted Diagonal
   (`pmShiftedExponentDensityRatio_hasProd`, `pmShiftedExponentDensityRatio_bounds`,
   `tendsto_pmShiftedExponentDensityRatio`, `tendsto_pmShiftedExponentSecondDensity_div_parameter`)**:
   As $\varepsilon \to 0^+$:
   $$\lim_{\varepsilon \to 0^+} \frac{\operatorname{pmShiftedExponentSecondDensity}\,\varepsilon}{(\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}} = 1
     \quad\text{and}\quad
     \lim_{\varepsilon \to 0^+} \frac{\operatorname{pmShiftedExponentSecondDensity}\,\varepsilon}{\varepsilon} = 1,$$
   exactly **twice** the small-damping rate $1/2$ of the unshifted square density `pmPowerDampedSecondDensity ε`.

3. **Active Sawtooth Martingale Density & Exact $+1/2$ Small-Damping Rate Equipartition
   (`tendsto_pmActiveSawtoothMartingale_mean`,
   `tendsto_pmActiveSawtoothMartingaleDensity_div_parameter`,
   `tendsto_pmActiveSawtoothMartingaleDensity_sub_divisorVariance_div_parameter`)**:
   The active sawtooth martingale contribution $\tau_\varepsilon(n)\bigl(\tau_{1+\varepsilon}(n) - \tau_\varepsilon(n)\bigr)$
   has asymptotic Cesàro mean
   $$\operatorname{pmActiveSawtoothMartingaleDensity}\,\varepsilon =
     \operatorname{pmShiftedExponentSecondDensity}\,\varepsilon -
     \operatorname{pmPowerDampedSecondDensity}\,\varepsilon \ge 0,$$
   with exact small-damping rate $+1/2$:
   $$\lim_{\varepsilon \to 0^+} \frac{\operatorname{pmActiveSawtoothMartingaleDensity}\,\varepsilon}{\varepsilon} = \frac{1}{2},
     \qquad
     \lim_{\varepsilon \to 0^+} \frac{\operatorname{pmActiveSawtoothMartingaleDensity}\,\varepsilon - \operatorname{pmPowerDampedDivisorVariance}\,\varepsilon}{\varepsilon} = 0.$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Divisor-Bound, Summability, and Euler Product of `pmShiftedExponentSecondDensity` -/

/-- For every `ε ≥ 0` and every prime `p`, `0 ≤ pmShiftedExponentSecondWeight ε p` and
`pmShiftedExponentSecondWeight ε p ≤ 2 * (p : ℝ) ^ (-ε)`. -/
theorem pmShiftedExponentSecondWeight_bounds {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ pmShiftedExponentSecondWeight ε p ∧
      pmShiftedExponentSecondWeight ε p ≤ 2 * (p : ℝ) ^ (-ε) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : 0 ≤ (p : ℝ) ^ (-ε) := Real.rpow_nonneg hp0.le (-ε)
  have ht1 : (p : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hε)
  rw [pmShiftedExponentSecondWeight_eq ε hp.pos]
  have hterm_nonneg : 0 ≤ (p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) / (p : ℝ) :=
    div_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hp0.le
  have hterm_le : (p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) / (p : ℝ) ≤ (p : ℝ) ^ (-ε) := by
    have hnum_le : (p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) ≤ (p : ℝ) ^ (-ε) := by
      nlinarith [sq_nonneg ((p : ℝ) ^ (-ε))]
    calc
      (p : ℝ) ^ (-ε) * (1 - (p : ℝ) ^ (-ε)) / (p : ℝ)
        ≤ (p : ℝ) ^ (-ε) / (p : ℝ) := div_le_div_of_nonneg_right hnum_le hp0.le
      _ ≤ (p : ℝ) ^ (-ε) := div_le_self ht0 hp1
  exact ⟨by linarith, by linarith⟩

/-- **Divisor-Card Bound on `pmShiftedExponentSecondCoeff` (`abs_pmShiftedExponentSecondCoeff_le`):**
For every `ε ≥ 0` and `n : ℕ`:
`|pmShiftedExponentSecondCoeff ε n| ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-ε)`. -/
theorem abs_pmShiftedExponentSecondCoeff_le {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    |pmShiftedExponentSecondCoeff ε n| ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-ε) := by
  by_cases hn : n = 0
  · subst hn
    simp
  by_cases hsq : Squarefree n
  · have hmu : |(moebius n : ℝ)| = 1 := by
      exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
    rw [pmShiftedExponentSecondCoeff, DampedMobius.dampedMobius, pmul_apply,
      intCoe_apply, prodPrimeFactors_apply hn, abs_mul, hmu, one_mul, Finset.abs_prod]
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (2 * (p : ℝ) ^ (-ε)) := by
        apply Finset.prod_le_prod
        · intro p _
          exact abs_nonneg _
        · intro p hp
          have hp_prime := Nat.prime_of_mem_primeFactors hp
          have hb := pmShiftedExponentSecondWeight_bounds hε hp_prime
          rw [abs_of_nonneg hb.1]
          exact hb.2
      _ = (2 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (-ε) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        congr 1
        change (∏ p ∈ n.primeFactors, pmNaturalRpowHom ε p) = pmNaturalRpowHom ε n
        simpa only [map_prod] using congrArg (pmNaturalRpowHom ε)
          (Nat.prod_primeFactors_of_squarefree hsq)
      _ = _ := by
        rw [Sieve.card_divisors_of_squarefree_squarefreeDivisorCount hsq hn]
        push_cast
        rfl
  · simp [pmShiftedExponentSecondCoeff, DampedMobius.dampedMobius, pmul_apply,
      intCoe_apply, moebius_eq_zero_of_not_squarefree hsq,
      mul_nonneg (Nat.cast_nonneg n.divisors.card) (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-- **Dirichlet Summability of `pmShiftedExponentSecondCoeff` (`summable_pmShiftedExponentSecondCoeff_div`):**
For every `ε > 0`, `fun n : ℕ => pmShiftedExponentSecondCoeff ε n / n` is summable. -/
theorem summable_pmShiftedExponentSecondCoeff_div {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => pmShiftedExponentSecondCoeff ε n / (n : ℝ)) := by
  apply summable_norm_iff.mp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    (summable_divisor_sq_rpow (σ := (1 + ε) / 2) (by linarith))
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc1 : 1 ≤ n.divisors.card := by
    exact Finset.one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  have hc1R : (1 : ℝ) ≤ n.divisors.card := by exact_mod_cast hc1
  have hcsq : (n.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by nlinarith
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnpos]
  calc
    _ ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (-ε)) / n :=
      div_le_div_of_nonneg_right (abs_pmShiftedExponentSecondCoeff_le hε.le n) hnpos.le
    _ ≤ ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-ε)) / n := by
      gcongr
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hnpos.ne']
      congr 2
      ring

/-- The asymptotic density of the active-deleted shifted-exponent product
`τ_ε(n) * τ_{1+ε}(n)`:
`pmShiftedExponentSecondDensity ε = ∑' n : ℕ, pmShiftedExponentSecondCoeff ε n / n`. -/
def pmShiftedExponentSecondDensity (ε : ℝ) : ℝ :=
  ∑' n : ℕ, pmShiftedExponentSecondCoeff ε n / (n : ℝ)

/-- **Infinite Euler Product for `pmShiftedExponentSecondDensity`
(`pmShiftedExponentSecondDensity_hasProd`):**
For every `ε > 0`:
`HasProd (fun p : Nat.Primes => 1 - pmShiftedExponentSecondWeight ε p / p) (pmShiftedExponentSecondDensity ε)`. -/
theorem pmShiftedExponentSecondDensity_hasProd {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes =>
      1 - pmShiftedExponentSecondWeight ε p / (p : ℕ))
      (pmShiftedExponentSecondDensity ε) := by
  let a := pmShiftedExponentSecondCoeff ε
  have hm := DampedMobius.isMultiplicative_dampedMobius (pmShiftedExponentSecondWeight ε)
  have h1 : a 1 / ((1 : ℕ) : ℝ) = 1 := by
    simpa [a, pmShiftedExponentSecondCoeff] using hm.map_one
  have hmul {m n : ℕ} (h : m.Coprime n) :
      a (m * n) / ((m * n : ℕ) : ℝ) = (a m / (m : ℝ)) * (a n / (n : ℝ)) := by
    rw [show a (m * n) = a m * a n from hm.map_mul_of_coprime h, Nat.cast_mul]
    ring
  have hp := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} h => hmul h)
    (summable_pmShiftedExponentSecondCoeff_div hε).norm (by simp)
  apply hp.congr_fun
  intro p
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · simp [pmShiftedExponentSecondCoeff, DampedMobius.dampedMobius_apply_prime_pow,
      p.property, sub_eq_add_neg, neg_div]
  · have hk0 : k ≠ 0 := fun h => hk (by simp [h])
    have hk1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [pmShiftedExponentSecondCoeff, DampedMobius.dampedMobius_apply_prime_pow,
      p.property, hk0, hk1]

/-- **Cesàro Mean Convergence of the Active-Deleted Product `τ_ε(n) * τ_{1+ε}(n)`
(`tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean`):**
For every `ε > 0`:
`Tendsto (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, τ_ε(n) * τ_{1+ε}(n)) / x) atTop (𝓝 (pmShiftedExponentSecondDensity ε))`. -/
theorem tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n) / x)
      atTop (𝓝 (pmShiftedExponentSecondDensity ε)) := by
  simpa only [← pmPowerDampedDivisorCoeff_mul_add_one, pmShiftedExponentSecondDensity] using
    pm_tendsto_divisor_average (a := pmShiftedExponentSecondCoeff ε)
      (summable_pmShiftedExponentSecondCoeff_div hε)

/-- **Universal Lower Bound by Unshifted Second Density
(`pmPowerDampedSecondDensity_le_pmShiftedExponentSecondDensity`):**
For every `ε > 0`, `pmPowerDampedSecondDensity ε ≤ pmShiftedExponentSecondDensity ε`. -/
theorem pmPowerDampedSecondDensity_le_pmShiftedExponentSecondDensity {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedSecondDensity ε ≤ pmShiftedExponentSecondDensity ε := by
  apply le_of_tendsto_of_tendsto (tendsto_pmPowerDampedDivisorCoeff_sq_mean hε)
    (tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean hε)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply div_le_div_of_nonneg_right _ hx.le
  apply Finset.sum_le_sum
  intro n _
  have h := pmPowerDampedDivisorCoeff_le_add_one hε.le n
  nlinarith

/-- **Universal Upper Bound by Single Divisor Density
(`pmShiftedExponentSecondDensity_le_density`):**
For every `ε > 0`, `pmShiftedExponentSecondDensity ε ≤ (pmPowerDampedDivisorDensity ε).re`. -/
theorem pmShiftedExponentSecondDensity_le_density {ε : ℝ} (hε : 0 < ε) :
    pmShiftedExponentSecondDensity ε ≤ (pmPowerDampedDivisorDensity ε).re := by
  apply le_of_tendsto_of_tendsto (tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean hε)
    (tendsto_pmPowerDampedDivisorSum_div_real hε)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  apply div_le_div_of_nonneg_right _ hx.le
  apply Finset.sum_le_sum
  intro n _
  have h0 := pmPowerDampedDivisorCoeff_nonneg hε.le n
  have h1 := pmPowerDampedDivisorCoeff_le_one (by linarith : (0 : ℝ) ≤ 1 + ε) n
  nlinarith

/-! ## §2. Exact Euler Product of `pmShiftedExponentDensityRatio` & Unit Small-Damping Limit (`ε → 0⁺`) -/

/-- The ratio of the active-deleted shifted-exponent density `pmShiftedExponentSecondDensity ε`
to the first-moment divisor density `(pmPowerDampedDivisorDensity ε).re`. -/
def pmShiftedExponentDensityRatio (ε : ℝ) : ℝ :=
  pmShiftedExponentSecondDensity ε / (pmPowerDampedDivisorDensity ε).re

/-- **Exact Euler Product for `pmShiftedExponentDensityRatio`
(`pmShiftedExponentDensityRatio_hasProd`):**
For every `ε > 0`:
`HasProd (fun p : Nat.Primes => 1 - pmShiftedExponentPrimeDeficit ε p) (pmShiftedExponentDensityRatio ε)`. -/
theorem pmShiftedExponentDensityRatio_hasProd {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes => 1 - pmShiftedExponentPrimeDeficit ε p)
      (pmShiftedExponentDensityRatio ε) := by
  have hnum : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (1 - pmShiftedExponentSecondWeight ε p / (p : ℝ)))
      atTop (𝓝 (pmShiftedExponentSecondDensity ε)) :=
    pmShiftedExponentSecondDensity_hasProd hε
  have hden : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (1 - (p : ℝ) ^ (-ε) / (p : ℝ)))
      atTop (𝓝 (pmPowerDampedDivisorDensity ε).re) :=
    pmPowerDampedDivisorDensity_hasProd_real hε
  have h := hnum.div hden (pmPowerDampedDivisorDensity_re_ne_zero hε)
  change Tendsto (fun S : Finset Nat.Primes =>
    ∏ p ∈ S, (1 - pmShiftedExponentPrimeDeficit ε p))
    atTop (𝓝 (pmShiftedExponentDensityRatio ε))
  apply h.congr
  intro S
  dsimp only [Pi.div_apply]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact pmShiftedExponentPrimeDeficit_eq_one_sub_div hε.le p

/-- **Uniform Prime-Deficit Sandwich for `pmShiftedExponentDensityRatio`
(`pmShiftedExponentDensityRatio_bounds`):**
For every `ε > 0`:
`1 - (∑' p : Nat.Primes, pmShiftedExponentPrimeDeficit ε p) ≤ pmShiftedExponentDensityRatio ε`
and `pmShiftedExponentDensityRatio ε ≤ 1`. -/
theorem pmShiftedExponentDensityRatio_bounds {ε : ℝ} (hε : 0 < ε) :
    1 - (∑' p : Nat.Primes, pmShiftedExponentPrimeDeficit ε p) ≤
        pmShiftedExponentDensityRatio ε ∧ pmShiftedExponentDensityRatio ε ≤ 1 :=
  pm_hasProd_one_sub_bounds
    (fun p => (pmShiftedExponentPrimeDeficit_bounds hε.le p).1)
    (fun p => (pmShiftedExponentPrimeDeficit_bounds hε.le p).2.1)
    (summable_pmShiftedExponentPrimeDeficit hε.le)
    (pmShiftedExponentDensityRatio_hasProd hε)

/-- **Unit Small-Damping Limit of `pmShiftedExponentDensityRatio`
(`tendsto_pmShiftedExponentDensityRatio`):**
As `ε → 0⁺`, `pmShiftedExponentDensityRatio ε → 1`:
`Tendsto pmShiftedExponentDensityRatio (𝓝[>] 0) (𝓝 1)`. -/
theorem tendsto_pmShiftedExponentDensityRatio :
    Tendsto pmShiftedExponentDensityRatio (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto
      (fun ε : ℝ => 1 - (∑' p : Nat.Primes, pmShiftedExponentPrimeDeficit ε p))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_tsum_pmShiftedExponentPrimeDeficit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmShiftedExponentDensityRatio_bounds hε).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (pmShiftedExponentDensityRatio_bounds hε).2

/-- **Unit Small-Damping Rate of `pmShiftedExponentSecondDensity`
(`tendsto_pmShiftedExponentSecondDensity_div_parameter`):**
As `ε → 0⁺`, `pmShiftedExponentSecondDensity ε / ε → 1` (exactly **twice** the small-damping rate
`1 / 2` of the unshifted second density `pmPowerDampedSecondDensity ε`):
`Tendsto (fun ε : ℝ => pmShiftedExponentSecondDensity ε / ε) (𝓝[>] 0) (𝓝 1)`. -/
theorem tendsto_pmShiftedExponentSecondDensity_div_parameter :
    Tendsto (fun ε : ℝ => pmShiftedExponentSecondDensity ε / ε) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_pmShiftedExponentDensityRatio.mul
    tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have hl : Tendsto (fun ε : ℝ =>
      pmShiftedExponentDensityRatio ε * ((pmPowerDampedDivisorDensity ε).re / ε))
      (𝓝[>] 0) (𝓝 1) := by
    simpa [Pi.mul_def] using h
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have ha := pmPowerDampedDivisorDensity_re_ne_zero hε
  dsimp only [pmShiftedExponentDensityRatio]
  field_simp

/-! ## §3. Active Sawtooth Martingale Density & Exact `+1 / 2` Small-Damping Equipartition -/

/-- The asymptotic density of the active sawtooth martingale increment
`-2 * τ_ε(n) * A_ε(n) = τ_ε(n) * (τ_{1+ε}(n) - τ_ε(n))`:
`pmActiveSawtoothMartingaleDensity ε = pmShiftedExponentSecondDensity ε - pmPowerDampedSecondDensity ε`. -/
def pmActiveSawtoothMartingaleDensity (ε : ℝ) : ℝ :=
  pmShiftedExponentSecondDensity ε - pmPowerDampedSecondDensity ε

/-- For every `ε > 0`, `0 ≤ pmActiveSawtoothMartingaleDensity ε`. -/
theorem pmActiveSawtoothMartingaleDensity_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ pmActiveSawtoothMartingaleDensity ε :=
  sub_nonneg.mpr (pmPowerDampedSecondDensity_le_pmShiftedExponentSecondDensity hε)

/-- **Cesàro Mean Convergence of the Active Sawtooth Martingale Term
(`tendsto_pmActiveSawtoothMartingale_mean`):**
For every `ε > 0`:
`Tendsto (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, τ_ε(n) * (τ_{1+ε}(n) - τ_ε(n))) / x) atTop (𝓝 (pmActiveSawtoothMartingaleDensity ε))`. -/
theorem tendsto_pmActiveSawtoothMartingale_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        pmPowerDampedDivisorCoeff ε n *
          (pmPowerDampedDivisorCoeff (1 + ε) n - pmPowerDampedDivisorCoeff ε n)) / x)
      atTop (𝓝 (pmActiveSawtoothMartingaleDensity ε)) := by
  have h := (tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean hε).sub
    (tendsto_pmPowerDampedDivisorCoeff_sq_mean hε)
  have hl : Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n) / x -
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, pmPowerDampedDivisorCoeff ε n ^ 2) / x)
      atTop (𝓝 (pmActiveSawtoothMartingaleDensity ε)) := by
    simpa [pmActiveSawtoothMartingaleDensity, Pi.sub_def] using h
  apply hl.congr
  intro x
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Exact `+1 / 2` Small-Damping Rate of `pmActiveSawtoothMartingaleDensity`
(`tendsto_pmActiveSawtoothMartingaleDensity_div_parameter`):**
As `ε → 0⁺`, `pmActiveSawtoothMartingaleDensity ε / ε → 1 / 2`:
`Tendsto (fun ε : ℝ => pmActiveSawtoothMartingaleDensity ε / ε) (𝓝[>] 0) (𝓝 (1 / 2))`. -/
theorem tendsto_pmActiveSawtoothMartingaleDensity_div_parameter :
    Tendsto (fun ε : ℝ => pmActiveSawtoothMartingaleDensity ε / ε) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_pmShiftedExponentSecondDensity_div_parameter.sub
    tendsto_pmPowerDampedSecondDensity_div_parameter
  have hl : Tendsto (fun ε : ℝ =>
      pmShiftedExponentSecondDensity ε / ε - pmPowerDampedSecondDensity ε / ε)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    convert h using 2
    norm_num
  apply hl.congr
  intro ε
  dsimp only [pmActiveSawtoothMartingaleDensity]
  ring

/-- **Small-Damping Equipartition Between `pmActiveSawtoothMartingaleDensity` and `pmPowerDampedDivisorVariance`
(`tendsto_pmActiveSawtoothMartingaleDensity_sub_divisorVariance_div_parameter`):**
As `ε → 0⁺`, the active sawtooth martingale density and the unshifted divisor variance share the
exact same leading small-damping rate `ε / 2`, so their difference is `o(ε)`:
`Tendsto (fun ε : ℝ => (pmActiveSawtoothMartingaleDensity ε - pmPowerDampedDivisorVariance ε) / ε) (𝓝[>] 0) (𝓝 0)`. -/
theorem tendsto_pmActiveSawtoothMartingaleDensity_sub_divisorVariance_div_parameter :
    Tendsto (fun ε : ℝ =>
      (pmActiveSawtoothMartingaleDensity ε - pmPowerDampedDivisorVariance ε) / ε)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_pmActiveSawtoothMartingaleDensity_div_parameter.sub
    tendsto_pmPowerDampedDivisorVariance_div_parameter
  have hl : Tendsto (fun ε : ℝ =>
      pmActiveSawtoothMartingaleDensity ε / ε - pmPowerDampedDivisorVariance ε / ε)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Pi.sub_def] using h
  apply hl.congr
  intro ε
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
