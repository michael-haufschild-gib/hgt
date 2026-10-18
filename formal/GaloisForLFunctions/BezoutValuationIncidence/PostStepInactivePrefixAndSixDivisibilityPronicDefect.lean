import GaloisForLFunctions.BezoutValuationIncidence.BezoutPronicTotientInteriorMartingaleSynthesis
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar XXV: Post-Step Inactive Prefix Smoothing, Divisor-Ordering Antitonicity & Universal `6`-Adic Bézout Ceilings

In Pillar XXIV (`BezoutPronicTotientInteriorMartingaleSynthesis`), we established the diagonal-free
Bézout Pronic–Totient–Interior Martingale Identity for Route PM.

In this twenty-fifth pillar of **Bézout–Valuation Incidence Mechanics**, we establish three new
foundational mechanisms:

1. **Post-Step Inactive Residual Prefix (`pmPostStepInactivePrefix`) & Two-Point Bézout Smoothing
   (`pmPostStepInactivePrefix_sub_pmInactiveResidualPrefix`,
   `pmPostStepInactivePrefix_sq_sub_pmInactiveResidualPrefix_sq`,
   `addDiff_pmPostStepInactivePrefix`,
   `pmActiveSawtoothComponent_bounds`)**:
   Defining $\operatorname{pmPostStepInactivePrefix}\,\varepsilon\,m := A_\varepsilon(m) + \operatorname{pmActiveSawtoothComponent}\,\varepsilon\,m$:
   - Across $n \mapsto n + 1$, the intra-step drift from `pmInactiveResidualPrefix ε n` to
     `pmPostStepInactivePrefix ε (n + 1)` is purely the shifted-exponent totient impulse
     $\tau_{1+\varepsilon}(n + 1) - (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}$.
   - The BVI forward difference `addDiff (pmPostStepInactivePrefix ε) n` replaces the raw impulse
     $\widetilde{\tau}_\varepsilon(n + 1)$ by the **two-point Bézout average**
     $\frac{1}{2}\bigl(\widetilde{\tau}_\varepsilon(n) + \widetilde{\tau}_\varepsilon(n + 1)\bigr)$
     plus $\frac{1}{2}\,\operatorname{addDiff}\,(\tau_{1+\varepsilon})\,n$, while remaining within
     $[0, 1/2]$ of $A_\varepsilon(n)$ uniformly for all $n \in \mathbb{N}$ and $\varepsilon \ge 0$.

2. **Universal Divisor-Ordering Antitonicity & Submultiplicativity of `pmPowerDampedDivisorCoeff`
   (`pmPowerDampedDivisorCoeff_eq_mul_sdiff_of_dvd`,
   `pmPowerDampedDivisorCoeff_le_of_dvd`,
   `pmPowerDampedDivisorCoeff_mul_le`)**:
   - For every $\varepsilon : \mathbb{R}$ and $d \mid m$ ($m \ne 0$):
     $$\tau_\varepsilon(m) = \tau_\varepsilon(d) \prod_{p \in m.\text{primeFactors} \setminus d.\text{primeFactors}} (1 - p^{-\varepsilon}),$$
     so for all $\varepsilon \ge 0$, $d \mid m \implies m \ne 0 \implies \tau_\varepsilon(m) \le \tau_\varepsilon(d)$.
   - For every $\varepsilon \ge 0$ and all $a, b \in \mathbb{N}$ (without coprimality):
     $$\tau_\varepsilon(a)\,\tau_\varepsilon(b) \le \tau_\varepsilon(a \cdot b).$$

3. **Two-Step and Universal Three-Step `6`-Adic Bézout Product Ceilings
   (`pmPowerDampedDivisorCoeff_pronicSeq_le_six_of_three_dvd`,
   `six_dvd_mul_succ_mul_add_two`,
   `pmPowerDampedDivisorCoeff_three_step_mul_le_six`)**:
   - Whenever $3 \mid k$ or $3 \mid (k + 1)$ ($k \ge 1$, holding for $2/3$ of all integers),
     $6 \mid \operatorname{pronicSeq}\,k$, so for all $\varepsilon \ge 0$:
     $$\tau_\varepsilon(k)\,\tau_\varepsilon(k + 1) = \tau_\varepsilon(\operatorname{pronicSeq}\,k) \le \tau_\varepsilon(6) = (1 - 2^{-\varepsilon})(1 - 3^{-\varepsilon}).$$
   - For **every** $k \ge 1$ and $\varepsilon \ge 0$, $6 \mid k(k + 1)(k + 2)$, so the three-step
     consecutive product obeys the universal quadratic ceiling:
     $$\tau_\varepsilon(k)\,\tau_\varepsilon(k + 1)\,\tau_\varepsilon(k + 2) \le \tau_\varepsilon\bigl(k(k + 1)(k + 2)\bigr) \le \tau_\varepsilon(6) = (1 - 2^{-\varepsilon})(1 - 3^{-\varepsilon}).$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Post-Step Inactive Residual Prefix & Two-Point Bézout Smoothing -/

/-- The **horizon-free post-step inactive residual prefix** of Route PM at integer `m`:
`pmPostStepInactivePrefix ε m = pmPowerDampedCenteredDivisorPrefix ε m + pmActiveSawtoothComponent ε m`
(obtained by subtracting the post-jump peak `-pmActiveSawtoothComponent ε m` from `A_ε(m)`). -/
def pmPostStepInactivePrefix (ε : ℝ) (m : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε m + pmActiveSawtoothComponent ε m

/-- **Intra-Step Shifted-Exponent Drift of the Inactive Prefix Across `n ↦ n + 1`
(`pmPostStepInactivePrefix_sub_pmInactiveResidualPrefix`):**
For every `ε : ℝ` and `n : ℕ`, the change from the pre-step inactive prefix
`pmInactiveResidualPrefix ε n` to the post-step inactive prefix
`pmPostStepInactivePrefix ε (n + 1)` equals the shifted-exponent totient impulse
`pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re`. -/
theorem pmPostStepInactivePrefix_sub_pmInactiveResidualPrefix (ε : ℝ) (n : ℕ) :
    pmPostStepInactivePrefix ε (n + 1) - pmInactiveResidualPrefix ε n =
      pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re := by
  unfold pmPostStepInactivePrefix pmInactiveResidualPrefix pmActiveSawtoothComponent
  rw [pmPowerDampedCenteredDivisorPrefix_succ]
  unfold pmPowerDampedCenteredDivisorCoeff
  ring

/-- **Midpoint Conservation Between Inactive and Full Prefixes
(`pmInactiveResidualPrefix_add_pmPostStepInactivePrefix`):**
For every `ε : ℝ` and `n : ℕ`:
`pmInactiveResidualPrefix ε n + pmPostStepInactivePrefix ε (n + 1) = pmPowerDampedCenteredDivisorPrefix ε n + pmPowerDampedCenteredDivisorPrefix ε (n + 1)`. -/
theorem pmInactiveResidualPrefix_add_pmPostStepInactivePrefix (ε : ℝ) (n : ℕ) :
    pmInactiveResidualPrefix ε n + pmPostStepInactivePrefix ε (n + 1) =
      pmPowerDampedCenteredDivisorPrefix ε n + pmPowerDampedCenteredDivisorPrefix ε (n + 1) := by
  unfold pmInactiveResidualPrefix pmPostStepInactivePrefix
  ring

/-- **Intra-Step Square Change of the Inactive Prefix Across `n ↦ n + 1`
(`pmPostStepInactivePrefix_sq_sub_pmInactiveResidualPrefix_sq`):**
For every `ε : ℝ` and `n : ℕ`:
`(pmPostStepInactivePrefix ε (n + 1))² - (pmInactiveResidualPrefix ε n)² = (τ_{1+ε}(n + 1) - α_ε) * (A_ε(n) + A_ε(n + 1))`. -/
theorem pmPostStepInactivePrefix_sq_sub_pmInactiveResidualPrefix_sq (ε : ℝ) (n : ℕ) :
    pmPostStepInactivePrefix ε (n + 1) ^ (2 : ℕ) -
      pmInactiveResidualPrefix ε n ^ (2 : ℕ) =
      (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
        (pmPowerDampedCenteredDivisorPrefix ε n +
          pmPowerDampedCenteredDivisorPrefix ε (n + 1)) := by
  have hfac :
      pmPostStepInactivePrefix ε (n + 1) ^ (2 : ℕ) -
        pmInactiveResidualPrefix ε n ^ (2 : ℕ) =
      (pmPostStepInactivePrefix ε (n + 1) - pmInactiveResidualPrefix ε n) *
        (pmInactiveResidualPrefix ε n + pmPostStepInactivePrefix ε (n + 1)) := by
    ring
  rw [hfac, pmPostStepInactivePrefix_sub_pmInactiveResidualPrefix,
    pmInactiveResidualPrefix_add_pmPostStepInactivePrefix]

/-- **Two-Point Bézout Smoothing of `addDiff (pmPostStepInactivePrefix ε)`
(`addDiff_pmPostStepInactivePrefix`):**
For every `ε : ℝ` and `n : ℕ`, the BVI forward difference of `pmPostStepInactivePrefix ε` replaces
the single impulse `widetilde_τ_ε(n + 1)` by the two-point Bézout average
`(1 / 2) * (widetilde_τ_ε(n) + widetilde_τ_ε(n + 1))` plus `(1 / 2) * addDiff (τ_{1+ε}) n`. -/
theorem addDiff_pmPostStepInactivePrefix (ε : ℝ) (n : ℕ) :
    addDiff (pmPostStepInactivePrefix ε) n =
      (1 / 2 : ℝ) *
        (pmPowerDampedCenteredDivisorCoeff ε n +
          pmPowerDampedCenteredDivisorCoeff ε (n + 1)) +
        (1 / 2 : ℝ) * addDiff (pmPowerDampedDivisorCoeff (1 + ε)) n := by
  unfold addDiff pmPostStepInactivePrefix pmActiveSawtoothComponent
  rw [pmPowerDampedCenteredDivisorPrefix_succ]
  unfold pmPowerDampedCenteredDivisorCoeff
  ring

/-- **Uniform `[0, 1 / 2]` Bounds on `pmActiveSawtoothComponent` (`pmActiveSawtoothComponent_bounds`):**
For every `ε ≥ 0` and `m : ℕ`:
`0 ≤ pmActiveSawtoothComponent ε m` and `pmActiveSawtoothComponent ε m ≤ 1 / 2`. -/
theorem pmActiveSawtoothComponent_bounds {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    0 ≤ pmActiveSawtoothComponent ε m ∧ pmActiveSawtoothComponent ε m ≤ 1 / 2 := by
  refine ⟨pmActiveSawtoothComponent_nonneg hε m, ?_⟩
  unfold pmActiveSawtoothComponent
  have h0 : 0 ≤ pmPowerDampedDivisorCoeff ε m := pmPowerDampedDivisorCoeff_nonneg hε m
  have h1 : pmPowerDampedDivisorCoeff (1 + ε) m ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one (by linarith) m
  linarith

/-- For every `ε ≥ 0` and `n : ℕ`, `pmPostStepInactivePrefix ε n` lies in the uniform interval
`[A_ε(n), A_ε(n) + 1 / 2]`. -/
theorem pmPostStepInactivePrefix_sandwich {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n ≤ pmPostStepInactivePrefix ε n ∧
      pmPostStepInactivePrefix ε n ≤ pmPowerDampedCenteredDivisorPrefix ε n + 1 / 2 := by
  obtain ⟨h0, h1⟩ := pmActiveSawtoothComponent_bounds hε n
  unfold pmPostStepInactivePrefix
  exact ⟨by linarith, by linarith⟩

/-! ## §2. Universal Divisor-Ordering Antitonicity & Submultiplicativity of `pmPowerDampedDivisorCoeff` -/

/-- **Exact Divisor-Quotient Euler Factorization of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_eq_mul_sdiff_of_dvd`):**
For every `ε : ℝ` and `d, m : ℕ` with `d ∣ m` and `m ≠ 0`:
`pmPowerDampedDivisorCoeff ε m = pmPowerDampedDivisorCoeff ε d * ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - p^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_eq_mul_sdiff_of_dvd (ε : ℝ) {d m : ℕ}
    (hdvd : d ∣ m) (hm : m ≠ 0) :
    pmPowerDampedDivisorCoeff ε m =
      pmPowerDampedDivisorCoeff ε d *
        ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℝ) ^ (-ε)) := by
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hdvd
  have hsub : d.primeFactors ⊆ m.primeFactors := Nat.primeFactors_mono hdvd hm
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hm,
    pmPowerDampedDivisorCoeff_eq_prod ε hd,
    ← Finset.prod_union disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset hsub]

/-- **Universal Divisor-Ordering Antitonicity of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_le_of_dvd`):**
For every `ε ≥ 0` and `d, m : ℕ` with `d ∣ m` and `m ≠ 0`:
`pmPowerDampedDivisorCoeff ε m ≤ pmPowerDampedDivisorCoeff ε d`. -/
theorem pmPowerDampedDivisorCoeff_le_of_dvd {ε : ℝ} (hε : 0 ≤ ε) {d m : ℕ}
    (hdvd : d ∣ m) (hm : m ≠ 0) :
    pmPowerDampedDivisorCoeff ε m ≤ pmPowerDampedDivisorCoeff ε d := by
  rw [pmPowerDampedDivisorCoeff_eq_mul_sdiff_of_dvd ε hdvd hm]
  have hd0 : 0 ≤ pmPowerDampedDivisorCoeff ε d := pmPowerDampedDivisorCoeff_nonneg hε d
  have hprod_le_one :
      (∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℝ) ^ (-ε))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have hp_prime : Nat.Prime p :=
        Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
      apply sub_nonneg.mpr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp_prime.one_le) (by linarith)
    · intro p _
      linarith [Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)]
  calc
    pmPowerDampedDivisorCoeff ε d *
        ∏ p ∈ m.primeFactors \ d.primeFactors, (1 - (p : ℝ) ^ (-ε))
      ≤ pmPowerDampedDivisorCoeff ε d * 1 := mul_le_mul_of_nonneg_left hprod_le_one hd0
    _ = pmPowerDampedDivisorCoeff ε d := mul_one _

/-- **Universal Submultiplicativity of `pmPowerDampedDivisorCoeff`
(`pmPowerDampedDivisorCoeff_mul_le`):**
For every `ε ≥ 0` and **all** `a, b : ℕ` (without any coprimality condition),
`pmPowerDampedDivisorCoeff ε a * pmPowerDampedDivisorCoeff ε b ≤ pmPowerDampedDivisorCoeff ε (a * b)`. -/
theorem pmPowerDampedDivisorCoeff_mul_le {ε : ℝ} (hε : 0 ≤ ε) (a b : ℕ) :
    pmPowerDampedDivisorCoeff ε a * pmPowerDampedDivisorCoeff ε b ≤
      pmPowerDampedDivisorCoeff ε (a * b) := by
  rw [pmPowerDampedDivisorCoeff_mul_eq_mul_gcd]
  have hab0 : 0 ≤ pmPowerDampedDivisorCoeff ε (a * b) :=
    pmPowerDampedDivisorCoeff_nonneg hε (a * b)
  have hgcd1 : pmPowerDampedDivisorCoeff ε (Nat.gcd a b) ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one hε (Nat.gcd a b)
  nlinarith

/-! ## §3. Two-Step and Universal Three-Step `6`-Adic Bézout Product Ceilings -/

/-- Whenever `3 ∣ k` or `3 ∣ (k + 1)`, `6 ∣ pronicSeq k`. -/
theorem six_dvd_pronicSeq_of_three_dvd {k : ℕ} (h3 : 3 ∣ k ∨ 3 ∣ (k + 1)) :
    6 ∣ pronicSeq k := by
  have h2 : 2 ∣ pronicSeq k := two_dvd_pronicSeq k
  have h3_pronic : 3 ∣ pronicSeq k := by
    unfold pronicSeq
    rcases h3 with hk | hk1
    · exact dvd_mul_of_dvd_left hk (k + 1)
    · exact dvd_mul_of_dvd_right hk1 k
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3_pronic

/-- **`6`-Adic Quadratic Ceiling on Pronic Bézout Nodes (`pmPowerDampedDivisorCoeff_pronicSeq_le_six_of_three_dvd`):**
For every `ε ≥ 0` and every `k ≥ 1` with `3 ∣ k ∨ 3 ∣ (k + 1)` (holding for `2 / 3` of all integers `k`):
`pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤ (1 - 2^{-ε}) * (1 - 3^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_pronicSeq_le_six_of_three_dvd
    {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : 1 ≤ k) (h3 : 3 ∣ k ∨ 3 ∣ (k + 1)) :
    pmPowerDampedDivisorCoeff ε (pronicSeq k) ≤
      (1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) := by
  have hle6 := pmPowerDampedDivisorCoeff_le_of_dvd hε
    (six_dvd_pronicSeq_of_three_dvd h3) (pronicSeq_ne_zero hk)
  rwa [(pmPowerDampedDivisorCoeff_four_and_six ε).2.1] at hle6

/-- Every product of three consecutive integers `k * (k + 1) * (k + 2)` is divisible by `3`. -/
theorem three_dvd_mul_succ_mul_add_two (k : ℕ) :
    3 ∣ k * (k + 1) * (k + 2) := by
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hdiv := Nat.div_add_mod k 3
  rcases hmod with h0 | h1 | h2
  · refine ⟨(k / 3) * (k + 1) * (k + 2), ?_⟩
    have hk : k = 3 * (k / 3) := by omega
    calc
      k * (k + 1) * (k + 2) = (3 * (k / 3)) * (k + 1) * (k + 2) := by rw [← hk]
      _ = 3 * ((k / 3) * (k + 1) * (k + 2)) := by ring
  · refine ⟨k * (k + 1) * (k / 3 + 1), ?_⟩
    have hk2 : k + 2 = 3 * (k / 3 + 1) := by omega
    calc
      k * (k + 1) * (k + 2) = k * (k + 1) * (3 * (k / 3 + 1)) := by rw [hk2]
      _ = 3 * (k * (k + 1) * (k / 3 + 1)) := by ring
  · refine ⟨k * (k / 3 + 1) * (k + 2), ?_⟩
    have hk1 : k + 1 = 3 * (k / 3 + 1) := by omega
    calc
      k * (k + 1) * (k + 2) = k * (3 * (k / 3 + 1)) * (k + 2) := by rw [hk1]
      _ = 3 * (k * (k / 3 + 1) * (k + 2)) := by ring

/-- Every product of three consecutive integers `k * (k + 1) * (k + 2)` is divisible by `6`. -/
theorem six_dvd_mul_succ_mul_add_two (k : ℕ) :
    6 ∣ k * (k + 1) * (k + 2) := by
  have h2 : 2 ∣ k * (k + 1) * (k + 2) :=
    dvd_mul_of_dvd_left (two_dvd_pronicSeq k) (k + 2)
  have h3 : 3 ∣ k * (k + 1) * (k + 2) := three_dvd_mul_succ_mul_add_two k
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3

/-- **Universal Three-Step `6`-Adic Bézout Product Ceiling
(`pmPowerDampedDivisorCoeff_three_step_mul_le_six`):**
For **every** `ε ≥ 0` and **every** `k ≥ 1`, the product of three consecutive power-damped divisor
coefficients is bounded above by the `6`-adic Wall 11 value `(1 - 2^{-ε}) * (1 - 3^{-ε})`:
`pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) * pmPowerDampedDivisorCoeff ε (k + 2) ≤ (1 - 2^{-ε}) * (1 - 3^{-ε})`. -/
theorem pmPowerDampedDivisorCoeff_three_step_mul_le_six {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℕ} (hk : 1 ≤ k) :
    pmPowerDampedDivisorCoeff ε k *
      pmPowerDampedDivisorCoeff ε (k + 1) *
      pmPowerDampedDivisorCoeff ε (k + 2) ≤
      (1 - (2 : ℝ) ^ (-ε)) * (1 - (3 : ℝ) ^ (-ε)) := by
  have h12 : pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) =
      pmPowerDampedDivisorCoeff ε (k * (k + 1)) :=
    pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq ε k
  have h123 : pmPowerDampedDivisorCoeff ε (k * (k + 1)) *
      pmPowerDampedDivisorCoeff ε (k + 2) ≤
      pmPowerDampedDivisorCoeff ε (k * (k + 1) * (k + 2)) :=
    pmPowerDampedDivisorCoeff_mul_le hε (k * (k + 1)) (k + 2)
  have hne : k * (k + 1) * (k + 2) ≠ 0 := by positivity
  have h6 := pmPowerDampedDivisorCoeff_le_of_dvd hε (six_dvd_mul_succ_mul_add_two k) hne
  rw [(pmPowerDampedDivisorCoeff_four_and_six ε).2.1] at h6
  rw [h12]
  exact h123.trans h6

end
end GaloisForLFunctions.BezoutValuationIncidence
