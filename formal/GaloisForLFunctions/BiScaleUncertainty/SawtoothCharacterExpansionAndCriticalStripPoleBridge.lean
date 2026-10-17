import GaloisForLFunctions.BiScaleUncertainty.RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCenteredEnergy
import GaloisForLFunctions.RHTower.PMRamanujanComplementarySourceBounds
import GaloisForLFunctions.RHTower.PMRamanujanComplementaryCancellation

/-!
# Sawtooth Period Moments, Complementary Ramanujan Cancellation & Critical-Strip Pole Bridge

This module builds **Missing Tool 2** of the `BiScaleUncertainty` framework on Route `FZZ-P` /
`Route PM`:

1. **Exact Complete-Period Second Moment & Reflection Anti-Symmetry of `centeredDiscreteSawtooth` (§1):**
   - For every modulus $d > 0$ and residue $1 \le r < d$, the centered discrete Bernoulli sawtooth
     satisfies the exact reflection anti-symmetry
     $$\widetilde{B}_1(d, d - r) = -\widetilde{B}_1(d, r).$$
   - Over a complete period $r \in \{0, \dots, d - 1\}$, its exact second moment is
     $$\sum_{r=0}^{d-1} \widetilde{B}_1(d, r)^2 = \frac{d^2 - 1}{12\,d},$$
     which vanishes identically at $d = 1$ and gives a per-residue mean square of
     $\frac{d^2 - 1}{12\,d^2} < \frac{1}{12}$.

2. **Centered Sawtooth Hyperbola Decomposition & Complementary Large-Prime Cancellation (§2):**
   - Refines the Dirichlet hyperbola decomposition `pmPowerDampedDivisorRemainder_harmonic_split`
     by separating the small-divisor fractional head into its constant period bias
     $-\sum_{d=1}^Y a_\varepsilon(d)\frac{d-1}{2d}$ and its zero-mean periodic Bernoulli sawtooth
     oscillation $-\sum_{d=1}^Y a_\varepsilon(d)\widetilde{B}_1(d, N)$.
   - Synthesizes the unconditional sub-power logarithmic saving
     `pmPowerDampedDivisorRemainder_eventually_log_four` with the asymptotic complementary-sector
     cancellation laws (`tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one` and
     `tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one`) across the entire critical strip
     $0 < \varepsilon < 1 / 2$.

3. **Critical-Strip Cleared Mellin Continuation, Zero Translation & Cofinal RH Bridge (§3):**
   - Connects `pmPowerDampedFermiSource_memLp_and_analytic_of_centeredSawtooth_budget` and
     `pmPowerDampedFermiSource_memLp_and_analytic_of_meanCenteredQuadratic_budget` directly to
     the cleared Mellin continuation `pmPowerDamped_cleared_mellin`, the off-line zero translation
     law `pmPowerDamped_zero_translation` ($\zeta(\rho) = 0 \implies \zeta(\rho - \varepsilon) = 0$),
     and the cofinal critical-strip criteria for `RiemannHypothesis`.
-/

open MeasureTheory Set Filter Topology Complex Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Reflection Anti-Symmetry & Complete-Period Second Moment of `centeredDiscreteSawtooth` -/

/-- **Reflection Anti-Symmetry of `centeredDiscreteSawtooth`:**
For every modulus `d > 0` and `1 ≤ r < d`,
$$\widetilde{B}_1(d, d - r) = -\widetilde{B}_1(d, r).$$ -/
theorem centeredDiscreteSawtooth_reflect {d r : ℕ} (hr1 : 1 ≤ r) (hrd : r < d) :
    centeredDiscreteSawtooth d (d - r) = -centeredDiscreteSawtooth d r := by
  have hd : 0 < d := by omega
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hmod1 : (d - r) % d = d - r := Nat.mod_eq_of_lt (Nat.sub_lt hd hr1)
  have hmod2 : r % d = r := Nat.mod_eq_of_lt hrd
  rw [centeredDiscreteSawtooth_eq_mod_sub_half hd (d - r),
    centeredDiscreteSawtooth_eq_mod_sub_half hd r, hmod1, hmod2,
    Nat.cast_sub hrd.le]
  field_simp [hdR]
  ring

/-- Polynomial summation identity `2 * ∑_{r=0}^{m-1} r = m * (m - 1)` in `ℝ`. -/
theorem two_mul_sum_range_cast (m : ℕ) :
    2 * (∑ r ∈ Finset.range m, (r : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Polynomial summation identity `6 * ∑_{r=0}^{m-1} r² = m * (m - 1) * (2m - 1)` in `ℝ`. -/
theorem six_mul_sum_range_sq_cast (m : ℕ) :
    6 * (∑ r ∈ Finset.range m, (r : ℝ) ^ 2) =
      (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- **Exact Complete-Period Second Moment of `centeredDiscreteSawtooth`:**
For every `d > 0`, summing `centeredDiscreteSawtooth d r ^ 2` over a complete period
`r ∈ Finset.range d` equals `((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ))`. -/
theorem sum_sq_centeredDiscreteSawtooth_range {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Finset.range d, centeredDiscreteSawtooth d r ^ 2) =
      ((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hterm : ∀ r ∈ Finset.range d,
      centeredDiscreteSawtooth d r ^ 2 =
        ((r : ℝ) ^ 2 - ((d : ℝ) - 1) * (r : ℝ) + (((d : ℝ) - 1) / 2) ^ 2) / (d : ℝ) ^ 2 := by
    intro r hr
    rw [centeredDiscreteSawtooth_eq_mod_sub_half hd r,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hr), div_pow]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 := two_mul_sum_range_cast d
  have h2 := six_mul_sum_range_sq_cast d
  have hnum :
      (∑ r ∈ Finset.range d, (r : ℝ) ^ 2) -
        ((d : ℝ) - 1) * (∑ r ∈ Finset.range d, (r : ℝ)) +
        (d : ℝ) * (((d : ℝ) - 1) / 2) ^ 2 =
      (d : ℝ) * ((d : ℝ) ^ 2 - 1) / 12 := by
    linear_combination (1 / 6) * h2 - ((d : ℝ) - 1) / 2 * h1
  rw [hnum]
  field_simp [hdR]

/-- **Complete-Period Mean Square Bound (`< 1 / 12`):**
For every `d > 0`, the complete-period sum of squares of `centeredDiscreteSawtooth d` is strictly
bounded by `(d : ℝ) / 12`. -/
theorem sum_sq_centeredDiscreteSawtooth_range_lt {d : ℕ} (hd : 0 < d) :
    (∑ r ∈ Finset.range d, centeredDiscreteSawtooth d r ^ 2) < (d : ℝ) / 12 := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [sum_sq_centeredDiscreteSawtooth_range hd]
  calc
    ((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ))
      < (d : ℝ) ^ 2 / (12 * (d : ℝ)) := by
        apply div_lt_div_of_pos_right (by linarith) (by positivity)
    _ = (d : ℝ) / 12 := by
        field_simp [hdR.ne']

/-! ## §2. Centered Sawtooth Hyperbola Split & Complementary Sector Cancellation -/

/-- Decomposition of the small-divisor fractional head in `pmPowerDampedDivisorRemainder_harmonic_split`
into its constant complete-period bias plus its zero-mean Bernoulli sawtooth sum. -/
theorem sum_pmPowerDampedMobiusCoeff_fract_eq_periodBias_add_centeredSawtooth
    (ε : ℝ) (Y N : ℕ) :
    (∑ d ∈ Finset.Icc 1 Y,
      pmPowerDampedMobiusCoeff ε d * ((Int.fract ((N : ℝ) / (d : ℝ)) : ℝ) : ℂ)) =
    (∑ d ∈ Finset.Icc 1 Y,
      pmPowerDampedMobiusCoeff ε d * ((((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ)) +
    (∑ d ∈ Finset.Icc 1 Y,
      pmPowerDampedMobiusCoeff ε d * ((centeredDiscreteSawtooth d N : ℝ) : ℂ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold centeredDiscreteSawtooth
  push_cast
  ring

/-- **Centered Sawtooth Hyperbola Split of `pmPowerDampedDivisorRemainder`:**
For every `ε > 0` and `Y ≤ N`, `pmPowerDampedDivisorRemainder ε N` splits into:
1. the constant period-bias head `-∑_{d=1}^Y a_ε(d) (d - 1) / (2d)`,
2. the zero-mean periodic Bernoulli sawtooth head `-∑_{d=1}^Y a_ε(d) B̃₁(d, N)`,
3. the large-divisor Dirichlet hyperbola block `∑_{k=1}^{⌊N/(Y+1)⌋} ∑_{Y < d ≤ N/k} a_ε(d)`, and
4. the infinite density tail `-N ∑_{k ≥ 0} a_ε(k + Y + 1) / (k + Y + 1)`. -/
theorem pmPowerDampedDivisorRemainder_centeredSawtooth_hyperbola_split
    {ε : ℝ} (hε : 0 < ε) {Y N : ℕ} (hYN : Y ≤ N) :
    pmPowerDampedDivisorRemainder ε N =
      -(∑ d ∈ Finset.Icc 1 Y,
          pmPowerDampedMobiusCoeff ε d * ((((d : ℝ) - 1) / (2 * (d : ℝ)) : ℝ) : ℂ)) -
      (∑ d ∈ Finset.Icc 1 Y,
          pmPowerDampedMobiusCoeff ε d * ((centeredDiscreteSawtooth d N : ℝ) : ℂ)) +
      (∑ k ∈ Finset.Icc 1 (N / (Y + 1)),
          ∑ d ∈ Finset.Ioc Y (N / k), pmPowerDampedMobiusCoeff ε d) -
      (N : ℂ) * (∑' k : ℕ,
          pmPowerDampedMobiusCoeff ε (k + (Y + 1)) / ((k + (Y + 1) : ℕ) : ℂ)) := by
  rw [pmPowerDampedDivisorRemainder_harmonic_split hε hYN,
    sum_pmPowerDampedMobiusCoeff_fract_eq_periodBias_add_centeredSawtooth]
  ring

/-- **Unconditional Critical-Strip Sub-Power Saving & Complementary Sector Cancellation Certificate:**
For every damping parameter `0 < ε < 1 / 2` in the critical strip:
1. `pmPowerDampedDivisorRemainder ε N` enjoys an unconditional `(log N)^4` saving over the trivial
   `N^(1 - ε)` divisor scale (`pmPowerDampedDivisorRemainder_eventually_log_four`),
2. the complete prefix energy on `1 ≤ N ≤ P - 1` is `o(1)` of `pmRamanujanLargePrimeSectorEnergy ε P`,
3. the signed mixed cross-energy `pmRamanujanLargePrimeComplementMixedEnergy ε P` asymptotically
   cancels `-1` times `pmRamanujanLargePrimeSectorEnergy ε P`, and
4. the complementary energy `pmRamanujanLargePrimeComplementEnergy ε P` is asymptotically `+1`
   times `pmRamanujanLargePrimeSectorEnergy ε P`. -/
theorem pmPowerDamped_complementary_cancellation_and_subpower_certificate
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖pmPowerDampedDivisorRemainder ε N‖ ≤
        1 + C * (N : ℝ) ^ (1 - ε) / Real.log (N : ℝ) ^ 4) ∧
    Tendsto (fun P : ℕ => pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) /
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 0) ∧
    Tendsto (fun P : ℕ => pmRamanujanLargePrimeComplementMixedEnergy ε P /
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 (-1)) ∧
    Tendsto (fun P : ℕ => pmRamanujanLargePrimeComplementEnergy ε P /
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 1) :=
  ⟨pmPowerDampedDivisorRemainder_eventually_log_four hε hεhalf,
    tendsto_pmRamanujanCompleteHeadEnergy_div_largePrimeSectorEnergy_zero hε hεhalf,
    tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf,
    tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one hε hεhalf⟩

/-! ## §3. Critical-Strip Cleared Mellin Identity, Zero Translation & Cofinal RH Bridge -/

/-- **Unconditional Three-Way Equivalence of Canonical Admission at `ε > 0`:**
For every `ε > 0`, `L²(0, ∞)` admission of `pmPowerDampedFermiSource ε` is equivalent both to
`L²(0, ∞)` admission of `pmPowerDampedCenteredSource ε` and to `L²(dx / x²)` integrability of
`pmPowerDampedDivisorRemainder ε`. -/
theorem pmPowerDampedFermiSource_admission_iff_centered_and_divisor_energy
    {ε : ℝ} (hε : 0 < ε) :
    (MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      MemLp (pmPowerDampedCenteredSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) ∧
    (MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ↔
      IntegrableOn (fun x => ‖pmPowerDampedDivisorRemainder ε x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ))) :=
  ⟨pmPowerDampedFermiSource_memLp_iff_centered hε,
    pmPowerDampedFermiSource_memLp_iff_divisor_energy hε⟩

/-- **Cleared Mellin Identity & Off-Line Zero Translation from Centered Sawtooth Variance:**
For any `0 < ε ≤ 1 / 2` and uniform bound `B` on the reciprocal-weighted second moment of
`pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N`:
1. The cleared Mellin identity
   `s * zetaResidueUnit (s + ε) * mellin (pmPowerDampedFermiSource ε) s = (s + ε - 1) * (1 - 2^(1 - s)) * riemannZeta s`
   holds throughout the open right critical strip `1 / 2 < s.re < 1`.
2. Every zeta zero `ρ` with `1 / 2 + ε < ρ.re < 1` translates to a zeta zero at `ρ - ε`. -/
theorem cleared_mellin_and_zero_translation_of_centeredSawtooth_budget
    {ε B : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hB : ∀ Q : ℕ,
      (∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))) ≤ B) :
    (∀ {s : ℂ}, 1 / 2 < s.re ∧ s.re < 1 →
      s * zetaResidueUnit (s + (ε : ℂ)) * mellin (pmPowerDampedFermiSource ε) s =
        (s + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) ∧
    (∀ {ρ : ℂ}, 1 / 2 + ε < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      riemannZeta (ρ - (ε : ℂ)) = 0) := by
  have hm : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    (pmPowerDampedFermiSource_memLp_and_analytic_of_centeredSawtooth_budget hε0 hB).1
  exact ⟨fun hs => pmPowerDamped_cleared_mellin ε hε0 hε1 hm hs,
    fun hρ hρ1 hzero => pmPowerDamped_zero_translation ε hε0 hε1 hm hρ hρ1 hzero⟩

/-- **Cofinal Centered Sawtooth Variance Bridge to `RiemannHypothesis`:**
If for every `δ > 0` there exist a damping parameter `0 < ε < δ` and a uniform bound `B` on the
reciprocal-weighted second moment of `pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofinal_centeredSawtooth_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∀ Q : ℕ,
      (∑' N : ℕ, (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q N) ^ 2 /
        ((N : ℝ) * ((N : ℝ) + 1))) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  obtain ⟨ε, hε0, hεδ, B, hB⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ,
    (pmPowerDampedFermiSource_memLp_and_analytic_of_centeredSawtooth_budget hε0 hB).1⟩

/-- **Cofinal Mean-Centered Gram Quadratic Bridge to `RiemannHypothesis`:**
If for every `δ > 0` there exist a damping parameter `0 < ε < δ` and a uniform bound `B` on the
Cesàro period-centered Gram quadratic form `pmPowerDampedRamanujanMeanCenteredQuadratic ε Q`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofinal_meanCenteredQuadratic_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∀ Q : ℕ,
      pmPowerDampedRamanujanMeanCenteredQuadratic ε Q ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_admission
  intro δ hδ
  obtain ⟨ε, hε0, hεδ, B, hB⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ,
    (pmPowerDampedFermiSource_memLp_and_analytic_of_meanCenteredQuadratic_budget hε0 hB).1⟩

end GaloisForLFunctions.BiScaleUncertainty

end
