import GaloisForLFunctions.BezoutValuationIncidence.TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds
import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation
import GaloisForLFunctions.BiScaleUncertainty.RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge

/-!
# Route PM Cofactor Sieve Bridge and Unified Physical–Spectral Energy Equivalence

This module completes the Post–Module 70 Wall 1 synthesis in `BezoutValuationIncidence` by
establishing the exact dictionary between the finite divisor-sieve pronic discrepancy calculus of
`BezoutValuationIncidence` and the Route PM power-damped Möbius / Ramanujan cofactor architecture
of `RHTower` and `BiScaleUncertainty`:

1. **Exact Identification of the Route PM Cofactor Divisor Weight with the Ramanujan Inverse**:
   Defining the real divisor weight
   $$\operatorname{pmCofactorDivisorWeight}(\varepsilon, Q, d)
     := \operatorname{Re}\bigl(\operatorname{pmPowerDampedRamanujanCofactor}(\varepsilon, Q + 1, d)\bigr),$$
   we prove (`pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff`) that it coincides identically
   with the finite Ramanujan multiples inverse `pmRamanujanResidueCoeff` applied to the real
   Ramanujan weights `q ↦ (pmPowerDampedRamanujanWeight ε q).re` at cutoff `Q + 1`.
   Consequently, by `selbergMultiplesCoord_ramanujan_inverse`:
   - `selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e = (pmPowerDampedRamanujanWeight ε e).re`
     for every `1 ≤ e ≤ Q + 1` (`selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem`);
   - the Selberg totient diagonal form, complete-period sieve variance, and Bézout coprime successor
     form evaluate unconditionally to diagonal sums in `((pmPowerDampedRamanujanWeight ε e).re)²`;
   - each divisor weight satisfies `|pmCofactorDivisorWeight ε Q d| ≤ d⁻ᵉ` for all `ε > 0` and
     `d ≥ 1` (`abs_pmCofactorDivisorWeight_le`).

2. **Exact Pointwise & Pronic Gram Equivalence Between BVI Discrepancy and Route PM**:
   Specializing the general BVI discrepancy functionals to `c = pmCofactorDivisorWeight ε Q` at
   level `N = Q + 1` recovers the Route PM spectral functionals identically:
   - Pointwise prefix discrepancy (`sievePrefixDiscrepancy_pmCofactorDivisorWeight_eq`):
     $$\operatorname{sievePrefixDiscrepancy}(Q + 1, M, \operatorname{pmCofactorDivisorWeight}(\varepsilon, Q))
       = \operatorname{Re}\bigl(\operatorname{pmPowerDampedRamanujanCumulativePrefix}(\varepsilon, Q, M)\bigr);$$
   - Pronic mean / von Mangoldt linear functional (`vonMangoldt_sum_pmCofactorDivisorWeight_eq`):
     $$-\sum_{e=2}^{Q+1} \Lambda(e)\,Y_{Q+1}(e)
       = \operatorname{pmPowerDampedRamanujanEnergyMean}(\varepsilon, Q);$$
   - Raw pronic Gram quadratic form (`sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq`):
     $$\operatorname{sievePronicDiscrepancyGramForm}(Q + 1, \operatorname{pmCofactorDivisorWeight}(\varepsilon, Q))
       = \operatorname{pmPowerDampedRamanujanGramQuadratic}(\varepsilon, Q);$$
   - Energy-centered pronic Gram form (`sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq`):
     $$\operatorname{sieveEnergyCenteredPronicGramForm}(Q + 1, \operatorname{pmCofactorDivisorWeight}(\varepsilon, Q))
       = \operatorname{pmPowerDampedRamanujanEnergyVariance}(\varepsilon, Q);$$
   - Mean-centered pronic Gram form (`sieveMeanCenteredPronicGramForm_pmCofactorDivisorWeight_eq`):
     $$\operatorname{sieveMeanCenteredPronicGramForm}(Q + 1, \operatorname{pmCofactorDivisorWeight}(\varepsilon, Q))
       = \operatorname{pmPowerDampedRamanujanMeanCenteredQuadratic}(\varepsilon, Q).$$

3. **Unified Physical–Spectral Route PM Synthesis (`routePM_physical_and_spectral_budget_synthesis`)**:
   Combines the physical-space interior pronic energy equivalence (`pmBezoutInteriorPronicEnergy`),
   the exact non-circular interior gradient conservation law, and the BVI-to-Route-PM spectral
   Gram criteria for $L^2(0, \infty)$ admission and Mellin half-plane analyticity of
   `pmPowerDampedFermiSource ε`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## §1. The Route PM Cofactor Divisor Weight & Exact Selberg Coordinate Inversion -/

/-- The real divisor weight on `1 ≤ d ≤ Q + 1` induced by the Route PM power-damped Ramanujan
cofactor `pmPowerDampedRamanujanCofactor ε (Q + 1) d`. -/
def pmCofactorDivisorWeight (ε : ℝ) (Q d : ℕ) : ℝ :=
  (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re

/-- **Exact Identification with `pmRamanujanResidueCoeff`**:
`pmCofactorDivisorWeight ε Q d` is literally the finite Ramanujan multiples inverse
`pmRamanujanResidueCoeff` applied to `q ↦ (pmPowerDampedRamanujanWeight ε q).re` at cutoff `Q + 1`. -/
theorem pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff (ε : ℝ) (Q d : ℕ) :
    pmCofactorDivisorWeight ε Q d =
      pmRamanujanResidueCoeff (fun q => (pmPowerDampedRamanujanWeight ε q).re) (Q + 1) d := by
  unfold pmCofactorDivisorWeight pmPowerDampedRamanujanCofactor pmRamanujanResidueCoeff
  rw [Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.mul_re]
  simp [Complex.intCast_re, Complex.intCast_im]

/-- **Pointwise Damping Bound on `pmCofactorDivisorWeight`**:
For every `ε > 0`, `Q : ℕ`, and `d > 0`, `|pmCofactorDivisorWeight ε Q d| ≤ d⁻ᵉ`. -/
theorem abs_pmCofactorDivisorWeight_le {ε : ℝ} (hε : 0 < ε) (Q : ℕ) {d : ℕ} (hd : 0 < d) :
    |pmCofactorDivisorWeight ε Q d| ≤ (d : ℝ) ^ (-ε) :=
  (Complex.abs_re_le_norm _).trans (norm_pmPowerDampedRamanujanCofactor_le hε (Q + 1) hd)

/-- **Exact Selberg Multiples Coordinate Recovery**:
Applying `selbergMultiplesCoord (Q + 1)` to `pmCofactorDivisorWeight ε Q` recovers the exact
Ramanujan weight `(pmPowerDampedRamanujanWeight ε e).re` for every `e ∈ Icc 1 (Q + 1)`, and `0`
outside `Icc 1 (Q + 1)`. -/
theorem selbergMultiplesCoord_pmCofactorDivisorWeight (ε : ℝ) (Q e : ℕ) :
    selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e =
      if e ∈ Finset.Icc 1 (Q + 1) then (pmPowerDampedRamanujanWeight ε e).re else 0 := by
  have hfun :
      pmCofactorDivisorWeight ε Q =
        pmRamanujanResidueCoeff (fun q => (pmPowerDampedRamanujanWeight ε q).re) (Q + 1) := by
    funext d
    exact pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff ε Q d
  rw [hfun, selbergMultiplesCoord_ramanujan_inverse]

/-- Within the cutoff `1 ≤ e ≤ Q + 1`, `selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e`
equals `(pmPowerDampedRamanujanWeight ε e).re`. -/
theorem selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem (ε : ℝ) {Q e : ℕ}
    (he : e ∈ Finset.Icc 1 (Q + 1)) :
    selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e =
      (pmPowerDampedRamanujanWeight ε e).re := by
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight, if_pos he]

/-- **Selberg Totient Diagonal Evaluation on `pmCofactorDivisorWeight`**:
The Selberg LCM quadratic form at cutoff `Q + 1` evaluates on `pmCofactorDivisorWeight ε Q` to the
totient-weighted sum of squares of `(pmPowerDampedRamanujanWeight ε e).re`. -/
theorem selbergTotientDiagonalForm_pmCofactorDivisorWeight (ε : ℝ) (Q : ℕ) :
    selbergTotientDiagonalForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
      ∑ e ∈ Finset.Icc 1 (Q + 1),
        (Nat.totient e : ℝ) * ((pmPowerDampedRamanujanWeight ε e).re) ^ 2 := by
  have hfun :
      pmCofactorDivisorWeight ε Q =
        pmRamanujanResidueCoeff (fun q => (pmPowerDampedRamanujanWeight ε q).re) (Q + 1) := by
    funext d
    exact pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff ε Q d
  rw [hfun, selbergForm_ramanujan_inverse]

/-- **Bézout Coprime Successor Evaluation on `pmCofactorDivisorWeight`**:
The Bézout coprime quadratic form at cutoff `Q + 1` evaluates on `pmCofactorDivisorWeight ε Q` to
the Möbius-weighted sum of squares of `(pmPowerDampedRamanujanWeight ε e).re`. -/
theorem bezoutCoprimeQuadraticForm_pmCofactorDivisorWeight (ε : ℝ) (Q : ℕ) :
    bezoutCoprimeQuadraticForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
      ∑ e ∈ Finset.Icc 1 (Q + 1),
        moebiusReal e * ((pmPowerDampedRamanujanWeight ε e).re) ^ 2 := by
  have hfun :
      pmCofactorDivisorWeight ε Q =
        pmRamanujanResidueCoeff (fun q => (pmPowerDampedRamanujanWeight ε q).re) (Q + 1) := by
    funext d
    exact pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff ε Q d
  rw [hfun, bezoutForm_ramanujan_inverse]

/-- **Complete-Period Sieve Variance Evaluation on `pmCofactorDivisorWeight`**:
The complete-period sieve variance at cutoff `Q + 1` evaluates on `pmCofactorDivisorWeight ε Q` to
`∑_{e=2}^{Q+1} φ(e) ((pmPowerDampedRamanujanWeight ε e).re)²`. -/
theorem sieveVariance_pmCofactorDivisorWeight (ε : ℝ) (Q : ℕ) :
    sieveVariance (Q + 1) (pmCofactorDivisorWeight ε Q) =
      ∑ e ∈ Finset.Icc 2 (Q + 1),
        (Nat.totient e : ℝ) * ((pmPowerDampedRamanujanWeight ε e).re) ^ 2 := by
  have hfun :
      pmCofactorDivisorWeight ε Q =
        pmRamanujanResidueCoeff (fun q => (pmPowerDampedRamanujanWeight ε q).re) (Q + 1) := by
    funext d
    exact pmCofactorDivisorWeight_eq_pmRamanujanResidueCoeff ε Q d
  rw [hfun, sieveVariance_ramanujan_inverse]

/-! ## §2. Exact Pointwise & Pronic Gram Equivalence Between BVI and Route PM -/

/-- Helper reindexing `Finset.Icc 2 (Q + 1)` to `Finset.range Q` via `p ↦ p + 2`. -/
private theorem sum_Icc_two_succ_eq_sum_range_add_two {α : Type*} [AddCommMonoid α]
    (Q : ℕ) (f : ℕ → α) :
    (∑ p ∈ Finset.Icc 2 (Q + 1), f p) = ∑ p ∈ Finset.range Q, f (p + 2) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ Q + 1 + 1),
      Finset.sum_range_succ, ih]

/-- **Exact Pointwise Prefix Discrepancy Bridge**:
For every `ε > 0` and `Q, M : ℕ`, the BVI prefix discrepancy of `pmCofactorDivisorWeight ε Q` at
level `Q + 1` and horizon `M` equals `(pmPowerDampedRamanujanCumulativePrefix ε Q M).re`. -/
theorem sievePrefixDiscrepancy_pmCofactorDivisorWeight_eq
    {ε : ℝ} (hε : 0 < ε) (Q M : ℕ) :
    sievePrefixDiscrepancy (Q + 1) M (pmCofactorDivisorWeight ε Q) =
      (pmPowerDampedRamanujanCumulativePrefix ε Q M).re := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum,
    pmPowerDampedRamanujanCumulativePrefix_re_eq_cofactor_fract hε Q M]
  rfl

/-- **Exact Von Mangoldt Linear Functional / Pronic Mean Bridge**:
For every `ε : ℝ` and `Q : ℕ`, the negative von Mangoldt functional of `pmCofactorDivisorWeight ε Q`
at cutoff `Q + 1` equals `pmPowerDampedRamanujanEnergyMean ε Q`. -/
theorem vonMangoldt_sum_pmCofactorDivisorWeight_eq (ε : ℝ) (Q : ℕ) :
    -(∑ e ∈ Finset.Icc 2 (Q + 1),
        vonMangoldt e * selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) =
      pmPowerDampedRamanujanEnergyMean ε Q := by
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  unfold pmPowerDampedRamanujanEnergyMean
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hmem : q + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]
    have := Finset.mem_range.mp hq
    omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hmem, mul_comm]

/-- Consequently, the pronic-weighted discrepancy series of `pmCofactorDivisorWeight ε Q` sums to
`pmPowerDampedRamanujanEnergyMean ε Q`. -/
theorem tsum_sievePrefixDiscrepancy_pmCofactorDivisorWeight_div_pronicSeq
    (ε : ℝ) (Q : ℕ) :
    (∑' M : ℕ,
      sievePrefixDiscrepancy (Q + 1) M (pmCofactorDivisorWeight ε Q) / (pronicSeq M : ℝ)) =
      pmPowerDampedRamanujanEnergyMean ε Q := by
  rw [tsum_sievePrefixDiscrepancy_div_pronicSeq, vonMangoldt_sum_pmCofactorDivisorWeight_eq]

/-- **Exact Raw Pronic Gram Quadratic Bridge**:
For every `ε : ℝ` and `Q : ℕ`, the BVI pronic discrepancy Gram quadratic form of
`pmCofactorDivisorWeight ε Q` at level `Q + 1` equals `pmPowerDampedRamanujanGramQuadratic ε Q`. -/
theorem sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq (ε : ℝ) (Q : ℕ) :
    sievePronicDiscrepancyGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
      pmPowerDampedRamanujanGramQuadratic ε Q := by
  unfold sievePronicDiscrepancyGramForm pmPowerDampedRamanujanGramQuadratic
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp_mem : p + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hp; omega
  have hq_mem : q + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hq; omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hp_mem,
    selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq_mem]

/-- **Exact Energy-Centered Pronic Gram Bridge**:
For every `ε > 0` and `Q : ℕ`, the BVI energy-centered pronic Gram quadratic form of
`pmCofactorDivisorWeight ε Q` at level `Q + 1` equals `pmPowerDampedRamanujanEnergyVariance ε Q`. -/
theorem sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
      pmPowerDampedRamanujanEnergyVariance ε Q := by
  rw [pmPowerDampedRamanujanEnergyVariance_eq_centeredGram_quadratic hε Q]
  unfold sieveEnergyCenteredPronicGramForm
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp_mem : p + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hp; omega
  have hq_mem : q + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hq; omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hp_mem,
    selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq_mem]

/-- **Exact Mean-Centered Pronic Gram Bridge**:
For every `ε : ℝ` and `Q : ℕ`, the BVI mean-centered pronic Gram quadratic form of
`pmCofactorDivisorWeight ε Q` at level `Q + 1` equals
`pmPowerDampedRamanujanMeanCenteredQuadratic ε Q`. -/
theorem sieveMeanCenteredPronicGramForm_pmCofactorDivisorWeight_eq (ε : ℝ) (Q : ℕ) :
    sieveMeanCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
      pmPowerDampedRamanujanMeanCenteredQuadratic ε Q := by
  unfold sieveMeanCenteredPronicGramForm pmPowerDampedRamanujanMeanCenteredQuadratic
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp_mem : p + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hp; omega
  have hq_mem : q + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hq; omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hp_mem,
    selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq_mem]

/-- **Exact Centering Discrepancy Linear Functional Bridge**:
For every `ε : ℝ` and `Q : ℕ`, the BVI centering-discrepancy sum on `pmCofactorDivisorWeight ε Q`
equals `pmPowerDampedRamanujanDiscrepancySum ε Q`. -/
theorem sieveCenteringDiscrepancy_sum_pmCofactorDivisorWeight_eq (ε : ℝ) (Q : ℕ) :
    (∑ e ∈ Finset.Icc 2 (Q + 1),
        sieveCenteringDiscrepancy e *
          selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) =
      pmPowerDampedRamanujanDiscrepancySum ε Q := by
  rw [sum_Icc_two_succ_eq_sum_range_add_two]
  unfold pmPowerDampedRamanujanDiscrepancySum
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq_mem : q + 2 ∈ Finset.Icc 1 (Q + 1) := by
    rw [Finset.mem_Icc]; have := Finset.mem_range.mp hq; omega
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq_mem]
  unfold sieveCenteringDiscrepancy ramanujanCenteringDiscrepancy
  ring

/-! ## §3. BVI Spectral Criteria for `L²(0, ∞)` Admission & Unified Physical–Spectral Synthesis -/

/-- **BVI Energy-Centered Pronic Gram Criterion for `L²(0, ∞)` Admission & Mellin Analyticity**:
For any `ε > 0`, if `sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B`
for all `Q : ℕ`, then `pmPowerDampedFermiSource ε ∈ L²(0, ∞)` and its Mellin transform is analytic
on `{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget
    {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ,
      sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  have hvar : ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B := by
    intro Q
    rw [← sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq hε Q]
    exact hB Q
  have hm := pmPowerDampedFermiSource_memLp_of_ramanujan_variance hε hvar
  exact ⟨hm, analyticOnNhd_mellin_pmPowerDampedFermiSource ε hm⟩

/-- **BVI Mean-Centered Pronic Gram Criterion for `L²(0, ∞)` Admission & Mellin Analyticity**:
For any `ε > 0`, if `sieveMeanCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B`
for all `Q : ℕ`, then `pmPowerDampedFermiSource ε ∈ L²(0, ∞)` and its Mellin transform is analytic
on `{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_sieveMeanCenteredPronicGramForm_budget
    {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ,
      sieveMeanCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  refine pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget
    (B := B) hε fun Q => ?_
  exact (sieveEnergyCenteredPronicGramForm_le_meanCentered
    (Q + 1) (pmCofactorDivisorWeight ε Q)).trans (hB Q)

/-- **BVI Raw Pronic Discrepancy Gram Criterion for `L²(0, ∞)` Admission & Mellin Analyticity**:
For any `ε > 0`, if `sievePronicDiscrepancyGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B`
for all `Q : ℕ`, then `pmPowerDampedFermiSource ε ∈ L²(0, ∞)` and its Mellin transform is analytic
on `{s : ℂ | 1 / 2 < s.re}`. -/
theorem pmPowerDampedFermiSource_memLp_and_analytic_of_sievePronicDiscrepancyGramForm_budget
    {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ Q : ℕ,
      sievePronicDiscrepancyGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) ≤ B) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} := by
  refine pmPowerDampedFermiSource_memLp_and_analytic_of_sieveEnergyCenteredPronicGramForm_budget
    (B := B) hε fun Q => ?_
  have hdecomp := sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered
    (Q + 1) (pmCofactorDivisorWeight ε Q)
  have hsq : 0 ≤ (∑ e ∈ Finset.Icc 2 (Q + 1),
      vonMangoldt e * selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) e) ^ (2 : ℕ) :=
    sq_nonneg _
  linarith [hB Q]

/-- **Unified Physical–Spectral Route PM Synthesis (`routePM_physical_and_spectral_budget_synthesis`)**:
Packages the four overarching bridges established across Modules 66–74:
1. **Physical-Space Two-Sided Interior Pronic Energy Sandwich**:
   For every `ε ≥ 0` and horizon `T`, `pmPowerDampedDivisorDiscreteEnergy ε T` and
   `pmBezoutInteriorPronicEnergy ε T` control each other within a factor of `2` and an additive
   `1 / 2`.
2. **Non-Circular Interior Gradient Conservation Law**:
   For every `ε > 0`, `(pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) / log T`
   converges unconditionally to `2 * pmInteriorLogCounterterm ε`.
3. **Exact BVI-to-Route-PM Spectral Gram Hierarchy**:
   For every `ε > 0` and `Q : ℕ`, the BVI energy-centered, mean-centered, and raw pronic Gram
   forms of `pmCofactorDivisorWeight ε Q` equal `pmPowerDampedRamanujanEnergyVariance ε Q`,
   `pmPowerDampedRamanujanMeanCenteredQuadratic ε Q`, and `pmPowerDampedRamanujanGramQuadratic ε Q`,
   with `sieveEnergyCenteredPronicGramForm ≤ sieveMeanCenteredPronicGramForm` and
   `sieveEnergyCenteredPronicGramForm ≤ sievePronicDiscrepancyGramForm`.
4. **Two-Prime Dilation Profile Identity**:
   For all primes `p, q` and `r > 1` with `¬ p ∣ r` and `¬ q ∣ r`,
   `G(pr, qr) + G(pr, r) + G(qr, r) + G(r, r) = √p √q pmRamanujanDilationProfile r hr (p / q)`. -/
theorem routePM_physical_and_spectral_budget_synthesis :
    (∀ {ε : ℝ}, 0 ≤ ε → ∀ T : ℕ,
      pmPowerDampedDivisorDiscreteEnergy ε T ≤ 2 * pmBezoutInteriorPronicEnergy ε T + 1 / 2 ∧
      pmBezoutInteriorPronicEnergy ε T ≤ 2 * pmPowerDampedDivisorDiscreteEnergy ε T + 1 / 2) ∧
    (∀ {ε : ℝ}, 0 < ε →
      Tendsto (fun T : ℕ =>
        (pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) / Real.log T)
        atTop (𝓝 (2 * pmInteriorLogCounterterm ε))) ∧
    (∀ {ε : ℝ}, 0 < ε → ∀ Q : ℕ,
      sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
        pmPowerDampedRamanujanEnergyVariance ε Q ∧
      sieveMeanCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
        pmPowerDampedRamanujanMeanCenteredQuadratic ε Q ∧
      sievePronicDiscrepancyGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
        pmPowerDampedRamanujanGramQuadratic ε Q) ∧
    (∀ {p q r : ℕ}, p.Prime → q.Prime → ∀ (hr : 1 < r),
      ¬ p ∣ r → ¬ q ∣ r →
      pmRamanujanPrimitiveGram (p * r) (q * r) +
          pmRamanujanPrimitiveGram (p * r) r +
          pmRamanujanPrimitiveGram (q * r) r +
          pmRamanujanPrimitiveGram r r =
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          pmRamanujanDilationProfile r hr ((p : ℝ) / q)) := by
  refine ⟨fun hε T =>
      ⟨pmPowerDampedDivisorDiscreteEnergy_le_two_mul_interiorPronic_add_half hε T,
        pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half hε T⟩,
    fun hε => tendsto_pmBezoutInteriorGradient_add_two_mul_localImpulse_div_log hε,
    fun {ε} hε Q =>
      ⟨sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq hε Q,
        sieveMeanCenteredPronicGramForm_pmCofactorDivisorWeight_eq ε Q,
        sievePronicDiscrepancyGramForm_pmCofactorDivisorWeight_eq ε Q⟩,
    fun hp hq hr hpr hqr =>
      pmRamanujanPrimitiveGram_two_prime_mul_eq_dilationProfile hp hq hr hpr hqr⟩

end GaloisForLFunctions.BezoutValuationIncidence
