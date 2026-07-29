import GaloisForLFunctions.HTGeometry.NormalizedMomentQuantumVariance
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail
import GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelRayleighRitz

/-!
# Theta-cusp ratio gates as thermal susceptibilities

The two live theta-cusp moment-ratio hypotheses are exactly a lower and an upper bound on the
static susceptibility of `X` in two adjacent size-biased moment states.  This is the equilibrium
fluctuation--response coordinate: susceptibility is variance of the observable coupled to the
external field.

For the positive theta source, write `m_j = thetaCuspRawEvenMoment j`.  The state at level `k`
has moments `m_(k+n) / m_k`.  Its mean and susceptibility are

`mu_k = m_(k+1) / m_k`,
`chi_k = m_(k+2) / m_k - mu_k^2`.

The existing raw inequalities become exactly

`5 mu_1^2 <= 9 chi_1`,
`16 chi_0 <= 29 mu_0^2`.

This exposes the remaining analytic problem as a two-sided coefficient-of-variation window and
lets Poincare/Brascamp--Lieb, Ward, or linear-response estimates target the quantities consumed by
the first nonconstant prime--Gamma Hankel block directly.

Information-theoretically, the next size-biased state has likelihood ratio `X / mu_k` relative to
the current state.  Its Pearson chi-square divergence is therefore `chi_k / mu_k^2`.  The two
source gates are equivalently the dimensionless window `5/9 <= D_1` and `D_0 <= 29/16`, and the
same value is the pure-state quantum Fisher information divided by `4 * mu_k^2`.

Physics provenance: fluctuation--response relations originate with Callen--Welton, Physical
Review 83 (1951), 34--40, DOI 10.1103/PhysRev.83.34, and Kubo, Journal of the Physical Society of
Japan 12 (1957), 570--586, DOI 10.1143/JPSJ.12.570.  The variance inequality for log-concave
Gibbs measures was established by Brascamp--Lieb, Journal of Functional Analysis 22 (1976),
366--389, DOI 10.1016/0022-1236(76)90004-5.  No such analytic inequality is assumed here: only
the exact value-coordinate change is formalized.
-/

open Polynomial MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### Positive atom masses -/

/-- Every positive-index theta atom is pointwise strictly positive on the open half-line. -/
theorem thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspSourceTerm x n := by
  rw [thetaCuspSourceTerm]
  apply mul_pos (Real.exp_pos _)
  apply thetaCuspSeed_pos
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
  have ht : 1 < (n : ℝ) * Real.exp x := by
    nlinarith [Real.exp_pos x]
  have ht2 : 1 < ((n : ℝ) * Real.exp x) ^ 2 := by nlinarith
  nlinarith [Real.pi_gt_three, Real.pi_pos,
    mul_pos (sub_pos.mpr ht2) (show 0 < 2 * Real.pi by positivity)]

/-- Every even moment of every positive-index theta atom has strictly positive mass. -/
theorem thetaCuspAtomRawEvenMoment_pos_of_nat_pos
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspAtomRawEvenMoment j n := by
  rw [thetaCuspAtomRawEvenMoment]
  apply mul_pos (by norm_num)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x n
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using integrableOn_pow_mul_thetaCuspSourceTerm j n
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _)
      (thetaCuspSourceTerm_nonneg_of_pos hx n)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change 1 ^ (2 * j) * thetaCuspSourceTerm 1 n ≠ 0
  simpa using (thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (x := 1) (by norm_num) hn).ne'

/-- Removing the first atom leaves strictly positive mass at every moment order; the second atom
already witnesses strictness. -/
theorem thetaCuspHigherAtomRawEvenMoment_pos (j : ℕ) :
    0 < thetaCuspHigherAtomRawEvenMoment j := by
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * (thetaCuspFullSource x - thetaCuspSourceTerm x 1)
  let ffull : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspFullSource x
  let fone : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x 1
  have hfull : IntegrableOn ffull (Ioi 0) := by
    simpa only [ffull] using integrableOn_thetaCuspRawMoment (2 * j)
  have hone : IntegrableOn fone (Ioi 0) := by
    simpa only [fone] using integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hfint : IntegrableOn f (Ioi 0) := by
    have hsub := hfull.sub hone
    apply hsub.congr
    filter_upwards [] with x
    simp only [f, ffull, fone, Pi.sub_apply]
    ring
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs := summable_thetaCuspSourceTerm x
    have honeLe : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
      rw [thetaCuspFullSource]
      exact hs.le_tsum 1 (fun n _ => thetaCuspSourceTerm_nonneg_of_pos hx n)
    exact mul_nonneg (pow_nonneg hx.le _) (sub_nonneg.mpr honeLe)
  have hfpos : 0 < ∫ x : ℝ in Ioi 0, f x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
    have hfcont : Continuous f := by
      dsimp only [f]
      exact (continuous_id.pow _).mul
        (contDiff_thetaCuspFullSource.continuous.sub (by
          unfold thetaCuspSourceTerm thetaCuspSeed
          fun_prop))
    have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
      hfcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    have hs := summable_thetaCuspSourceTerm (1 : ℝ)
    have hpair :
        thetaCuspSourceTerm 1 1 + thetaCuspSourceTerm 1 2 ≤
          thetaCuspFullSource 1 := by
      rw [thetaCuspFullSource]
      have hsum := hs.sum_le_tsum ({1, 2} : Finset ℕ)
        (fun n _ => thetaCuspSourceTerm_nonneg_of_pos (by norm_num) n)
      norm_num at hsum ⊢
      exact hsum
    have htwo : 0 < thetaCuspSourceTerm 1 2 :=
      thetaCuspSourceTerm_pos_of_pos_of_nat_pos (by norm_num) (by norm_num)
    have hdiff : 0 < thetaCuspFullSource 1 - thetaCuspSourceTerm 1 1 := by
      linarith
    change 1 ^ (2 * j) *
        (thetaCuspFullSource 1 - thetaCuspSourceTerm 1 1) ≠ 0
    simpa using hdiff.ne'
  have heq : thetaCuspHigherAtomRawEvenMoment j =
      2 * ∫ x : ℝ in Ioi 0, f x := by
    rw [thetaCuspHigherAtomRawEvenMoment, thetaCuspRawEvenMoment,
      thetaCuspAtomRawEvenMoment]
    rw [show (fun x : ℝ =>
        x ^ (2 * j) * (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) =
      ffull - fone by
        funext x
        simp only [ffull, fone, Pi.sub_apply]
        ring]
    change
      2 * (∫ x : ℝ in Ioi 0, ffull x) -
          2 * (∫ x : ℝ in Ioi 0, fone x) =
        2 * ∫ x : ℝ in Ioi 0, ffull x - fone x
    rw [integral_sub hfull hone]
    ring
  rw [heq]
  exact mul_pos (by norm_num) hfpos

/-- Mean of the energy coordinate in the `k`-th size-biased theta-cusp moment state. -/
def thetaCuspSizeBiasedMean (k : ℕ) : ℝ :=
  HTGeometry.momentNormalizedExpectation
    (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k) X

/-- Static susceptibility of the energy coordinate in the `k`-th size-biased theta-cusp state. -/
def thetaCuspSizeBiasedSusceptibility (k : ℕ) : ℝ :=
  HTGeometry.momentNormalizedVariance
    (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k) X

/-- Expectation of an arbitrary power of the energy coordinate in the `k`-th size-biased theta
state. -/
def thetaCuspSizeBiasedPowerExpectation (k n : ℕ) : ℝ :=
  HTGeometry.momentNormalizedExpectation
    (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k) (X ^ n)

/-- Selection covariance between the energy coordinate and its `n`-th power in the `k`-th
size-biased theta state. -/
def thetaCuspSizeBiasPowerCovariance (k n : ℕ) : ℝ :=
  HTGeometry.momentNormalizedCovariance
    (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k) X (X ^ n)

/-- Size-biased moment sequence of the dominant first theta atom. -/
def thetaCuspFirstAtomSizeBiasedSequence (k : ℕ) : ℕ → ℝ :=
  HTGeometry.momentSizeBiasedSequence
    (fun j => thetaCuspAtomRawEvenMoment j 1) k

/-- Size-biased moment sequence of all theta atoms above the first. -/
def thetaCuspHigherAtomSizeBiasedSequence (k : ℕ) : ℕ → ℝ :=
  HTGeometry.momentSizeBiasedSequence thetaCuspHigherAtomRawEvenMoment k

theorem thetaCuspFirstAtomSizeBiasedSequence_zero_pos (k : ℕ) :
    0 < thetaCuspFirstAtomSizeBiasedSequence k 0 := by
  simpa [thetaCuspFirstAtomSizeBiasedSequence,
    HTGeometry.momentSizeBiasedSequence] using
      thetaCuspAtomRawEvenMoment_pos_of_nat_pos k (n := 1) (by norm_num)

theorem thetaCuspHigherAtomSizeBiasedSequence_zero_pos (k : ℕ) :
    0 < thetaCuspHigherAtomSizeBiasedSequence k 0 := by
  simpa [thetaCuspHigherAtomSizeBiasedSequence,
    HTGeometry.momentSizeBiasedSequence] using
      thetaCuspHigherAtomRawEvenMoment_pos k

/-- The complete size-biased theta state is exactly the mixture of the dominant atom and the
higher-atom tail. -/
theorem thetaCuspSizeBiasedSequence_eq_first_add_higher (k : ℕ) :
    HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k =
      HTGeometry.momentSequenceSum
        (thetaCuspFirstAtomSizeBiasedSequence k)
        (thetaCuspHigherAtomSizeBiasedSequence k) := by
  funext n
  simp only [HTGeometry.momentSizeBiasedSequence, HTGeometry.momentSequenceSum,
    thetaCuspFirstAtomSizeBiasedSequence, thetaCuspHigherAtomSizeBiasedSequence]
  exact thetaCuspRawEvenMoment_eq_one_add_higher (k + n)

/-- **Theta law of total susceptibility.**  The complete theta fluctuation is the weighted
within-first-atom fluctuation, the weighted higher-tail fluctuation, and the nonnegative squared
mismatch of their means. -/
theorem thetaCuspSizeBiasedSusceptibility_eq_within_add_between (k : ℕ) :
    thetaCuspSizeBiasedSusceptibility k =
      thetaCuspFirstAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedVariance
            (thetaCuspFirstAtomSizeBiasedSequence k) X +
        thetaCuspHigherAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedVariance
            (thetaCuspHigherAtomSizeBiasedSequence k) X +
        (thetaCuspFirstAtomSizeBiasedSequence k 0 *
            thetaCuspHigherAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) ^ 2) *
          (HTGeometry.momentNormalizedExpectation
              (thetaCuspFirstAtomSizeBiasedSequence k) X -
            HTGeometry.momentNormalizedExpectation
              (thetaCuspHigherAtomSizeBiasedSequence k) X) ^ 2 := by
  rw [thetaCuspSizeBiasedSusceptibility,
    thetaCuspSizeBiasedSequence_eq_first_add_higher]
  exact HTGeometry.momentNormalizedVariance_sequenceSum
    (thetaCuspFirstAtomSizeBiasedSequence k)
    (thetaCuspHigherAtomSizeBiasedSequence k)
    (thetaCuspFirstAtomSizeBiasedSequence_zero_pos k).ne'
    (thetaCuspHigherAtomSizeBiasedSequence_zero_pos k).ne'
    (add_pos (thetaCuspFirstAtomSizeBiasedSequence_zero_pos k)
      (thetaCuspHigherAtomSizeBiasedSequence_zero_pos k)).ne' X

theorem thetaCuspSizeBiasedMean_eq_momentRatio (k : ℕ) :
    thetaCuspSizeBiasedMean k =
      thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k := by
  exact HTGeometry.momentNormalizedExpectation_X_sizeBiased
    thetaCuspRawEvenMoment k

/-- Every theta power expectation is the corresponding shifted completed-moment ratio. -/
theorem thetaCuspSizeBiasedPowerExpectation_eq_momentRatio (k n : ℕ) :
    thetaCuspSizeBiasedPowerExpectation k n =
      thetaCuspRawEvenMoment (k + n) / thetaCuspRawEvenMoment k := by
  exact HTGeometry.momentNormalizedExpectation_X_pow_sizeBiased
    thetaCuspRawEvenMoment k n

/-- The first power expectation is the existing size-biased mean. -/
theorem thetaCuspSizeBiasedPowerExpectation_one_eq_mean (k : ℕ) :
    thetaCuspSizeBiasedPowerExpectation k 1 = thetaCuspSizeBiasedMean k := by
  simp only [thetaCuspSizeBiasedPowerExpectation, thetaCuspSizeBiasedMean, pow_one]

theorem thetaCuspSizeBiasedSusceptibility_eq_momentRatios (k : ℕ) :
    thetaCuspSizeBiasedSusceptibility k =
      thetaCuspRawEvenMoment (k + 2) / thetaCuspRawEvenMoment k -
        (thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k) ^ 2 := by
  exact HTGeometry.momentNormalizedVariance_X_sizeBiased
    thetaCuspRawEvenMoment k

/-- Pearson chi-square information from the next theta size bias to the current one. -/
def thetaCuspSizeBiasPearsonChiSq (k : ℕ) : ℝ :=
  HTGeometry.momentSizeBiasPearsonChiSq thetaCuspRawEvenMoment k

/-- The theta Pearson information is the dimensionless susceptibility-to-signal ratio. -/
theorem thetaCuspSizeBiasPearsonChiSq_eq_susceptibility_div_mean_sq (k : ℕ) :
    thetaCuspSizeBiasPearsonChiSq k =
      thetaCuspSizeBiasedSusceptibility k /
        thetaCuspSizeBiasedMean k ^ 2 := by
  rfl

theorem thetaCuspSizeBiasedMean_pos (k : ℕ) :
    0 < thetaCuspSizeBiasedMean k := by
  rw [thetaCuspSizeBiasedMean_eq_momentRatio]
  exact div_pos (thetaCuspRawEvenMoment_pos (k + 1))
    (thetaCuspRawEvenMoment_pos k)

/-- All separated `2 x 2` theta moment minors are nonnegative.  This extends adjacent
log-convexity by iterating the already-proved monotonicity of consecutive moment ratios. -/
theorem thetaCuspRawEvenMoment_cross_le (k n : ℕ) :
    thetaCuspRawEvenMoment (k + 1) * thetaCuspRawEvenMoment (k + n) ≤
      thetaCuspRawEvenMoment k * thetaCuspRawEvenMoment (k + n + 1) := by
  have hratio :
      thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k ≤
        thetaCuspRawEvenMoment (k + n + 1) /
          thetaCuspRawEvenMoment (k + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        exact ih.trans (by
          convert thetaCuspRawEvenMoment_ratio_mono (k + n) using 1 <;> omega)
  rw [div_le_div_iff₀ (thetaCuspRawEvenMoment_pos k)
    (thetaCuspRawEvenMoment_pos (k + n))] at hratio
  nlinarith

/-- Existing theta log-convexity discharges every Price selection-covariance sign, not merely the
variance case `n=1`. -/
theorem thetaCuspSizeBiasPowerCovariance_nonneg (k n : ℕ) :
    0 ≤ thetaCuspSizeBiasPowerCovariance k n := by
  apply (HTGeometry.momentNormalizedCovariance_X_X_pow_sizeBiased_nonneg_iff_crossHankel
    thetaCuspRawEvenMoment k n (thetaCuspRawEvenMoment_pos k)).2
  exact thetaCuspRawEvenMoment_cross_le k n

/-- **Theta Robertson--Price response law.**  The covariance is the current energy mean times the
increase of every power expectation under one further size bias. -/
theorem thetaCuspSizeBiasPowerCovariance_eq_mean_mul_response (k n : ℕ) :
    thetaCuspSizeBiasPowerCovariance k n =
      thetaCuspSizeBiasedMean k *
        (thetaCuspSizeBiasedPowerExpectation (k + 1) n -
          thetaCuspSizeBiasedPowerExpectation k n) := by
  exact HTGeometry.momentNormalizedCovariance_X_X_pow_sizeBiased_eq_mean_mul_response
    thetaCuspRawEvenMoment k n (thetaCuspRawEvenMoment_pos k).ne'
      (thetaCuspRawEvenMoment_pos (k + 1)).ne'

/-- The first Price-response covariance is exactly the existing static susceptibility. -/
theorem thetaCuspSizeBiasPowerCovariance_one_eq_susceptibility (k : ℕ) :
    thetaCuspSizeBiasPowerCovariance k 1 =
      thetaCuspSizeBiasedSusceptibility k := by
  rw [thetaCuspSizeBiasPowerCovariance, thetaCuspSizeBiasedSusceptibility, pow_one,
    HTGeometry.momentNormalizedCovariance_self]

/-- **Atomwise law of total Price response.**  Every theta power-response covariance splits into
the within-first-atom response, the within-higher-tail response, and one polarized between-atom
term.  For `n=1` this reduces to the existing law of total susceptibility; for higher `n` it
isolates exactly which atom ordering can strengthen the global response sign. -/
theorem thetaCuspSizeBiasPowerCovariance_eq_within_add_between (k n : ℕ) :
    thetaCuspSizeBiasPowerCovariance k n =
      thetaCuspFirstAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedCovariance
            (thetaCuspFirstAtomSizeBiasedSequence k) X (X ^ n) +
        thetaCuspHigherAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) *
          HTGeometry.momentNormalizedCovariance
            (thetaCuspHigherAtomSizeBiasedSequence k) X (X ^ n) +
        (thetaCuspFirstAtomSizeBiasedSequence k 0 *
            thetaCuspHigherAtomSizeBiasedSequence k 0 /
          (thetaCuspFirstAtomSizeBiasedSequence k 0 +
            thetaCuspHigherAtomSizeBiasedSequence k 0) ^ 2) *
          (HTGeometry.momentNormalizedExpectation
              (thetaCuspFirstAtomSizeBiasedSequence k) X -
            HTGeometry.momentNormalizedExpectation
              (thetaCuspHigherAtomSizeBiasedSequence k) X) *
          (HTGeometry.momentNormalizedExpectation
              (thetaCuspFirstAtomSizeBiasedSequence k) (X ^ n) -
            HTGeometry.momentNormalizedExpectation
              (thetaCuspHigherAtomSizeBiasedSequence k) (X ^ n)) := by
  rw [thetaCuspSizeBiasPowerCovariance,
    thetaCuspSizeBiasedSequence_eq_first_add_higher]
  exact HTGeometry.momentNormalizedCovariance_sequenceSum
    (thetaCuspFirstAtomSizeBiasedSequence k)
    (thetaCuspHigherAtomSizeBiasedSequence k)
    (thetaCuspFirstAtomSizeBiasedSequence_zero_pos k).ne'
    (thetaCuspHigherAtomSizeBiasedSequence_zero_pos k).ne'
    (add_pos (thetaCuspFirstAtomSizeBiasedSequence_zero_pos k)
      (thetaCuspHigherAtomSizeBiasedSequence_zero_pos k)).ne' X (X ^ n)

/-- Every power expectation increases under successive theta size bias.  The proof consumes the
general Price equation together with the existing all-order theta log-convexity theorem. -/
theorem thetaCuspSizeBiasedPowerExpectation_le_next (k n : ℕ) :
    thetaCuspSizeBiasedPowerExpectation k n ≤
      thetaCuspSizeBiasedPowerExpectation (k + 1) n := by
  rw [← sub_nonneg]
  change 0 ≤
    HTGeometry.momentNormalizedExpectation
        (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment (k + 1)) (X ^ n) -
      HTGeometry.momentNormalizedExpectation
        (HTGeometry.momentSizeBiasedSequence thetaCuspRawEvenMoment k) (X ^ n)
  rw [HTGeometry.momentSizeBiasPriceEquation_X_pow
    thetaCuspRawEvenMoment k n (thetaCuspRawEvenMoment_pos k).ne'
      (thetaCuspRawEvenMoment_pos (k + 1)).ne']
  change 0 ≤ thetaCuspSizeBiasPowerCovariance k n / thetaCuspSizeBiasedMean k
  exact div_nonneg (thetaCuspSizeBiasPowerCovariance_nonneg k n)
    (thetaCuspSizeBiasedMean_pos k).le

/-- The size-biased theta means form a nondecreasing sequence. -/
theorem thetaCuspSizeBiasedMean_le_next (k : ℕ) :
    thetaCuspSizeBiasedMean k ≤ thetaCuspSizeBiasedMean (k + 1) := by
  rw [← thetaCuspSizeBiasedPowerExpectation_one_eq_mean k,
    ← thetaCuspSizeBiasedPowerExpectation_one_eq_mean (k + 1)]
  exact thetaCuspSizeBiasedPowerExpectation_le_next k 1

/-- Existing all-order theta moment log-convexity discharges nonnegativity of every successive
size-bias Pearson information value. -/
theorem thetaCuspSizeBiasPearsonChiSq_nonneg (k : ℕ) :
    0 ≤ thetaCuspSizeBiasPearsonChiSq k := by
  apply (HTGeometry.momentSizeBiasPearsonChiSq_nonneg_iff_adjacentHankel
    thetaCuspRawEvenMoment k (thetaCuspRawEvenMoment_pos k)
      (thetaCuspRawEvenMoment_pos (k + 1))).2
  have h := thetaCuspRawEvenMoment_sq_le_adjacent (k + 1) (by omega)
  rw [show k + 1 - 1 = k by omega,
    show k + 1 + 1 = k + 2 by omega] at h
  exact h

/-- Adjacent theta moment-ratio curvature is exactly `1 +` the Pearson information. -/
theorem thetaCuspSizeBiasPearsonChiSq_add_one_eq_adjacentRatioQuotient (k : ℕ) :
    thetaCuspSizeBiasPearsonChiSq k + 1 =
      (thetaCuspRawEvenMoment (k + 2) / thetaCuspRawEvenMoment (k + 1)) /
        (thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k) := by
  exact HTGeometry.momentSizeBiasPearsonChiSq_add_one_eq_adjacentRatioQuotient
    thetaCuspRawEvenMoment k (thetaCuspRawEvenMoment_pos k).ne'
      (thetaCuspRawEvenMoment_pos (k + 1)).ne'

/-- Theta fluctuation is exactly the current size-biased mean times its increase after one more
size bias. -/
theorem thetaCuspSizeBiasedSusceptibility_eq_mean_mul_next_sub_mean (k : ℕ) :
    thetaCuspSizeBiasedSusceptibility k =
      thetaCuspSizeBiasedMean k *
        (thetaCuspSizeBiasedMean (k + 1) - thetaCuspSizeBiasedMean k) := by
  exact HTGeometry.momentNormalizedVariance_X_sizeBiased_eq_mean_mul_next_sub_mean
    thetaCuspRawEvenMoment k (thetaCuspRawEvenMoment_pos k).ne'
      (thetaCuspRawEvenMoment_pos (k + 1)).ne'

/-- The theta size-bias pair saturates the Hammersley--Chapman--Robbins chi-square bound for its
energy coordinate. -/
theorem thetaCuspSizeBiasPearsonChiSq_hcr_saturation (k : ℕ) :
    (thetaCuspSizeBiasedMean (k + 1) - thetaCuspSizeBiasedMean k) ^ 2 =
      thetaCuspSizeBiasedSusceptibility k *
        thetaCuspSizeBiasPearsonChiSq k := by
  exact HTGeometry.momentSizeBiasPearsonChiSq_hcr_saturation
    thetaCuspRawEvenMoment k (thetaCuspRawEvenMoment_pos k).ne'
      (thetaCuspRawEvenMoment_pos (k + 1)).ne'

/-- The strengthened upper adjacent-ratio hypothesis is exactly a lower susceptibility bound in
the once-size-biased theta state. -/
theorem thetaCuspUpperAdjacentRatioSeparation_iff_susceptibility_lower :
    ThetaCuspUpperAdjacentRatioSeparation ↔
      5 * thetaCuspSizeBiasedMean 1 ^ 2 ≤
        9 * thetaCuspSizeBiasedSusceptibility 1 := by
  rw [ThetaCuspUpperAdjacentRatioSeparation,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedSusceptibility_eq_momentRatios]
  norm_num only [Nat.reduceAdd]
  have h1 := thetaCuspRawEvenMoment_pos 1
  constructor
  · intro h
    field_simp [h1.ne']
    nlinarith
  · intro h
    field_simp [h1.ne'] at h
    nlinarith

/-- The relaxed fourth-moment hypothesis is exactly an upper susceptibility bound in the
unbiased theta state. -/
theorem thetaCuspRelaxedFourthMomentConcentration_iff_susceptibility_upper :
    ThetaCuspRelaxedFourthMomentConcentration ↔
      16 * thetaCuspSizeBiasedSusceptibility 0 ≤
        29 * thetaCuspSizeBiasedMean 0 ^ 2 := by
  rw [ThetaCuspRelaxedFourthMomentConcentration,
    thetaCuspSizeBiasedMean_eq_momentRatio,
    thetaCuspSizeBiasedSusceptibility_eq_momentRatios]
  norm_num only [Nat.reduceAdd]
  have h0 := thetaCuspRawEvenMoment_pos 0
  constructor
  · intro h
    field_simp [h0.ne']
    nlinarith
  · intro h
    field_simp [h0.ne'] at h
    nlinarith

/-- The complete fluctuation-response window replacing the two raw theta moment ratios. -/
def ThetaCuspSizeBiasedSusceptibilityWindow : Prop :=
  5 * thetaCuspSizeBiasedMean 1 ^ 2 ≤
      9 * thetaCuspSizeBiasedSusceptibility 1 ∧
    16 * thetaCuspSizeBiasedSusceptibility 0 ≤
      29 * thetaCuspSizeBiasedMean 0 ^ 2

theorem thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit :
    ThetaCuspSizeBiasedSusceptibilityWindow ↔
      ThetaCuspUpperAdjacentRatioSeparation ∧
        ThetaCuspRelaxedFourthMomentConcentration := by
  rw [ThetaCuspSizeBiasedSusceptibilityWindow,
    ← thetaCuspUpperAdjacentRatioSeparation_iff_susceptibility_lower,
    ← thetaCuspRelaxedFourthMomentConcentration_iff_susceptibility_upper]

/-- Dimensionless information form of the two low theta gates.  Each term is a literal Pearson
chi-square divergence for the positive theta representing measure. -/
def ThetaCuspSizeBiasPearsonWindow : Prop :=
  (5 / 9 : ℝ) ≤ thetaCuspSizeBiasPearsonChiSq 1 ∧
    thetaCuspSizeBiasPearsonChiSq 0 ≤ (29 / 16 : ℝ)

theorem thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow :
    ThetaCuspSizeBiasPearsonWindow ↔
      ThetaCuspSizeBiasedSusceptibilityWindow := by
  rw [ThetaCuspSizeBiasPearsonWindow,
    ThetaCuspSizeBiasedSusceptibilityWindow,
    thetaCuspSizeBiasPearsonChiSq_eq_susceptibility_div_mean_sq,
    thetaCuspSizeBiasPearsonChiSq_eq_susceptibility_div_mean_sq]
  have hsq1 : 0 < thetaCuspSizeBiasedMean 1 ^ 2 :=
    sq_pos_of_pos (thetaCuspSizeBiasedMean_pos 1)
  have hsq0 : 0 < thetaCuspSizeBiasedMean 0 ^ 2 :=
    sq_pos_of_pos (thetaCuspSizeBiasedMean_pos 0)
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · have hmul := (le_div_iff₀ hsq1).mp hlower
      nlinarith
    · have hmul := (div_le_iff₀ hsq0).mp hupper
      nlinarith
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply (le_div_iff₀ hsq1).2
      nlinarith
    · apply (div_le_iff₀ hsq0).2
      nlinarith

theorem thetaCuspSizeBiasPearsonWindow_iff_ratioSplit :
    ThetaCuspSizeBiasPearsonWindow ↔
      ThetaCuspUpperAdjacentRatioSeparation ∧
        ThetaCuspRelaxedFourthMomentConcentration := by
  rw [thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow,
    thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit]

/-- Linear size-bias-lift form of the two low theta gates.  The quadratic fluctuation products
have disappeared: only three successive normalized means remain. -/
def ThetaCuspSizeBiasMeanLiftWindow : Prop :=
  14 * thetaCuspSizeBiasedMean 1 ≤ 9 * thetaCuspSizeBiasedMean 2 ∧
    16 * thetaCuspSizeBiasedMean 1 ≤ 45 * thetaCuspSizeBiasedMean 0

theorem thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow :
    ThetaCuspSizeBiasMeanLiftWindow ↔
      ThetaCuspSizeBiasedSusceptibilityWindow := by
  rw [ThetaCuspSizeBiasMeanLiftWindow,
    ThetaCuspSizeBiasedSusceptibilityWindow,
    thetaCuspSizeBiasedSusceptibility_eq_mean_mul_next_sub_mean 1,
    thetaCuspSizeBiasedSusceptibility_eq_mean_mul_next_sub_mean 0]
  norm_num only [Nat.reduceAdd]
  have hmu1 := thetaCuspSizeBiasedMean_pos 1
  have hmu0 := thetaCuspSizeBiasedMean_pos 0
  constructor
  · rintro ⟨hupper, hrelaxed⟩
    constructor
    · have hprod :
          thetaCuspSizeBiasedMean 1 *
              (14 * thetaCuspSizeBiasedMean 1 -
                9 * thetaCuspSizeBiasedMean 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hmu1.le (by linarith)
      nlinarith
    · have hprod :
          thetaCuspSizeBiasedMean 0 *
              (16 * thetaCuspSizeBiasedMean 1 -
                45 * thetaCuspSizeBiasedMean 0) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hmu0.le (by linarith)
      nlinarith
  · rintro ⟨hupper, hrelaxed⟩
    constructor
    · by_contra h
      have hdiff : 0 <
          14 * thetaCuspSizeBiasedMean 1 -
            9 * thetaCuspSizeBiasedMean 2 := by
        push Not at h
        linarith
      have hprod := mul_pos hmu1 hdiff
      nlinarith
    · by_contra h
      have hdiff : 0 <
          16 * thetaCuspSizeBiasedMean 1 -
            45 * thetaCuspSizeBiasedMean 0 := by
        push Not at h
        linarith
      have hprod := mul_pos hmu0 hdiff
      nlinarith

theorem thetaCuspSizeBiasMeanLiftWindow_iff_pearsonWindow :
    ThetaCuspSizeBiasMeanLiftWindow ↔
      ThetaCuspSizeBiasPearsonWindow := by
  rw [thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow,
    thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow]

theorem thetaCuspSizeBiasMeanLiftWindow_iff_ratioSplit :
    ThetaCuspSizeBiasMeanLiftWindow ↔
      ThetaCuspUpperAdjacentRatioSeparation ∧
        ThetaCuspRelaxedFourthMomentConcentration := by
  rw [thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow,
    thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit]

/-- A first-atom `k=1` radial fluctuation bound transfers to the full-source lower
susceptibility bound. -/
theorem thetaCuspSizeBiasedSusceptibility_one_lower_of_firstRadial
    (hupper :
      14 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
        9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
          thetaCuspBornWittenRadialRawMoment 2 1 1) :
    5 * thetaCuspSizeBiasedMean 1 ^ 2 ≤
      9 * thetaCuspSizeBiasedSusceptibility 1 := by
  apply thetaCuspUpperAdjacentRatioSeparation_iff_susceptibility_lower.mp
  apply thetaCuspUpperAdjacentRatioSeparation_of_first_atom
  rw [thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 1 1 1,
    thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 0 1 1,
    thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 2 1 1]
  norm_num only [Nat.reduceAdd]
  have hscaled := mul_le_mul_of_nonneg_right hupper (sq_nonneg (2 * Real.pi))
  convert hscaled using 1 <;> ring

/-- A first-atom `k=0` radial fluctuation bound transfers to the full-source upper
susceptibility bound. -/
theorem thetaCuspSizeBiasedSusceptibility_zero_upper_of_firstRadial
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    16 * thetaCuspSizeBiasedSusceptibility 0 ≤
      29 * thetaCuspSizeBiasedMean 0 ^ 2 := by
  apply thetaCuspRelaxedFourthMomentConcentration_iff_susceptibility_upper.mp
  apply thetaCuspRelaxedFourthMomentConcentration_of_first_atom
  rw [thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 0 0 1,
    thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 2 0 1,
    thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment 1 0 1]
  norm_num only [Nat.reduceAdd]
  have hscaled := mul_le_mul_of_nonneg_right hrelaxed (sq_nonneg (2 * Real.pi))
  convert hscaled using 1 <;> ring

/-- The existing two-channel Robertson/Rayleigh--Ritz certificate supplies exactly the lower
half of the full-source susceptibility window. -/
theorem thetaCuspSizeBiasedSusceptibility_one_lower_of_twoChannelRayleighRitz
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate) :
    5 * thetaCuspSizeBiasedMean 1 ^ 2 ≤
      9 * thetaCuspSizeBiasedSusceptibility 1 :=
  thetaCuspSizeBiasedSusceptibility_one_lower_of_firstRadial
    (thetaCusp_firstRadial_upper_of_twoChannelRayleighRitzCertificate hcert)

/-- The two-channel certificate and the remaining radial `k=0` upper fluctuation bound assemble
the complete full-source susceptibility window. -/
theorem thetaCuspSizeBiasedSusceptibilityWindow_of_twoChannelRayleighRitz
    (hcert : ThetaCuspFirstRadialTwoChannelRayleighRitzCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ThetaCuspSizeBiasedSusceptibilityWindow := by
  constructor
  · exact thetaCuspSizeBiasedSusceptibility_one_lower_of_twoChannelRayleighRitz hcert
  · exact thetaCuspSizeBiasedSusceptibility_zero_upper_of_firstRadial hrelaxed

/-- The susceptibility window directly discharges every real linear-polynomial prime--Gamma
Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_susceptibilityWindow
    (h : ThetaCuspSizeBiasedSusceptibilityWindow) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  obtain ⟨hupper, hrelaxed⟩ :=
    thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit.mp h
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit hupper hrelaxed

/-- Direct information-theoretic consumer for every real linear prime--Gamma Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_pearsonWindow
    (h : ThetaCuspSizeBiasPearsonWindow) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_susceptibilityWindow
    (thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow.mp h)

/-- The linear mean-lift window directly supplies every real linear prime--Gamma Hankel test. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_meanLiftWindow
    (h : ThetaCuspSizeBiasMeanLiftWindow) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_susceptibilityWindow
    (thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow.mp h)

/-- Direct RH consumer: the thermal susceptibility window supplies the omitted low block of the
existing degree-two-tail criterion. -/
theorem riemannHypothesis_of_thetaCuspSusceptibilityWindow_of_primeArchDegreeTwoTail
    (h : ThetaCuspSizeBiasedSusceptibilityWindow)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis := by
  obtain ⟨hupper, hrelaxed⟩ :=
    thetaCuspSizeBiasedSusceptibilityWindow_iff_ratioSplit.mp h
  exact riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail
    hupper hrelaxed htail

/-- Direct RH consumer for the Pearson-information window and the existing degree-two tail. -/
theorem riemannHypothesis_of_thetaCuspPearsonWindow_of_primeArchDegreeTwoTail
    (h : ThetaCuspSizeBiasPearsonWindow)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspSusceptibilityWindow_of_primeArchDegreeTwoTail
    (thetaCuspSizeBiasPearsonWindow_iff_susceptibilityWindow.mp h) htail

/-- Direct RH consumer for the linear size-bias mean-lift window. -/
theorem riemannHypothesis_of_thetaCuspMeanLiftWindow_of_primeArchDegreeTwoTail
    (h : ThetaCuspSizeBiasMeanLiftWindow)
    (htail : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_thetaCuspSusceptibilityWindow_of_primeArchDegreeTwoTail
    (thetaCuspSizeBiasMeanLiftWindow_iff_susceptibilityWindow.mp h) htail

end

end RHTower
