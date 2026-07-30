import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaCancellation
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula
import GaloisForLFunctions.RHTower.CCMDyadicSharpRectangularTransfer
import GaloisForLFunctions.RHTower.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.CCMRectangularTransverseGrowth
import GaloisForLFunctions.RHTower.CCMRectangularStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum

/-!
# Rectangular Gamma--polar source law

The complete sharp rectangular Xi-Weil value is the sum of two source-pure values: the finite
prime--polar coefficient and an absolutely convergent Gamma cancellation integral.  The latter is
uniformly bounded when the window length is fixed.  Consequently the Gamma edge can be removed
from every one-sided subpower question without changing the exponent or the eventual quantifiers.

This gives two interface-free source criteria for RH.  At any fixed positive window length, RH is
equivalent both to uniform boundedness of the finite prime--polar coefficient over all separated
apertures and to its eventual all-epsilon one-sided subpower lower bound.  The latter is also
equivalent to the same value relation for the completed critical-Mellin adjacent block.
-/

open Complex Filter MeasureTheory Set

noncomputable section

namespace RHTower

/-- **Exact rectangular Gamma--polar source law.**  The full sharp Xi-Weil value is the finite
prime--polar source plus the real Gamma cancellation correction. -/
theorem xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      ((rectangularPrimePolarSourceCoefficient L a +
        rectangularGammaPolarCorrection L a : ℝ) : ℂ) := by
  rw [xiWeilPolarization_rectangular_eq_prime_add_arch hL ha,
    rectangularPrimePolarSourceCoefficient]
  push_cast
  have hp : (((2 * rectangularEvenPolarFeature L a ^ 2 : ℝ) : ℂ)) =
      2 * (rectangularEvenPolarFeature L a : ℂ) ^ 2 := by norm_cast
  have harch :=
    normalizedRectangularBottomArchContribution_sub_two_mul_polar_sq hL ha
  rw [hp] at harch
  linear_combination harch

/-- Logarithmic sample form of the exact rectangular Gamma--polar source law. -/
theorem xiRectangularWeilLogCoefficient_re_eq_primePolarSource_add_gammaCorrection
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hLn : L ≤ Real.log n / 2) :
    (xiRectangularWeilLogCoefficient L n).re =
      rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
        rectangularGammaPolarCorrection L (Real.log n / 2) := by
  rw [xiRectangularWeilLogCoefficient]
  exact congrArg Complex.re
    (xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection hL hLn)

/-- On any admissible tail, one-sided all-epsilon subpower lower control is unchanged when the
raw Xi-Weil value is replaced by the finite prime--polar source. -/
theorem rectangularWeil_subpowerLower_iff_primePolarSource
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ (xiRectangularWeilLogCoefficient L n).re + C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
          C * (n : ℝ) ^ epsilon) := by
  let B : ℝ := rectangularGammaPolarUniformBound L
  have hB : 0 ≤ B := rectangularGammaPolarUniformBound_nonneg hL
  constructor
  · intro hq epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hq epsilon hepsilon
    refine ⟨C + B, add_nonneg hC hB, fun n hn => ?_⟩
    obtain ⟨hn1, hLn⟩ := hN n hn
    have hp : 1 ≤ (n : ℝ) ^ epsilon :=
      Real.one_le_rpow (by exact_mod_cast hn1) hepsilon.le
    have heq :=
      xiRectangularWeilLogCoefficient_re_eq_primePolarSource_add_gammaCorrection hL hLn
    have hcorr := abs_rectangularGammaPolarCorrection_le_uniformBound hL hLn
    have hupper := (abs_le.mp hcorr).2
    have hqn := htail n hn
    nlinarith [mul_le_mul_of_nonneg_left hp hB]
  · intro hs epsilon hepsilon
    obtain ⟨C, hC, htail⟩ := hs epsilon hepsilon
    refine ⟨C + B, add_nonneg hC hB, fun n hn => ?_⟩
    obtain ⟨hn1, hLn⟩ := hN n hn
    have hp : 1 ≤ (n : ℝ) ^ epsilon :=
      Real.one_le_rpow (by exact_mod_cast hn1) hepsilon.le
    have heq :=
      xiRectangularWeilLogCoefficient_re_eq_primePolarSource_add_gammaCorrection hL hLn
    have hcorr := abs_rectangularGammaPolarCorrection_le_uniformBound hL hLn
    have hlower := (abs_le.mp hcorr).1
    have hsn := htail n hn
    nlinarith [mul_le_mul_of_nonneg_left hp hB]

/-- **Prime--polar subpower RH law.**  For any fixed positive window length, RH is equivalent to
an eventual all-epsilon one-sided subpower lower bound for the literal finite prime--polar values.
There is no named proposition interface or archimedean hypothesis in the statement. -/
theorem riemannHypothesis_iff_exists_eventually_rectangularPrimePolarSource_subpowerLower
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
            C * (n : ℝ) ^ epsilon := by
  rw [riemannHypothesis_iff_exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower hL]
  constructor
  · rintro ⟨Nq, hq⟩
    obtain ⟨Na, ha⟩ := exists_xiRectangularAdmissibleCutoff L
    let N := max Nq Na
    have hNa : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2 := by
      intro n hn
      exact ha n ((Nat.le_max_right Nq Na).trans hn)
    have hqN : ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ (xiRectangularWeilLogCoefficient L n).re + C * (n : ℝ) ^ epsilon := by
      intro epsilon hepsilon
      obtain ⟨C, hC, ht⟩ := hq epsilon hepsilon
      exact ⟨C, hC, fun n hn => ht n ((Nat.le_max_left Nq Na).trans hn)⟩
    exact ⟨N, (rectangularWeil_subpowerLower_iff_primePolarSource hL.le hNa).mp hqN⟩
  · rintro ⟨Ns, hs⟩
    obtain ⟨Na, ha⟩ := exists_xiRectangularAdmissibleCutoff L
    let N := max Ns Na
    have hNa : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2 := by
      intro n hn
      exact ha n ((Nat.le_max_right Ns Na).trans hn)
    have hsN : ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
            C * (n : ℝ) ^ epsilon := by
      intro epsilon hepsilon
      obtain ⟨C, hC, ht⟩ := hs epsilon hepsilon
      exact ⟨C, hC, fun n hn => ht n ((Nat.le_max_left Ns Na).trans hn)⟩
    exact ⟨N, (rectangularWeil_subpowerLower_iff_primePolarSource hL.le hNa).mpr hsN⟩

/-- **Uniform prime--polar RH law.**  At every fixed positive window length, RH is equivalent to
uniform absolute boundedness of the finite prime--polar source over all separated apertures. -/
theorem riemannHypothesis_iff_rectangularPrimePolarSource_uniformlyBounded
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, L ≤ a →
        |rectangularPrimePolarSourceCoefficient L a| ≤ C := by
  let Q : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let B : ℝ := rectangularGammaPolarUniformBound L
  have hQ : 0 ≤ Q := mul_nonneg
    (by unfold rectangularTwoEdgeRemainderBound; positivity)
    (tsum_nonneg fun q => by positivity)
  have hB : 0 ≤ B := rectangularGammaPolarUniformBound_nonneg hL.le
  constructor
  · intro hRH
    refine ⟨Q + B, add_nonneg hQ hB, fun a ha => ?_⟩
    have hnorm := norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis hRH ha
    have hre : |(xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a)).re| ≤ Q :=
      (Complex.abs_re_le_norm _).trans hnorm
    have heq := congrArg Complex.re
      (xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection hL.le ha)
    have hcorr := abs_rectangularGammaPolarCorrection_le_uniformBound hL.le ha
    have hsabs : |rectangularPrimePolarSourceCoefficient L a| ≤
        |(xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a)).re| +
            |rectangularGammaPolarCorrection L a| := by
      rw [heq]
      simpa only [add_sub_cancel_right] using!
        abs_sub
          (rectangularPrimePolarSourceCoefficient L a +
            rectangularGammaPolarCorrection L a)
          (rectangularGammaPolarCorrection L a)
    exact hsabs.trans (add_le_add hre hcorr)
  · rintro ⟨C, _hC, hsource⟩
    apply (riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd hL).mpr
    refine ⟨C + B, fun n hLn => ?_⟩
    rw [xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection hL.le hLn,
      Complex.norm_real, Real.norm_eq_abs]
    exact (abs_add_le _ _).trans
      (add_le_add (hsource (Real.log n / 2) hLn)
        (abs_rectangularGammaPolarCorrection_le_uniformBound hL.le hLn))

/-- **Completed adjacent-block RH law.**  The remaining source obligation can equivalently be
placed on one completed critical-Mellin adjacent-block value sequence.  Fixed prime and polar
terms, as well as the Gamma edge, have all been discharged into aperture-independent constants. -/
theorem riemannHypothesis_iff_exists_eventually_criticalMellinAdjacentBlock_subpowerLower
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ criticalMellinAdjacentBlock L (Real.log n) +
            C * (n : ℝ) ^ epsilon := by
  rw [riemannHypothesis_iff_exists_eventually_rectangularPrimePolarSource_subpowerLower hL]
  constructor
  · rintro ⟨Ns, hs⟩
    obtain ⟨Na, ha⟩ := exists_xiRectangularAdmissibleCutoff L
    let N := max Ns Na
    have hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ 2 * L ≤ Real.log n := by
      intro n hn
      obtain ⟨hn1, hLn⟩ := ha n ((Nat.le_max_right Ns Na).trans hn)
      exact ⟨hn1, by linarith⟩
    have hsN : ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ rectangularPrimePolarSourceCoefficient L (Real.log n / 2) +
            C * (n : ℝ) ^ epsilon := by
      intro epsilon hepsilon
      obtain ⟨C, hC, ht⟩ := hs epsilon hepsilon
      exact ⟨C, hC, fun n hn => ht n ((Nat.le_max_left Ns Na).trans hn)⟩
    exact ⟨N,
      (rectangularPrimePolarSource_subpowerLower_iff_adjacentBlock hL.le hN).mp hsN⟩
  · rintro ⟨Na, ha⟩
    obtain ⟨Nc, hc⟩ := exists_xiRectangularAdmissibleCutoff L
    let N := max Na Nc
    have hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ 2 * L ≤ Real.log n := by
      intro n hn
      obtain ⟨hn1, hLn⟩ := hc n ((Nat.le_max_right Na Nc).trans hn)
      exact ⟨hn1, by linarith⟩
    have haN : ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ criticalMellinAdjacentBlock L (Real.log n) +
            C * (n : ℝ) ^ epsilon := by
      intro epsilon hepsilon
      obtain ⟨C, hC, ht⟩ := ha epsilon hepsilon
      exact ⟨C, hC, fun n hn => ht n ((Nat.le_max_left Na Nc).trans hn)⟩
    exact ⟨N,
      (rectangularPrimePolarSource_subpowerLower_iff_adjacentBlock hL.le hN).mpr haN⟩

/-! ## Source-only negative-energy law -/

/-- The finite prime--polar source after deletion of a finite prefix. -/
def rectangularPrimePolarSourceTailCoefficient
    (L : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then
    rectangularPrimePolarSourceCoefficient L (Real.log n / 2)
  else 0

/-- Negative part of the finite prime--polar source tail. -/
def rectangularPrimePolarSourceTailNegativePart
    (L : ℝ) (N n : ℕ) : ℝ :=
  (rectangularPrimePolarSourceTailCoefficient L N n)⁻

theorem rectangularPrimePolarSourceTailNegativePart_nonneg
    (L : ℝ) (N n : ℕ) :
    0 ≤ rectangularPrimePolarSourceTailNegativePart L N n :=
  negPart_nonneg _

/-- The negative finite prime--polar source mass regarded as a complex Dirichlet coefficient. -/
def rectangularPrimePolarSourceTailNegativeDirichletCoefficient
    (L : ℝ) (N n : ℕ) : ℂ :=
  ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ)

/-- The observable rectangular Weil tail and the finite prime--polar source tail differ by at
most the aperture-uniform Gamma--polar bound. -/
theorem abs_xiRectangularWeilTail_re_sub_primePolarSourceTail_le
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (n : ℕ) :
    |(xiRectangularWeilTailCoefficient L N n).re -
        rectangularPrimePolarSourceTailCoefficient L N n| ≤
      rectangularGammaPolarUniformBound L := by
  by_cases hn : N ≤ n
  · obtain ⟨_hn1, hLn⟩ := hN n hn
    rw [xiRectangularWeilTailCoefficient, if_pos hn,
      rectangularPrimePolarSourceTailCoefficient, if_pos hn,
      xiRectangularWeilLogCoefficient_re_eq_primePolarSource_add_gammaCorrection
        hL hLn]
    simpa only [add_sub_cancel_left] using
      abs_rectangularGammaPolarCorrection_le_uniformBound hL hLn
  · rw [xiRectangularWeilTailCoefficient, if_neg hn,
      rectangularPrimePolarSourceTailCoefficient, if_neg hn]
    simpa only [Complex.zero_re, sub_zero, abs_zero] using
      rectangularGammaPolarUniformBound_nonneg hL

/-- Bounded Gamma--polar correction transfers the negative Weil channel to the source channel. -/
theorem xiRectangularWeilTailNegativePart_le_primePolarSourceTail
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (n : ℕ) :
    xiRectangularWeilTailNegativePart L N n ≤
      rectangularPrimePolarSourceTailNegativePart L N n +
        rectangularGammaPolarUniformBound L := by
  exact negPart_le_negPart_add_of_abs_sub_le _ _ _
    (abs_xiRectangularWeilTail_re_sub_primePolarSourceTail_le hL hN n)

/-- The same bounded correction transfers the source negative channel back to the Weil channel. -/
theorem rectangularPrimePolarSourceTailNegativePart_le_xiRectangularWeilTail
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (n : ℕ) :
    rectangularPrimePolarSourceTailNegativePart L N n ≤
      xiRectangularWeilTailNegativePart L N n +
        rectangularGammaPolarUniformBound L := by
  apply negPart_le_negPart_add_of_abs_sub_le
  rw [abs_sub_comm]
  exact abs_xiRectangularWeilTail_re_sub_primePolarSourceTail_le hL hN n

private theorem constantGammaPolarUniformBound_LSeriesSummable
    {L : ℝ} (hL : 0 ≤ L) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun _n : ℕ => ((rectangularGammaPolarUniformBound L : ℝ) : ℂ)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := rectangularGammaPolarUniformBound L)
  · intro n hn
    rw [norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rectangularGammaPolarUniformBound_nonneg hL)]
  · exact hs

private theorem add_gammaPolarUniformBound_LSeriesSummable
    {f : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L) {s : ℂ} (hs : 1 < s.re)
    (hsource : LSeriesSummable (fun n => ((f n : ℝ) : ℂ)) s) :
    LSeriesSummable
      (fun n => (((f n + rectangularGammaPolarUniformBound L : ℝ) : ℂ))) s := by
  have hadd := hsource.add (constantGammaPolarUniformBound_LSeriesSummable hL hs)
  change Summable (LSeries.term _ s)
  change Summable (LSeries.term _ s) at hadd
  exact hadd.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
      simp only [Pi.add_apply, ofReal_add]

/-- **Quantitative source negative-energy law.**  At every transverse width `alpha`, the global
Xi zero-free half-plane is equivalent to all-abscissa negative Dirichlet energy of only the
finite prime--polar source values.  The condition is averaged and one-sided; it is strictly
weaker than pointwise all-epsilon lower control. -/
theorem all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeEnergyAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ↔
      ∀ epsilon : ℝ, 0 < epsilon →
        LSeriesSummable
          (fun n => ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ))
          (((1 + alpha + epsilon : ℝ) : ℂ)) := by
  rw [show (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) =
      XiZeroHalfPlaneBound alpha by rfl]
  constructor
  · intro hzeros epsilon hepsilon
    have hq :=
      (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove hL halpha hN).mp
        hzeros epsilon hepsilon
    apply LSeriesSummable_of_nonneg_of_le
      (rectangularPrimePolarSourceTailNegativePart_nonneg L N)
      (fun n => add_nonneg
        (xiRectangularWeilTailNegativePart_nonneg L N n)
        (rectangularGammaPolarUniformBound_nonneg hL.le))
      (rectangularPrimePolarSourceTailNegativePart_le_xiRectangularWeilTail hL.le hN)
    apply add_gammaPolarUniformBound_LSeriesSummable hL.le
    · simp only [ofReal_re]
      linarith
    · exact hq
  · intro hsource
    apply (xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove hL halpha hN).mpr
    intro epsilon hepsilon
    apply LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (fun n => add_nonneg
        (rectangularPrimePolarSourceTailNegativePart_nonneg L N n)
        (rectangularGammaPolarUniformBound_nonneg hL.le))
      (xiRectangularWeilTailNegativePart_le_primePolarSourceTail hL.le hN)
    apply add_gammaPolarUniformBound_LSeriesSummable hL.le
    · simp only [ofReal_re]
      linarith
    · exact hsource epsilon hepsilon

/-- **Prime--polar negative-energy RH law.**  RH is equivalent to weighted negative-part energy
of one finite prime--polar value sequence at every real abscissa strictly larger than one.  This
direct, unbundled statement removes Gamma, polar, contour, and pointwise hypotheses from the
remaining source obligation. -/
theorem riemannHypothesis_iff_rectangularPrimePolarSource_negativeEnergy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ epsilon : ℝ, 0 < epsilon →
        LSeriesSummable
          (fun n => ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ))
          (((1 + epsilon : ℝ) : ℂ)) := by
  constructor
  · intro hRH epsilon hepsilon
    obtain ⟨C, hC, hsource⟩ :=
      (riemannHypothesis_iff_rectangularPrimePolarSource_uniformlyBounded hL).mp hRH
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := C)
    · intro n hn
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg (rectangularPrimePolarSourceTailNegativePart_nonneg L N n)]
      rw [rectangularPrimePolarSourceTailNegativePart,
        rectangularPrimePolarSourceTailCoefficient]
      split_ifs with hNn
      · change (rectangularPrimePolarSourceCoefficient L (Real.log n / 2))⁻ ≤ C
        rw [negPart_def]
        exact max_le
          ((neg_le_abs _).trans (hsource _ (hN n hNn).2)) hC
      · simp only [negPart_zero]
        exact hC
    · simp only [ofReal_re]
      linarith
  · intro hsource
    apply riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
    intro epsilon hepsilon
    apply LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (fun n => add_nonneg
        (rectangularPrimePolarSourceTailNegativePart_nonneg L N n)
        (rectangularGammaPolarUniformBound_nonneg hL.le))
      (xiRectangularWeilTailNegativePart_le_primePolarSourceTail hL.le hN)
    apply add_gammaPolarUniformBound_LSeriesSummable hL.le
    · simp only [ofReal_re]
      linarith
    · exact hsource epsilon hepsilon

/-- **Quantitative prime--polar source abscissa law.**  At every nonnegative transverse width,
the horizontal Xi zero-free region is equivalent to one intrinsic threshold: the absolute-
convergence abscissa of the negative finite prime--polar source is at most `1 + alpha`.  This
compresses the all-epsilon energy family to a single source invariant. -/
theorem all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ↔
      LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 + alpha : ℝ) : EReal) := by
  rw [all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeEnergyAbove
    hL halpha hN]
  constructor
  · intro henergy
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro sigma hsigma
    have hsigmaR : 1 + alpha < sigma := by
      exact_mod_cast hsigma
    have hepsilon : 0 < sigma - (1 + alpha) := by linarith
    have hsum := henergy (sigma - (1 + alpha)) hepsilon
    change LSeriesSummable
      (fun n => ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ))
      (sigma : ℂ)
    convert hsum using 1
    norm_num
  · intro habscissa epsilon hepsilon
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    have hstrict :
        ((1 + alpha : ℝ) : EReal) <
          ((1 + alpha + epsilon : ℝ) : EReal) := by
      exact_mod_cast (by linarith : 1 + alpha < 1 + alpha + epsilon)
    simpa only [ofReal_re] using! habscissa.trans_lt hstrict

/-- **Critical prime--polar source abscissa law.**  RH is equivalent to the negative part of one
finite prime--polar source sequence having absolute-convergence abscissa at most one.  No Gamma
term, continuation hypothesis, pointwise floor, or epsilon-indexed family remains in the statement. -/
theorem riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) := by
  rw [riemannHypothesis_iff_rectangularPrimePolarSource_negativeEnergy hL hN]
  constructor
  · intro henergy
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro sigma hsigma
    have hsigmaR : 1 < sigma := by exact_mod_cast hsigma
    have hepsilon : 0 < sigma - 1 := by linarith
    have hsum := henergy (sigma - 1) hepsilon
    change LSeriesSummable
      (fun n => ((rectangularPrimePolarSourceTailNegativePart L N n : ℝ) : ℂ))
      (sigma : ℂ)
    convert hsum using 1
    norm_num
  · intro habscissa epsilon hepsilon
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    have hstrict : ((1 : ℝ) : EReal) < ((1 + epsilon : ℝ) : EReal) := by
      exact_mod_cast (by linarith : (1 : ℝ) < 1 + epsilon)
    simpa only [ofReal_re] using! habscissa.trans_lt hstrict

end RHTower
