import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceDivisorTomography
import GaloisForLFunctions.RHTower.CCMRectangularManuscriptCapstone
import GaloisForLFunctions.RHTower.HedenmalmEssentialFlowSymbol
import GaloisForLFunctions.RHTower.HedenmalmPrimeTranslationJordanCapstone
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularFullFormula

/-!
# Essential inverse-flow trace of the Hedenmalm theta source

This module indexes the nonzero spectrum of the source-derived compact operator directly, with
each spectral point repeated by the finrank of its maximal generalized eigenspace.  The resulting
punctured trace is absolutely summable, its spectral cutoffs converge independently of every
cofinal admissible choice, and the complete trace is the fixed-width Xi--Weil polarization.  Its
logarithmic samples are therefore the literal finite prime--Gamma source coefficients and inherit
the full divisor tomography and RH boundedness criterion.
-/

open Complex Filter Function Set
open GaloisForLFunctions.HTGeometry
open MeasureTheory Module.End
open scoped Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-! ## Multiplicity-exact source spectrum -/

/-- Nonzero spectrum of the source-derived compact operator. -/
abbrev ThetaNonzeroSpectrum :=
  {mu : ℂ // mu ∈ spectrum ℂ thetaKernelOperator ∧ mu ≠ 0}

/-- Algebraic multiplicity of a nonzero source spectral point. -/
def thetaSpectrumMultiplicity (mu : ThetaNonzeroSpectrum) : ℕ :=
  Module.finrank ℂ (maxGenEigenspace
    (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ))

/-- Every nonzero source spectral point, repeated by its full algebraic multiplicity. -/
abbrev ThetaSpectrumCopy :=
  Σ mu : ThetaNonzeroSpectrum, Fin (thetaSpectrumMultiplicity mu)

/-- A Xi support point gives its reciprocal nonzero source spectral point. -/
def thetaSpectrumOfXiSupport (rho : XiDivisorSupport) : ThetaNonzeroSpectrum := by
  let z := xiSpectralPointSupport rho
  have hXi : XiC z = 0 := XiC_xiSpectralPointSupport_eq_zero rho
  have hz : z ≠ 0 := fun hz ↦ XiC_zero_ne (hz ▸ hXi)
  exact ⟨-z⁻¹,
    (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero
      (neg_ne_zero.mpr (inv_ne_zero hz))).2 ⟨z, hXi, rfl⟩,
    neg_ne_zero.mpr (inv_ne_zero hz)⟩

@[simp] theorem thetaSpectrumOfXiSupport_val (rho : XiDivisorSupport) :
    (thetaSpectrumOfXiSupport rho : ℂ) = -(xiSpectralPointSupport rho)⁻¹ := by
  rfl

/-- Reciprocal transport is a bijection from the actual Xi support to the nonzero source
spectrum.  No zero enumeration is chosen. -/
theorem thetaSpectrumOfXiSupport_bijective :
    Function.Bijective thetaSpectrumOfXiSupport := by
  constructor
  · intro rho tau h
    apply xiSpectralPointSupport_injective
    apply inv_injective
    exact neg_injective (congrArg Subtype.val h)
  · intro mu
    obtain ⟨z, hXi, hmu⟩ :=
      (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero mu.2.2).1 mu.2.1
    have hxi : xi (1 / 2 + z * I) = 0 := by
      simpa only [XiC] using hXi
    let rho : XiDivisorSupport :=
      ⟨1 / 2 + z * I, mem_xi_divisor_support_of_eq_zero hxi⟩
    have hrho : xiSpectralPointSupport rho = z := by
      dsimp only [rho, xiSpectralPointSupport]
      rw [sub_eq_add_neg]
      ring_nf
      rw [I_sq]
      ring
    refine ⟨rho, Subtype.ext ?_⟩
    rw [thetaSpectrumOfXiSupport_val, hrho]
    exact hmu.symm

/-- Canonical support/nonzero-spectrum equivalence. -/
def xiSupportEquivThetaNonzeroSpectrum :
    XiDivisorSupport ≃ ThetaNonzeroSpectrum :=
  Equiv.ofBijective thetaSpectrumOfXiSupport
    thetaSpectrumOfXiSupport_bijective

@[simp] theorem xiSupportEquivThetaNonzeroSpectrum_apply
    (rho : XiDivisorSupport) :
    (xiSupportEquivThetaNonzeroSpectrum rho : ℂ) =
      -(xiSpectralPointSupport rho)⁻¹ := by
  rfl

/-- The Xi multiplicity copies and generalized source spectral copies are exactly equivalent. -/
def xiZeroCopyEquivThetaSpectrumCopy : XiZeroCopy ≃ ThetaSpectrumCopy :=
  Equiv.sigmaCongr xiSupportEquivThetaNonzeroSpectrum fun rho =>
    finCongr (by
      change xiSupportMultiplicity rho =
        thetaSpectrumMultiplicity (xiSupportEquivThetaNonzeroSpectrum rho)
      exact (finrank_maxGenEigenspace_thetaKernelOperator_eq_xiSupportMultiplicity rho).symm)

@[simp] theorem xiZeroCopyEquivThetaSpectrumCopy_spectralValue (q : XiZeroCopy) :
    ((xiZeroCopyEquivThetaSpectrumCopy q).1 : ℂ) =
      -(xiSpectralPoint q)⁻¹ := by
  rfl

/-! ## Root-block symbol transport -/

/-- Away from the removable origin, the paper's width amplitude is the rectangular amplitude. -/
theorem weilWidthAmplitude_eq_rectangularWindowAmplitude
    {L : ℝ} {w : ℂ} (hw : w ≠ 0) :
    weilWidthAmplitude L w = rectangularWindowAmplitude L w := by
  rw [weilWidthAmplitude, rectangularWindowAmplitude_eq_div hw]

/-- The paper's fixed-width sample is the bilateral rectangular transform off the origin. -/
theorem weilFixedWidthSample_eq_rectangularTwoEdgeTransform
    {a L : ℝ} {w : ℂ} (hw : w ≠ 0) :
    weilFixedWidthSample a L w = rectangularTwoEdgeTransform L a w := by
  rw [weilFixedWidthSample, rectangularTwoEdgeTransform,
    weilWidthAmplitude_eq_rectangularWindowAmplitude hw,
    weilWidthAmplitude_eq_rectangularWindowAmplitude (neg_ne_zero.mpr hw)]
  rw [neg_mul]

/-- Each multiplicity copy of the source spectrum carries exactly the corresponding Xi
rectangular value. -/
theorem essentialFlowSymbol_xiZeroCopy (a L : ℝ) (q : XiZeroCopy) :
    essentialFlowSymbol a L
        ((xiZeroCopyEquivThetaSpectrumCopy q).1 : ℂ) =
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) := by
  rw [xiZeroCopyEquivThetaSpectrumCopy_spectralValue,
    essentialFlowSymbol_root a L (xiSpectralPoint_ne_zero q),
    xiRectangularTwoEdgeTransform]
  exact weilFixedWidthSample_eq_rectangularTwoEdgeTransform
    (mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q))

/-! ## Absolutely convergent punctured trace -/

/-- One algebraic-multiplicity copy of the inverse-flow trace. -/
def thetaEssentialTraceTerm (a L : ℝ) (q : ThetaSpectrumCopy) : ℂ :=
  essentialFlowSymbol a L (q.1 : ℂ) ^ 2

theorem thetaEssentialTraceTerm_xiZeroCopy (a L : ℝ) (q : XiZeroCopy) :
    thetaEssentialTraceTerm a L (xiZeroCopyEquivThetaSpectrumCopy q) =
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
  rw [thetaEssentialTraceTerm, essentialFlowSymbol_xiZeroCopy]

/-- Absolute summability of the complete multiplicity-exact source trace. -/
theorem thetaEssentialTraceTerm_summable (a L : ℝ) :
    Summable (thetaEssentialTraceTerm a L) := by
  rw [← xiZeroCopyEquivThetaSpectrumCopy.summable_iff]
  exact (xiRectangularTwoEdgeTransform_sq_summable L a).congr
    (fun q => (thetaEssentialTraceTerm_xiZeroCopy a L q).symm)

/-- Absolute convergence in norm, not merely unconditional convergence. -/
theorem norm_thetaEssentialTraceTerm_summable (a L : ℝ) :
    Summable (fun q => ‖thetaEssentialTraceTerm a L q‖) :=
  (thetaEssentialTraceTerm_summable a L).norm

/-- Complete essential inverse-flow trace of the source-derived operator. -/
def thetaEssentialTrace (a L : ℝ) : ℂ :=
  ∑' q : ThetaSpectrumCopy, thetaEssentialTraceTerm a L q

/-- The operator-side trace is exactly the fixed-width Xi--Weil polarization. -/
theorem thetaEssentialTrace_eq_xiWeilPolarization (a L : ℝ) :
    thetaEssentialTrace a L =
      xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) := by
  rw [thetaEssentialTrace, ← xiZeroCopyEquivThetaSpectrumCopy.tsum_eq]
  calc
    ∑' q : XiZeroCopy,
        thetaEssentialTraceTerm a L (xiZeroCopyEquivThetaSpectrumCopy q) =
        ∑' q : XiZeroCopy,
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
      apply tsum_congr
      exact thetaEssentialTraceTerm_xiZeroCopy a L
    _ = xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a) :=
      (xiWeilPolarization_rectangular_eq_tsum_sq L a).symm

/-! ## Intrinsic spectral cutoffs and cutoff independence -/

/-- Nonzero spectral points above a positive modulus cutoff. -/
def thetaNonzeroSpectrumCutoffSet (eps : ℝ) : Set ThetaNonzeroSpectrum :=
  Subtype.val ⁻¹' {mu : ℂ |
    mu ∈ spectrum ℂ thetaKernelOperator ∧ eps ≤ ‖mu‖}

theorem thetaNonzeroSpectrumCutoffSet_finite
    {eps : ℝ} (heps : 0 < eps) :
    (thetaNonzeroSpectrumCutoffSet eps).Finite := by
  exact (finite_setOf_mem_spectrum_norm_ge_general
    isCompactOperator_thetaKernelOperator heps).preimage
      (Set.injOn_of_injective Subtype.val_injective)

/-- Finite packet containing every algebraic copy above `eps`; empty outside positive cutoffs. -/
def thetaSpectrumCutoffCopies (eps : ℝ) : Finset ThetaSpectrumCopy :=
  if heps : 0 < eps then
    (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset.sigma
      (fun mu => Finset.univ)
  else ∅

theorem mem_thetaSpectrumCutoffCopies {eps : ℝ} (heps : 0 < eps)
    (q : ThetaSpectrumCopy) :
    q ∈ thetaSpectrumCutoffCopies eps ↔ eps ≤ ‖(q.1 : ℂ)‖ := by
  simp [thetaSpectrumCutoffCopies, heps, thetaNonzeroSpectrumCutoffSet,
    q.1.2.1]

/-- Finite punctured trace at spectral modulus cutoff `eps`. -/
def thetaEssentialCutoffTrace (a L eps : ℝ) : ℂ :=
  ∑ q ∈ thetaSpectrumCutoffCopies eps, thetaEssentialTraceTerm a L q

/-- The finite copy sum is the algebraic-multiplicity-weighted spectral sum. -/
theorem thetaEssentialCutoffTrace_eq_finrank_sum
    (a L : ℝ) {eps : ℝ} (heps : 0 < eps) :
    thetaEssentialCutoffTrace a L eps =
      ∑ mu ∈ (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset,
        (thetaSpectrumMultiplicity mu : ℂ) *
          essentialFlowSymbol a L (mu : ℂ) ^ 2 := by
  rw [thetaEssentialCutoffTrace, thetaSpectrumCutoffCopies, dif_pos heps,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro mu hmu
  change (∑ _j : Fin (thetaSpectrumMultiplicity mu),
      essentialFlowSymbol a L (mu : ℂ) ^ 2) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Every finite algebraic packet is eventually contained in the intrinsic modulus cutoff. -/
theorem eventually_subset_thetaSpectrumCutoffCopies
    (s : Finset ThetaSpectrumCopy) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ), s ⊆ thetaSpectrumCutoffCopies eps := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
      have hnorm : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr q.1.2.2
      have hupper : ∀ᶠ eps in 𝓝[>] (0 : ℝ), eps ≤ ‖(q.1 : ℂ)‖ :=
        (eventually_le_nhds hnorm).filter_mono inf_le_left
      filter_upwards [self_mem_nhdsWithin, ih, hupper] with eps heps hs hqeps
      have heps0 : 0 < eps := heps
      intro r hr
      rw [Finset.mem_insert] at hr
      rcases hr with hr | hrs
      · subst r
        exact (mem_thetaSpectrumCutoffCopies heps0 q).2 hqeps
      · exact hs hrs

/-- Cutoff packets form a cofinal net in all finite multiplicity packets. -/
theorem tendsto_thetaSpectrumCutoffCopies_at_zero :
    Tendsto thetaSpectrumCutoffCopies (𝓝[>] (0 : ℝ)) atTop := by
  apply Filter.tendsto_atTop.mpr
  exact eventually_subset_thetaSpectrumCutoffCopies

/-- The punctured source traces converge absolutely to the complete trace as `eps ↓ 0`. -/
theorem thetaEssentialCutoffTrace_tendsto (a L : ℝ) :
    Tendsto (thetaEssentialCutoffTrace a L) (𝓝[>] (0 : ℝ))
      (𝓝 (thetaEssentialTrace a L)) := by
  have h := (thetaEssentialTraceTerm_summable a L).hasSum
  exact h.comp tendsto_thetaSpectrumCutoffCopies_at_zero

/-- Every cofinal admissible cutoff family has the same trace limit. -/
theorem thetaEssentialCutoffTrace_tendsto_along
    { ι : Type* } {l : Filter ι} {eps : ι → ℝ}
    (heps : Tendsto eps l (𝓝[>] (0 : ℝ))) (a L : ℝ) :
    Tendsto (fun i => thetaEssentialCutoffTrace a L (eps i)) l
      (𝓝 (thetaEssentialTrace a L)) :=
  (thetaEssentialCutoffTrace_tendsto a L).comp heps

/-! ## Prime--Gamma sampling, tomography, and RH criterion -/

/-- Logarithmic integer orbit of the essential source trace. -/
def thetaEssentialLogCoefficient (L : ℝ) (n : ℕ) : ℂ :=
  thetaEssentialTrace (Real.log n / 2) L

theorem thetaEssentialLogCoefficient_eq_weil (L : ℝ) (n : ℕ) :
    thetaEssentialLogCoefficient L n = xiRectangularWeilLogCoefficient L n := by
  exact thetaEssentialTrace_eq_xiWeilPolarization (Real.log n / 2) L

/-- Every admissible logarithmic trace sample is the literal finite prime--Gamma coefficient. -/
theorem thetaEssentialLogCoefficient_eq_primeGamma
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hLn : L ≤ Real.log n / 2) :
    thetaEssentialLogCoefficient L n =
      (xiRectangularPrimeGammaLogCoefficient L n : ℂ) := by
  apply Complex.ext
  · rw [thetaEssentialLogCoefficient_eq_weil,
      xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re hL hLn]
    rfl
  · rw [thetaEssentialLogCoefficient_eq_weil]
    simpa using xiRectangularWeilLogCoefficient_im_eq_zero L n

/-- Prime--Gamma expansion of every admissible source trace sample. -/
theorem thetaEssentialTrace_eq_prime_add_arch
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    thetaEssentialTrace a L =
      -2 * (rectangularPrimeAutocorrelationSum L a : ℂ) +
        normalizedRectangularBottomArchContribution L a := by
  rw [thetaEssentialTrace_eq_xiWeilPolarization]
  exact xiWeilPolarization_rectangular_eq_prime_add_arch hL ha

/-- Boundedness of one positive-width source trace orbit is exactly RH. -/
theorem riemannHypothesis_iff_thetaEssentialLogCoefficient_norm_bdd
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n : ℕ, L ≤ Real.log n / 2 →
        ‖thetaEssentialLogCoefficient L n‖ ≤ C := by
  simpa only [thetaEssentialLogCoefficient,
    thetaEssentialTrace_eq_xiWeilPolarization] using
      (riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd hL)

/-- The complete trace sequence has the canonical cutoff-free continuation and therefore
recovers every shifted right Xi pole. -/
theorem thetaEssentialTrace_full_tomography
    {L : ℝ} (hL : 0 < L) :
    (∀ (delta : ℝ), 0 ≤ delta →
      (∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ delta) →
      ∀ s : ℂ, 1 + delta < s.re →
        LSeries (thetaEssentialLogCoefficient L) s =
          xiRectangularWeilFullContinuation L s) ∧
    MeromorphicOn (xiRectangularWeilFullContinuation L)
      {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re →
      (meromorphicOrderAt (xiRectangularWeilFullContinuation L) s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) ∧
    (∀ q : XiRightZeroCopy,
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
            (xiRightShiftedPole q) /
          (2 * xiRectangularRightCoefficient L q) =
        (xiRightMultiplicity q : ℂ)) := by
  have hcoeff : thetaEssentialLogCoefficient L =
      xiRectangularWeilLogCoefficient L := by
    funext n
    exact thetaEssentialLogCoefficient_eq_weil L n
  obtain ⟨hseries, hmero, hpoles, hresidue, _⟩ :=
    fixedWindowFullObservableDivisorTomography_capstone hL
  refine ⟨?_, hmero, hpoles, fun q => (hresidue q).2⟩
  intro delta hdelta hupper s hs
  rw [hcoeff]
  exact hseries delta hdelta hupper s hs

end

end RHTower.HedenmalmThetaSource
