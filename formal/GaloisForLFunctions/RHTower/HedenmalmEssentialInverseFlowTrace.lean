import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.HTGeometry.CompactRieszProjectionTrace
import GaloisForLFunctions.HTGeometry.FinrankIndependentSup
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

/-! ## Finite-rank Riesz fibres and ordinary root-block calculus -/

/-- Every nonzero source spectral point has an isolating finite-rank Riesz projection whose range
is exactly its maximal generalized eigenspace. -/
theorem exists_thetaRieszProjection_range_eq_maxGenEigenspace
    (mu : ThetaNonzeroSpectrum) :
    ∃ r : ℝ, 0 < r ∧ r < ‖(mu : ℂ)‖ ∧
      (∀ lam ∈ Metric.sphere (mu : ℂ) r,
        lam ∈ resolventSet ℂ thetaKernelOperator) ∧
      rieszProjection thetaKernelOperator (mu : ℂ) r *
          rieszProjection thetaKernelOperator (mu : ℂ) r =
        rieszProjection thetaKernelOperator (mu : ℂ) r ∧
      FiniteDimensional ℂ
        (LinearMap.range
          ((rieszProjection thetaKernelOperator (mu : ℂ) r : ThetaH →L[ℂ] ThetaH) :
            ThetaH →ₗ[ℂ] ThetaH)) ∧
      LinearMap.range
          ((rieszProjection thetaKernelOperator (mu : ℂ) r : ThetaH →L[ℂ] ThetaH) :
            ThetaH →ₗ[ℂ] ThetaH) =
        maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) :=
  exists_rieszProjection_range_eq_maxGenEigenspace_of_isCompactOperator
    isCompactOperator_thetaKernelOperator mu.2.1 mu.2.2

/-- Canonical chosen isolating radius for a nonzero source spectral point. -/
def thetaRieszRadius (mu : ThetaNonzeroSpectrum) : ℝ :=
  Classical.choose (exists_thetaRieszProjection_range_eq_maxGenEigenspace mu)

theorem thetaRieszRadius_spec (mu : ThetaNonzeroSpectrum) :
    0 < thetaRieszRadius mu ∧ thetaRieszRadius mu < ‖(mu : ℂ)‖ ∧
      (∀ lam ∈ Metric.sphere (mu : ℂ) (thetaRieszRadius mu),
        lam ∈ resolventSet ℂ thetaKernelOperator) ∧
      rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu) *
          rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu) =
        rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu) ∧
      FiniteDimensional ℂ
        (LinearMap.range
          ((rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu) :
            ThetaH →L[ℂ] ThetaH) : ThetaH →ₗ[ℂ] ThetaH)) ∧
      LinearMap.range
          ((rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu) :
            ThetaH →L[ℂ] ThetaH) : ThetaH →ₗ[ℂ] ThetaH) =
        maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) :=
  Classical.choose_spec (exists_thetaRieszProjection_range_eq_maxGenEigenspace mu)

/-- Isolated finite-rank Riesz projection onto one complete source root block. -/
def thetaLocalRieszProjection (mu : ThetaNonzeroSpectrum) : ThetaH →L[ℂ] ThetaH :=
  rieszProjection thetaKernelOperator (mu : ℂ) (thetaRieszRadius mu)

theorem thetaLocalRieszProjection_idempotent (mu : ThetaNonzeroSpectrum) :
    thetaLocalRieszProjection mu * thetaLocalRieszProjection mu =
      thetaLocalRieszProjection mu :=
  (thetaRieszRadius_spec mu).2.2.2.1

theorem range_thetaLocalRieszProjection (mu : ThetaNonzeroSpectrum) :
    LinearMap.range ((thetaLocalRieszProjection mu : ThetaH →L[ℂ] ThetaH) :
        ThetaH →ₗ[ℂ] ThetaH) =
      maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) :=
  (thetaRieszRadius_spec mu).2.2.2.2.2

/-- Algebraic source root spaces are finite dimensional, proved from their compact Riesz
projections rather than assumed. -/
noncomputable instance thetaMaxGenEigenspace_finiteDimensional
    (mu : ThetaNonzeroSpectrum) :
    FiniteDimensional ℂ
      (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)) := by
  obtain ⟨r, _hr, _hrmu, _hres, _hidem, hfin, hrange⟩ :=
    exists_thetaRieszProjection_range_eq_maxGenEigenspace mu
  rw [← hrange]
  exact hfin

/-- Restriction of the source operator to one full generalized spectral fibre. -/
def thetaRootBlockOperator (mu : ThetaNonzeroSpectrum) :
    Module.End ℂ
      (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)) :=
  (thetaKernelOperator : Module.End ℂ ThetaH).restrict
    (Module.End.mapsTo_maxGenEigenspace_of_comm
      (f := (thetaKernelOperator : Module.End ℂ ThetaH))
      (g := (thetaKernelOperator : Module.End ℂ ThetaH))
      (Commute.refl _) (mu : ℂ))

/-- Nilpotent Jordan part on every source root block. -/
theorem thetaRootBlockOperator_sub_isNilpotent (mu : ThetaNonzeroSpectrum) :
    IsNilpotent
      (thetaRootBlockOperator mu -
        algebraMap ℂ
          (Module.End ℂ
            (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)))
          (mu : ℂ)) := by
  rw [Module.End.isNilpotent_iff_of_finite]
  intro x
  obtain ⟨n, hn⟩ :=
    (Module.End.mem_maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) (x : ThetaH)).mp x.2
  refine ⟨n, ?_⟩
  apply Subtype.ext
  have hmaps : ∀ y ∈
      maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ),
      (thetaKernelOperator : Module.End ℂ ThetaH) y ∈
        maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) (mu : ℂ)
  have hsub := restrict_sub_smul
    (thetaKernelOperator : Module.End ℂ ThetaH) hmaps (mu : ℂ)
  have hroot : thetaRootBlockOperator mu =
      (thetaKernelOperator : Module.End ℂ ThetaH).restrict hmaps := by
    ext y
    rfl
  have hcalc :
      thetaRootBlockOperator mu -
          algebraMap ℂ
            (Module.End ℂ
              (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)))
            (mu : ℂ) =
        ((thetaKernelOperator : Module.End ℂ ThetaH) - (mu : ℂ) • 1).restrict
          (fun y hy =>
            (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)).sub_mem
              (hmaps y hy)
              ((maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)).smul_mem
                (mu : ℂ) hy)) := by
    rw [Algebra.algebraMap_eq_smul_one, hroot]
    exact hsub
  rw [hcalc, coe_restrict_pow]
  exact hn

/-- Normalized positive-order Taylor jet of the essential symbol at a nonzero root. -/
def thetaEssentialTaylorCoefficient (a L : ℝ) (mu : ThetaNonzeroSpectrum)
    (k : ℕ) : ℂ :=
  iteratedDeriv (k + 1) (essentialFlowSymbol a L) (mu : ℂ) /
    (Nat.factorial (k + 1) : ℂ)

/-- Ordinary finite-dimensional Taylor/holomorphic functional calculus on one generalized source
root block.  Nilpotence makes the Taylor expansion finite. -/
def thetaRootBlockFunctionalCalculus (a L : ℝ) (mu : ThetaNonzeroSpectrum) :
    Module.End ℂ
      (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)) :=
  finiteRootBlockTaylorCalculus (thetaRootBlockOperator mu) (mu : ℂ)
    (essentialFlowSymbol a L (mu : ℂ))
    (thetaEssentialTaylorCoefficient a L mu)

/-- Exact Jordan-block trace law: every derivative term is nilpotent and has zero trace. -/
theorem trace_thetaRootBlockFunctionalCalculus_sq
    (a L : ℝ) (mu : ThetaNonzeroSpectrum) :
    LinearMap.trace ℂ
        (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ))
        (thetaRootBlockFunctionalCalculus a L mu ∘ₗ
          thetaRootBlockFunctionalCalculus a L mu) =
      (thetaSpectrumMultiplicity mu : ℂ) *
        essentialFlowSymbol a L (mu : ℂ) ^ 2 := by
  exact trace_finiteRootBlockTaylorCalculus_sq
    (thetaRootBlockOperator mu) (mu : ℂ)
    (essentialFlowSymbol a L (mu : ℂ))
    (thetaEssentialTaylorCoefficient a L mu)
    (thetaRootBlockOperator_sub_isNilpotent mu)

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

/-- Finite direct sum of all Riesz root fibres above a positive modulus cutoff. -/
def thetaEssentialRieszCutoffRange {eps : ℝ} (heps : 0 < eps) : Submodule ℂ ThetaH :=
  (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset.sup fun mu =>
    maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)

noncomputable instance thetaEssentialRieszCutoffRange_finiteDimensional
    {eps : ℝ} (heps : 0 < eps) :
    FiniteDimensional ℂ (thetaEssentialRieszCutoffRange heps) := by
  dsimp [thetaEssentialRieszCutoffRange]
  letI : ∀ mu : ThetaNonzeroSpectrum,
      FiniteDimensional ℂ
        (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)) :=
    fun mu => thetaMaxGenEigenspace_finiteDimensional mu
  exact Submodule.finite_finset_sup _ _

/-- Dimension of the cutoff Riesz range is the sum of full algebraic multiplicities. -/
theorem finrank_thetaEssentialRieszCutoffRange
    {eps : ℝ} (heps : 0 < eps) :
    Module.finrank ℂ (thetaEssentialRieszCutoffRange heps) =
      ∑ mu ∈ (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset,
        thetaSpectrumMultiplicity mu := by
  exact finrank_finset_sup_of_iSupIndep
    (fun mu : ThetaNonzeroSpectrum =>
      maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ))
    ((Module.End.independent_maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH)).comp Subtype.val_injective)
    (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset

/-- Finite punctured Riesz trace, defined as the ordinary finite-dimensional functional-calculus
trace on each isolated Riesz fibre and then on their finite direct sum. -/
def thetaEssentialRieszCutoffTrace (a L : ℝ) {eps : ℝ} (heps : 0 < eps) : ℂ :=
  ∑ mu ∈ (thetaNonzeroSpectrumCutoffSet_finite heps).toFinset,
    LinearMap.trace ℂ
      (maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ))
      (thetaRootBlockFunctionalCalculus a L mu ∘ₗ
        thetaRootBlockFunctionalCalculus a L mu)

/-- The literal finite Riesz-fibre trace equals the intrinsic algebraic-multiplicity cutoff sum. -/
theorem thetaEssentialRieszCutoffTrace_eq
    (a L : ℝ) {eps : ℝ} (heps : 0 < eps) :
    thetaEssentialRieszCutoffTrace a L heps = thetaEssentialCutoffTrace a L eps := by
  rw [thetaEssentialCutoffTrace_eq_finrank_sum a L heps]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact trace_thetaRootBlockFunctionalCalculus_sq a L mu

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

/-- Totalized finite Riesz trace; nonpositive parameters are irrelevant to the punctured limit. -/
def thetaEssentialRieszCutoffTraceTotal (a L eps : ℝ) : ℂ :=
  if heps : 0 < eps then thetaEssentialRieszCutoffTrace a L heps else 0

theorem thetaEssentialRieszCutoffTraceTotal_eq
    (a L eps : ℝ) :
    thetaEssentialRieszCutoffTraceTotal a L eps =
      thetaEssentialCutoffTrace a L eps := by
  by_cases heps : 0 < eps
  · simp only [thetaEssentialRieszCutoffTraceTotal, dif_pos heps]
    exact thetaEssentialRieszCutoffTrace_eq a L heps
  · simp [thetaEssentialRieszCutoffTraceTotal, heps, thetaEssentialCutoffTrace,
      thetaSpectrumCutoffCopies]

/-- Absolute and cutoff-independent convergence of genuine finite Riesz-fibre traces. -/
theorem thetaEssentialRieszCutoffTrace_tendsto (a L : ℝ) :
    Tendsto (thetaEssentialRieszCutoffTraceTotal a L) (𝓝[>] (0 : ℝ))
      (𝓝 (thetaEssentialTrace a L)) := by
  have hfun : thetaEssentialRieszCutoffTraceTotal a L =
      thetaEssentialCutoffTrace a L := by
    funext eps
    exact thetaEssentialRieszCutoffTraceTotal_eq a L eps
  rw [hfun]
  exact thetaEssentialCutoffTrace_tendsto a L

/-- Every cofinal admissible cutoff family has the same trace limit. -/
theorem thetaEssentialCutoffTrace_tendsto_along
    { ι : Type* } {l : Filter ι} {eps : ι → ℝ}
    (heps : Tendsto eps l (𝓝[>] (0 : ℝ))) (a L : ℝ) :
    Tendsto (fun i => thetaEssentialCutoffTrace a L (eps i)) l
      (𝓝 (thetaEssentialTrace a L)) :=
  (thetaEssentialCutoffTrace_tendsto a L).comp heps

/-- Every cofinal positive cutoff family gives the same genuine finite Riesz trace limit. -/
theorem thetaEssentialRieszCutoffTrace_tendsto_along
    {ι : Type*} {l : Filter ι} {eps : ι → ℝ}
    (heps : Tendsto eps l (𝓝[>] (0 : ℝ))) (a L : ℝ) :
    Tendsto (fun i => thetaEssentialRieszCutoffTraceTotal a L (eps i)) l
      (𝓝 (thetaEssentialTrace a L)) :=
  (thetaEssentialRieszCutoffTrace_tendsto a L).comp heps

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

/-! ## Closed card capstone -/

/-- **Essential inverse-flow prime tomography, unconditionally.**  This closed theorem packages
the finite-rank Riesz realization, ordinary finite-dimensional root-block calculus, absolute and
cutoff-independent trace limit, exact Xi--Weil and prime--Gamma identities, global divisor
tomography, reflection, essential boundary singularity, and terminal RH boundedness equivalence.
No hypothesis or axiom is attached to the theorem itself. -/
theorem hedenmalmEssentialInverseFlowPrimeTomography_capstone :
    (∀ mu : ThetaNonzeroSpectrum,
      ∃ r : ℝ, 0 < r ∧ r < ‖(mu : ℂ)‖ ∧
        (∀ lam ∈ Metric.sphere (mu : ℂ) r,
          lam ∈ resolventSet ℂ thetaKernelOperator) ∧
        rieszProjection thetaKernelOperator (mu : ℂ) r *
            rieszProjection thetaKernelOperator (mu : ℂ) r =
          rieszProjection thetaKernelOperator (mu : ℂ) r ∧
        FiniteDimensional ℂ
          (LinearMap.range
            ((rieszProjection thetaKernelOperator (mu : ℂ) r : ThetaH →L[ℂ] ThetaH) :
              ThetaH →ₗ[ℂ] ThetaH)) ∧
        LinearMap.range
            ((rieszProjection thetaKernelOperator (mu : ℂ) r : ThetaH →L[ℂ] ThetaH) :
              ThetaH →ₗ[ℂ] ThetaH) =
          maxGenEigenspace (thetaKernelOperator : Module.End ℂ ThetaH) (mu : ℂ)) ∧
    (∀ (a L : ℝ) (eps : ℝ) (heps : 0 < eps),
      thetaEssentialRieszCutoffTrace a L heps =
        thetaEssentialCutoffTrace a L eps) ∧
    (∀ a L : ℝ,
      Tendsto (thetaEssentialRieszCutoffTraceTotal a L) (𝓝[>] (0 : ℝ))
        (𝓝 (thetaEssentialTrace a L))) ∧
    (∀ a L : ℝ,
      thetaEssentialTrace a L =
        xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a)) ∧
    (∀ (L : ℝ) (n : ℕ), 0 ≤ L → L ≤ Real.log n / 2 →
      thetaEssentialLogCoefficient L n =
        (xiRectangularPrimeGammaLogCoefficient L n : ℂ)) ∧
    (∀ (L a : ℝ), 0 < L → L ≤ a →
      (∀ mu : ℂ, essentialFlowSymbol a L (-mu) = essentialFlowSymbol a L mu) ∧
      (∀ mu : ℂ, mu ≠ 0 → DifferentiableAt ℂ (essentialFlowSymbol a L) mu) ∧
      ¬ MeromorphicAt (essentialFlowSymbol a L) 0) ∧
    (∀ (f : ℝ → ℂ), Integrable f (volume : Measure ℝ) → ∀ x : ℝ,
      HedenmalmQuantile.sourceInverse thetaSource
          (HedenmalmHilbertSchmidt.sourceReflection f) (-x) =
        -HedenmalmQuantile.sourceInverse thetaSource f x) ∧
    (∀ L : ℝ, 0 < L →
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
          (xiRightMultiplicity q : ℂ))) ∧
    (∀ L : ℝ, 0 < L →
      (RiemannHypothesis ↔
        ∃ C : ℝ, ∀ n : ℕ, L ≤ Real.log n / 2 →
          ‖thetaEssentialLogCoefficient L n‖ ≤ C)) := by
  refine ⟨exists_thetaRieszProjection_range_eq_maxGenEigenspace,
    ?_, ?_, thetaEssentialTrace_eq_xiWeilPolarization, ?_, ?_, ?_, ?_, ?_⟩
  · intro a L eps heps
    exact thetaEssentialRieszCutoffTrace_eq a L heps
  · exact thetaEssentialRieszCutoffTrace_tendsto
  · intro L n hL hLn
    exact thetaEssentialLogCoefficient_eq_primeGamma hL hLn
  · intro L a hL _ha
    exact ⟨essentialFlowSymbol_neg a L,
      fun mu hmu => essentialFlowSymbol_differentiableAt a L hmu,
      essentialFlowSymbol_not_meromorphicAt_zero hL a⟩
  · intro f hf x
    exact sourceInverse_sourceReflection_theta hf x
  · intro L hL
    exact thetaEssentialTrace_full_tomography hL
  · intro L hL
    exact riemannHypothesis_iff_thetaEssentialLogCoefficient_norm_bdd hL

end

end RHTower.HedenmalmThetaSource
