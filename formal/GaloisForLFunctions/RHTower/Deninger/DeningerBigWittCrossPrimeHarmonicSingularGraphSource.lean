import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusCrossPairSingularOneLegGraphCompletion
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeIncidenceHorizon

/-!
# Prime-harmonic Big-Witt source of the singular one-leg graph

The abstract one-leg graph admits arbitrary averaging packets converging to
its vertical generator, but those packets need not come from arithmetic.
This module constructs a genuine Big-Witt source sequence.

Take the canonical ordered row from prime two to every later prime.  Its
literal Big-Witt horizon coefficient is `1/(2q)`.  Euler divergence makes its
finite algebraic trace tend to infinity, while square summability of the full
cross-prime horizon uniformly bounds its Calderón--Witt `ℓ²` norm.  Dividing
each finite row by its own trace therefore produces actual labelled source
packets whose ambient realization tends to zero, whose trace is exactly one,
and whose singular graph realization tends to the vertical generator.

Multiplying by a completed Xi Green coefficient yields the corresponding
Xi-fibre vertical vector.  On every retained coordinate, undoing the finite
trace normalization gives exactly the existing raw all-cross-prime completed
Xi incidence comparison.  Thus this is a source-derived singular transport,
not a generic Hilbert averaging substitute.  No RH, zero-location,
positivity conjecture, spectral synthesis, or computation premise occurs.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

noncomputable local instance instDecidableEqCrossPrimePacketIndexHarmonicGraphSource :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- Canonical source row: prime two on the left and every later prime on the
right. -/
def deningerBigWittPrimeTwoRightEdgeEmbedding :
    ℕ ↪ DeningerCalderonWittCrossPrimePacketIndex where
  toFun n :=
    ⟨(nthPrimeSubtype 0, nthPrimeSubtype (n + 1)), by
      intro h
      have hi : 0 = n + 1 := nthPrimeSubtype_injective h
      omega⟩
  inj' := by
    intro m n h
    have hright : nthPrimeSubtype (m + 1) = nthPrimeSubtype (n + 1) :=
      congrArg (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.2) h
    have hmn : m + 1 = n + 1 := nthPrimeSubtype_injective hright
    omega

/-- Literal positive Big-Witt atom on the canonical prime-two row. -/
def deningerBigWittPrimeTwoRightEdgeWeight (n : ℕ) : ℝ :=
  ((nthPrimeSubtype 0 : ℝ) * (nthPrimeSubtype (n + 1) : ℝ))⁻¹

theorem deningerBigWittPrimeTwoRightEdgeWeight_pos (n : ℕ) :
    0 < deningerBigWittPrimeTwoRightEdgeWeight n := by
  rw [deningerBigWittPrimeTwoRightEdgeWeight]
  exact inv_pos.mpr
    (mul_pos (nthPrimeSubtype_pos 0) (nthPrimeSubtype_pos (n + 1)))

/-- The canonical row weight is exactly the coefficient of the existing raw
Big-Witt cross-prime horizon. -/
theorem deningerBigWittCrossPrimePacketRawCoefficient_primeTwoRightEdge
    (n : ℕ) :
    deningerBigWittCrossPrimePacketRawCoefficient
        (deningerBigWittPrimeTwoRightEdgeEmbedding n) =
      (deningerBigWittPrimeTwoRightEdgeWeight n : ℂ) := by
  simp [deningerBigWittCrossPrimePacketRawCoefficient,
    deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace,
    deningerBigWittPrimeTwoRightEdgeWeight,
    deningerBigWittPrimeTwoRightEdgeEmbedding, mul_comm]

/-- Euler divergence persists on the canonical prime-two source row. -/
theorem not_summable_deningerBigWittPrimeTwoRightEdgeWeight :
    ¬ Summable deningerBigWittPrimeTwoRightEdgeWeight := by
  intro h
  have hconst : (nthPrimeSubtype 0 : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (nthPrimeSubtype_pos 0))
  have htail : Summable (fun n : ℕ => (nthPrimeSubtype (n + 1) : ℝ)⁻¹) := by
    apply (summable_mul_left_iff hconst).mp
    apply h.congr
    intro n
    rw [deningerBigWittPrimeTwoRightEdgeWeight, mul_inv]
  have hall : Summable (fun n : ℕ => (nthPrimeSubtype n : ℝ)⁻¹) := by
    exact (summable_nat_add_iff 1).mp htail
  apply not_summable_nthPrime_reciprocal
  simpa [one_div] using hall

/-- Finite algebraic trace mass of the canonical source row. -/
def deningerBigWittPrimeTwoRightEdgeMass (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deningerBigWittPrimeTwoRightEdgeWeight k

/-- The finite source trace mass diverges to positive infinity. -/
theorem tendsto_deningerBigWittPrimeTwoRightEdgeMass_atTop :
    Tendsto deningerBigWittPrimeTwoRightEdgeMass atTop atTop := by
  change Tendsto
    (fun n : ℕ => ∑ k ∈ Finset.range n, deningerBigWittPrimeTwoRightEdgeWeight k)
    atTop atTop
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => (deningerBigWittPrimeTwoRightEdgeWeight_pos n).le)).mp
      not_summable_deningerBigWittPrimeTwoRightEdgeWeight

theorem deningerBigWittPrimeTwoRightEdgeMass_pos (n : ℕ) :
    0 < deningerBigWittPrimeTwoRightEdgeMass (n + 1) := by
  rw [deningerBigWittPrimeTwoRightEdgeMass, Finset.sum_range_succ]
  exact add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun i _ => (deningerBigWittPrimeTwoRightEdgeWeight_pos i).le)
    (deningerBigWittPrimeTwoRightEdgeWeight_pos n)

/-- First `n` actual ordered edges in the canonical prime-two row. -/
def deningerBigWittPrimeTwoRightEdgePrefix
    (n : ℕ) : Finset DeningerCalderonWittCrossPrimePacketIndex :=
  (Finset.range n).map deningerBigWittPrimeTwoRightEdgeEmbedding

/-- Literal finite truncation of the raw Big-Witt cross-prime horizon on the
canonical row. -/
def deningerBigWittPrimeTwoRightEdgeRawPacket
    (n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  (deningerBigWittPrimeTwoRightEdgePrefix n).sum fun i =>
    Finsupp.single i (deningerBigWittCrossPrimePacketRawCoefficient i)

@[simp] theorem deningerBigWittPrimeTwoRightEdgeRawPacket_apply
    (n : ℕ) (j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittPrimeTwoRightEdgeRawPacket n j =
      if j ∈ deningerBigWittPrimeTwoRightEdgePrefix n then
        deningerBigWittCrossPrimePacketRawCoefficient j else 0 := by
  classical
  simp [deningerBigWittPrimeTwoRightEdgeRawPacket, Finsupp.single_apply]

/-- Algebraic one-leg trace of the finite source row is its prime-harmonic
mass. -/
theorem deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeRawPacket
    (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittPrimeTwoRightEdgeRawPacket n) =
      (deningerBigWittPrimeTwoRightEdgeMass n : ℂ) := by
  classical
  rw [deningerBigWittPrimeTwoRightEdgeRawPacket, map_sum]
  simp only [deningerBigWittCrossPairAlgebraicOneLegTrace_single]
  rw [deningerBigWittPrimeTwoRightEdgePrefix, Finset.sum_map]
  rw [deningerBigWittPrimeTwoRightEdgeMass]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  exact deningerBigWittCrossPrimePacketRawCoefficient_primeTwoRightEdge k

/-- Every finite source row is an ambient truncation of the square-summable
raw horizon, hence has uniformly bounded `ℓ²` norm. -/
theorem norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeRawPacket_le
    (n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeRawPacket n)‖ ≤
      ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
  apply lp.norm_mono (by norm_num)
  intro j
  rw [show (deningerBigWittCrossPairFinitePacketAdmission
      (deningerBigWittPrimeTwoRightEdgeRawPacket n)) j =
        deningerBigWittPrimeTwoRightEdgeRawPacket n j by
      exact deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _,
    deningerBigWittPrimeTwoRightEdgeRawPacket_apply,
    deningerBigWittCrossPrimePacketRawHorizon_apply]
  by_cases hj : j ∈ deningerBigWittPrimeTwoRightEdgePrefix n <;> simp [hj]

/-- Finite actual source row divided by its own nonzero algebraic trace. -/
def deningerBigWittPrimeTwoRightEdgeNormalizedPacket
    (n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  ((deningerBigWittPrimeTwoRightEdgeMass (n + 1) : ℂ)⁻¹) •
    deningerBigWittPrimeTwoRightEdgeRawPacket (n + 1)

/-- Every normalized actual source packet has one-leg trace exactly one. -/
@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeNormalizedPacket
    (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n) = 1 := by
  rw [deningerBigWittPrimeTwoRightEdgeNormalizedPacket, map_smul,
    deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeRawPacket]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (deningerBigWittPrimeTwoRightEdgeMass_pos n)))

/-- Quantitative ambient collapse after source-trace normalization. -/
theorem norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket_le
    (n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)‖ ≤
      (deningerBigWittPrimeTwoRightEdgeMass (n + 1))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
  rw [deningerBigWittPrimeTwoRightEdgeNormalizedPacket, map_smul, norm_smul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerBigWittPrimeTwoRightEdgeMass_pos n)]
  exact mul_le_mul_of_nonneg_left
    (norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeRawPacket_le (n + 1))
    (inv_nonneg.mpr (deningerBigWittPrimeTwoRightEdgeMass_pos n).le)

/-- Normalized actual source rows disappear in the ambient Calderón--Witt
`ℓ²` carrier. -/
theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n))
      atTop (nhds 0) := by
  have hmass : Tendsto
      (fun n => deningerBigWittPrimeTwoRightEdgeMass (n + 1)) atTop atTop :=
    tendsto_deningerBigWittPrimeTwoRightEdgeMass_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hmaj : Tendsto
      (fun n => (deningerBigWittPrimeTwoRightEdgeMass (n + 1))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖) atTop (nhds 0) := by
    simpa [mul_comm] using
      hmass.inv_tendsto_atTop.const_mul ‖deningerBigWittCrossPrimePacketRawHorizon‖
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
  exact Eventually.of_forall
    norm_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket_le

/-- **Source-derived vertical generator.** Normalized finite Big-Witt horizon
rows converge in the singular graph to the vertical one-leg trace generator. -/
theorem tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_primeTwoRightEdgeNormalizedPacket :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have htrace : Tendsto
      (fun n => deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n))
      atTop (nhds (1 : ℂ)) := by
    simpa only [
      deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeNormalizedPacket] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1))
  have hpair : Tendsto
      (fun n =>
        (deningerBigWittCrossPairFinitePacketAdmission
            (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n),
          deningerBigWittCrossPairAlgebraicOneLegTrace
            (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using
      tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket.prodMk
        htrace
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

/-! ## Completed Xi Green weighting -/

/-- Prime-harmonic singular source packet weighted by one completed Xi
provenance coordinate. -/
def deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) (n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  x r • deningerBigWittPrimeTwoRightEdgeNormalizedPacket n

/-- Undoing finite trace normalization at every retained edge recovers
exactly the existing raw all-cross-prime Xi incidence comparison. -/
theorem deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket_coordinate_eq_rawComparison
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) {n k : ℕ}
    (hk : k < n + 1) :
    (deningerBigWittPrimeTwoRightEdgeMass (n + 1) : ℂ) *
        deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket x r n
          (deningerBigWittPrimeTwoRightEdgeEmbedding k) =
      deningerBigWittRawAllCrossPrimeXiIncidenceComparison x r
        (deningerBigWittPrimeTwoRightEdgeEmbedding k) := by
  have hi : deningerBigWittPrimeTwoRightEdgeEmbedding k ∈
      deningerBigWittPrimeTwoRightEdgePrefix (n + 1) := by
    rw [deningerBigWittPrimeTwoRightEdgePrefix]
    exact Finset.mem_map.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  rw [deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket,
    Finsupp.smul_apply, deningerBigWittPrimeTwoRightEdgeNormalizedPacket,
    Finsupp.smul_apply, deningerBigWittPrimeTwoRightEdgeRawPacket_apply,
    if_pos hi, deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply]
  have hmass : (deningerBigWittPrimeTwoRightEdgeMass (n + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (deningerBigWittPrimeTwoRightEdgeMass_pos n))
  change (deningerBigWittPrimeTwoRightEdgeMass (n + 1) : ℂ) *
      (x r * ((deningerBigWittPrimeTwoRightEdgeMass (n + 1) : ℂ)⁻¹ *
        deningerBigWittCrossPrimePacketRawCoefficient
          (deningerBigWittPrimeTwoRightEdgeEmbedding k))) =
    x r * deningerBigWittCrossPrimePacketRawCoefficient
      (deningerBigWittPrimeTwoRightEdgeEmbedding k)
  field_simp

/-- Xi-weighted packet trace is exactly the selected Xi coefficient. -/
@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_xiProvenancePrimeTwoRightNormalizedPacket
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket x r n) = x r := by
  rw [deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket, map_smul,
    deningerBigWittCrossPairAlgebraicOneLegTrace_primeTwoRightEdgeNormalizedPacket,
    smul_eq_mul, mul_one]

theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_xiProvenancePrimeTwoRightNormalizedPacket
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket x r n))
      atTop (nhds 0) := by
  simpa [deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket] using
    tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket.const_smul
      (x r)

/-- Completed Xi provenance weights the source-derived vertical generator
coefficient-faithfully. -/
theorem tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_xiProvenancePrimeTwoRightNormalizedPacket
    (x : DeningerArithmeticCompletedH1) (r : XiZeroCopy) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket x r n))
      atTop (nhds (x r • deningerBigWittCrossPairOneLegGraphSingularVector)) := by
  simpa [deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket] using
    tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_primeTwoRightEdgeNormalizedPacket.const_smul
      (x r)

/-- Literal completed Green specialization of the Xi-weighted source row. -/
def deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket
    (ell : DeningerArithmeticTopologicalH1Compact) (r : XiZeroCopy) (n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittXiProvenancePrimeTwoRightNormalizedPacket
    (deningerArithmeticSourceGreen ell) r n

/-- Completed Xi Green coefficient is the exact vertical graph-limit weight. -/
theorem tendsto_deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket_graph
    (ell : DeningerArithmeticTopologicalH1Compact) (r : XiZeroCopy) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket ell r n))
      atTop (nhds ((deningerArithmeticSourceGreen ell r) •
        deningerBigWittCrossPairOneLegGraphSingularVector)) := by
  exact
    tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_xiProvenancePrimeTwoRightNormalizedPacket
      (deningerArithmeticSourceGreen ell) r

/-- The continuous fixed-left graph reader converges to the completed Green
coefficient times its unsummed Big-Witt Frobenius left leg. -/
theorem tendsto_deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket_fiberReadout
    (ell : DeningerArithmeticTopologicalH1Compact) (r : XiZeroCopy)
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    Tendsto (fun n => deningerBigWittCrossPairOneLegGraphFiberReadout a p q
        (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket ell r n)))
      atTop (nhds ((deningerArithmeticSourceGreen ell r) *
        (-2 * deningerBigWittCrossPairLeftLeg a p q))) := by
  have h := (deningerBigWittCrossPairOneLegGraphFiberReadout a p q).continuous.tendsto
    ((deningerArithmeticSourceGreen ell r) •
      deningerBigWittCrossPairOneLegGraphSingularVector)
  have hc := h.comp
    (tendsto_deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket_graph ell r)
  change Tendsto (fun n => deningerBigWittCrossPairOneLegGraphFiberReadout a p q
      (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerArithmeticCompletedGreenPrimeTwoRightNormalizedPacket ell r n)))
    atTop (nhds (deningerBigWittCrossPairOneLegGraphFiberReadout a p q
      ((deningerArithmeticSourceGreen ell r) •
        deningerBigWittCrossPairOneLegGraphSingularVector))) at hc
  simpa only [map_smul,
    deningerBigWittCrossPairOneLegGraphFiberReadout_singularVector,
    smul_eq_mul] using hc

/-! ## Actual Gamma boundary on the source-derived vertical sector -/

/-- Continuous Gamma-boundary readout on the singular one-leg graph.  It pairs
the graph trace with the already-identified normalized base Gamma defect. -/
def deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout
    (r : XiZeroCopy) :
    DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ :=
  deningerBigWittCrossPairOneLegGraphTrace.smulRight
    (deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r)

/-- On the vertical graph sector, the actual Gamma readout is exactly scalar
multiplication by the normalized base Gamma defect coefficient. -/
@[simp] theorem deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout_smul_singularVector
    (r : XiZeroCopy) (z : ℂ) :
    deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout r
        (z • deningerBigWittCrossPairOneLegGraphSingularVector) =
      z * deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r := by
  change deningerBigWittCrossPairOneLegGraphTrace
      (z • deningerBigWittCrossPairOneLegGraphSingularVector) •
        deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r = _
  rw [map_smul, deningerBigWittCrossPairOneLegGraphTrace_singularVector]
  simp [smul_eq_mul]

/-- For the reflected-Gaussian completed-Xi provenance, vanishing of the
source-derived singular graph Gamma readout is equivalent to the critical-line
condition.  The comparison is anchored at the literal nonzero `(2,3)`
Big-Witt cross-prime coefficient, so no cancellation or RH premise enters. -/
theorem deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout_reflectedGaussian_eq_zero_iff
    (r : XiZeroCopy) :
    deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout r
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
          deningerBigWittCrossPairOneLegGraphSingularVector) = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  let i := deningerCalderonWittTwoThreePacketIndex
  have hcompare :
      deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
          (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) r i =
        deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout r
            (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
              deningerBigWittCrossPairOneLegGraphSingularVector) *
          deningerBigWittCrossPrimePacketRawCoefficient i := by
    rw [deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_apply]
    change deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
        deningerBigWittRawAllCrossPrimeXiIncidenceComparison
          DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r i = _
    rw [deningerBigWittRawAllCrossPrimeXiIncidenceComparison_apply,
      deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout_smul_singularVector]
    change deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r *
          deningerBigWittCrossPrimePacketRawCoefficient i) =
      (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r *
        deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r) *
          deningerBigWittCrossPrimePacketRawCoefficient i
    simpa only [mul_assoc] using congrArg
      (fun z : ℂ => z * deningerBigWittCrossPrimePacketRawCoefficient i)
      (mul_comm
        (deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r)
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r))
  have hraw : deningerBigWittCrossPrimePacketRawCoefficient i ≠ 0 :=
    deningerBigWittCrossPrimePacketRawCoefficient_ne_zero i
  calc
    deningerBigWittCrossPairOneLegGraphGammaBoundaryReadout r
          (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
            deningerBigWittCrossPairOneLegGraphSingularVector) = 0 ↔
        deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
          (deningerBigWittRawAllCrossPrimeXiIncidenceComparison
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) r i = 0 := by
          rw [hcompare, mul_eq_zero, or_iff_left hraw]
    _ ↔ (r.1 : ℂ).re = 1 / 2 :=
      deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_bigWittReflectedGaussian_eq_zero_iff
        r i

end

end RHTower
