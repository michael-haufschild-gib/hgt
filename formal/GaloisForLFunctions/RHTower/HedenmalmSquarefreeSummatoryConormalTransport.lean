import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyHilbertTransport
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall

/-!
# Arithmetic summatory transport across the physical MSC Hilbert wall

The density and the weighted squarefree counting discrepancy form one fixed
Hilbert source. Explicit strongly holomorphic value and derivative vectors
recover the squarefree partition and its derivative at the original spectral
point throughout the strict-right half-plane away from the density pole.

Normalizing at a safe Euler base recovers exactly the MSC overlap and its
division-free Fisher numerator. Thus the transport preserves the full divisor
and conormal while admitting points where the literal Dirichlet source column
has infinite square mass. It changes the arithmetic representation before
Hilbert admission; it does not assert positivity of a Sonin energy form.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower.SquarefreeDiscrepancy

/-- Density and discrepancy are retained as separate source coordinates. -/
abbrev ArithmeticHilbert := WithLp 2 (ℂ × LogHilbert)

/-- A single arithmetic source, independent of the spectral point and the safe base. -/
def arithmeticSource : ArithmeticHilbert :=
  WithLp.toLp 2 ((Sieve.squarefreeDensity : ℂ), hilbertSource)

/-- Value vector for the original squarefree partition, including its density pole. -/
def partitionVector (s : ℂ) : ArithmeticHilbert :=
  WithLp.toLp 2 (s / (s - 1), s • hilbertEvaluation s)

/-- The explicit spectral derivative vector. -/
def partitionJet (s : ℂ) : ArithmeticHilbert :=
  WithLp.toLp 2 (-1 / (s - 1) ^ (2 : ℕ),
    hilbertEvaluation s + s • hilbertEvaluationJet s)

/-- Physical MSC evaluation domain, without a selected zero. -/
def transportDomain : Set ℂ := {s | 1 / 2 < s.re ∧ s ≠ 1}

theorem isOpen_transportDomain : IsOpen transportDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isClosed_singleton.isOpen_compl

theorem arithmeticSource_ne_zero : arithmeticSource ≠ 0 := by
  intro h
  have hc : (Sieve.squarefreeDensity : ℂ) = 0 :=
    congrArg (fun v : ArithmeticHilbert => v.fst) h
  have hd : 0 < Sieve.squarefreeDensity := by
    rw [Sieve.squarefreeDensity_eq]
    positivity
  exact hd.ne' (Complex.ofReal_eq_zero.mp hc)

/-- Admission does not collapse the physical spectral column, even at a divisor. -/
theorem partitionVector_ne_zero {s : ℂ} (hs : s ∈ transportDomain) :
    partitionVector s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  intro h
  have hh : s / (s - 1) = 0 :=
    congrArg (fun v : ArithmeticHilbert => v.fst) h
  exact (div_ne_zero hs0 (sub_ne_zero.mpr hs.2)) hh

/-- The conormal jet is a strong derivative in the same fixed positive Hilbert space. -/
theorem hasDerivAt_partitionVector {s : ℂ} (hs : s ∈ transportDomain) :
    HasDerivAt partitionVector (partitionJet s) s := by
  have hh : HasDerivAt (fun z : ℂ => z / (z - 1))
      (-1 / (s - 1) ^ (2 : ℕ)) s := by
    convert (hasDerivAt_id s).div ((hasDerivAt_id s).sub_const 1)
      (sub_ne_zero.mpr hs.2) using 1 <;> ring
  have ht : HasDerivAt (fun z : ℂ => z • hilbertEvaluation z)
      (hilbertEvaluation s + s • hilbertEvaluationJet s) s := by
    simpa only [Pi.smul_apply, one_smul, add_comm] using
      (hasDerivAt_id s).smul (hasDerivAt_hilbertEvaluation hs.1)
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ LogHilbert).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s (hh.prodMk ht)

theorem analyticOnNhd_partitionVector :
    AnalyticOnNhd ℂ partitionVector transportDomain := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_transportDomain
  exact fun _ hs => (hasDerivAt_partitionVector hs).differentiableAt.differentiableWithinAt

/-- Exact source identity, derived from counting coefficients rather than prescribed Xi values. -/
theorem inner_arithmeticSource_partitionVector {s : ℂ} (hs : s ∈ transportDomain) :
    inner ℂ arithmeticSource (partitionVector s) =
      GaloisForLFunctions.squarefreePartition s := by
  rw [arithmeticSource, partitionVector, WithLp.prod_inner_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, RCLike.inner_apply,
    star_def, Complex.conj_ofReal, inner_smul_right]
  rw [inner_hilbertSource_evaluation hs.1, moment_eq_quotient hs.1 hs.2]
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hz : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp only [two_mul, add_re]; linarith [hs.1])
  unfold GaloisForLFunctions.squarefreePartition
  field_simp [hs0, sub_ne_zero.mpr hs.2, hz]
  ring

theorem inner_arithmeticSource_partitionVector_eventuallyEq {s : ℂ}
    (hs : s ∈ transportDomain) :
    (fun z => inner ℂ arithmeticSource (partitionVector z)) =ᶠ[𝓝 s]
      GaloisForLFunctions.squarefreePartition := by
  filter_upwards [isOpen_transportDomain.mem_nhds hs] with z hz
  exact inner_arithmeticSource_partitionVector hz

/-- The same fixed source recovers the derivative, without dividing by a vanishing overlap. -/
theorem inner_arithmeticSource_partitionJet {s : ℂ} (hs : s ∈ transportDomain) :
    inner ℂ arithmeticSource (partitionJet s) =
      deriv GaloisForLFunctions.squarefreePartition s := by
  have h := (innerSL ℂ arithmeticSource).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_partitionVector hs)
  exact (h.congr_of_eventuallyEq
    (inner_arithmeticSource_partitionVector_eventuallyEq hs).symm).deriv.symm

/-- The overlap column uses the original affine coordinate, with no spectral translation. -/
def overlapVector (sigma epsilon u : ℂ) : ArithmeticHilbert :=
  (GaloisForLFunctions.squarefreePartition sigma)⁻¹ •
    partitionVector (sigma + u * epsilon)

/-- Division-free pointed Fisher jet in the same arithmetic Hilbert carrier. -/
def fisherVector (sigma epsilon u : ℂ) : ArithmeticHilbert :=
  (2 / GaloisForLFunctions.squarefreePartition sigma) •
    (epsilon • partitionJet (sigma + u * epsilon) +
      (epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma) •
        partitionVector (sigma + u * epsilon))

theorem inner_arithmeticSource_overlapVector (sigma epsilon u : ℂ)
    (hs : sigma + u * epsilon ∈ transportDomain) :
    inner ℂ arithmeticSource (overlapVector sigma epsilon u) =
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u := by
  rw [overlapVector, inner_smul_right, inner_arithmeticSource_partitionVector hs]
  simp only [GaloisForLFunctions.squarefreeBoundaryOverlap, div_eq_mul_inv]
  ring

theorem inner_arithmeticSource_fisherVector (sigma epsilon u : ℂ)
    (hs : sigma + u * epsilon ∈ transportDomain) :
    inner ℂ arithmeticSource (fisherVector sigma epsilon u) =
      GaloisForLFunctions.squarefreeFisherScore sigma epsilon u := by
  rw [fisherVector, inner_smul_right, inner_add_right, inner_smul_right,
    inner_smul_right, inner_arithmeticSource_partitionJet hs,
    inner_arithmeticSource_partitionVector hs,
    GaloisForLFunctions.squarefreeFisherScore,
    deriv_squarefreeBoundaryOverlap_eq_affine_partition
      (analyticAt_squarefreePartition_of_half_lt_re hs.1 hs.2)]
  simp only [GaloisForLFunctions.squarefreeBoundaryOverlap, div_eq_mul_inv]
  ring

/-- Exact conormal fidelity includes the source normalization and the connection term. -/
theorem summatoryConormal_eq (sigma epsilon u : ℂ)
    (hs : sigma + u * epsilon ∈ transportDomain) :
    inner ℂ arithmeticSource (fisherVector sigma epsilon u) /
        inner ℂ arithmeticSource (overlapVector sigma epsilon u) =
      GaloisForLFunctions.squarefreeFisherScore sigma epsilon u /
        GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u := by
  rw [inner_arithmeticSource_fisherVector sigma epsilon u hs,
    inner_arithmeticSource_overlapVector sigma epsilon u hs]

/-- The Hilbert observation retains every multiplicity of the strict-right Xi divisor. -/
theorem analyticOrderAt_hilbertPartition_eq_xi
    (s : {s : ℂ // 1 / 2 < s.re ∧ s.re < 1}) :
    analyticOrderAt (fun z => inner ℂ arithmeticSource (partitionVector z)) s =
      analyticOrderAt xi s := by
  have hs : (s : ℂ) ∈ transportDomain := ⟨s.property.1, by
    intro h
    have hh := s.property.2
    rw [h] at hh
    norm_num at hh⟩
  rw [analyticOrderAt_congr (inner_arithmeticSource_partitionVector_eventuallyEq hs)]
  exact analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
    s.property.1 s.property.2

/-- A fixed, nonzero arithmetic source admits every physical strict-right spectral point
and both value and derivative columns, although its literal Dirichlet column is not in ℓ². -/
theorem physicalSummatoryHilbertAdmission :
    arithmeticSource ≠ 0 ∧ AnalyticOnNhd ℂ partitionVector transportDomain ∧
      ∀ rho : {s : ℂ // 1 / 2 < s.re ∧ s.re < 1},
        partitionVector rho ≠ 0 ∧
        inner ℂ arithmeticSource (partitionVector rho) =
          GaloisForLFunctions.squarefreePartition rho ∧
        inner ℂ arithmeticSource (partitionJet rho) =
          deriv GaloisForLFunctions.squarefreePartition rho ∧
        ∀ sigma : {x : ℝ // 1 < x},
          ¬ Summable (fun n : ℕ =>
            ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma
              (mscPhysicalZeroCoordinate rho sigma) n‖ ^ (2 : ℕ)) := by
  refine ⟨arithmeticSource_ne_zero, analyticOnNhd_partitionVector, ?_⟩
  intro rho
  have hs : (rho : ℂ) ∈ transportDomain := ⟨rho.property.1, by
    intro h
    have hh := rho.property.2
    rw [h] at hh
    norm_num at hh⟩
  refine ⟨partitionVector_ne_zero hs, inner_arithmeticSource_partitionVector hs,
    inner_arithmeticSource_partitionJet hs, ?_⟩
  intro sigma
  exact HedenmalmThetaSource.not_summable_mscPhysicalZeroSourceColumn
    rho.property.2 sigma.property

end RHTower.SquarefreeDiscrepancy
