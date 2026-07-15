import GaloisForLFunctions.HTGeometry.VacuumFeshbachValue
import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer
import GaloisForLFunctions.RHTower.TraceHankelSequenceCone

/-!
# Vacuum-Feshbach reduction of the coupled Sonin comparison

The constant polynomial is the one-dimensional vacuum channel of the prime--Gamma Hankel form.
Feshbach/Schur elimination completes the square in that channel.  Consequently the RH-equivalent
source sign problem does not require an independent comparison for every integer constant term:
one canonically centered real observable for each zero-constant integer tail is enough.

The coupled Sonin consumer below is quotient-free.  It asks for an aperture at which the squared
norm of the centered coupled source vector is bounded by the target Feshbach remainder, up to a
positive error, after cross multiplication by the strictly positive zeroth coupled energy.
Nonnegativity of the source norm then forces every target Feshbach remainder to be nonnegative.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Direct bridge to the shared RHTower moment cone.  Every existing producer of
`SequenceTraceHankelNonnegative` may equivalently target only the vacuum Feshbach remainders of
zero-constant real polynomial tails. -/
theorem sequenceTraceHankelNonnegative_iff_vacuumFeshbach
    (m : ℕ → ℝ) (h0 : 0 < m 0) :
    SequenceTraceHankelNonnegative m ↔
      ∀ q : Polynomial ℝ, q.coeff 0 = 0 →
        0 ≤ HTGeometry.momentVacuumFeshbachRemainder m q := by
  simpa only [SequenceTraceHankelNonnegative,
    sequenceTraceHankel_eq_momentFunctional] using
      HTGeometry.all_momentFunctional_sq_nonneg_iff_vacuumFeshbach m h0

/-- Quotient-free Robertson version of the shared moment-cone reduction. -/
theorem sequenceTraceHankelNonnegative_iff_vacuumRobertson
    (m : ℕ → ℝ) (h0 : 0 < m 0) :
    SequenceTraceHankelNonnegative m ↔
      ∀ q : Polynomial ℝ, q.coeff 0 = 0 →
        HTGeometry.momentFunctional m q ^ 2 ≤
          m 0 * HTGeometry.momentFunctional m (q ^ 2) := by
  rw [sequenceTraceHankelNonnegative_iff_vacuumFeshbach m h0]
  constructor
  · intro h q hq
    apply (HTGeometry.momentVacuumRobertsonDeterminant_nonneg_iff_cauchySchwarz
      m q).1
    exact (HTGeometry.momentVacuumFeshbachRemainder_nonneg_iff_robertson
      m h0 q).1 (h q hq)
  · intro h q hq
    apply (HTGeometry.momentVacuumFeshbachRemainder_nonneg_iff_robertson
      m h0 q).2
    exact (HTGeometry.momentVacuumRobertsonDeterminant_nonneg_iff_cauchySchwarz
      m q).2 (h q hq)

/-- The countable prime--Gamma Feshbach condition after the constant-polynomial channel has been
eliminated.  Only integer tails with zero constant coefficient remain. -/
def PrimeArchVacuumFeshbachIntNonnegative : Prop :=
  ∀ q : Polynomial ℤ, q.coeff 0 = 0 →
    0 ≤ HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ))

/-- The target-mean-zero representative of one integer polynomial tail. -/
def primeArchVacuumCenteredPolynomial (q : Polynomial ℤ) : Polynomial ℝ :=
  HTGeometry.momentVacuumCenteredPolynomial normalizedPrimeArchMoment
    (q.map (Int.castRingHom ℝ))

/-- The completed prime--Gamma value of the centered observable is exactly its vacuum Feshbach
remainder. -/
theorem re_primeArchSourceTraceHankel_vacuumCentered_eq_feshbach
    (q : Polynomial ℤ) :
    (primeArchSourceTraceHankel (primeArchVacuumCenteredPolynomial q)).re =
      HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
        (q.map (Int.castRingHom ℝ)) := by
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_momentVacuumCenteredPolynomial_sq
    normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne' _

/-- Nonnegativity of the countable vacuum Schur complements restores every integer-polynomial
prime--Gamma Hankel inequality.  The constant coefficient is discharged by the positive vacuum
square. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_vacuumFeshbach
    (h : PrimeArchVacuumFeshbachIntNonnegative) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  let qz : Polynomial ℤ := HTGeometry.polynomialVacuumTail p
  let q : Polynomial ℝ := qz.map (Int.castRingHom ℝ)
  let c : ℝ := ((p.coeff 0 : ℤ) : ℝ)
  have hqz : qz.coeff 0 = 0 := by
    simpa only [qz] using HTGeometry.polynomialVacuumTail_coeff_zero p
  have hrem :
      0 ≤ HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment q := by
    simpa only [q] using h qz hqz
  have hmap : p.map (Int.castRingHom ℝ) = C c + q := by
    have hsplit := congrArg (Polynomial.map (Int.castRingHom ℝ))
      (HTGeometry.C_coeff_zero_add_polynomialVacuumTail p)
    simpa only [qz, q, c, map_add, map_C] using hsplit.symm
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  rw [hmap,
    HTGeometry.momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
  exact add_nonneg
    (mul_nonneg normalizedPrimeArchMoment_zero_pos.le (sq_nonneg _)) hrem

/-- **Vacuum-Feshbach criterion for RH.**  The full integer-polynomial source cone is equivalent
to the countable family of scalar Schur complements on zero-constant tails. -/
theorem primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis :
    PrimeArchVacuumFeshbachIntNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
      (primeArchSourceTraceHankelIntNonnegative_of_vacuumFeshbach h)
  · intro hRH q _hq
    rw [← re_primeArchSourceTraceHankel_vacuumCentered_eq_feshbach]
    rw [← xiCentralTraceHankel_eq_primeArchSourceTraceHankel]
    exact xiCentralTraceHankelNonnegative_of_riemannHypothesis hRH _

/-- Exact theorem-interface simplification: the zero-constant Feshbach family has precisely the
same sign content as the former all-integer-polynomial family. -/
theorem primeArchVacuumFeshbachIntNonnegative_iff_sourceTraceHankelIntNonnegative :
    PrimeArchVacuumFeshbachIntNonnegative ↔
      PrimeArchSourceTraceHankelIntNonnegative := by
  rw [primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis,
    primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis]

/-- Quotient-free vacuum--tail Robertson inequalities for the countable prime--Gamma source. -/
def PrimeArchVacuumRobertsonIntNonnegative : Prop :=
  ∀ q : Polynomial ℤ, q.coeff 0 = 0 →
    HTGeometry.momentFunctional normalizedPrimeArchMoment
        (q.map (Int.castRingHom ℝ)) ^ 2 ≤
      normalizedPrimeArchMoment 0 *
        HTGeometry.momentFunctional normalizedPrimeArchMoment
          ((q.map (Int.castRingHom ℝ)) ^ 2)

/-- The quotient-free Robertson family and the vacuum Feshbach family are exactly equivalent. -/
theorem primeArchVacuumRobertsonIntNonnegative_iff_feshbach :
    PrimeArchVacuumRobertsonIntNonnegative ↔
      PrimeArchVacuumFeshbachIntNonnegative := by
  constructor
  · intro h q hq
    apply (HTGeometry.momentVacuumFeshbachRemainder_nonneg_iff_robertson
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos _).2
    exact (HTGeometry.momentVacuumRobertsonDeterminant_nonneg_iff_cauchySchwarz
      normalizedPrimeArchMoment _).2 (h q hq)
  · intro h q hq
    apply (HTGeometry.momentVacuumRobertsonDeterminant_nonneg_iff_cauchySchwarz
      normalizedPrimeArchMoment _).1
    exact (HTGeometry.momentVacuumFeshbachRemainder_nonneg_iff_robertson
      normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos _).1 (h q hq)

/-- **Vacuum Robertson criterion for RH.**  RH is equivalent to a countable family of
two-channel Cauchy--Schwarz/uncertainty inequalities between the constant vacuum and each
zero-constant integer polynomial tail. -/
theorem primeArchVacuumRobertsonIntNonnegative_iff_riemannHypothesis :
    PrimeArchVacuumRobertsonIntNonnegative ↔ RiemannHypothesis :=
  primeArchVacuumRobertsonIntNonnegative_iff_feshbach.trans
    primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis

/-! ## Coupled Sonin producer after vacuum elimination -/

/-- Quotient-free, one-sided Feshbach comparison.  For each zero-constant integer tail, compare
only its target-centered observable.  Thus no separate aperture comparison is required for the
constant-polynomial direction. -/
def SoninCoupledPrimeArchVacuumFeshbachRayleighUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (primeArchVacuumCenteredPolynomial q)‖ ^ 2 ≤
          (HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re

/-- The centered coupled-source comparison forces every prime--Gamma vacuum Schur complement to
be nonnegative.  This uses only a squared source norm and concrete source nondegeneracy. -/
theorem primeArchVacuumFeshbachIntNonnegative_of_soninCoupledRayleigh
    (h : SoninCoupledPrimeArchVacuumFeshbachRayleighUpperBound) :
    PrimeArchVacuumFeshbachIntNonnegative := by
  intro q hq
  let target : ℝ :=
    HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ))
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨a, ha⟩ := h q hq ε hε
  have hden : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
    (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
  have htargetε : target + ε < 0 := by
    dsimp only [ε]
    linarith
  have hright :
      (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re < 0 :=
    mul_neg_of_neg_of_pos htargetε hden
  have hleft :
      0 ≤ normalizedPrimeArchMoment 0 *
        ‖soninAllPrimeCoupledPolynomialPowerVector a.1
          (primeArchVacuumCenteredPolynomial q)‖ ^ 2 :=
    mul_nonneg normalizedPrimeArchMoment_zero_pos.le (sq_nonneg _)
  change normalizedPrimeArchMoment 0 *
      ‖soninAllPrimeCoupledPolynomialPowerVector a.1
        (primeArchVacuumCenteredPolynomial q)‖ ^ 2 ≤
    (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re at ha
  linarith

/-- Weaker source-variational form.  The scalar counterterm may be chosen independently at each
aperture, so the Sonin source itself performs the one-dimensional Mori/Feshbach least-squares
projection.  The target still contains only the fixed prime--Gamma Feshbach remainder. -/
def SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ (a : SoninCoupledNondegenerateAperture) (c : ℝ),
        normalizedPrimeArchMoment 0 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 ≤
          (HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re

/-- Fully quotient-free Robertson form of the same source-variational comparison.  Both the
target Feshbach denominator and its error rescaling have been cross-multiplied by the positive
vacuum mass. -/
def SoninCoupledPrimeArchVacuumRobertsonRayleighUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ (a : SoninCoupledNondegenerateAperture) (c : ℝ),
        normalizedPrimeArchMoment 0 ^ 2 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 ≤
          (HTGeometry.momentVacuumRobertsonDeterminant normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re

/-- The variance and quotient-free Robertson source interfaces are exactly equivalent; the only
change is multiplication by the positive vacuum mass and the corresponding error rescaling. -/
theorem soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound_iff_variance :
    SoninCoupledPrimeArchVacuumRobertsonRayleighUpperBound ↔
      SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound := by
  constructor
  · intro h q hq ε hε
    let δ : ℝ := normalizedPrimeArchMoment 0 * ε
    have hδ : 0 < δ :=
      mul_pos normalizedPrimeArchMoment_zero_pos hε
    obtain ⟨a, c, ha⟩ := h q hq δ hδ
    refine ⟨a, c, ?_⟩
    have hscaled :
        normalizedPrimeArchMoment 0 *
            (normalizedPrimeArchMoment 0 *
              ‖soninAllPrimeCoupledPolynomialPowerVector a.1
                (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2) ≤
          normalizedPrimeArchMoment 0 *
            ((HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
                (q.map (Int.castRingHom ℝ)) + ε) *
              (soninAllPrimeCoupledTraceMoment a.1 0).re) := by
      calc
        normalizedPrimeArchMoment 0 *
            (normalizedPrimeArchMoment 0 *
              ‖soninAllPrimeCoupledPolynomialPowerVector a.1
                (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2) =
            normalizedPrimeArchMoment 0 ^ 2 *
              ‖soninAllPrimeCoupledPolynomialPowerVector a.1
                (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 := by ring
        _ ≤ (HTGeometry.momentVacuumRobertsonDeterminant normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + δ) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re := ha
        _ = normalizedPrimeArchMoment 0 *
            ((HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
                (q.map (Int.castRingHom ℝ)) + ε) *
              (soninAllPrimeCoupledTraceMoment a.1 0).re) := by
          rw [HTGeometry.momentVacuumRobertsonDeterminant_eq_mul_feshbach
            normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
          dsimp only [δ]
          ring
    exact (mul_le_mul_iff_of_pos_left normalizedPrimeArchMoment_zero_pos).mp hscaled
  · intro h q hq ε hε
    have hε' : 0 < ε / normalizedPrimeArchMoment 0 :=
      div_pos hε normalizedPrimeArchMoment_zero_pos
    obtain ⟨a, c, ha⟩ := h q hq
      (ε / normalizedPrimeArchMoment 0) hε'
    refine ⟨a, c, ?_⟩
    have hscaled := mul_le_mul_of_nonneg_left ha
      normalizedPrimeArchMoment_zero_pos.le
    calc
      normalizedPrimeArchMoment 0 ^ 2 *
          ‖soninAllPrimeCoupledPolynomialPowerVector a.1
            (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 =
        normalizedPrimeArchMoment 0 *
          (normalizedPrimeArchMoment 0 *
            ‖soninAllPrimeCoupledPolynomialPowerVector a.1
              (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2) := by ring
      _ ≤ normalizedPrimeArchMoment 0 *
          ((HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) +
                ε / normalizedPrimeArchMoment 0) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re) := hscaled
      _ = (HTGeometry.momentVacuumRobertsonDeterminant normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re := by
        rw [HTGeometry.momentVacuumRobertsonDeterminant_eq_mul_feshbach
          normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
        field_simp [normalizedPrimeArchMoment_zero_pos.ne']
        ring

/-- The target-centered comparison implies the weaker source-variational comparison by choosing
the target moment mean as the scalar counterterm. -/
theorem soninCoupledPrimeArchVacuumVarianceRayleighUpperBound_of_centered
    (h : SoninCoupledPrimeArchVacuumFeshbachRayleighUpperBound) :
    SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound := by
  intro q hq ε hε
  obtain ⟨a, ha⟩ := h q hq ε hε
  refine ⟨a,
    HTGeometry.momentFunctional normalizedPrimeArchMoment
        (q.map (Int.castRingHom ℝ)) /
      normalizedPrimeArchMoment 0, ?_⟩
  simpa only [primeArchVacuumCenteredPolynomial,
    HTGeometry.momentVacuumCenteredPolynomial] using ha

/-- Even with an aperture-dependent scalar counterterm, the source norm remains nonnegative.
Consequently the weaker variance comparison still forces every target Feshbach remainder to be
nonnegative. -/
theorem primeArchVacuumFeshbachIntNonnegative_of_soninCoupledVarianceRayleigh
    (h : SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound) :
    PrimeArchVacuumFeshbachIntNonnegative := by
  intro q hq
  let target : ℝ :=
    HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ))
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨a, c, ha⟩ := h q hq ε hε
  have hden : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
    (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
  have htargetε : target + ε < 0 := by
    dsimp only [ε]
    linarith
  have hright :
      (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re < 0 :=
    mul_neg_of_neg_of_pos htargetε hden
  have hleft :
      0 ≤ normalizedPrimeArchMoment 0 *
        ‖soninAllPrimeCoupledPolynomialPowerVector a.1
          (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 :=
    mul_nonneg normalizedPrimeArchMoment_zero_pos.le (sq_nonneg _)
  change normalizedPrimeArchMoment 0 *
      ‖soninAllPrimeCoupledPolynomialPowerVector a.1
        (q.map (Int.castRingHom ℝ) - C c)‖ ^ 2 ≤
    (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re at ha
  linarith

/-- **Source-variational vacuum-Feshbach chain to RH.**  For each zero-constant integer tail, both
the aperture and its scalar source counterterm may vary.  This is the weakest source-norm form
exposed by the one-channel physics projection. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumVarianceRayleighUpperBound
    (h : SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound) :
    RiemannHypothesis :=
  primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp
    (primeArchVacuumFeshbachIntNonnegative_of_soninCoupledVarianceRayleigh h)

/-- Quotient-free vacuum--tail Robertson chain to RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound
    (h : SoninCoupledPrimeArchVacuumRobertsonRayleighUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchVacuumVarianceRayleighUpperBound
    (soninCoupledPrimeArchVacuumRobertsonRayleighUpperBound_iff_variance.mp h)

/-- **Vacuum-eliminated coupled-Sonin chain to RH.**  It is enough to prove the aperture Rayleigh
upper bound on the canonical target-centered representative of each zero-constant integer tail.
The full constant direction has been removed from the open comparison. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumFeshbachRayleighUpperBound
    (h : SoninCoupledPrimeArchVacuumFeshbachRayleighUpperBound) :
    RiemannHypothesis :=
  primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp
    (primeArchVacuumFeshbachIntNonnegative_of_soninCoupledRayleigh h)

end

end RHTower
