import GaloisForLFunctions.HTGeometry.MomentFiniteCoordinateValue
import GaloisForLFunctions.HTGeometry.NormalizedMomentQuantumVariance
import GaloisForLFunctions.RHTower.SoninCoupledProjectiveQuantumFisher

/-!
# Coupled Sonin projective/Feshbach value equivalence

Pure-state quantum Fisher geometry removes a scalar phase by a projective Gram determinant.  For
the actual coupled Sonin columns, that determinant is not merely analogous to a variance: it is
exactly the vacuum Robertson determinant of the real coupled trace-moment sequence.  After the
nonzero vacuum mass is cancelled, it is the source vacuum Feshbach remainder.

Consequently the counterterm-free projective source hypothesis is exactly equivalent to the
previous weakest aperture-plus-counterterm hypothesis.  The proof avoids a separate coefficient-
linearity theorem for the polynomial source vector: finite-coordinate moment values identify its
squared norm first, and the general Mori/Feshbach minimization then supplies the optimal scalar.
-/

open scoped BigOperators InnerProductSpace
open Polynomial

namespace RHTower

noncomputable section

/-- Real coupled trace-moment sequence at one aperture. -/
def soninAllPrimeCoupledRealTraceMoment
    (a : SoninPositiveAperture) (k : ℕ) : ℝ :=
  (soninAllPrimeCoupledTraceMoment a k).re

/-- The complex coupled trace moment is the cast of its real value. -/
theorem soninAllPrimeCoupledTraceMoment_eq_ofReal
    (a : SoninPositiveAperture) (k : ℕ) :
    soninAllPrimeCoupledTraceMoment a k =
      (soninAllPrimeCoupledRealTraceMoment a k : ℂ) := by
  apply Complex.ext <;>
    simp [soninAllPrimeCoupledRealTraceMoment,
      soninAllPrimeCoupledTraceMoment_im_eq_zero]

/-- The vacuum-column mass is the zeroth real coupled trace moment. -/
theorem norm_soninAllPrimeCoupledPowerVector_zero_sq
    (a : SoninPositiveAperture) :
    ‖soninAllPrimeCoupledPowerVector a 0‖ ^ 2 =
      soninAllPrimeCoupledRealTraceMoment a 0 := by
  have h := soninAllPrimeCoupledGramBlock_eq_traceMoment
    1 a (0 : Fin 1) (0 : Fin 1)
  have hinner :
      inner ℂ (soninAllPrimeCoupledPowerVector a 0)
          (soninAllPrimeCoupledPowerVector a 0) =
        soninAllPrimeCoupledTraceMoment a 0 := by
    simpa [soninAllPrimeCoupledGramBlock, Matrix.gram_apply] using h
  calc
    ‖soninAllPrimeCoupledPowerVector a 0‖ ^ 2 =
        (inner ℂ (soninAllPrimeCoupledPowerVector a 0)
          (soninAllPrimeCoupledPowerVector a 0)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ)
        (soninAllPrimeCoupledPowerVector a 0)).symm
    _ = (soninAllPrimeCoupledTraceMoment a 0).re := congrArg Complex.re hinner
    _ = soninAllPrimeCoupledRealTraceMoment a 0 := rfl

/-- The actual coupled polynomial Gram value is exactly the abstract moment-functional square
value of the real coupled trace sequence. -/
theorem soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledPolynomialGramValue a p =
      HTGeometry.momentFunctional (soninAllPrimeCoupledRealTraceMoment a) (p ^ 2) := by
  let N : ℕ := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  have hN : p.natDegree < N := by omega
  have hp : Polynomial.ofFn N c = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hN
  calc
    soninAllPrimeCoupledPolynomialGramValue a p =
        c ⬝ᵥ (HTGeometry.momentHankelMatrix
          (soninAllPrimeCoupledRealTraceMoment a) N).mulVec c := by
      unfold soninAllPrimeCoupledPolynomialGramValue
      change
        (∑ i : Fin N, ∑ j : Fin N,
          ((c i * c j : ℝ) : ℂ) *
            soninAllPrimeCoupledGramBlock N a i j).re = _
      simp_rw [soninAllPrimeCoupledGramBlock_eq_traceMoment,
        soninAllPrimeCoupledTraceMoment_eq_ofReal]
      push_cast
      simp [dotProduct, Matrix.mulVec, HTGeometry.momentHankelMatrix,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = HTGeometry.momentFunctional
        (soninAllPrimeCoupledRealTraceMoment a)
        ((Polynomial.ofFn N c) ^ 2) :=
      HTGeometry.dotProduct_mulVec_momentHankelMatrix
        (soninAllPrimeCoupledRealTraceMoment a) N c
    _ = HTGeometry.momentFunctional
        (soninAllPrimeCoupledRealTraceMoment a) (p ^ 2) := by rw [hp]

/-- The complete coupled source trace-Hankel value is literally the squared norm of the actual
polynomial source vector. -/
theorem sequenceTraceHankel_soninAllPrimeCoupledRealTraceMoment_eq_norm_sq
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    sequenceTraceHankel (soninAllPrimeCoupledRealTraceMoment a) p =
      ‖soninAllPrimeCoupledPolynomialPowerVector a p‖ ^ 2 := by
  rw [sequenceTraceHankel_eq_momentFunctional,
    ← soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional,
    soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq]

/-- Every actual coupled source moment sequence belongs to the complete trace-Hankel cone. -/
theorem sequenceTraceHankelNonnegative_soninAllPrimeCoupledRealTraceMoment
    (a : SoninPositiveAperture) :
    SequenceTraceHankelNonnegative (soninAllPrimeCoupledRealTraceMoment a) := by
  intro p
  rw [sequenceTraceHankel_soninAllPrimeCoupledRealTraceMoment_eq_norm_sq]
  exact sq_nonneg _

/-- The vacuum--polynomial mixed Gram entry is the coupled moment functional evaluated on that
polynomial. -/
theorem inner_soninAllPrimeCoupledPowerVector_zero_polynomial
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    inner ℂ (soninAllPrimeCoupledPowerVector a 0)
        (soninAllPrimeCoupledPolynomialPowerVector a p) =
      (HTGeometry.momentFunctional
        (soninAllPrimeCoupledRealTraceMoment a) p : ℂ) := by
  let N : ℕ := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  let z : Fin N := ⟨0, by dsimp only [N]; omega⟩
  have hN : p.natDegree < N := by omega
  have hp : Polynomial.ofFn N c = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hN
  change inner ℂ (soninAllPrimeCoupledPowerVector a 0)
      (∑ i : Fin N, ((c i : ℝ) : ℂ) •
        soninAllPrimeCoupledPowerVector a (i : ℕ)) = _
  calc
    _ = ∑ i : Fin N, ((c i : ℝ) : ℂ) *
          inner ℂ (soninAllPrimeCoupledPowerVector a 0)
            (soninAllPrimeCoupledPowerVector a (i : ℕ)) := by
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_smul_right]
    _ = ∑ i : Fin N, ((c i : ℝ) : ℂ) *
          soninAllPrimeCoupledGramBlock N a z i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [soninAllPrimeCoupledGramBlock, Matrix.gram_apply]
    _ = ∑ i : Fin N, ((c i : ℝ) : ℂ) *
          soninAllPrimeCoupledTraceMoment a (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [soninAllPrimeCoupledGramBlock_eq_traceMoment]
      simp [z]
    _ = (∑ i : Fin N,
          c i * soninAllPrimeCoupledRealTraceMoment a (i : ℕ) : ℝ) := by
      simp_rw [soninAllPrimeCoupledTraceMoment_eq_ofReal]
      push_cast
      rfl
    _ = (HTGeometry.momentFunctional
          (soninAllPrimeCoupledRealTraceMoment a)
          (Polynomial.ofFn N c) : ℂ) := by
      rw [HTGeometry.momentFunctional_ofFn]
    _ = (HTGeometry.momentFunctional
          (soninAllPrimeCoupledRealTraceMoment a) p : ℂ) := by rw [hp]

/-- **Source projective/Feshbach value identity.**  The actual coupled projective quantum tangent
energy is exactly the vacuum Robertson determinant of the real coupled trace-moment sequence. -/
theorem soninAllPrimeCoupledProjectiveTangentEnergy_eq_sourceRobertson
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledProjectiveTangentEnergy a p =
      HTGeometry.momentVacuumRobertsonDeterminant
        (soninAllPrimeCoupledRealTraceMoment a) p := by
  unfold soninAllPrimeCoupledProjectiveTangentEnergy
    HTGeometry.projectiveGramTangentEnergy
    HTGeometry.momentVacuumRobertsonDeterminant
  rw [norm_soninAllPrimeCoupledPowerVector_zero_sq,
    ← soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq,
    soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional,
    inner_soninAllPrimeCoupledPowerVector_zero_polynomial,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Nondegenerate apertures give positive source vacuum mass. -/
theorem soninAllPrimeCoupledRealTraceMoment_zero_pos
    (a : SoninCoupledNondegenerateAperture) :
    0 < soninAllPrimeCoupledRealTraceMoment a.1 0 := by
  exact (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2

/-- The projective source value is the source vacuum mass times its Feshbach remainder. -/
theorem soninAllPrimeCoupledProjectiveTangentEnergy_eq_mass_mul_sourceFeshbach
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledProjectiveTangentEnergy a.1 p =
      soninAllPrimeCoupledRealTraceMoment a.1 0 *
        HTGeometry.momentVacuumFeshbachRemainder
          (soninAllPrimeCoupledRealTraceMoment a.1) p := by
  rw [soninAllPrimeCoupledProjectiveTangentEnergy_eq_sourceRobertson]
  exact HTGeometry.momentVacuumRobertsonDeterminant_eq_mul_feshbach
    (soninAllPrimeCoupledRealTraceMoment a.1)
    (soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne' p

/-- The dimensionless coupled pure-state quantum Fisher value is four times the intrinsic source
Feshbach remainder divided by the source vacuum mass. -/
theorem soninAllPrimeCoupledPureStateQuantumFisherValue_eq_sourceFeshbach
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledPureStateQuantumFisherValue a.1 p =
      4 * HTGeometry.momentVacuumFeshbachRemainder
          (soninAllPrimeCoupledRealTraceMoment a.1) p /
        soninAllPrimeCoupledRealTraceMoment a.1 0 := by
  rw [soninAllPrimeCoupledPureStateQuantumFisherValue,
    soninAllPrimeCoupledProjectiveTangentEnergy_eq_mass_mul_sourceFeshbach]
  change 4 * (soninAllPrimeCoupledRealTraceMoment a.1 0 *
      HTGeometry.momentVacuumFeshbachRemainder
        (soninAllPrimeCoupledRealTraceMoment a.1) p) /
      soninAllPrimeCoupledRealTraceMoment a.1 0 ^ 2 =
    4 * HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p /
      soninAllPrimeCoupledRealTraceMoment a.1 0
  field_simp [(soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne']

/-- The coupled pure-state quantum Fisher value is exactly four times the normalized variance of
the polynomial observable in the source moment state. -/
theorem soninAllPrimeCoupledPureStateQuantumFisherValue_eq_four_mul_normalizedVariance
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    soninAllPrimeCoupledPureStateQuantumFisherValue a.1 p =
      4 * HTGeometry.momentNormalizedVariance
        (soninAllPrimeCoupledRealTraceMoment a.1) p := by
  rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_sourceFeshbach,
    HTGeometry.momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
      (soninAllPrimeCoupledRealTraceMoment a.1)
      (soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne' p]
  field_simp [(soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne']

/-- For a monomial tangent, the coupled QFI is the elementary variance of two existing normalized
trace-moment ratios. -/
theorem soninAllPrimeCoupledPureStateQuantumFisherValue_X_pow_eq_traceRatios
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    soninAllPrimeCoupledPureStateQuantumFisherValue a.1 (X ^ n) =
      4 * (soninAllPrimeCoupledRealTraceMoment a.1 (n + n) /
          soninAllPrimeCoupledRealTraceMoment a.1 0 -
        (soninAllPrimeCoupledRealTraceMoment a.1 n /
          soninAllPrimeCoupledRealTraceMoment a.1 0) ^ 2) := by
  rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_four_mul_normalizedVariance,
    HTGeometry.momentNormalizedVariance_X_pow]

/-- Every intrinsic coupled source Feshbach value is nonnegative. -/
theorem soninAllPrimeCoupledSourceFeshbach_nonneg
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    0 ≤ HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p := by
  apply (HTGeometry.momentVacuumFeshbachRemainder_nonneg_iff_robertson
    (soninAllPrimeCoupledRealTraceMoment a.1)
    (soninAllPrimeCoupledRealTraceMoment_zero_pos a) p).2
  rw [← soninAllPrimeCoupledProjectiveTangentEnergy_eq_sourceRobertson]
  exact soninAllPrimeCoupledProjectiveTangentEnergy_nonneg a.1 p

/-- Every scalar-shifted actual source norm bounds the intrinsic source Feshbach value below. -/
theorem sourceFeshbach_le_norm_soninAllPrimeCoupledPolynomialShift
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) (c : ℝ) :
    HTGeometry.momentVacuumFeshbachRemainder
        (soninAllPrimeCoupledRealTraceMoment a.1) p ≤
      ‖soninAllPrimeCoupledPolynomialPowerVector a.1 (p - C c)‖ ^ 2 := by
  rw [← soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq,
    soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional]
  exact HTGeometry.momentVacuumFeshbachRemainder_le_shifted_sq
    (soninAllPrimeCoupledRealTraceMoment a.1)
    (soninAllPrimeCoupledRealTraceMoment_zero_pos a) p c

/-- The source Feshbach value is attained by an actual scalar-shifted polynomial source norm.
This closes the value-level counterterm minimization without a coefficient-linearity premise. -/
theorem exists_norm_soninAllPrimeCoupledPolynomialShift_eq_sourceFeshbach
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    ∃ c : ℝ,
      ‖soninAllPrimeCoupledPolynomialPowerVector a.1 (p - C c)‖ ^ 2 =
        HTGeometry.momentVacuumFeshbachRemainder
          (soninAllPrimeCoupledRealTraceMoment a.1) p := by
  obtain ⟨c, hc⟩ := HTGeometry.exists_shifted_sq_eq_momentVacuumFeshbachRemainder
    (soninAllPrimeCoupledRealTraceMoment a.1)
    (soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne' p
  refine ⟨c, ?_⟩
  rw [← soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq,
    soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional]
  exact hc

/-- The optimizer in the preceding source minimization is the explicit source moment mean. -/
theorem norm_soninAllPrimeCoupledCanonicalPolynomialShift_sq_eq_sourceFeshbach
    (a : SoninCoupledNondegenerateAperture) (p : Polynomial ℝ) :
    ‖soninAllPrimeCoupledPolynomialPowerVector a.1
        (HTGeometry.momentVacuumCenteredPolynomial
          (soninAllPrimeCoupledRealTraceMoment a.1) p)‖ ^ 2 =
      HTGeometry.momentVacuumFeshbachRemainder
        (soninAllPrimeCoupledRealTraceMoment a.1) p := by
  rw [← soninAllPrimeCoupledPolynomialGramValue_eq_norm_sq,
    soninAllPrimeCoupledPolynomialGramValue_eq_momentFunctional]
  exact HTGeometry.momentFunctional_momentVacuumCenteredPolynomial_sq
    (soninAllPrimeCoupledRealTraceMoment a.1)
    (soninAllPrimeCoupledRealTraceMoment_zero_pos a).ne' p

/-- Moment-only form of the weakest coupled source comparison.  It compares the canonically
profiled source and target vacuum Feshbach values and contains neither a vector nor a scalar
counterterm. -/
def SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            HTGeometry.momentVacuumFeshbachRemainder
              (soninAllPrimeCoupledRealTraceMoment a.1)
              (q.map (Int.castRingHom ℝ)) ≤
          (HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            soninAllPrimeCoupledRealTraceMoment a.1 0

/-- Dimensionless pure-state quantum-Fisher form of the weakest coupled source comparison.  The
positive source mass has cancelled completely. -/
def SoninCoupledPrimeArchPureStateQuantumFisherUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            soninAllPrimeCoupledPureStateQuantumFisherValue a.1
              (q.map (Int.castRingHom ℝ)) ≤
          4 * (HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
            (q.map (Int.castRingHom ℝ)) + ε)

/-- Normalized-state variance form of the weakest coupled source comparison.  Every projective,
Feshbach, mass, and conventional factor-four term has been eliminated. -/
def SoninCoupledPrimeArchNormalizedVarianceUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            HTGeometry.momentNormalizedVariance
              (soninAllPrimeCoupledRealTraceMoment a.1)
              (q.map (Int.castRingHom ℝ)) ≤
          normalizedPrimeArchMoment 0 *
              HTGeometry.momentNormalizedVariance normalizedPrimeArchMoment
                (q.map (Int.castRingHom ℝ)) + ε

/-- Small-source-variance boundary case: every fixed zero-constant test admits nondegenerate
apertures with arbitrarily small normalized source variance. -/
def SoninCoupledPrimeArchNormalizedVarianceCollapseToZero : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ δ : ℝ, 0 < δ →
      ∃ a : SoninCoupledNondegenerateAperture,
        HTGeometry.momentNormalizedVariance
            (soninAllPrimeCoupledRealTraceMoment a.1)
            (q.map (Int.castRingHom ℝ)) ≤ δ

/-- The dimensionless quantum-Fisher comparison is exactly the normalized source--target variance
comparison. -/
theorem soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_normalizedVariance :
    SoninCoupledPrimeArchPureStateQuantumFisherUpperBound ↔
      SoninCoupledPrimeArchNormalizedVarianceUpperBound := by
  constructor
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceVar : ℝ := HTGeometry.momentNormalizedVariance
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetVar : ℝ := HTGeometry.momentNormalizedVariance
      normalizedPrimeArchMoment p
    rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_four_mul_normalizedVariance,
      HTGeometry.momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
        normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne'] at ha
    change normalizedPrimeArchMoment 0 * (4 * sourceVar) ≤
      4 * (normalizedPrimeArchMoment 0 * targetVar + ε) at ha
    change normalizedPrimeArchMoment 0 * sourceVar ≤
      normalizedPrimeArchMoment 0 * targetVar + ε
    nlinarith
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceVar : ℝ := HTGeometry.momentNormalizedVariance
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetVar : ℝ := HTGeometry.momentNormalizedVariance
      normalizedPrimeArchMoment p
    rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_four_mul_normalizedVariance,
      HTGeometry.momentVacuumFeshbachRemainder_eq_mass_mul_normalizedVariance
        normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
    change normalizedPrimeArchMoment 0 * (4 * sourceVar) ≤
      4 * (normalizedPrimeArchMoment 0 * targetVar + ε)
    change normalizedPrimeArchMoment 0 * sourceVar ≤
      normalizedPrimeArchMoment 0 * targetVar + ε at ha
    nlinarith

/-- Cancelling the positive source mass identifies the moment-Feshbach comparison exactly with a
dimensionless pure-state quantum-Fisher bound. -/
theorem soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_sourceFeshbach :
    SoninCoupledPrimeArchPureStateQuantumFisherUpperBound ↔
      SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound := by
  constructor
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      normalizedPrimeArchMoment p
    let sourceMass : ℝ := soninAllPrimeCoupledRealTraceMoment a.1 0
    have hmass : 0 < sourceMass := soninAllPrimeCoupledRealTraceMoment_zero_pos a
    rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_sourceFeshbach] at ha
    change normalizedPrimeArchMoment 0 * (4 * sourceRem / sourceMass) ≤
      4 * (targetRem + ε) at ha
    have hscaled := mul_le_mul_of_nonneg_right ha hmass.le
    have hleft :
        normalizedPrimeArchMoment 0 * (4 * sourceRem / sourceMass) * sourceMass =
          4 * (normalizedPrimeArchMoment 0 * sourceRem) := by
      field_simp [hmass.ne']
    have hright :
        4 * (targetRem + ε) * sourceMass =
          4 * ((targetRem + ε) * sourceMass) := by ring
    rw [hleft, hright] at hscaled
    nlinarith
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      normalizedPrimeArchMoment p
    let sourceMass : ℝ := soninAllPrimeCoupledRealTraceMoment a.1 0
    have hmass : 0 < sourceMass := soninAllPrimeCoupledRealTraceMoment_zero_pos a
    rw [soninAllPrimeCoupledPureStateQuantumFisherValue_eq_sourceFeshbach]
    change normalizedPrimeArchMoment 0 * (4 * sourceRem / sourceMass) ≤
      4 * (targetRem + ε)
    rw [show normalizedPrimeArchMoment 0 * (4 * sourceRem / sourceMass) =
        4 * (normalizedPrimeArchMoment 0 * sourceRem) / sourceMass by ring]
    apply (div_le_iff₀ hmass).2
    calc
      4 * (normalizedPrimeArchMoment 0 * sourceRem) ≤
          4 * ((targetRem + ε) * sourceMass) :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = 4 * (targetRem + ε) * sourceMass := by ring

/-- Cancelling the positive source vacuum mass makes the projective and moment-Feshbach source
interfaces exactly equivalent. -/
theorem soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_sourceFeshbach :
    SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound ↔
      SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound := by
  constructor
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      normalizedPrimeArchMoment p
    let sourceMass : ℝ := soninAllPrimeCoupledRealTraceMoment a.1 0
    have hmass : 0 < sourceMass := soninAllPrimeCoupledRealTraceMoment_zero_pos a
    have ha' :
        (normalizedPrimeArchMoment 0 * sourceRem) * sourceMass ≤
          ((targetRem + ε) * sourceMass) * sourceMass := by
      calc
        (normalizedPrimeArchMoment 0 * sourceRem) * sourceMass =
            normalizedPrimeArchMoment 0 *
              soninAllPrimeCoupledProjectiveTangentEnergy a.1 p := by
          rw [soninAllPrimeCoupledProjectiveTangentEnergy_eq_mass_mul_sourceFeshbach]
          ring
        _ ≤ (targetRem + ε) * sourceMass ^ 2 := by
          simpa only [p, targetRem, sourceMass,
            soninAllPrimeCoupledRealTraceMoment] using ha
        _ = ((targetRem + ε) * sourceMass) * sourceMass := by ring
    exact (mul_le_mul_iff_of_pos_right hmass).mp ha'
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let sourceRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    let targetRem : ℝ := HTGeometry.momentVacuumFeshbachRemainder
      normalizedPrimeArchMoment p
    let sourceMass : ℝ := soninAllPrimeCoupledRealTraceMoment a.1 0
    have hmass : 0 ≤ sourceMass :=
      (soninAllPrimeCoupledRealTraceMoment_zero_pos a).le
    have hscaled := mul_le_mul_of_nonneg_right ha hmass
    calc
      normalizedPrimeArchMoment 0 *
          soninAllPrimeCoupledProjectiveTangentEnergy a.1 p =
        (normalizedPrimeArchMoment 0 * sourceRem) * sourceMass := by
          rw [soninAllPrimeCoupledProjectiveTangentEnergy_eq_mass_mul_sourceFeshbach]
          ring
      _ ≤ ((targetRem + ε) * sourceMass) * sourceMass := hscaled
      _ = (targetRem + ε) * sourceMass ^ 2 := by ring

/-- The moment-Feshbach source interface is exactly the older aperture-plus-counterterm variance
interface: the former chooses the canonical minimizer, while the latter can never beat it. -/
theorem soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_variance :
    SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound ↔
      SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound := by
  constructor
  · intro h q hq ε hε
    obtain ⟨a, ha⟩ := h q hq ε hε
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    obtain ⟨c, hc⟩ :=
      exists_norm_soninAllPrimeCoupledPolynomialShift_eq_sourceFeshbach a p
    refine ⟨a, c, ?_⟩
    simpa only [p, hc, soninAllPrimeCoupledRealTraceMoment] using ha
  · intro h q hq ε hε
    obtain ⟨a, c, ha⟩ := h q hq ε hε
    refine ⟨a, ?_⟩
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    have hlower := sourceFeshbach_le_norm_soninAllPrimeCoupledPolynomialShift a p c
    have hscaled := mul_le_mul_of_nonneg_left hlower
      normalizedPrimeArchMoment_zero_pos.le
    exact hscaled.trans (by simpa only [p, soninAllPrimeCoupledRealTraceMoment] using ha)

/-- **Exact closure of the physics bridge.**  The counterterm-free projective quantum-Fisher
condition and the previous weakest source-variational condition are equivalent. -/
theorem soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_variance :
    SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound ↔
      SoninCoupledPrimeArchVacuumVarianceRayleighUpperBound :=
  soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_iff_sourceFeshbach.trans
    soninCoupledPrimeArchVacuumSourceFeshbachUpperBound_iff_variance

/-- The moment-only comparison directly forces every target vacuum Feshbach remainder to be
nonnegative. -/
theorem primeArchVacuumFeshbachIntNonnegative_of_soninCoupledSourceFeshbach
    (h : SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound) :
    PrimeArchVacuumFeshbachIntNonnegative := by
  intro q hq
  let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
  let target : ℝ := HTGeometry.momentVacuumFeshbachRemainder
    normalizedPrimeArchMoment p
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨a, ha⟩ := h q hq ε hε
  have hsource :
      0 ≤ normalizedPrimeArchMoment 0 *
        HTGeometry.momentVacuumFeshbachRemainder
          (soninAllPrimeCoupledRealTraceMoment a.1) p :=
    mul_nonneg normalizedPrimeArchMoment_zero_pos.le
      (soninAllPrimeCoupledSourceFeshbach_nonneg a p)
  have hmass : 0 < soninAllPrimeCoupledRealTraceMoment a.1 0 :=
    soninAllPrimeCoupledRealTraceMoment_zero_pos a
  have htargetε : target + ε < 0 := by
    dsimp only [ε]
    linarith
  have hright :
      (target + ε) * soninAllPrimeCoupledRealTraceMoment a.1 0 < 0 :=
    mul_neg_of_neg_of_pos htargetε hmass
  change normalizedPrimeArchMoment 0 *
      HTGeometry.momentVacuumFeshbachRemainder
        (soninAllPrimeCoupledRealTraceMoment a.1) p ≤
    (target + ε) * soninAllPrimeCoupledRealTraceMoment a.1 0 at ha
  linarith

/-- **Small-variance no-go.**  If the coupled source variance can collapse to zero for every
test, then the normalized source comparison is exactly target Feshbach positivity.  Under this
boundary behavior the comparison is a sign test, not an independent mechanism for proving the
target sign. -/
theorem soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_targetNonnegative_of_collapse
    (hcollapse : SoninCoupledPrimeArchNormalizedVarianceCollapseToZero) :
    SoninCoupledPrimeArchNormalizedVarianceUpperBound ↔
      PrimeArchVacuumFeshbachIntNonnegative := by
  constructor
  · intro h
    apply primeArchVacuumFeshbachIntNonnegative_of_soninCoupledSourceFeshbach
    apply soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_sourceFeshbach.mp
    exact soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_normalizedVariance.mpr h
  · intro htarget q hq ε hε
    let p : Polynomial ℝ := q.map (Int.castRingHom ℝ)
    let targetVar : ℝ := HTGeometry.momentNormalizedVariance
      normalizedPrimeArchMoment p
    have htargetVar : 0 ≤ targetVar := by
      apply (HTGeometry.momentNormalizedVariance_nonneg_iff_feshbach
        normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos p).2
      exact htarget q hq
    let δ : ℝ := ε / normalizedPrimeArchMoment 0
    have hδ : 0 < δ := div_pos hε normalizedPrimeArchMoment_zero_pos
    obtain ⟨a, ha⟩ := hcollapse q hq δ hδ
    refine ⟨a, ?_⟩
    let sourceVar : ℝ := HTGeometry.momentNormalizedVariance
      (soninAllPrimeCoupledRealTraceMoment a.1) p
    change normalizedPrimeArchMoment 0 * sourceVar ≤
      normalizedPrimeArchMoment 0 * targetVar + ε
    change sourceVar ≤ δ at ha
    have hscaled := mul_le_mul_of_nonneg_left ha normalizedPrimeArchMoment_zero_pos.le
    have hdelta : normalizedPrimeArchMoment 0 * δ = ε := by
      dsimp only [δ]
      field_simp [normalizedPrimeArchMoment_zero_pos.ne']
    rw [hdelta] at hscaled
    exact hscaled.trans (by
      nlinarith [mul_nonneg normalizedPrimeArchMoment_zero_pos.le htargetVar])

/-- Under source-variance collapse, the normalized-variance comparison is exactly RH. -/
theorem soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis_of_collapse
    (hcollapse : SoninCoupledPrimeArchNormalizedVarianceCollapseToZero) :
    SoninCoupledPrimeArchNormalizedVarianceUpperBound ↔ RiemannHypothesis :=
  (soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_targetNonnegative_of_collapse
    hcollapse).trans primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis

/-- The moment-only source-Feshbach comparison proves RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumSourceFeshbachUpperBound
    (h : SoninCoupledPrimeArchVacuumSourceFeshbachUpperBound) :
    RiemannHypothesis :=
  primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp
    (primeArchVacuumFeshbachIntNonnegative_of_soninCoupledSourceFeshbach h)

/-- The dimensionless pure-state quantum-Fisher comparison proves RH directly. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchPureStateQuantumFisherUpperBound
    (h : SoninCoupledPrimeArchPureStateQuantumFisherUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchVacuumSourceFeshbachUpperBound
    (soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_sourceFeshbach.mp h)

/-- The normalized source--target variance comparison proves RH directly. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchNormalizedVarianceUpperBound
    (h : SoninCoupledPrimeArchNormalizedVarianceUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchPureStateQuantumFisherUpperBound
    (soninCoupledPrimeArchPureStateQuantumFisherUpperBound_iff_normalizedVariance.mpr h)

end

end RHTower
