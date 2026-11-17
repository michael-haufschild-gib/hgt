import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.ClippedPhaseCovariance
import GaloisForLFunctions.HTGeometry.InfinitesimalCompressionCurvature
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The minimum-energy carrier of the actual signed Weil pairing

The conjugate conductor-four phase represents the signed row pairing in the
finite class Hilbert space. Orthogonal projection onto its line retains that
pairing exactly. The discarded component has zero pairing and contributes an
exact nonnegative energy defect. Thus the projected vector is the unique
minimum-norm representative of every prescribed signed pairing, including
the class masses of every finite order-six row sum.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

local instance : Finite ResidueFour :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
local instance : Fintype ResidueFour := Fintype.ofFinite _

abbrev ClassHilbert := EuclideanSpace ℂ ResidueFour

def classVector (f : ResidueFour → ℂ) : ClassHilbert := WithLp.toLp 2 f

/-- The Riesz vector of the bilinear signed Weil-phase sum. -/
def phaseVector : ClassHilbert := classVector (fun r => star (phase r))

theorem inner_phaseVector (f : ResidueFour → ℂ) :
    inner ℂ phaseVector (classVector f) = weightedSum f := by
  rw [PiLp.inner_apply]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro r _
  change inner ℂ (star (phase r)) (f r) = phase r * f r
  rw [RCLike.inner_apply]
  change f r * star (star (phase r)) = phase r * f r
  rw [star_star, mul_comm]

theorem phaseVector_ne_zero : phaseVector ≠ 0 := by
  intro h
  have he := congrArg (fun v : ClassHilbert => v (1 : ResidueFour)) h
  change star (phase (1 : ResidueFour)) = 0 at he
  rw [phase_one, star_one] at he
  exact one_ne_zero he

/-- The exact positive local normalization constant of the phase line. -/
def phaseMass : ℝ := ‖phaseVector‖ ^ 2

theorem phaseMass_pos : 0 < phaseMass := sq_pos_of_pos (norm_pos_iff.mpr phaseVector_ne_zero)

theorem phaseMass_eq_sum : phaseMass = ∑ r : ResidueFour, ‖phase r‖ ^ 2 := by
  rw [phaseMass, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r _
  change ‖star (phase r)‖ ^ 2 = ‖phase r‖ ^ 2
  rw [norm_star]

def phaseLine : Submodule ℂ ClassHilbert := ℂ ∙ phaseVector

/-- The canonical class vector with the same signed pairing and minimum energy. -/
def coherentClassVector (f : ResidueFour → ℂ) : ClassHilbert :=
  phaseLine.starProjection (classVector f)

theorem coherentClassVector_formula (f : ResidueFour → ℂ) :
    coherentClassVector f = (weightedSum f / (phaseMass : ℂ)) • phaseVector := by
  change (ℂ ∙ phaseVector).starProjection (classVector f) = _
  rw [Submodule.starProjection_singleton, inner_phaseVector]
  rfl

/-- Projection preserves the actual signed pairing exactly. -/
theorem coherentClassVector_pairing (f : ResidueFour → ℂ) :
    inner ℂ phaseVector (coherentClassVector f) = weightedSum f := by
  have hv : inner ℂ phaseVector phaseVector = (phaseMass : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (algebraMap ℝ ℂ) ‖phaseVector‖ ^ 2 = (algebraMap ℝ ℂ) (‖phaseVector‖ ^ 2)
    exact (map_pow _ _ _).symm
  rw [coherentClassVector_formula, inner_smul_right, hv]
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt phaseMass_pos))

theorem weightedSum_coherentClassVector (f : ResidueFour → ℂ) :
    weightedSum (coherentClassVector f).ofLp = weightedSum f := by
  rw [← inner_phaseVector]
  exact coherentClassVector_pairing f

theorem phase_residual_pairing_zero (f : ResidueFour → ℂ) :
    inner ℂ phaseVector (classVector f - coherentClassVector f) = 0 := by
  rw [inner_sub_right, inner_phaseVector, coherentClassVector_pairing, sub_self]

/-- The retained energy is the squared signed pairing divided by the exact phase mass. -/
theorem coherentClassVector_energy (f : ResidueFour → ℂ) :
    ‖coherentClassVector f‖ ^ 2 = ‖weightedSum f‖ ^ 2 / phaseMass := by
  rw [coherentClassVector_formula, norm_smul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos phaseMass_pos, mul_pow, div_pow]
  change (‖weightedSum f‖ ^ 2 / phaseMass ^ 2) * phaseMass = _
  field_simp [ne_of_gt phaseMass_pos]

/-- Exact orthogonal decomposition into the visible signed pairing and its invisible residual. -/
theorem phase_energy_decomposition (f : ResidueFour → ℂ) :
    ‖coherentClassVector f‖ ^ 2 + ‖classVector f - coherentClassVector f‖ ^ 2 =
      ‖classVector f‖ ^ 2 := by
  have h := HTGeometry.norm_sq_causalCompression_add_orthogonalLeakage
    phaseLine (1 : ClassHilbert →L[ℂ] ClassHilbert) (fun x => rfl) (classVector f)
  change ‖coherentClassVector f‖ * ‖coherentClassVector f‖ +
    ‖classVector f - coherentClassVector f‖ * ‖classVector f - coherentClassVector f‖ =
      ‖classVector f‖ * ‖classVector f‖ at h
  simpa only [pow_two] using h

/-- Every vector with the same signed pairing has at least the canonical carrier's norm. -/
theorem coherentClassVector_minimum (f g : ResidueFour → ℂ)
    (hpair : weightedSum g = weightedSum f) : ‖coherentClassVector f‖ ≤ ‖classVector g‖ := by
  have he : coherentClassVector g = coherentClassVector f := by
    rw [coherentClassVector_formula, coherentClassVector_formula, hpair]
  have h := phase_energy_decomposition g
  rw [he] at h
  nlinarith only [h, sq_nonneg ‖classVector g - coherentClassVector f‖,
    norm_nonneg (coherentClassVector f), norm_nonneg (classVector g)]

/-- The minimum is attained only by the canonical phase carrier. -/
theorem coherentClassVector_minimum_eq_iff (f g : ResidueFour → ℂ)
    (hpair : weightedSum g = weightedSum f) :
    ‖classVector g‖ = ‖coherentClassVector f‖ ↔ classVector g = coherentClassVector f := by
  constructor
  · intro heq
    have he : coherentClassVector g = coherentClassVector f := by
      rw [coherentClassVector_formula, coherentClassVector_formula, hpair]
    have h := phase_energy_decomposition g
    rw [he, heq] at h
    have hz : ‖classVector g - coherentClassVector f‖ = 0 := by
      nlinarith only [h, norm_nonneg (classVector g - coherentClassVector f)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [h]

/-- Sharp energy accounting for the literal finite arithmetic row sum. -/
theorem finite_row_sum_phase_energy (S : Finset O) (w : O → ℂ) :
    ‖∑ c ∈ S, fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c‖ ^ 2 +
      phaseMass * ‖classVector (gaussSquareClassMass S w) -
        coherentClassVector (gaussSquareClassMass S w)‖ ^ 2 =
      phaseMass * ‖classVector (gaussSquareClassMass S w)‖ ^ 2 := by
  rw [finite_row_sum_eq_projected, weightedSum_eq_projected]
  have h := phase_energy_decomposition (gaussSquareClassMass S w)
  rw [coherentClassVector_energy] at h
  have hmul := congrArg (fun t : ℝ => t * phaseMass) h
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt phaseMass_pos)] at hmul
  nlinarith only [hmul]

#print axioms weightedSum_coherentClassVector
#print axioms coherentClassVector_minimum
#print axioms coherentClassVector_minimum_eq_iff
#print axioms finite_row_sum_phase_energy

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
