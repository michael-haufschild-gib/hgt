import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSourceSmoothing
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CoprimalityMasksAndSexticRows
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.FixedCuspShapes

/-!
# Angular phases of fixed cusp denominators

Sixfold jet increments remove the unit rotation in a fixed cusp coordinate. Their extra
phase depends multiplicatively on the original denominator and has modulus one away from
zero. Thus angular reflection changes fixed cusp amplitudes by separated unit phases.
-/

open Complex
open scoped ComplexConjugate Classical MatrixGroups Matrix BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

private lemma neg_sixth_pow (z : ℂ) : (-z) ^ 6 = z ^ 6 := by ring

private lemma angular_phase_unit_div (k : ℕ) (z u : ℂ) (hu : u ^ 6 = 1) :
    (-conj (z / u) / (z / u)) ^ (6 * k) = (-conj z / z) ^ (6 * k) := by
  have hcu : conj u ^ 6 = 1 := by rw [← map_pow, hu, map_one]
  rw [pow_mul, pow_mul]
  congr 1
  simp only [map_div₀, div_pow, neg_sixth_pow, hu, hcu, div_one]

private lemma angular_phase_unit_mul (k : ℕ) (z u : ℂ) (hu : u ^ 6 = 1) :
    (-conj (z * u) / (z * u)) ^ (6 * k) = (-conj z / z) ^ (6 * k) := by
  have hcu : conj u ^ 6 = 1 := by rw [← map_pow, hu, map_one]
  rw [pow_mul, pow_mul]
  congr 1
  simp only [div_pow, neg_sixth_pow, map_mul, mul_pow, hu, hcu, mul_one]

/-- The extra angular factor is a multiplicative phase of the cusp denominator. -/
def angularCuspDenominatorPhase (k : ℕ) : O →* ℂ where
  toFun c := (-conj (ringComplex c) / ringComplex c) ^ (6 * k)
  map_one' := by simp only [map_one, div_one, pow_mul]; norm_num
  map_mul' c d := by
    simp only [map_mul, pow_mul, neg_sixth_pow, mul_pow,
      div_eq_mul_inv, mul_inv_rev]
    ring

lemma angularCuspDenominatorPhase_norm (k : ℕ) (c : O) (hc : c ≠ 0) :
    ‖angularCuspDenominatorPhase k c‖ = 1 := by
  change ‖(-conj (ringComplex c) / ringComplex c) ^ (6 * k)‖ = 1
  rw [norm_pow, norm_div, norm_neg, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)), one_pow]

/-- Unit changes of the lower cusp entry disappear at sixfold jet increments. -/
lemma fixedMatrixCusp_angular_phase (M : SL(2, O)) (hc : M 1 0 ≠ 0) (k : ℕ) :
    (-conj ((fixedMatrixCusp M hc).matrix 1 0) / (fixedMatrixCusp M hc).matrix 1 0) ^ (6 * k) =
      angularCuspDenominatorPhase k (M 1 0) := by
  obtain ⟨u, hu⟩ := (fixedCuspTriangular_properties (fixedCuspSector M)).2.1
  have hu6 : ringComplex (fixedCuspTriangular (fixedCuspSector M) 0 0) ^ 6 = 1 := by
    rw [← hu, ← map_pow, CanonicalRowCompletion.unit_pow_six, map_one]
  rw [fixedMatrixCusp_lower]
  exact angular_phase_unit_div k _ _ hu6

/-- The angular smoothing multiplier differs by exactly the denominator phase. -/
lemma SourceCuspDatum.angularSmoothingMultiplier_eq (d : SourceCuspDatum) (k : ℕ) :
    d.angularSmoothingMultiplier k = d.smoothingMultiplier *
      (-conj (d.matrix 1 0) / d.matrix 1 0) ^ (6 * k) := by
  rw [SourceCuspDatum.angularSmoothingMultiplier, d.jetMultiplier_six_mul,
    SourceCuspDatum.smoothingMultiplier]
  ring

lemma fixedMatrixCusp_angularSmoothingMultiplier (M : SL(2, O)) (hc : M 1 0 ≠ 0) (k : ℕ) :
    (fixedMatrixCusp M hc).angularSmoothingMultiplier k =
      (fixedMatrixCusp M hc).smoothingMultiplier * angularCuspDenominatorPhase k (M 1 0) := by
  rw [SourceCuspDatum.angularSmoothingMultiplier_eq, fixedMatrixCusp_angular_phase]

/-- Removing any fixed upper triangular cusp factor leaves the same angular phase. -/
lemma FixedCuspShape.datum_angular_phase {H : SL(2, O)} (s : FixedCuspShape H)
    (g : rationalExtension) (h : ((g : SL(2, O)) * H) 1 0 ≠ 0) (k : ℕ) :
    (-conj ((s.datum g h).matrix 1 0) / (s.datum g h).matrix 1 0) ^ (6 * k) =
      angularCuspDenominatorPhase k (((g : SL(2, O)) * H) 1 0) := by
  have hu6 : ringComplex (s.upper 1 1) ^ 6 = 1 := by
    obtain ⟨u, hu⟩ := s.lower_unit
    rw [← hu, ← map_pow, CanonicalRowCompletion.unit_pow_six, map_one]
  rw [s.datum_matrix, integralComplexMatrix_apply,
    upper_right_removed_bottom _ _ s.lower_zero, map_mul]
  exact angular_phase_unit_mul k _ _ hu6

lemma FixedCuspShape.datum_angularSmoothingMultiplier {H : SL(2, O)}
    (s : FixedCuspShape H) (g : rationalExtension)
    (h : ((g : SL(2, O)) * H) 1 0 ≠ 0) (k : ℕ) :
    (s.datum g h).angularSmoothingMultiplier k =
      (s.datum g h).smoothingMultiplier *
        angularCuspDenominatorPhase k (((g : SL(2, O)) * H) 1 0) := by
  rw [SourceCuspDatum.angularSmoothingMultiplier_eq, s.datum_angular_phase]

/-- The angular phase of a controlled cusp separates into its fixed denominator and
prime factors, independently of the finite Fourier residue. -/
lemma ControlledStratumArithmetic.datum_angularSmoothingMultiplier
    {ι : Type*} [Fintype ι] {p : ι → O} {N a0 c0 : O} {mode : Bool}
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hN : (9 : O) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (fixedCusp a0 c0 mode)) (hp : ∀ i, p i ≠ 0)
    (hc0 : c0 ≠ 0) (v : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (k : ℕ) :
    (D.datum hN hr hbase s hp hc0 v).angularSmoothingMultiplier k =
      (D.datum hN hr hbase s hp hc0 v).smoothingMultiplier *
        (angularCuspDenominatorPhase k c0 * ∏ i, angularCuspDenominatorPhase k (p i)) := by
  rw [ControlledStratumArithmetic.datum, s.datum_angularSmoothingMultiplier,
    D.sourceGamma_mul, D.denominator, map_mul, map_prod]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
