import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.InvariantForms
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.PairingForms
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.CurveTensorReceivers
import GaloisForLFunctions.ArithmeticKunnethTheory.KunnethPositivityIsPointCountPositivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.HTGeometry.Sl2CocycleUpperEntry

/-!
# The golden spectrum has the expected invariant tensor weights

The golden curve datum has Frobenius eigenvalues `√5 φ` and `√5 / φ`, with product `5`.
On every invariant form of degree `2k`, its Frobenius acts by `5^k`, exactly as the pure
scalar Frobenius `√5`. Nevertheless its normalized spectrum is impure. This is an
algebraic countermodel to extracting local purity from invariant weights alone.
It does not supply a sheaf on an arithmetic base or a global cohomological trace formula.
-/

open Matrix Real
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

/-- Frobenius with the two eigenvalues of the golden curve datum. -/
def goldenFrobenius : Matrix (Fin 2) (Fin 2) ℂ :=
  (√5 : ℂ) • sl2Torus (goldenRatio : ℂ)

/-- The scalar Frobenius with both eigenvalues equal to `√5`. -/
def pureScalarFrobenius : Matrix (Fin 2) (Fin 2) ℂ := (√5 : ℂ) • 1

theorem goldenFrobenius_eigenvalues (i : Fin 2) :
    goldenFrobenius i i = (goldenDatum.sqrtq : ℂ) * goldenDatum.β i := by
  fin_cases i <;> simp [goldenFrobenius, sl2Torus, goldenDatum, CurveDatum.sqrtq]

theorem goldenFrobenius_det : goldenFrobenius.det = 5 := by
  rw [goldenFrobenius, Matrix.det_smul, det_sl2Torus (by exact_mod_cast goldenRatio_ne_zero)]
  simp only [Fintype.card_fin, mul_one, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

theorem goldenFrobenius_trace : goldenFrobenius.trace = 5 := by
  have hs := sqrt_five_pow_sum 1
  simp only [pow_one, goldenLucas] at hs
  simp only [Matrix.trace, Fin.sum_univ_two, goldenFrobenius, Matrix.smul_apply,
    sl2Torus_apply_00, sl2Torus_apply_11, smul_eq_mul]
  exact_mod_cast hs

/-- The local characteristic factor has rational coefficients despite impurity. -/
theorem golden_euler_polynomial (t : ℂ) :
    Matrix.det (1 - t • goldenFrobenius) = 1 - 5 * t + 5 * t ^ 2 := by
  have h (A : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.det (1 - t • A) = 1 - A.trace * t + A.det * t ^ 2 := by
    simp [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
    ring
  rw [h, goldenFrobenius_det, goldenFrobenius_trace]

/-- The two Frobenius operators agree on every invariant tensor, in every degree. -/
theorem golden_eq_pure_on_invariants (n : ℕ) (f : invariantForms n) (v : Fin n → Plane) :
    f.val (fun i => goldenFrobenius.mulVec (v i)) =
      f.val (fun i => pureScalarFrobenius.mulVec (v i)) := by
  rw [goldenFrobenius, pureScalarFrobenius,
    invariant_scalar_mul n f _ _ (det_sl2Torus (by exact_mod_cast goldenRatio_ne_zero)),
    invariant_scalar_mul n f _ _ Matrix.det_one]

/-- Every even invariant has the weight prescribed by the determinant `5`. -/
theorem golden_invariant_weight (k : ℕ) (f : invariantForms (2 * k))
    (v : Fin (2 * k) → Plane) :
    f.val (fun i => goldenFrobenius.mulVec (v i)) = (5 : ℂ) ^ k * f.val v := by
  rw [invariant_even_det k f goldenFrobenius (by rw [goldenFrobenius_det]; norm_num),
    goldenFrobenius_det]

/-- All invariant weights are correct although the golden spectrum is impure. -/
theorem golden_invariant_weights_do_not_force_purity :
    (∀ k, ∀ f : invariantForms (2 * k), ∀ v,
      f.val (fun i => goldenFrobenius.mulVec (v i)) = (5 : ℂ) ^ k * f.val v) ∧
      ¬ (∀ i, ‖goldenDatum.β i‖ = 1) :=
  ⟨golden_invariant_weight, goldenDatum_not_unitary⟩

/-- Even tensor traces give nonnegative Euler coefficients, including on the impure datum. -/
theorem golden_even_tensor_coefficients_nonneg (k n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      sigmaCoeff (fun j => ((goldenDatum.trace j ^ (2 * k) : ℝ) : ℂ)) n = c := by
  apply exists_sigmaCoeff_eq_ofReal_nonneg
  intro j _
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- Correct invariant weights and positive local coefficients do not give a fixed base rate. -/
theorem golden_no_fixed_base_rate :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |goldenDatum.trace n| ^ (2 * (k + 1)) ≤ C * B ^ n := by
  rw [curve_fixed_base_tensor_bound_iff]
  exact goldenDatum_not_unitary

/-- The exact base rate in degree `m` is `φ^m`; the coefficient constant cannot reduce it. -/
theorem golden_tensor_rate_iff (m : ℕ) (hm : m ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    (∃ C : ℝ, ∀ n : ℕ, |goldenDatum.trace n| ^ m ≤ C * B ^ n) ↔ goldenRatio ^ m ≤ B := by
  have htrace (n : ℕ) : ‖∑ i, goldenDatum.β i ^ n‖ = |goldenDatum.trace n| := by
    change ‖goldenDatum.powerSum n‖ = _
    rw [goldenDatum.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
  have h := tensor_moment_bound_iff goldenDatum.β m hm hB
  simp only [htrace] at h
  rw [h]
  have h0 : ‖goldenDatum.β 0‖ = goldenRatio := by
    simp [goldenDatum, Complex.norm_real, abs_of_pos goldenRatio_pos]
  have h1 : ‖goldenDatum.β 1‖ = goldenRatio⁻¹ := by
    simp [goldenDatum, Complex.norm_real, abs_of_pos (inv_pos.mpr goldenRatio_pos)]
  refine ⟨fun hb => by simpa only [h0] using hb 0, fun hb i => ?_⟩
  fin_cases i
  · simpa only [h0] using hb
  · rw [h1]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr goldenRatio_pos.le)
      (((inv_le_one₀ goldenRatio_pos).mpr one_lt_goldenRatio.le).trans one_lt_goldenRatio.le) m).trans hb

/-- The obstruction persists at every even degree and concerns the global growth estimate. -/
theorem golden_weight_and_coefficient_countermodel :
    (∀ k, ∃ f : invariantForms (2 * k), f.val ≠ 0) ∧
    (∀ k, ∀ f : invariantForms (2 * k), ∀ v,
      f.val (fun i => goldenFrobenius.mulVec (v i)) = (5 : ℂ) ^ k * f.val v) ∧
    (∀ k n, ∃ c : ℝ, 0 ≤ c ∧
      sigmaCoeff (fun j => ((goldenDatum.trace j ^ (2 * k) : ℝ) : ℂ)) n = c) ∧
    ¬ (∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |goldenDatum.trace n| ^ (2 * (k + 1)) ≤ C * B ^ n) :=
  ⟨exists_nonzero_even_invariant, golden_invariant_weight,
    golden_even_tensor_coefficients_nonneg, golden_no_fixed_base_rate⟩

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
