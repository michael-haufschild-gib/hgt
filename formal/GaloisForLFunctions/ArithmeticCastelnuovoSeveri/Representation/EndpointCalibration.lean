import GaloisForLFunctions.HTGeometry.SymmetricCharacters.EndpointCoordinates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve

/-!
# Endpoint alphabets of curves and the principal-branch trap

The endpoint coordinate of a zero in the first positive period is real exactly when its
Frobenius eigenvalue is unitary. Principal zeros alone do not suffice: every principal endpoint
weight of the golden fake is positive real although the datum is not pure.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open SymmetricCharacters

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The first positive period avoids the real-axis exceptional locus of the endpoint map. -/
theorem zetaZero_one_im_ne_zero (i : ι) : (D.zetaZero i 1).im ≠ 0 := by
  have h := D.sq_le_sq_im_zetaZero i 1
  have hp : 0 < (D.period / 2) ^ 2 := sq_pos_of_pos (by linarith [D.period_pos])
  intro him
  rw [him] at h
  norm_num only [Int.cast_one, one_mul, zero_pow (by omega : 2 ≠ 0)] at h
  exact (not_le_of_gt hp) h

theorem zetaZero_re_eq_half_iff (i : ι) (k : ℤ) :
    (D.zetaZero i k).re = 1 / 2 ↔ ‖D.β i‖ = 1 := by
  rw [re_zetaZero]
  constructor
  · intro h
    have hdiv : Real.log ‖D.β i‖ / Real.log D.q = 0 := by linarith
    have hlog := (div_eq_zero_iff.mp hdiv).resolve_right D.log_q_pos.ne'
    have he := congrArg Real.exp hlog
    rwa [Real.exp_log (norm_pos_iff.mpr (D.β_ne_zero i)), Real.exp_zero] at he
  · intro h
    rw [h, Real.log_one, zero_div, add_zero]

/-- One nonzero periodic representative per eigenvalue is a complete reality test. -/
theorem endpoint_firstPeriod_real_iff (i : ι) :
    (endpointCoordinate (D.zetaZero i 1)).im = 0 ↔ ‖D.β i‖ = 1 := by
  rw [endpointCoordinate_im_eq_zero_iff, or_iff_left (D.zetaZero_one_im_ne_zero i),
    D.zetaZero_re_eq_half_iff]

/-- All periodic endpoint weights are positive real exactly for pure curve data. -/
theorem endpoint_alphabet_positive_iff_unitary :
    (∀ i k, (endpointCoordinate (D.zetaZero i k)).im = 0 ∧
      0 < (endpointCoordinate (D.zetaZero i k)).re) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h i
    exact (D.endpoint_firstPeriod_real_iff i).mp (h i 1).1
  · intro h i k
    have hr := (D.zetaZero_re_eq_half_iff i k).mpr (h i)
    exact ⟨(endpointCoordinate_im_eq_zero_iff _).mpr (Or.inl hr),
      endpointCoordinate_re_pos (by rw [hr]; norm_num) (by rw [hr]; norm_num)⟩

end CurveDatum

private theorem golden_log_ratio_bounds :
    0 < Real.log Real.goldenRatio / Real.log 5 ∧
      Real.log Real.goldenRatio / Real.log 5 < 1 / 2 := by
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨div_pos (Real.log_pos Real.one_lt_goldenRatio) hlog5, ?_⟩
  have hs : Real.goldenRatio ^ 2 < 5 := by
    nlinarith only [Real.goldenRatio_pos, Real.goldenRatio_lt_two]
  have hl := Real.log_lt_log (sq_pos_of_pos Real.goldenRatio_pos) hs
  rw [Real.log_pow] at hl
  rw [div_lt_iff₀ hlog5]
  norm_num only [Nat.cast_ofNat] at hl
  linarith

private theorem golden_principal_im (i : Fin 2) : (goldenDatum.zetaZero i 0).im = 0 := by
  rw [CurveDatum.im_zetaZero]
  have harg : Complex.arg (goldenDatum.β i) = 0 := by
    fin_cases i
    · exact Complex.arg_ofReal_of_nonneg Real.goldenRatio_pos.le
    · exact Complex.arg_ofReal_of_nonneg (inv_pos.mpr Real.goldenRatio_pos).le
  simp only [harg, Int.cast_zero, zero_mul, zero_div, add_zero]

private theorem golden_principal_strip (i : Fin 2) :
    0 < (goldenDatum.zetaZero i 0).re ∧ (goldenDatum.zetaZero i 0).re < 1 := by
  obtain ⟨h0, h1⟩ := golden_log_ratio_bounds
  rw [CurveDatum.re_zetaZero]
  change 0 < 1 / 2 + Real.log ‖goldenDatum.β i‖ / Real.log 5 ∧
    1 / 2 + Real.log ‖goldenDatum.β i‖ / Real.log 5 < 1
  fin_cases i
  · change 0 < 1 / 2 + Real.log ‖(Real.goldenRatio : ℂ)‖ / Real.log 5 ∧
      1 / 2 + Real.log ‖(Real.goldenRatio : ℂ)‖ / Real.log 5 < 1
    rw [Complex.norm_real, Real.norm_of_nonneg Real.goldenRatio_pos.le]
    constructor <;> linarith
  · change 0 < 1 / 2 + Real.log ‖((Real.goldenRatio⁻¹ : ℝ) : ℂ)‖ / Real.log 5 ∧
      1 / 2 + Real.log ‖((Real.goldenRatio⁻¹ : ℝ) : ℂ)‖ / Real.log 5 < 1
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr Real.goldenRatio_pos).le,
      Real.log_inv, neg_div]
    constructor <;> linarith

/-- The golden fake passes every reality and positivity test on principal endpoint weights. -/
theorem golden_principal_endpoint_positive (i : Fin 2) :
    (endpointCoordinate (goldenDatum.zetaZero i 0)).im = 0 ∧
      0 < (endpointCoordinate (goldenDatum.zetaZero i 0)).re := by
  exact ⟨(endpointCoordinate_im_eq_zero_iff _).mpr (Or.inr (golden_principal_im i)),
    endpointCoordinate_re_pos (golden_principal_strip i).1 (golden_principal_strip i).2⟩

/-- Periodic continuation exposes the defect hidden by the real principal branch. -/
theorem golden_endpoint_period_test :
    (∀ i, (endpointCoordinate (goldenDatum.zetaZero i 0)).im = 0 ∧
      0 < (endpointCoordinate (goldenDatum.zetaZero i 0)).re) ∧
    ¬ (∀ i, (endpointCoordinate (goldenDatum.zetaZero i 1)).im = 0) := by
  refine ⟨golden_principal_endpoint_positive, ?_⟩
  intro h
  exact goldenDatum_not_unitary (fun i => (goldenDatum.endpoint_firstPeriod_real_iff i).mp (h i))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
