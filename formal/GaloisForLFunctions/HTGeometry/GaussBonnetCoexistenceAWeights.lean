import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernel

/-!
# Physical parameter weights for logarithmic-entropy coexistence

Solve the positivity problem exposed by the model-A equal-temperature and
equal-Gibbs equations of arXiv:2609.00025. The actual positive log kernel
controls a quadratic charge constraint. Its positive root supplies a full
angular family with positive temperature, pressure, and effective charge,
including the uncharged endpoint, without assumed physical inequalities.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceAQuadraticA (τ : ℝ) : ℝ := 4 * egbCoexistenceALogKernel τ * (thermalRatio τ ^ 2 + 1)
def egbCoexistenceAQuadraticB (τ : ℝ) : ℝ :=
  8 * thermalRatio τ * (thermalRatio τ ^ 2 + thermalRatio τ + 1) +
    egbCoexistenceShape τ * (thermalRatio τ ^ 2 + 1) - 4 * thermalRatio τ ^ 2 * egbCoexistenceALogKernel τ
def egbCoexistenceAQuadraticC (τ : ℝ) : ℝ := thermalRatio τ ^ 2 * (thermalRatio τ ^ 2 + 1)
def egbCoexistenceAMaxCoupling (τ : ℝ) : ℝ :=
  2 * egbCoexistenceAQuadraticC τ / (egbCoexistenceAQuadraticB τ +
    sqrt (egbCoexistenceAQuadraticB τ ^ 2 + 4 * egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ))
def egbCoexistenceACouplingWeight (τ θ : ℝ) : ℝ := egbCoexistenceAMaxCoupling τ * sin θ ^ 2
def egbCoexistenceADenominator (τ θ : ℝ) : ℝ :=
  egbCoexistenceShape τ + 4 * egbCoexistenceACouplingWeight τ θ * egbCoexistenceALogKernel τ
def egbCoexistenceATemperatureWeight (τ θ : ℝ) : ℝ := 4 * (thermalRatio τ + 1) / egbCoexistenceADenominator τ θ
def egbCoexistenceAPressureWeight (τ θ : ℝ) : ℝ :=
  (3 * (thermalRatio τ ^ 2 + 1) + 4 * egbCoexistenceACouplingWeight τ θ * (2 - egbCoexistenceALogKernel τ)) /
    (egbCoexistenceADenominator τ θ * (thermalRatio τ ^ 2 + 1))
def egbCoexistenceAChargeWeight (τ θ : ℝ) : ℝ :=
  (thermalRatio τ ^ 2 * egbCoexistenceADenominator τ θ -
    4 * thermalRatio τ * (thermalRatio τ ^ 2 + 2 * egbCoexistenceACouplingWeight τ θ * (thermalRatio τ ^ 2 + thermalRatio τ + 1))) /
      (egbCoexistenceADenominator τ θ * (thermalRatio τ ^ 2 + 1))
def egbCoexistenceAChargeFactor (τ θ : ℝ) : ℝ :=
  egbCoexistenceAMaxCoupling τ * (egbCoexistenceAQuadraticB τ + egbCoexistenceAQuadraticA τ *
    (egbCoexistenceAMaxCoupling τ + egbCoexistenceACouplingWeight τ θ)) /
      (egbCoexistenceADenominator τ θ * (thermalRatio τ ^ 2 + 1))

theorem egbCoexistenceAQuadraticA_pos (τ : ℝ) : 0 < egbCoexistenceAQuadraticA τ := by
  have h := egbCoexistenceALogKernel_pos τ
  unfold egbCoexistenceAQuadraticA
  positivity

theorem egbCoexistenceAQuadraticC_pos (τ : ℝ) : 0 < egbCoexistenceAQuadraticC τ := by
  have h := thermalRatio_pos τ
  unfold egbCoexistenceAQuadraticC
  positivity

theorem egbCoexistenceAQuadraticB_lower_bound (τ : ℝ) :
    egbCoexistenceShape τ * (thermalRatio τ ^ 2 + 1) < egbCoexistenceAQuadraticB τ := by
  have hz := thermalRatio_pos τ
  have hk := (le_div_iff₀ hz).1 (egbCoexistenceALogKernel_upper_bound τ)
  have hm := mul_nonneg (show 0 ≤ 4 * thermalRatio τ by positivity) (sub_nonneg.mpr hk)
  have hp : 0 < thermalRatio τ * (thermalRatio τ ^ 2 + thermalRatio τ + 1) := by positivity
  unfold egbCoexistenceAQuadraticB
  nlinarith

theorem egbCoexistenceAQuadraticB_pos (τ : ℝ) : 0 < egbCoexistenceAQuadraticB τ := by
  have h := egbCoexistenceShape_pos τ
  have hp : 0 < egbCoexistenceShape τ * (thermalRatio τ ^ 2 + 1) := by positivity
  exact lt_trans hp (egbCoexistenceAQuadraticB_lower_bound τ)

theorem egbCoexistenceAMaxCoupling_pos (τ : ℝ) : 0 < egbCoexistenceAMaxCoupling τ := by
  have hB := egbCoexistenceAQuadraticB_pos τ
  have hC := egbCoexistenceAQuadraticC_pos τ
  unfold egbCoexistenceAMaxCoupling
  positivity

/-- The positive root solves the exact charge-positivity boundary equation. -/
theorem egbCoexistenceAMaxCoupling_quadratic (τ : ℝ) :
    egbCoexistenceAQuadraticA τ * egbCoexistenceAMaxCoupling τ ^ 2 +
      egbCoexistenceAQuadraticB τ * egbCoexistenceAMaxCoupling τ - egbCoexistenceAQuadraticC τ = 0 := by
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hB := egbCoexistenceAQuadraticB_pos τ
  have hC := egbCoexistenceAQuadraticC_pos τ
  have hs := sq_sqrt (show 0 ≤ egbCoexistenceAQuadraticB τ ^ 2 +
    4 * egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ by positivity)
  rw [show egbCoexistenceAQuadraticB τ ^ 2 + 4 * egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ =
    egbCoexistenceAQuadraticB τ ^ 2 + egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ * 4 by ring] at hs
  unfold egbCoexistenceAMaxCoupling
  field_simp
  linear_combination -egbCoexistenceAQuadraticC τ * hs

theorem egbCoexistenceAMaxCoupling_upper_bound (τ : ℝ) :
    egbCoexistenceAMaxCoupling τ < thermalRatio τ ^ 2 / egbCoexistenceShape τ := by
  have hm := egbCoexistenceAMaxCoupling_pos τ
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hD := egbCoexistenceShape_pos τ
  have hq := egbCoexistenceAMaxCoupling_quadratic τ
  have hpos : 0 < egbCoexistenceAQuadraticA τ * egbCoexistenceAMaxCoupling τ ^ 2 := by positivity
  have hBc : egbCoexistenceAQuadraticB τ * egbCoexistenceAMaxCoupling τ < egbCoexistenceAQuadraticC τ := by linarith
  have hmul := mul_lt_mul_of_pos_right (egbCoexistenceAQuadraticB_lower_bound τ) hm
  have hl := lt_trans hmul hBc
  unfold egbCoexistenceAQuadraticC at hl
  apply (lt_div_iff₀ hD).2
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) (show 0 ≤ thermalRatio τ ^ 2 + 1 by positivity)
  nlinarith

theorem egbCoexistenceACouplingWeight_bounds (τ θ : ℝ) :
    0 ≤ egbCoexistenceACouplingWeight τ θ ∧ egbCoexistenceACouplingWeight τ θ ≤ egbCoexistenceAMaxCoupling τ := by
  have hm := egbCoexistenceAMaxCoupling_pos τ
  have ht := sin_sq_add_cos_sq θ
  unfold egbCoexistenceACouplingWeight
  constructor
  · positivity
  · nlinarith [mul_nonneg (le_of_lt hm) (sq_nonneg (cos θ))]

theorem egbCoexistenceACouplingWeight_upper_bound (τ θ : ℝ) :
    egbCoexistenceACouplingWeight τ θ < thermalRatio τ ^ 2 / egbCoexistenceShape τ :=
  lt_of_le_of_lt (egbCoexistenceACouplingWeight_bounds τ θ).2 (egbCoexistenceAMaxCoupling_upper_bound τ)

theorem egbCoexistenceADenominator_pos (τ θ : ℝ) : 0 < egbCoexistenceADenominator τ θ := by
  have hD := egbCoexistenceShape_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hH := egbCoexistenceALogKernel_pos τ
  unfold egbCoexistenceADenominator
  positivity

theorem egbCoexistenceATemperatureWeight_pos (τ θ : ℝ) : 0 < egbCoexistenceATemperatureWeight τ θ := by
  have hD := egbCoexistenceADenominator_pos τ θ
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceATemperatureWeight
  positivity

theorem egbCoexistenceAPressureWeight_pos (τ θ : ℝ) : 0 < egbCoexistenceAPressureWeight τ θ := by
  have hz := thermalRatio_pos τ
  have hD := egbCoexistenceShape_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hbU := egbCoexistenceACouplingWeight_upper_bound τ θ
  have hH := egbCoexistenceALogKernel_upper_bound τ
  have hG : 0 < thermalRatio τ ^ 2 - thermalRatio τ + 1 := by nlinarith [sq_nonneg (thermalRatio τ - 1 / 2)]
  have he : (thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ - 2 =
      (thermalRatio τ ^ 2 - thermalRatio τ + 1) / thermalRatio τ := by field_simp; ring
  have hG' : 0 < (thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ - 2 := by rw [he]; positivity
  have h₁ := mul_le_mul_of_nonneg_left (show egbCoexistenceALogKernel τ - 2 ≤
    (thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ - 2 by linarith) hb
  have h₂ := mul_lt_mul_of_pos_right hbU hG'
  have h₃ : 4 * ((thermalRatio τ ^ 2 / egbCoexistenceShape τ) *
      ((thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ - 2)) < 3 * (thermalRatio τ ^ 2 + 1) := by
    have heq : 4 * ((thermalRatio τ ^ 2 / egbCoexistenceShape τ) *
        ((thermalRatio τ ^ 2 + thermalRatio τ + 1) / thermalRatio τ - 2)) =
      (4 * thermalRatio τ * (thermalRatio τ ^ 2 - thermalRatio τ + 1)) / egbCoexistenceShape τ := by field_simp; ring
    rw [heq, div_lt_iff₀ hD]
    unfold egbCoexistenceShape
    have hp : 0 < 3 * thermalRatio τ ^ 4 + 8 * thermalRatio τ ^ 3 + 10 * thermalRatio τ ^ 2 + 8 * thermalRatio τ + 3 := by positivity
    nlinarith
  have hn : 0 < 3 * (thermalRatio τ ^ 2 + 1) +
      4 * egbCoexistenceACouplingWeight τ θ * (2 - egbCoexistenceALogKernel τ) := by nlinarith
  have hDD := egbCoexistenceADenominator_pos τ θ
  unfold egbCoexistenceAPressureWeight
  positivity

theorem egbCoexistenceAChargeFactor_pos (τ θ : ℝ) : 0 < egbCoexistenceAChargeFactor τ θ := by
  have hm := egbCoexistenceAMaxCoupling_pos τ
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hB := egbCoexistenceAQuadraticB_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hD := egbCoexistenceADenominator_pos τ θ
  unfold egbCoexistenceAChargeFactor
  positivity

/-- The electric charge squared is controlled by a single concave quadratic. -/
theorem egbCoexistenceAChargeWeight_defect (τ θ : ℝ) :
    egbCoexistenceAChargeWeight τ θ - egbCoexistenceACouplingWeight τ θ =
      (egbCoexistenceAQuadraticC τ - egbCoexistenceAQuadraticB τ * egbCoexistenceACouplingWeight τ θ -
        egbCoexistenceAQuadraticA τ * egbCoexistenceACouplingWeight τ θ ^ 2) /
          (egbCoexistenceADenominator τ θ * (thermalRatio τ ^ 2 + 1)) := by
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hH := egbCoexistenceALogKernel_pos τ
  have hD := egbCoexistenceShape_pos τ
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceAChargeWeight egbCoexistenceAQuadraticA egbCoexistenceAQuadraticB egbCoexistenceAQuadraticC
    egbCoexistenceADenominator egbCoexistenceShape
  field_simp
  ring

/-- The angular construction factorizes the charge defect into a nonnegative square and positive factor. -/
theorem egbCoexistenceAChargeWeight_factorization (τ θ : ℝ) :
    egbCoexistenceAChargeWeight τ θ - egbCoexistenceACouplingWeight τ θ = cos θ ^ 2 * egbCoexistenceAChargeFactor τ θ := by
  have hc : cos θ ^ 2 = 1 - sin θ ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
  have he : egbCoexistenceAQuadraticC τ - egbCoexistenceAQuadraticB τ * egbCoexistenceACouplingWeight τ θ -
      egbCoexistenceAQuadraticA τ * egbCoexistenceACouplingWeight τ θ ^ 2 =
    cos θ ^ 2 * egbCoexistenceAMaxCoupling τ * (egbCoexistenceAQuadraticB τ +
      egbCoexistenceAQuadraticA τ * (egbCoexistenceAMaxCoupling τ + egbCoexistenceACouplingWeight τ θ)) := by
    rw [hc]
    unfold egbCoexistenceACouplingWeight
    have hq := egbCoexistenceAMaxCoupling_quadratic τ
    linear_combination -hq
  rw [egbCoexistenceAChargeWeight_defect, he]
  unfold egbCoexistenceAChargeFactor
  ring

theorem egbCoexistenceAChargeWeight_pos (τ θ : ℝ) : 0 < egbCoexistenceAChargeWeight τ θ := by
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hF := egbCoexistenceAChargeFactor_pos τ θ
  have he := egbCoexistenceAChargeWeight_factorization τ θ
  by_cases hc : cos θ = 0
  · have hs : sin θ ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq θ]
    have hbp : 0 < egbCoexistenceACouplingWeight τ θ := by
      unfold egbCoexistenceACouplingWeight
      rw [hs, mul_one]
      exact egbCoexistenceAMaxCoupling_pos τ
    rw [hc] at he
    norm_num at he
    linarith
  · have hcp : 0 < cos θ ^ 2 * egbCoexistenceAChargeFactor τ θ := mul_pos (sq_pos_iff.mpr hc) hF
    linarith

end GaloisForLFunctions.HTGeometry
