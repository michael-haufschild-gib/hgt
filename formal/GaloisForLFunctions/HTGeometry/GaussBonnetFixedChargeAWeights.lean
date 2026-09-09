import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAWeights

/-!
# Fixed charge fraction in logarithmic-entropy coexistence

Fix α/(Q²+α) by an unrestricted angular parameter. A rationalized positive
quadratic root gives the effective-charge weight without division by the
coupling fraction, including zero coupling. Prove its balance equation and
its inclusion in the already globally stable coexistence family.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAFraction (φ : ℝ) : ℝ := sin φ ^ 2

def egbFixedChargeABase (τ : ℝ) : ℝ := egbCoexistenceShape τ * (thermalRatio τ ^ 2 + 1)

def egbFixedChargeALinearCorrection (τ : ℝ) : ℝ :=
  4 * thermalRatio τ ^ 2 * egbCoexistenceALogKernel τ -
    8 * thermalRatio τ * (thermalRatio τ ^ 2 + thermalRatio τ + 1)

def egbFixedChargeAQuadraticB (τ φ : ℝ) : ℝ :=
  egbFixedChargeABase τ - egbFixedChargeAFraction φ * egbFixedChargeALinearCorrection τ

def egbFixedChargeADiscriminant (τ φ : ℝ) : ℝ :=
  egbFixedChargeAQuadraticB τ φ ^ 2 +
    4 * egbCoexistenceAQuadraticA τ * egbFixedChargeAFraction φ * egbCoexistenceAQuadraticC τ

def egbFixedChargeAWeight (τ φ : ℝ) : ℝ :=
  2 * egbCoexistenceAQuadraticC τ /
    (egbFixedChargeAQuadraticB τ φ + sqrt (egbFixedChargeADiscriminant τ φ))

def egbFixedChargeACouplingWeight (τ φ : ℝ) : ℝ :=
  egbFixedChargeAFraction φ * egbFixedChargeAWeight τ φ

theorem egbFixedChargeAFraction_bounds (φ : ℝ) :
    0 ≤ egbFixedChargeAFraction φ ∧ egbFixedChargeAFraction φ ≤ 1 := by
  unfold egbFixedChargeAFraction
  exact ⟨sq_nonneg _, by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (cos φ)]⟩

theorem egbFixedChargeABase_pos (τ : ℝ) : 0 < egbFixedChargeABase τ := by
  have h := egbCoexistenceShape_pos τ
  unfold egbFixedChargeABase
  positivity

theorem egbFixedChargeALinearCorrection_neg (τ : ℝ) : egbFixedChargeALinearCorrection τ < 0 := by
  have hz := thermalRatio_pos τ
  have hH := (le_div_iff₀ hz).1 (egbCoexistenceALogKernel_upper_bound τ)
  have hp : 0 < thermalRatio τ * (thermalRatio τ ^ 2 + thermalRatio τ + 1) := by positivity
  have hm := mul_nonneg (le_of_lt hz) (sub_nonneg.mpr hH)
  unfold egbFixedChargeALinearCorrection
  nlinarith

theorem egbFixedChargeABase_sub_correction (τ : ℝ) :
    egbFixedChargeABase τ - egbFixedChargeALinearCorrection τ = egbCoexistenceAQuadraticB τ := by
  unfold egbFixedChargeABase egbFixedChargeALinearCorrection egbCoexistenceAQuadraticB
  ring

theorem egbFixedChargeAQuadraticB_pos (τ φ : ℝ) : 0 < egbFixedChargeAQuadraticB τ φ := by
  unfold egbFixedChargeAQuadraticB
  have hE := egbFixedChargeABase_pos τ
  have hL := mul_nonpos_of_nonneg_of_nonpos (egbFixedChargeAFraction_bounds φ).1
    (le_of_lt (egbFixedChargeALinearCorrection_neg τ))
  linarith

theorem egbFixedChargeADiscriminant_pos (τ φ : ℝ) : 0 < egbFixedChargeADiscriminant τ φ := by
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hB := egbFixedChargeAQuadraticB_pos τ φ
  have hC := egbCoexistenceAQuadraticC_pos τ
  have hρ := (egbFixedChargeAFraction_bounds φ).1
  unfold egbFixedChargeADiscriminant
  positivity

theorem egbFixedChargeAWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeAWeight τ φ := by
  have hB := egbFixedChargeAQuadraticB_pos τ φ
  have hC := egbCoexistenceAQuadraticC_pos τ
  unfold egbFixedChargeAWeight
  positivity

/-- The rationalized root solves the balance equation even at zero coupling fraction. -/
theorem egbFixedChargeAWeight_quadratic (τ φ : ℝ) :
    egbCoexistenceAQuadraticA τ * egbFixedChargeAFraction φ * egbFixedChargeAWeight τ φ ^ 2 +
      egbFixedChargeAQuadraticB τ φ * egbFixedChargeAWeight τ φ - egbCoexistenceAQuadraticC τ = 0 := by
  have hB := egbFixedChargeAQuadraticB_pos τ φ
  have hs : sqrt (egbFixedChargeADiscriminant τ φ) ^ 2 =
      egbFixedChargeAQuadraticB τ φ ^ 2 +
        4 * egbCoexistenceAQuadraticA τ * egbFixedChargeAFraction φ * egbCoexistenceAQuadraticC τ :=
    sq_sqrt (le_of_lt (egbFixedChargeADiscriminant_pos τ φ))
  unfold egbFixedChargeAWeight
  field_simp
  linear_combination -egbCoexistenceAQuadraticC τ * hs

theorem egbFixedChargeACouplingWeight_bounds (τ φ : ℝ) :
    0 ≤ egbFixedChargeACouplingWeight τ φ ∧ egbFixedChargeACouplingWeight τ φ ≤ egbFixedChargeAWeight τ φ := by
  have hs := egbFixedChargeAWeight_pos τ φ
  have hρ := egbFixedChargeAFraction_bounds φ
  unfold egbFixedChargeACouplingWeight
  exact ⟨mul_nonneg hρ.1 hs.le, by nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2) hs.le]⟩

/-- The new effective charge and coupling satisfy the original coexistence balance. -/
theorem egbFixedChargeAWeight_charge_balance (τ φ : ℝ) :
    (egbFixedChargeABase τ + egbCoexistenceAQuadraticA τ * egbFixedChargeACouplingWeight τ φ) *
      egbFixedChargeAWeight τ φ = egbCoexistenceAQuadraticC τ +
        egbFixedChargeALinearCorrection τ * egbFixedChargeACouplingWeight τ φ := by
  have h := egbFixedChargeAWeight_quadratic τ φ
  unfold egbFixedChargeAQuadraticB at h
  unfold egbFixedChargeACouplingWeight
  linear_combination h

theorem egbFixedChargeACouplingWeight_boundary_polynomial (τ φ : ℝ) :
    egbCoexistenceAQuadraticA τ * egbFixedChargeACouplingWeight τ φ ^ 2 +
      egbCoexistenceAQuadraticB τ * egbFixedChargeACouplingWeight τ φ - egbCoexistenceAQuadraticC τ ≤ 0 := by
  have hbalance := egbFixedChargeAWeight_charge_balance τ φ
  have hbounds := egbFixedChargeACouplingWeight_bounds τ φ
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hE := egbFixedChargeABase_pos τ
  have he : egbCoexistenceAQuadraticA τ * egbFixedChargeACouplingWeight τ φ ^ 2 +
      egbCoexistenceAQuadraticB τ * egbFixedChargeACouplingWeight τ φ - egbCoexistenceAQuadraticC τ =
    (egbFixedChargeACouplingWeight τ φ - egbFixedChargeAWeight τ φ) *
      (egbFixedChargeABase τ + egbCoexistenceAQuadraticA τ * egbFixedChargeACouplingWeight τ φ) := by
    rw [← egbFixedChargeABase_sub_correction]
    linear_combination hbalance
  rw [he]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbounds.2)
    (add_nonneg hE.le (mul_nonneg hA.le hbounds.1))

/-- Every fixed-fraction state belongs to the proven charge-admissible coexistence interval. -/
theorem egbFixedChargeACouplingWeight_le_max (τ φ : ℝ) :
    egbFixedChargeACouplingWeight τ φ ≤ egbCoexistenceAMaxCoupling τ := by
  have hq := egbFixedChargeACouplingWeight_boundary_polynomial τ φ
  have hm := egbCoexistenceAMaxCoupling_quadratic τ
  have hp := egbCoexistenceAMaxCoupling_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  have hA := egbCoexistenceAQuadraticA_pos τ
  have hB := egbCoexistenceAQuadraticB_pos τ
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hprod : 0 < (egbFixedChargeACouplingWeight τ φ - egbCoexistenceAMaxCoupling τ) *
      (egbCoexistenceAQuadraticA τ * (egbFixedChargeACouplingWeight τ φ + egbCoexistenceAMaxCoupling τ) +
        egbCoexistenceAQuadraticB τ) := mul_pos (sub_pos.mpr hlt) (by positivity)
  nlinarith

end GaloisForLFunctions.HTGeometry
