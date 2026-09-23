import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanCoefficientLimits

/-!
# The first critical correction of the actual mean-radius weight

Subtracting the two exact equilibrium quadratics gives a positive secant
denominator. Thus the even first correction exists, has an explicit
formula and is strictly negative for every conserved charge mixture.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanCriticalCorrection (φ : ℝ) : ℝ :=
  -(1 + (4 + 4 * egbFixedChargeAFraction φ / 5) * egbFixedChargeACriticalWeight φ +
    (92 * egbFixedChargeAFraction φ / 5) * egbFixedChargeACriticalWeight φ ^ (2 : ℕ)) /
    (24 * egbFixedChargeAFraction φ * egbFixedChargeACriticalWeight φ + 6 * (1 + egbFixedChargeAFraction φ))

theorem egbFixedChargeAMeanCriticalCorrection_denominator_pos (φ : ℝ) :
    0 < 24 * egbFixedChargeAFraction φ * egbFixedChargeACriticalWeight φ + 6 * (1 + egbFixedChargeAFraction φ) := by
  have hr := (egbFixedChargeAFraction_bounds φ).1
  have hs := egbFixedChargeACriticalWeight_pos φ
  positivity

theorem egbFixedChargeAMeanCriticalCorrection_neg (φ : ℝ) : egbFixedChargeAMeanCriticalCorrection φ < 0 := by
  have hr := (egbFixedChargeAFraction_bounds φ).1
  have hs := egbFixedChargeACriticalWeight_pos φ
  unfold egbFixedChargeAMeanCriticalCorrection
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (egbFixedChargeAMeanCriticalCorrection_denominator_pos φ)

theorem egbFixedChargeAMeanWeight_secant_denominator_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanQuadraticA τ φ *
      (egbFixedChargeAMeanWeight τ φ + egbFixedChargeACriticalWeight φ) + egbFixedChargeAMeanQuadraticB τ φ)
      atBot (𝓝 (24 * egbFixedChargeAFraction φ * egbFixedChargeACriticalWeight φ + 6 * (1 + egbFixedChargeAFraction φ))) := by
  have h := ((egbFixedChargeAMeanQuadraticA_critical_limit φ).mul
    ((egbFixedChargeAMeanWeight_critical_limit φ).add (tendsto_const_nhds (x := egbFixedChargeACriticalWeight φ)))).add
      (egbFixedChargeAMeanQuadraticB_critical_limit φ)
  convert h using 1 <;> ring

theorem egbFixedChargeAMeanWeight_normalized_difference (τ φ : ℝ) :
    (egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
    ((egbFixedChargeAMeanQuadraticC τ - 1) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) -
      ((egbFixedChargeAMeanQuadraticA τ φ - 12 * egbFixedChargeAFraction φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbFixedChargeACriticalWeight φ ^ (2 : ℕ) -
      ((egbFixedChargeAMeanQuadraticB τ φ - 6 * (1 + egbFixedChargeAFraction φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbFixedChargeACriticalWeight φ) /
      (egbFixedChargeAMeanQuadraticA τ φ * (egbFixedChargeAMeanWeight τ φ + egbFixedChargeACriticalWeight φ) + egbFixedChargeAMeanQuadraticB τ φ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hden := egbFixedChargeAMeanWeight_secant_denominator_pos τ φ
  apply (eq_div_iff hden.ne').2
  have h := egbFixedChargeAMeanWeight_critical_difference τ φ
  calc
    _ = ((egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) *
      (egbFixedChargeAMeanQuadraticA τ φ * (egbFixedChargeAMeanWeight τ φ + egbFixedChargeACriticalWeight φ) + egbFixedChargeAMeanQuadraticB τ φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by ring
    _ = _ := by rw [h]; ring

theorem egbFixedChargeAMeanWeight_quadratic_critical_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanCriticalCorrection φ)) := by
  simp only [egbFixedChargeAMeanWeight_normalized_difference]
  have hn : Tendsto (fun τ => (egbFixedChargeAMeanQuadraticC τ - 1) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) -
      ((egbFixedChargeAMeanQuadraticA τ φ - 12 * egbFixedChargeAFraction φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbFixedChargeACriticalWeight φ ^ (2 : ℕ) -
      ((egbFixedChargeAMeanQuadraticB τ φ - 6 * (1 + egbFixedChargeAFraction φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbFixedChargeACriticalWeight φ)
      atBot (𝓝 (-(1 + (4 + 4 * egbFixedChargeAFraction φ / 5) * egbFixedChargeACriticalWeight φ + (92 * egbFixedChargeAFraction φ / 5) * egbFixedChargeACriticalWeight φ ^ (2 : ℕ)))) := by
    convert (egbFixedChargeAMeanQuadraticC_remainder_limit.sub
      ((egbFixedChargeAMeanQuadraticA_remainder_limit φ).mul (tendsto_const_nhds (x := egbFixedChargeACriticalWeight φ ^ (2 : ℕ))))).sub
        ((egbFixedChargeAMeanQuadraticB_remainder_limit φ).mul (tendsto_const_nhds (x := egbFixedChargeACriticalWeight φ))) using 1 <;> ring
  exact hn.div (egbFixedChargeAMeanWeight_secant_denominator_limit φ)
    (egbFixedChargeAMeanCriticalCorrection_denominator_pos φ).ne'

theorem egbFixedChargeAMeanCoupling_quadratic_critical_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanCoupling τ φ - egbFixedChargeACriticalCouplingWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAFraction φ * egbFixedChargeAMeanCriticalCorrection φ)) := by
  have h := (tendsto_const_nhds (x := egbFixedChargeAFraction φ)).mul (egbFixedChargeAMeanWeight_quadratic_critical_limit φ)
  convert h using 1
  funext τ
  unfold egbFixedChargeAMeanCoupling egbFixedChargeACriticalCouplingWeight
  ring

end GaloisForLFunctions.HTGeometry
