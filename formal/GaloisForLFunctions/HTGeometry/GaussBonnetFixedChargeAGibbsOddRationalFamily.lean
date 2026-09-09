import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddProfile

/-!
# A finite-parameter rational family for the odd Gibbs force correction

The exact divided force difference lies in one rational family with
seven convergent real coefficients. This exposes a compactness route to
uniform convergence, beyond the already established pointwise limit.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

abbrev EGBGibbsOddState := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

def egbFixedChargeAGibbsOddState (w φ τ : ℝ) : EGBGibbsOddState :=
  (egbCoexistenceASymmetricRatio τ,
   (egbFixedChargeAGibbsPrefactor w φ τ - egbFixedChargeAGibbsCriticalPrefactor w φ) / egbCoexistenceASymmetricRatio τ,
   (egbFixedChargeAGibbsLinear τ φ - 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ,
   egbFixedChargeAGibbsPrefactor w φ τ, egbFixedChargeAGibbsLinear τ φ,
   egbFixedChargeAMeanPressureNumerator τ φ, egbFixedChargeAGibbsResidual τ φ)

def egbFixedChargeAGibbsOddCriticalState (w φ : ℝ) : EGBGibbsOddState :=
  (0, 0, 0, egbFixedChargeAGibbsCriticalPrefactor w φ,
   4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ),
   3 - 2 * egbFixedChargeACriticalCouplingWeight φ,
   1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5)

def egbFixedChargeAGibbsOddRationalFamily (w φ : ℝ) (s : EGBGibbsOddState) (t : ℝ) : ℝ :=
  let d := s.1
  let a₁ := s.2.1
  let l₁ := s.2.2.1
  let a := s.2.2.2.1
  let l := s.2.2.2.2.1
  let n := s.2.2.2.2.2.1
  let r := s.2.2.2.2.2.2
  (t ^ 2 - 1) * (a₁ * l * t + egbFixedChargeAGibbsCriticalPrefactor w φ * l₁ * t -
    egbFixedChargeAGibbsCriticalPrefactor w φ * (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) *
      t ^ 2 * (2 + d * t) + a * (n * t ^ 2 + r)) / (1 + d * t) ^ 2

theorem egbFixedChargeAGibbsOddState_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAGibbsOddState w φ) atBot (𝓝 (egbFixedChargeAGibbsOddCriticalState w φ)) := by
  exact egbCoexistenceASymmetricRatio_critical_limit.prodMk_nhds
    ((egbFixedChargeAGibbsPrefactor_linear_limit w φ).prodMk_nhds
    ((egbFixedChargeAGibbsLinear_linear_limit φ).prodMk_nhds
    ((egbFixedChargeAGibbsPrefactor_critical_limit w φ).prodMk_nhds
    ((egbFixedChargeAGibbsLinear_critical_limit φ).prodMk_nhds
    ((egbFixedChargeAMeanPressureNumerator_critical_limit φ).prodMk_nhds
    (egbFixedChargeAGibbsResidual_critical_limit φ))))))

theorem egbFixedChargeAGibbsOddKernel_rational_family (w φ τ : ℝ) :
    EqOn (egbFixedChargeAGibbsOddKernel w φ τ)
      (egbFixedChargeAGibbsOddRationalFamily w φ (egbFixedChargeAGibbsOddState w φ τ)) (Icc (-1 : ℝ) 1) := by
  intro t ht
  have he := egbFixedChargeAGibbsReciprocal_difference_onInterval τ ht
  dsimp only at he
  rw [egbFixedChargeAGibbsOddKernel_decomposition, he]
  unfold egbFixedChargeAGibbsReciprocal
  dsimp [egbFixedChargeAGibbsOddRationalFamily, egbFixedChargeAGibbsOddState]
  ring

theorem egbFixedChargeAGibbsOddRationalFamily_critical (w φ t : ℝ) :
    egbFixedChargeAGibbsOddRationalFamily w φ (egbFixedChargeAGibbsOddCriticalState w φ) t =
      egbFixedChargeAGibbsOddLimitKernel w φ t := by
  have hR := egbFixedChargeAGibbsCriticalPrefactor_residual_product w φ
  change egbFixedChargeAGibbsCriticalPrefactor w φ * (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) =
    -egbFixedChargeAGibbsOddCoefficient w φ at hR
  dsimp [egbFixedChargeAGibbsOddRationalFamily, egbFixedChargeAGibbsOddCriticalState]
  unfold egbFixedChargeAGibbsOddLimitKernel
  calc
    _ = -(egbFixedChargeAGibbsCriticalPrefactor w φ * (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5)) *
        (t ^ 2 - 1) * (5 * t ^ 2 - 1) := by ring
    _ = _ := by rw [hR]; ring

end GaloisForLFunctions.HTGeometry
