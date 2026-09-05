import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPlanar
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaVerticalClosure
import Mathlib.Tactic

/-!
# Vertical jump of the planar elastica

The paper's torsionless `q₀ = m` branch has normalized vertical jump
`2 / √m * (2 E(m) - K(m))`.  A strict pointwise integral comparison proves this jump is
positive on the full traveling range `0 < m ≤ 1/2`.  Its exact factorization through
`Q(m) - m` also identifies the classical closure graph as its complete zero locus.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Strict version of the elementary complete-integral comparison. -/
theorem one_sub_mul_completeK_lt_completeE (m : ClassicalModulus) :
    (1 - (m : ℝ)) * completeEllipticK m < completeEllipticE m := by
  let f : ℝ → ℝ := fun θ =>
    completeEIntegrand m θ - (1 - (m : ℝ)) * completeKIntegrand m θ
  have hKcont : Continuous (completeKIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeKIntegrand (classicalAsSubcritical m)
  have hEcont : Continuous (completeEIntegrand m) := by
    simpa [classicalAsSubcritical] using
      continuous_completeEIntegrand (classicalAsSubcritical m)
  have hscaledKcont : Continuous (fun θ : ℝ =>
      (1 - (m : ℝ)) * completeKIntegrand m θ) :=
    continuous_const.mul hKcont
  have hfcont : Continuous f := by
    dsimp only [f]
    exact hEcont.sub (continuous_const.mul hKcont)
  have hfnonneg : ∀ θ : ℝ, 0 ≤ f θ := by
    intro θ
    exact sub_nonneg.mpr (classical_complete_integrand_bound m θ)
  have hfzero : 0 < f 0 := by
    simp [f, completeEIntegrand, completeKIntegrand]
    exact m.property.1
  have hint : 0 < ∫ θ in (0 : ℝ)..Real.pi / 2, f θ := by
    apply intervalIntegral.integral_pos (by positivity) hfcont.continuousOn
      (fun θ _ => hfnonneg θ)
    exact ⟨0, Set.mem_Icc.2 ⟨le_rfl, by positivity⟩, hfzero⟩
  dsimp only [f] at hint
  rw [intervalIntegral.integral_sub
    (hEcont.intervalIntegrable 0 (Real.pi / 2))
    (hscaledKcont.intervalIntegrable 0 (Real.pi / 2)),
    intervalIntegral.integral_const_mul] at hint
  simpa [completeEllipticE, completeEllipticK, completeEIntegrand,
    completeKIntegrand] using hint

/-- Paper's vertical displacement after one period on the torsionless `q₀ = m` wall. -/
noncomputable def torsionlessVerticalJump (m : ClassicalModulus) : ℝ :=
  2 / Real.sqrt (m : ℝ) *
    (2 * completeEllipticE m - completeEllipticK m)

/-- Exact closure-gap factorization of the planar vertical displacement. -/
theorem torsionlessVerticalJump_eq_closureGap (m : ClassicalModulus) :
    torsionlessVerticalJump m =
      2 * completeEllipticK m / Real.sqrt (m : ℝ) *
        (closureQ m - (m : ℝ)) := by
  have hK : completeEllipticK m ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos m)
  rw [torsionlessVerticalJump, closureQ]
  field_simp [hK]
  ring

/-- Across the classical range, zero planar displacement is exactly the closure equation. -/
theorem torsionlessVerticalJump_eq_zero_iff (m : ClassicalModulus) :
    torsionlessVerticalJump m = 0 ↔ closureQ m = (m : ℝ) := by
  rw [torsionlessVerticalJump_eq_closureGap]
  have hK : completeEllipticK m ≠ 0 :=
    ne_of_gt (completeEllipticK_classical_pos m)
  have hs : Real.sqrt (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr m.property.1)
  rw [mul_eq_zero]
  simp [hK, hs, sub_eq_zero]

noncomputable def planarAsClassical (m : PlanarTravelingModulus) : ClassicalModulus :=
  ⟨m, m.property.1, lt_of_le_of_lt m.property.2 (by norm_num)⟩

@[simp] theorem planarAsClassical_coe (m : PlanarTravelingModulus) :
    (planarAsClassical m : ℝ) = (m : ℝ) := rfl

/-- The closure graph lies strictly above the full admissible planar traveling branch. -/
theorem planar_closureQ_gt_modulus (m : PlanarTravelingModulus) :
    (m : ℝ) < closureQ m := by
  let n := planarAsClassical m
  have hK : 0 < completeEllipticK n := completeEllipticK_classical_pos n
  have hEK : (1 - (n : ℝ)) * completeEllipticK n < completeEllipticE n :=
    one_sub_mul_completeK_lt_completeE n
  have hhalf : completeEllipticK n / 2 ≤
      (1 - (n : ℝ)) * completeEllipticK n := by
    change completeEllipticK n / 2 ≤
      (1 - (m : ℝ)) * completeEllipticK n
    nlinarith [m.property.2, hK]
  have hratio : 1 / 2 < completeEllipticE n / completeEllipticK n := by
    rw [lt_div_iff₀ hK]
    nlinarith
  change (n : ℝ) < closureQ n
  rw [closureQ]
  have hrewrite : 2 * completeEllipticE n / completeEllipticK n =
      2 * (completeEllipticE n / completeEllipticK n) := by ring
  rw [hrewrite]
  linarith

/-- The paper's planar vertical jump is strictly positive, hence this branch never closes. -/
theorem torsionlessVerticalJump_pos_on_planar (m : PlanarTravelingModulus) :
    0 < torsionlessVerticalJump (planarAsClassical m) := by
  rw [torsionlessVerticalJump_eq_closureGap]
  exact mul_pos
    (div_pos (mul_pos (by norm_num) (completeEllipticK_classical_pos _))
      (Real.sqrt_pos.mpr m.property.1))
    (sub_pos.mpr (planar_closureQ_gt_modulus m))

theorem torsionlessVerticalJump_ne_zero_on_planar (m : PlanarTravelingModulus) :
    torsionlessVerticalJump (planarAsClassical m) ≠ 0 :=
  ne_of_gt (torsionlessVerticalJump_pos_on_planar m)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
