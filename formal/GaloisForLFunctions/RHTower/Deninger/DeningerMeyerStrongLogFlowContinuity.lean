import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogTopology
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerDilationFlow

/-!
# Continuity of the strong logarithmic translation flow

Translation by `c` conjugates each integral weighted-derivative gauge to
domain translation on bounded continuous functions, multiplied by the exact
scalar `exp(c)^k`.  Domain translation is `1`-Lipschitz in uniform norm.
Therefore every fixed Meyer flow operator is continuous for the natural strong
topology.
-/

noncomputable section

open Topology
open scoped BoundedContinuousFunction

namespace RHTower

/-- Translation of the real gauge variable. -/
def deningerMeyerStrongLogGaugeShift (c : ℝ) : C(ℝ, ℝ) where
  toFun t := t - c
  continuous_toFun := continuous_id.sub continuous_const

/-- Exact conjugacy of weighted gauges under logarithmic flow. -/
theorem deningerMeyerStrongLogGauge_flow
    (c : ℝ) (n : ℕ) (k : ℤ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGauge n k (deningerMeyerStrongLogFlow c g) =
      ((Real.exp c ^ (k : ℝ) : ℝ) : ℂ) •
        (deningerMeyerStrongLogGauge n k g).compContinuous
          (deningerMeyerStrongLogGaugeShift c) := by
  apply BoundedContinuousFunction.ext
  intro t
  rw [deningerMeyerStrongLogGauge_apply,
    BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.compContinuous_apply,
    deningerMeyerStrongLogGauge_apply]
  have hflow :
      ((deningerMeyerStrongLogFlow c g : DeningerMeyerStrongLogTarget) :
        ℝ → ℂ) = fun x => (g : ℝ → ℂ) (x - c) :=
    rfl
  rw [hflow, iteratedDeriv_comp_sub_const]
  change
    ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
        iteratedDeriv n (g : ℝ → ℂ) (t - c) =
      ((Real.exp c ^ (k : ℝ) : ℝ) : ℂ) *
        (((Real.exp (t - c) ^ (k : ℝ) : ℝ) : ℂ) *
          iteratedDeriv n (g : ℝ → ℂ) (t - c))
  rw [← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.mul_rpow
      (Real.exp_pos c).le (Real.exp_pos (t - c)).le,
    ← Real.exp_add]
  congr 2
  ring

/-- Every fixed logarithmic translation is continuous in the natural strong
weighted-derivative topology. -/
theorem deningerMeyerStrongLogFlow_continuous (c : ℝ) :
    @Continuous DeningerMeyerStrongLogTarget DeningerMeyerStrongLogTarget
      deningerMeyerStrongLogTopology deningerMeyerStrongLogTopology
      (deningerMeyerStrongLogFlow c) := by
  letI : TopologicalSpace DeningerMeyerStrongLogTarget :=
    deningerMeyerStrongLogTopology
  rw [deningerMeyerStrongLogTopology, continuous_iInf_rng]
  intro i
  rw [continuous_induced_rng]
  rw [show deningerMeyerStrongLogGaugeLinear i.1 i.2 ∘
      deningerMeyerStrongLogFlow c =
    fun g => ((Real.exp c ^ (i.2 : ℝ) : ℝ) : ℂ) •
      (deningerMeyerStrongLogGaugeLinear i.1 i.2 g).compContinuous
        (deningerMeyerStrongLogGaugeShift c) by
      funext g
      exact deningerMeyerStrongLogGauge_flow c i.1 i.2 g]
  have hcomp : Continuous (fun g : DeningerMeyerStrongLogTarget =>
      (deningerMeyerStrongLogGaugeLinear i.1 i.2 g).compContinuous
        (deningerMeyerStrongLogGaugeShift c)) :=
    (BoundedContinuousFunction.continuous_compContinuous
      (deningerMeyerStrongLogGaugeShift c)).comp
        (continuous_deningerMeyerStrongLogGaugeLinear i.1 i.2)
  exact hcomp.const_smul (((Real.exp c ^ (i.2 : ℝ) : ℝ) : ℂ))

end RHTower
