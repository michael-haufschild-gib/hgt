import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpace
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTopology
import Mathlib.Analysis.RCLike.BoundedContinuous

/-!
# Continuity of Real conjugation on Meyer's strong logarithmic target

Complex conjugation commutes with every iterated real derivative and sends
each weighted uniform gauge to pointwise conjugation of that gauge.  Hence the
Real involution is continuous for the full all-derivative,
all-exponential-weight topology.
-/

noncomputable section

open Complex Filter Function Set Topology
open scoped BoundedContinuousFunction ContDiff

namespace RHTower

/-- Complex conjugation commutes with every iterated real derivative of a
smooth complex-valued function. -/
theorem iteratedDeriv_complexConj_strongLog :
    ∀ (n : ℕ) {g : ℝ → ℂ}, ContDiff ℝ (⊤ : ℕ∞) g →
      iteratedDeriv n (fun x => star (g x)) =
        fun x => star (iteratedDeriv n g x) := by
  intro n
  induction n with
  | zero =>
      intro g hg
      simp
  | succ n ihn =>
      intro g hg
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ihn hg]
      funext x
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n g) x := by
        have h := hg.differentiable_iteratedDeriv n
          (compareOfLessAndEq_eq_lt.mp rfl)
        exact h.differentiableAt
      exact ((Complex.conjCLE.hasFDerivAt).comp_hasDerivAt
        x hdiff.hasDerivAt).deriv

/-- Conjugation as a conjugate-linear involution of the radial strong space. -/
def deningerMeyerStrongLogConjₛₗ :
    DeningerMeyerStrongLogTarget →ₗ⋆[ℂ] DeningerMeyerStrongLogTarget where
  toFun := deningerMeyerStrongLogConj
  map_add' := deningerMeyerStrongLogConj_add
  map_smul' := deningerMeyerStrongLogConj_smul

/-- Every defining gauge intertwines radial Real conjugation with pointwise
conjugation in the bounded-function recipient. -/
theorem deningerMeyerStrongLogGauge_conj
    (n : ℕ) (k : ℤ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGauge n k (deningerMeyerStrongLogConj g) =
      star (deningerMeyerStrongLogGauge n k g) := by
  apply BoundedContinuousFunction.ext
  intro t
  rw [deningerMeyerStrongLogGauge_apply]
  change ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
      iteratedDeriv n
        (deningerMeyerStrongLogConj g : DeningerMeyerStrongLogTarget) t =
    star (deningerMeyerStrongLogGauge n k g t)
  have hfun :
      ((deningerMeyerStrongLogConj g : DeningerMeyerStrongLogTarget) :
          ℝ → ℂ) = fun x => star ((g : ℝ → ℂ) x) :=
    rfl
  rw [deningerMeyerStrongLogGauge_apply, hfun,
    iteratedDeriv_complexConj_strongLog n g.property.smooth]
  change ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
      star (iteratedDeriv n (g : ℝ → ℂ) t) =
    star (((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) *
      iteratedDeriv n (g : ℝ → ℂ) t)
  have hweight :
      star (((Real.exp t ^ (k : ℝ) : ℝ) : ℂ)) =
        (((Real.exp t ^ (k : ℝ) : ℝ) : ℂ)) := by
    exact Complex.conj_ofReal _
  rw [star_mul, hweight, mul_comm]

/-- Radial Real conjugation is continuous for Meyer's natural strong
weighted-derivative topology. -/
theorem deningerMeyerStrongLogConj_continuous :
    @Continuous DeningerMeyerStrongLogTarget DeningerMeyerStrongLogTarget
      deningerMeyerStrongLogTopology deningerMeyerStrongLogTopology
      deningerMeyerStrongLogConj := by
  letI : TopologicalSpace DeningerMeyerStrongLogTarget :=
    deningerMeyerStrongLogTopology
  rw [deningerMeyerStrongLogTopology, continuous_iInf_rng]
  intro i
  rw [continuous_induced_rng]
  rw [show deningerMeyerStrongLogGaugeLinear i.1 i.2 ∘
      deningerMeyerStrongLogConj =
      fun g => star (deningerMeyerStrongLogGaugeLinear i.1 i.2 g) by
    funext g
    exact deningerMeyerStrongLogGauge_conj i.1 i.2 g]
  exact continuous_star.comp
    (continuous_deningerMeyerStrongLogGaugeLinear i.1 i.2)

end RHTower
