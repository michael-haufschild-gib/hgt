import GaloisForLFunctions.RHTower.ConnesLocalShellAbstract
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The global Tate assembly over an arbitrary global field

Appendix I Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `Δ_s = (∏_{v finite, v ∉ P} (1 - Χ_{0,v}(π) q_v^{-s})^{-1}) Δ'_s = L(Χ_0, s) Δ'_s`.

The places of a global field form a countable index set; at each of them the multiplicative Haar
measure is the shell measure of `ConnesLocalShellAbstract`, and the local Tate factor is
`(1 - Χ_{0,v}(π)q_v^{-s})^{-1}`.  The global integral of a tensor test function is the limit of
its finite-stage truncations along the directed system of finite sets of places, so it is the
infinite product of the local factors: Connes' `L(Χ_0,s)`.  The displayed Euler product *is*
Connes' definition of `L(Χ_0,s)`, and it enters here as the value of a `HasProd`.

Nothing in this file mentions `ℚ`: the places, the units and the local data are arbitrary.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

instance connesShellMeasure_sigmaFinite {U : Type*} [MeasurableSpace U] (ν : Measure U)
    [IsProbabilityMeasure ν] : SigmaFinite (connesShellMeasure ν) := by
  rw [connesShellMeasure]
  infer_instance

variable {ι : Type*} (U : ι → Type*) [∀ i, MeasurableSpace (U i)]
  (ν : ∀ i, Measure (U i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- The Tate integral over a finite set of places of a global field. -/
def connesShellStageIntegral (S : Finset ι) (w : ι → ℂ) : ℂ :=
  ∫ x : (i : ↥S) → (Multiplicative ℤ × U (i : ι)),
    ∏ i : ↥S, connesShellRadial (connesPadicUnitBallProfile (w (i : ι))) (x i)
    ∂(Measure.pi fun i : ↥S => connesShellMeasure (ν (i : ι)))

/-- **Appendix I Lemma 1, finite stage, arbitrary global field.**  The finite-stage Tate integral
is the partial Euler product of the local factors. -/
theorem connesShellStageIntegral_eq (S : Finset ι) {w : ι → ℂ} (hw : ∀ i, ‖w i‖ < 1) :
    connesShellStageIntegral U ν S w = ∏ i ∈ S, (1 - w i)⁻¹ := by
  rw [connesShellStageIntegral,
    integral_fintype_prod_eq_prod (ι := ↥S)
      (fun i : ↥S => connesShellRadial
        (connesPadicUnitBallProfile (w ((i : ↥S) : ι))))]
  have hfac : ∀ i : ↥S,
      (∫ z, connesShellRadial (connesPadicUnitBallProfile (w ((i : ↥S) : ι))) z
        ∂(connesShellMeasure (ν ((i : ↥S) : ι)))) = (1 - w ((i : ↥S) : ι))⁻¹ := fun i =>
    connes_shell_unitBall_geometric (ν ((i : ↥S) : ι)) (hw _)
  rw [Finset.prod_congr rfl fun i _ => hfac i]
  exact Finset.prod_coe_sort S (fun i => (1 - w i)⁻¹)

/-- **Appendix I Lemma 1, global assembly, arbitrary global field.**  The finite-stage Tate
integrals converge to the Euler product of the local factors — Connes' `L(Χ_0, s)`. -/
theorem connes_shell_stage_tendsto {w : ι → ℂ} (hw : ∀ i, ‖w i‖ < 1) {L : ℂ}
    (hL : HasProd (fun i : ι => (1 - w i)⁻¹) L) :
    Tendsto (fun S : Finset ι => connesShellStageIntegral U ν S w) atTop (𝓝 L) := by
  refine hL.congr fun S => ?_
  exact (connesShellStageIntegral_eq U ν S hw).symm

end

end GaloisForLFunctions.RHTower
