import GaloisForLFunctions.HTGeometry.MultivariateEntireCompactOpen
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Continuous directional jets on the compact-open entire-source space

Restricting a line-entire source to `z ↦ x + z v` gives an entire one-variable function.  Its
order-`n` derivative at zero is a complex-linear functional of the source.  Compact-open
continuity follows from the project's all-orders locally-uniform derivative theorem
`iteratedDeriv_tendsto_of_locallyUniform`.
-/

open Filter Function Set TopologicalSpace Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Restriction of a multivariate entire source to the affine line `z ↦ x + z v`. -/
def affineLineRestriction {d : ℕ} (x v : Fin d → ℂ)
    (f : MultivariateEntire d) : ℂ → ℂ :=
  fun z ↦ f.1 (x + z • v)

/-- The order-`n` directional jet of a line-entire source at `x` in direction `v`. -/
def directionalJetEval {d : ℕ} (n : ℕ) (x v : Fin d → ℂ)
    (f : MultivariateEntire d) : ℂ :=
  iteratedDeriv n (affineLineRestriction x v f) 0

theorem directionalJetEval_add {d : ℕ} (n : ℕ) (x v : Fin d → ℂ)
    (f g : MultivariateEntire d) :
    directionalJetEval n x v (f + g) =
      directionalJetEval n x v f + directionalJetEval n x v g := by
  simpa [directionalJetEval, affineLineRestriction] using
    (iteratedDeriv_add (n := n) (x := (0 : ℂ))
      ((f.property x v).contDiff.contDiffAt)
      ((g.property x v).contDiff.contDiffAt))

theorem directionalJetEval_smul {d : ℕ} (n : ℕ) (x v : Fin d → ℂ)
    (c : ℂ) (f : MultivariateEntire d) :
    directionalJetEval n x v (c • f) = c • directionalJetEval n x v f := by
  change iteratedDeriv n (c • fun z ↦ f.1 (x + z • v)) 0 = _
  exact iteratedDeriv_const_smul_field c (fun z ↦ f.1 (x + z • v))

/-- Every fixed directional jet is continuous for the compact-open topology. -/
theorem continuous_directionalJetEval {d : ℕ} (n : ℕ) (x v : Fin d → ℂ) :
    Continuous (directionalJetEval n x v : MultivariateEntire d → ℂ) := by
  rw [continuous_iff_seqContinuous]
  intro u f huf
  have hval : Tendsto (fun k ↦ (u k).1) atTop (𝓝 f.1) :=
    (continuous_subtype_val.tendsto f).comp huf
  let line := affineComplexLine x v
  have hcomp : Tendsto (fun k ↦ (u k).1.comp line) atTop (𝓝 (f.1.comp line)) :=
    ((ContinuousMap.uniformContinuous_comp_left line).continuous.tendsto f.1).comp hval
  have hloc : TendstoLocallyUniformly
      (fun k z ↦ (u k).1.comp line z) (f.1.comp line) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hcomp
  have hjet := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ hloc.tendstoLocallyUniformlyOn
      (Filter.Eventually.of_forall fun k ↦ ((u k).property x v).differentiableOn)
      n (Set.mem_univ (0 : ℂ))
  simpa [directionalJetEval, affineLineRestriction, line,
    affineComplexLine, Function.comp_def] using hjet

/-- A fixed directional jet, bundled as a continuous complex-linear observation of the source. -/
def directionalJetEvalCLM {d : ℕ} (n : ℕ) (x v : Fin d → ℂ) :
    MultivariateEntire d →L[ℂ] ℂ where
  toFun := directionalJetEval n x v
  map_add' := directionalJetEval_add n x v
  map_smul' := directionalJetEval_smul n x v
  cont := continuous_directionalJetEval n x v

@[simp]
theorem directionalJetEvalCLM_apply {d : ℕ} (n : ℕ) (x v : Fin d → ℂ)
    (f : MultivariateEntire d) :
    directionalJetEvalCLM n x v f = directionalJetEval n x v f :=
  rfl

end

end GaloisForLFunctions.HTGeometry
