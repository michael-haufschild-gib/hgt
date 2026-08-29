import GaloisForLFunctions.HTGeometry.OneDimJetEvalBridge
import GaloisForLFunctions.HTGeometry.RandomAffineJetPacketFreeness

/-!
# One-coordinate translation jet packets

For a one-coordinate source and a palette of translations, every coordinate of a finite affine jet
packet is an ordinary iterated derivative of the scalar function at a translated base point.  The
packet therefore reads a finite table of points with prescribed derivative orders, and its total
size is the sum of those orders.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translating the one-coordinate embedding is the embedding of the translated function. -/
theorem pullback_oneDimTranslationFrame (h : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    multivariateEntireAffinePullback (oneDimTranslationFrame h)
        (oneDimMultivariateEntireOfDifferentiable g hg)
      = oneDimMultivariateEntireOfDifferentiable (fun w => g (w + h))
          (hg.comp (differentiable_id.add_const h)) := by
  ext z
  rw [multivariateEntireAffinePullback_apply, oneDimMultivariateEntireOfDifferentiable_apply,
    oneDimMultivariateEntireOfDifferentiable_apply, oneDimTranslationFrame_apply]

theorem affineMultiIndexJetEvalCLM_oneDimTranslation (hh : ℂ) (x : Fin 1 → ℂ) (a : Fin 1 →₀ ℕ)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    affineMultiIndexJetEvalCLM (oneDimTranslationFrame hh) x a
        (oneDimMultivariateEntireOfDifferentiable g hg)
      = iteratedDeriv (a 0) g (x 0 + hh) := by
  rw [affineMultiIndexJetEvalCLM_apply, pullback_oneDimTranslationFrame,
    multiIndexJetEvalCLM_oneDim]
  exact congrFun (iteratedDeriv_comp_add_const (a 0) g hh) (x 0)

variable {H : Type*}

/-- The evaluation point read by a packet coordinate. -/
def packetPoint (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ)
    (k : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) : ℂ :=
  base k.1 0 + shift (p.frameCode k.2.1)

/-- The derivative order read by a packet coordinate. -/
def packetOrder (p : FiniteMultivariateAffineJetPattern H 1)
    (k : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) : ℕ :=
  k.2.2.1 0

theorem multivariateAffinePatternObservationCLM_oneDim (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (k : MultivariateAffinePatternRow p × MultivariateAffinePatternJet p) :
    multivariateAffinePatternObservationCLM (fun h => oneDimTranslationFrame (shift h)) p base
        (oneDimMultivariateEntireOfDifferentiable g hg) k
      = iteratedDeriv (packetOrder p k) g (packetPoint shift p base k) :=
  affineMultiIndexJetEvalCLM_oneDimTranslation _ _ _ g hg

end

end GaloisForLFunctions.HTGeometry
