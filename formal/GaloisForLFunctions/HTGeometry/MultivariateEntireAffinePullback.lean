import GaloisForLFunctions.HTGeometry.MultivariateEntireDirectionalJet
import GaloisForLFunctions.HTGeometry.AffineIteratedFDeriv

/-!
# Affine pullback on compact-open multivariate entire sources

The affine-line definition of `MultivariateEntire` is invariant under every continuous complex
affine automorphism.  Precomposition therefore acts by a continuous complex-linear equivalence on
the source space.  Directional jets obey the exact affine chain rule: the base point is transported
by the affine map and the direction by its linear part.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem lineEntire_comp_continuousAffineEquiv {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f : C(Fin d → ℂ, ℂ)) (hf : LineEntire f) :
    LineEntire (f.comp e.toContinuousAffineMap.toContinuousMap) := by
  let L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    e.toContinuousAffineMap.contLinear
  intro x v
  have he (z : ℂ) : e (x + z • v) = e x + z • L v := by
    have h := e.toContinuousAffineMap.map_vadd x (z • v)
    simpa [L, add_comm] using h
  have hdiff := hf (e x) (L v)
  convert hdiff using 1
  funext z
  exact congrArg f (he z)

/-- Pull an entire source back along a continuous complex affine automorphism. -/
def multivariateEntireAffinePullback {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f : MultivariateEntire d) : MultivariateEntire d :=
  ⟨f.1.comp e.toContinuousAffineMap.toContinuousMap,
    lineEntire_comp_continuousAffineEquiv e f.1 f.property⟩

@[simp]
theorem multivariateEntireAffinePullback_apply {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f : MultivariateEntire d) (x : Fin d → ℂ) :
    (multivariateEntireAffinePullback e f).1 x = f.1 (e x) :=
  rfl

theorem multivariateEntireAffinePullback_add {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f g : MultivariateEntire d) :
    multivariateEntireAffinePullback e (f + g) =
      multivariateEntireAffinePullback e f + multivariateEntireAffinePullback e g := by
  ext x
  rfl

theorem multivariateEntireAffinePullback_smul {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (c : ℂ) (f : MultivariateEntire d) :
    multivariateEntireAffinePullback e (c • f) =
      c • multivariateEntireAffinePullback e f := by
  ext x
  rfl

theorem continuous_multivariateEntireAffinePullback {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) :
    Continuous (multivariateEntireAffinePullback e :
      MultivariateEntire d → MultivariateEntire d) := by
  apply Continuous.subtype_mk
  let ec : C(Fin d → ℂ, Fin d → ℂ) := e.toContinuousAffineMap.toContinuousMap
  exact (ContinuousMap.uniformContinuous_comp_left ec).continuous.comp continuous_subtype_val

/-- Affine pullback is a continuous complex-linear automorphism of the entire-source space. -/
def multivariateEntireAffinePullbackCLE {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) :
    MultivariateEntire d ≃L[ℂ] MultivariateEntire d where
  toFun := multivariateEntireAffinePullback e
  invFun := multivariateEntireAffinePullback e.symm
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
  map_add' := multivariateEntireAffinePullback_add e
  map_smul' := multivariateEntireAffinePullback_smul e
  continuous_toFun := continuous_multivariateEntireAffinePullback e
  continuous_invFun := continuous_multivariateEntireAffinePullback e.symm

/-- Exact affine chain rule for intrinsic directional jets. -/
theorem directionalJetEval_affinePullback {d n : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (f : MultivariateEntire d) (x v : Fin d → ℂ) :
    directionalJetEval n x v (multivariateEntireAffinePullback e f) =
      directionalJetEval n (e x) (e.toContinuousAffineMap.contLinear v) f := by
  have hfun : affineLineRestriction x v (multivariateEntireAffinePullback e f) =
      affineLineRestriction (e x) (e.toContinuousAffineMap.contLinear v) f := by
    funext z
    have h := e.toContinuousAffineMap.map_vadd x (z • v)
    simp only [affineLineRestriction, multivariateEntireAffinePullback_apply]
    congr 1
    simpa [add_comm] using h
  exact congrFun (congrArg (iteratedDeriv n) hfun) 0

end

end GaloisForLFunctions.HTGeometry
