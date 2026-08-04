import GaloisForLFunctions.RHTower.DeningerAlternatizationOperator
import GaloisForLFunctions.RHTower.DeningerStageDeRham
import Mathlib.Analysis.Analytic.CPolynomial

/-!
# Pullback of differential forms along an analytic map

The transition maps between finite character stages are holomorphic, and a differential form is
transported along them by composing with the derivative.  The pullback of a holomorphic form is
holomorphic: composing with a linear map is multilinear in that map once antisymmetry is forgotten,
and antisymmetrization is a bounded retraction, so analyticity survives.  The pullback commutes with
the exterior derivative, so the finite stages assemble into a directed system of complexes and the
cylinder de Rham complex is their colimit.

* `deningerPullbackForm` : the pullback of a differential form along a map.
* `deningerPullbackForm_analyticAt` : the pullback of an analytic form is analytic.
* `deningerPullbackForm_extDeriv` : the pullback commutes with the exterior derivative.
* `deningerStagePullback_holomorphic`, `deningerStagePullback_extDeriv` : the same on the stages.
-/

namespace RHTower

open ContinuousAlternatingMap

section Pullback

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ}

/-- **The pullback of a differential form** along a map: compose with the derivative. -/
noncomputable def deningerPullbackForm (f : E → F) (ω : F → F [⋀^Fin n]→L[𝕜] G) :
    E → E [⋀^Fin n]→L[𝕜] G :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)

omit [CharZero 𝕜] in
theorem deningerPullbackForm_apply (f : E → F) (ω : F → F [⋀^Fin n]→L[𝕜] G) (x : E)
    (v : Fin n → E) :
    deningerPullbackForm f ω x v = ω (f x) fun i => fderiv 𝕜 f x (v i) := rfl

omit [CharZero 𝕜] in
/-- Composing an alternating form with a linear map is, after forgetting antisymmetry, the
multilinear composition with the constant tuple of that map. -/
theorem deningerPullbackForm_toContinuousMultilinearMap (f : E → F)
    (ω : F → F [⋀^Fin n]→L[𝕜] G) (x : E) :
    (deningerPullbackForm f ω x).toContinuousMultilinearMap =
      ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
          (fun _ : Fin n => E) (fun _ : Fin n => F) G).flipLinear
        (ω (f x)).toContinuousMultilinearMap) fun _ => fderiv 𝕜 f x := rfl

/-- **The pullback of an analytic form along an analytic map is analytic.** -/
theorem deningerPullbackForm_analyticAt {f : E → F} {ω : F → F [⋀^Fin n]→L[𝕜] G} {x : E}
    (hω : AnalyticAt 𝕜 ω (f x)) (hf : AnalyticAt 𝕜 f x)
    (hf' : AnalyticAt 𝕜 (fderiv 𝕜 f) x) :
    AnalyticAt 𝕜 (deningerPullbackForm f ω) x := by
  refine deningerAnalyticAt_of_toContinuousMultilinearMap ?_
  have h1 : AnalyticAt 𝕜 (fun y => (ω (f y)).toContinuousMultilinearMap) x := by
    have h := (ContinuousLinearMap.analyticAt
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM (E := F) (F := G) (ι := Fin n) 𝕜)
      ((ω ∘ f) x)).comp (hω.comp hf)
    exact h
  have h2 : AnalyticAt 𝕜 (fun y => fun _ : Fin n => fderiv 𝕜 f y) x :=
    AnalyticAt.pi fun _ => hf'
  have hpair : AnalyticAt 𝕜
      (fun y => ((ω (f y)).toContinuousMultilinearMap, fun _ : Fin n => fderiv 𝕜 f y)) x :=
    h1.prod h2
  have hΘ : AnalyticAt 𝕜
      (fun p : (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) G) × (Fin n → (E →L[𝕜] F)) =>
        ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
          (fun _ : Fin n => E) (fun _ : Fin n => F) G).flipLinear p.1) p.2)
      ((ω (f x)).toContinuousMultilinearMap, fun _ : Fin n => fderiv 𝕜 f x) :=
    ContinuousLinearMap.analyticAt_uncurry_of_multilinear _
  have hres : AnalyticAt 𝕜 (fun y =>
      ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : Fin n => E) (fun _ : Fin n => F) G).flipLinear
        ((ω (f y)).toContinuousMultilinearMap)) (fun _ : Fin n => fderiv 𝕜 f y)) x :=
    AnalyticAt.comp
      (f := fun y => ((ω (f y)).toContinuousMultilinearMap, fun _ : Fin n => fderiv 𝕜 f y))
      hΘ hpair
  exact hres

omit [CharZero 𝕜] in
/-- **The pullback commutes with the exterior derivative.** -/
theorem deningerPullbackForm_extDeriv {f : E → F} {ω : F → F [⋀^Fin n]→L[𝕜] G} {x : E}
    (hω : DifferentiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 ⊤ f x) :
    extDeriv (deningerPullbackForm f ω) x = deningerPullbackForm f (extDeriv ω) x :=
  extDeriv_pullback (r := ⊤) hω hf le_top

end Pullback

section StagePullback

variable {r s n : ℕ}

/-- **The pullback of a stage form along a holomorphic transition map.** -/
noncomputable abbrev deningerStagePullback (φ : (Fin s → ℂ) → (Fin r → ℂ))
    (ω : DeningerStageForm r n) : DeningerStageForm s n :=
  deningerPullbackForm φ ω

/-- **The pullback of a holomorphic stage form along a holomorphic transition map is
holomorphic.** -/
theorem deningerStagePullback_holomorphic {φ : (Fin s → ℂ) → (Fin r → ℂ)}
    {ω : DeningerStageForm r n} (hφ : AnalyticOnNhd ℂ φ (deningerStageTorus s))
    (hmaps : Set.MapsTo φ (deningerStageTorus s) (deningerStageTorus r))
    (hω : DeningerIsHolomorphicForm ω) :
    DeningerIsHolomorphicForm (deningerStagePullback φ ω) := by
  intro z hz
  exact deningerPullbackForm_analyticAt (hω _ (hmaps hz)) (hφ z hz)
    (hφ.fderiv_of_isOpen (deningerStageTorus_isOpen s) z hz)

/-- **The exterior derivative of a stage form transports along transition maps**, so the finite
stages form a directed system of holomorphic de Rham complexes. -/
theorem deningerStagePullback_extDeriv {φ : (Fin s → ℂ) → (Fin r → ℂ)}
    {ω : DeningerStageForm r n} (hφ : AnalyticOnNhd ℂ φ (deningerStageTorus s))
    (hmaps : Set.MapsTo φ (deningerStageTorus s) (deningerStageTorus r))
    (hω : DeningerIsHolomorphicForm ω) {z : Fin s → ℂ} (hz : z ∈ deningerStageTorus s) :
    extDeriv (deningerStagePullback φ ω) z = deningerStagePullback φ (extDeriv ω) z :=
  deningerPullbackForm_extDeriv (hω _ (hmaps hz)).differentiableAt (hφ z hz).contDiffAt

end StagePullback

end RHTower
