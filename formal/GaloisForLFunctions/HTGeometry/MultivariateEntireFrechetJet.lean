import GaloisForLFunctions.HTGeometry.MultivariateEntireAffinePullback

/-!
# Directional jets as diagonal Frechet jets

For a genuinely Frechet-holomorphic source, the intrinsic line jet used by the compact-open
source space is exactly the diagonal value of the iterated Frechet derivative.  This is the
analytic bridge needed to recover ordinary mixed partial derivatives from continuous directional
observations.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A directional line jet of a Frechet-holomorphic source is the corresponding diagonal
iterated Frechet jet. -/
theorem directionalJetEval_eq_iteratedFDeriv
    {d n : ℕ} (x v : Fin d → ℂ) (f : MultivariateEntire d)
    (hf : ContDiff ℂ (⊤ : ℕ∞) f.1) :
    directionalJetEval n x v f =
      iteratedFDeriv ℂ n f.1 x (fun _ : Fin n ↦ v) := by
  let L : ℂ →L[ℂ] (Fin d → ℂ) :=
    (1 : ℂ →L[ℂ] ℂ).smulRight v
  have hfun : affineLineRestriction x v f =
      (fun y ↦ f.1 (x + y)) ∘ L := by
    funext z
    simp [affineLineRestriction, L]
  have hfShift : ContDiff ℂ (⊤ : ℕ∞) (fun y ↦ f.1 (x + y)) := by
    exact hf.comp (contDiff_const.add contDiff_id)
  have hcomp := L.iteratedFDeriv_comp_right
    (f := fun y ↦ f.1 (x + y)) hfShift (0 : ℂ)
      (show (n : ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  have happ := congrArg
    (fun B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ ℂ) ℂ ↦
      B (fun _ ↦ (1 : ℂ))) hcomp
  rw [iteratedFDeriv_comp_add_left] at happ
  rw [directionalJetEval, hfun, iteratedDeriv_eq_iteratedFDeriv]
  simpa [L] using happ

end

end GaloisForLFunctions.HTGeometry
