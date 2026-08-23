import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Precomposition by a nonzero scalar rescales the `n`-th derivative jet by its `n`-th power.
No smoothness hypothesis is needed: an invertible continuous linear change preserves the raw
Fréchet jet, including mathlib's zero value outside the differentiability locus. -/
theorem iteratedDeriv_comp_const_mul_of_ne
    (f : ℂ → ℂ) (n : ℕ) {μ : ℂ} (hμ : μ ≠ 0) (x : ℂ) :
    iteratedDeriv n (fun y => f (μ * y)) x =
      μ ^ n * iteratedDeriv n f (μ * x) := by
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 μ hμ)
  have he (y : ℂ) : e y = μ * y := by
    simp [e]
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (mem_univ (e x)) n
  have h' : iteratedFDeriv ℂ n (f ∘ e) x =
      (iteratedFDeriv ℂ n f (e x)).compContinuousLinearMap (fun _ => e) := by
    simpa only [iteratedFDerivWithin_univ, preimage_univ] using h
  have happ := congrArg
    (fun p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ => p (fun _ => 1)) h'
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he] at happ
  have heconst : (fun _ : Fin n => e (1 : ℂ)) = (fun _ => μ) := by
    funext i
    simpa using he 1
  change _ = (iteratedFDeriv ℂ n f (μ * x) : (Fin n → ℂ) → ℂ)
    (fun _ => e (1 : ℂ)) at happ
  rw [heconst] at happ
  have hscale : (iteratedFDeriv ℂ n f (μ * x) : (Fin n → ℂ) → ℂ) (fun _ => μ) =
      μ ^ n * iteratedDeriv n f (μ * x) := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp
  rw [hscale] at happ
  have hcomp : f ∘ e = (fun y => f (μ * y)) := by
    funext y
    simp [Function.comp_apply, he]
  rw [hcomp] at happ
  simpa [Function.comp_apply, he, iteratedDeriv_eq_iteratedFDeriv] using happ

/-- Taylor coefficient of the residue-filled completed-flux germ of an arbitrary function. -/
def fluxGermTaylorCoeff (f : ℂ → ℂ) (w : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (fluxGerm f w) 0 / n.factorial

/-- Flux Taylor coefficients transform covariantly under an invertible affine coordinate change. -/
theorem fluxGermTaylorCoeff_comp_affine {f : ℂ → ℂ} {μ ν z : ℂ} {m : ℕ}
    (hμ : μ ≠ 0) (hf : ∀ w, AnalyticAt ℂ f w)
    (hord : analyticOrderAt f (μ * z + ν) = m) (n : ℕ) :
    fluxGermTaylorCoeff (fun s : ℂ => f (μ * s + ν)) z n =
      μ ^ n * fluxGermTaylorCoeff f (μ * z + ν) n := by
  have hfun : fluxGerm (fun s : ℂ => f (μ * s + ν)) z =
      (fun x => fluxGerm f (μ * z + ν) (μ * x)) := by
    funext x
    exact fluxGerm_comp_affine hμ hf hord x
  rw [fluxGermTaylorCoeff, fluxGermTaylorCoeff, hfun,
    iteratedDeriv_comp_const_mul_of_ne _ n hμ]
  simp only [mul_zero]
  ring

end GaloisForLFunctions.HTGeometry
