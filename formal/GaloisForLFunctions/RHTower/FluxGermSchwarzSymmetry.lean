import GaloisForLFunctions.HTGeometry.FluxGermSymmetry
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A Schwarz-equivariant complex function has a Schwarz-equivariant derivative. -/
theorem deriv_conj_of_conjEquivariant {f : ℂ → ℂ}
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) (z : ℂ) :
    deriv f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv f z) := by
  have hfun : (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = f := by
    funext w
    simp [Function.comp_apply, hconj]
  have hder : deriv f = (starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ) := by
    calc
      deriv f = deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) := congrArg deriv hfun.symm
      _ = (starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ) := deriv_conj_conj
  have h := congrFun hder ((starRingEnd ℂ) z)
  simpa [Function.comp_apply] using h

/-- Schwarz-equivariance transports the residue-filled completed-flux germ to the conjugate
centre, including its filled value at the origin. -/
theorem fluxGerm_conj_of_conjEquivariant {f : ℂ → ℂ} {ρ : ℂ}
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hord : analyticOrderAt f ((starRingEnd ℂ) ρ) = analyticOrderAt f ρ) (x : ℂ) :
    fluxGerm f ((starRingEnd ℂ) ρ) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (fluxGerm f ρ x) := by
  have hderiv : deriv f ((starRingEnd ℂ) (ρ + x)) =
      (starRingEnd ℂ) (deriv f (ρ + x)) := by
    exact deriv_conj_of_conjEquivariant hconj (ρ + x)
  by_cases hx : x = 0
  · subst x
    rw [map_zero, fluxGerm_zero, fluxGerm_zero, hord]
    simp
  · have hcx : (starRingEnd ℂ) x ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hx
    rw [fluxGerm_of_ne_zero _ _ hcx, fluxGerm_of_ne_zero _ _ hx]
    rw [show (starRingEnd ℂ) ρ + (starRingEnd ℂ) x =
      (starRingEnd ℂ) (ρ + x) by simp, hderiv, hconj]
    simp

/-- Completed-flux jets at Schwarz-conjugate centres are coefficientwise conjugate. -/
theorem iteratedDeriv_fluxGerm_conj_of_conjEquivariant {f : ℂ → ℂ} {ρ : ℂ}
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hord : analyticOrderAt f ((starRingEnd ℂ) ρ) = analyticOrderAt f ρ) (k : ℕ) :
    iteratedDeriv k (fluxGerm f ((starRingEnd ℂ) ρ)) 0 =
      (starRingEnd ℂ) (iteratedDeriv k (fluxGerm f ρ) 0) := by
  have hflux : fluxGerm f ((starRingEnd ℂ) ρ) =
      (starRingEnd ℂ) ∘ fluxGerm f ρ ∘ (starRingEnd ℂ) := by
    funext x
    simpa [Function.comp_apply] using
      fluxGerm_conj_of_conjEquivariant hconj hord ((starRingEnd ℂ) x)
  rw [hflux, iteratedDeriv_conj_conj]
  simp [Function.comp_apply]

/-- Combining evenness and Schwarz reality gives the exact graded-real partner law at
`-conj ρ`. -/
theorem iteratedDeriv_fluxGerm_neg_conj_of_even_conjEquivariant
    {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hf : ∀ z, AnalyticAt ℂ f z) (hord : analyticOrderAt f ρ = n) (k : ℕ) :
    iteratedDeriv k (fluxGerm f (-((starRingEnd ℂ) ρ))) 0 =
      (-1 : ℂ) ^ k * (starRingEnd ℂ) (iteratedDeriv k (fluxGerm f ρ) 0) := by
  have hordconjEq : analyticOrderAt f ((starRingEnd ℂ) ρ) = analyticOrderAt f ρ :=
    analyticOrderAt_conj_of_conjEquivariant hconj (hf ρ) (hf ((starRingEnd ℂ) ρ))
  have hordconj : analyticOrderAt f ((starRingEnd ℂ) ρ) = n := hordconjEq.trans hord
  calc
    iteratedDeriv k (fluxGerm f (-((starRingEnd ℂ) ρ))) 0 =
        (-1 : ℂ) ^ k *
          iteratedDeriv k (fluxGerm f ((starRingEnd ℂ) ρ)) 0 :=
      GaloisForLFunctions.HTGeometry.iteratedDeriv_fluxGerm_neg_of_even
        heven hf hordconj k
    _ = (-1 : ℂ) ^ k *
        (starRingEnd ℂ) (iteratedDeriv k (fluxGerm f ρ) 0) := by
      rw [iteratedDeriv_fluxGerm_conj_of_conjEquivariant hconj hordconjEq]

end RHTower
