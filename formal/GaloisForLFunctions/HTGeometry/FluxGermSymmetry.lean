import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Evenness transports the residue-filled completed-flux germ at `ρ` to the reflected centre
`-ρ`, with reversal of its local coordinate. -/
theorem fluxGerm_neg_of_even {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (heven : ∀ z, f (-z) = f z) (hf : ∀ z, AnalyticAt ℂ f z)
    (hord : analyticOrderAt f ρ = n) (x : ℂ) :
    fluxGerm f (-ρ) x = fluxGerm f ρ (-x) := by
  have hcomp := fluxGerm_comp_affine (f := f) (μ := (-1 : ℂ)) (ν := 0) (z := -ρ) (n := n)
    (by norm_num) hf (by simpa using hord) x
  have hfun : (fun s : ℂ => f ((-1 : ℂ) * s + 0)) = f := by
    funext s
    rw [show (-1 : ℂ) * s + 0 = -s by ring, heven]
  rw [hfun] at hcomp
  simpa using hcomp

/-- The `k`-th completed-flux jet of an even entire function acquires exactly the parity factor
at the reflected centre. -/
theorem iteratedDeriv_fluxGerm_neg_of_even {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (heven : ∀ z, f (-z) = f z) (hf : ∀ z, AnalyticAt ℂ f z)
    (hord : analyticOrderAt f ρ = n) (k : ℕ) :
    iteratedDeriv k (fluxGerm f (-ρ)) 0 =
      (-1 : ℂ) ^ k * iteratedDeriv k (fluxGerm f ρ) 0 := by
  have hflux : fluxGerm f (-ρ) = fun x => fluxGerm f ρ (-x) :=
    funext (fluxGerm_neg_of_even heven hf hord)
  rw [hflux]
  simpa using iteratedDeriv_comp_neg k (fluxGerm f ρ) 0

end GaloisForLFunctions.HTGeometry
