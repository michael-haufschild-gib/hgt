import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue

noncomputable section

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- Conjugation reflects height and conjugates every coefficient of a finite Dirichlet polynomial. -/
theorem star_cdpoly (a : ℕ → ℂ) (s : Finset ℕ) (sigma t : ℝ) :
    (starRingEnd ℂ) (cdpoly a s sigma t) =
      cdpoly (fun n => (starRingEnd ℂ) (a n)) s sigma (-t) := by
  unfold cdpoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [conj_cdterm]
  unfold cdterm
  congr 1
  ring_nf

/-- A conjugation-fixed coefficient family has even Dirichlet-polynomial norm in height. -/
theorem norm_cdpoly_neg_eq_of_star_coeff
    (a : ℕ → ℂ) (s : Finset ℕ) (sigma t : ℝ)
    (ha : ∀ n ∈ s, (starRingEnd ℂ) (a n) = a n) :
    ‖cdpoly a s sigma (-t)‖ = ‖cdpoly a s sigma t‖ := by
  have hstar : (starRingEnd ℂ) (cdpoly a s sigma t) = cdpoly a s sigma (-t) := by
    rw [star_cdpoly]
    apply Finset.sum_congr rfl
    intro n hn
    unfold cdterm
    simp only [ha n hn]
  rw [← hstar, Complex.norm_conj]

end RHTower.Sieve
