import GaloisForLFunctions.RHTower.XiMassJetFourierIdentity
import GaloisForLFunctions.RHTower.XiMassJetPrimeLineCriterion

/-!
# The jet atom-series criterion

Atomizing the jet Euler-line prime integral turns the prime-line criterion into a statement about a
single absolutely convergent series of Fourier atoms at the prime-power logarithms, each of which is
the iterated caustic-null jet of the mass profile read at that logarithm.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- **The jet atom-series RH criterion.**  RH is equivalent to uniform boundedness, on one positive
vertical line, of the jet-modified prime-log Fourier atom series. -/
theorem riemannHypothesis_iff_exists_xiMassJetAtomSeries_line_bound {a c : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) (hhalf : 1 / 2 < c) (hca : c < a) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
        ‖∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
            ((σ : ℂ) + (x : ℂ) * I) n‖ ≤ C := by
  rw [riemannHypothesis_iff_exists_xiMassJetBottomPrime_line_bound ha N hhalf hca]
  constructor
  · rintro ⟨σ, C, hσ, hline⟩
    refine ⟨σ, C, hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    rw [← integral_xiMassPolyBottomPrimeIntegrand_eq_tsum_centeredAtom
      (xiMassJetPoly a N) hhalf hca hτ]
    exact hline x
  · rintro ⟨σ, C, hσ, hline⟩
    refine ⟨σ, C, hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    rw [integral_xiMassPolyBottomPrimeIntegrand_eq_tsum_centeredAtom
      (xiMassJetPoly a N) hhalf hca hτ]
    exact hline x

/-- The atom series written through the iterated jet, at every logarithm above the height. -/
theorem xiMassPolyCenteredPrimeAtom_jet_eq {a σ u : ℝ} (ha : 1 / 2 < a) (hσ : 0 < σ) (N : ℕ)
    {n : ℕ} (hn : |u| < Real.log n) :
    xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a ((σ : ℂ) + (u : ℂ) * I) n
      = xiMassJetPrimeAtom a ((σ : ℂ) + (u : ℂ) * I) (2 * N) n :=
  xiMassPolyCenteredPrimeAtom_eq_jetPrimeAtom ha hσ N hn

end

end RHTower
