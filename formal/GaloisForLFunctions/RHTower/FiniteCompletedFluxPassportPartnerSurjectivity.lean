import GaloisForLFunctions.HTGeometry.EulerContractionResidueSigns
import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportJetSurjectivity
import GaloisForLFunctions.RHTower.FluxGermSchwarzSymmetry

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The completed-flux jet forced at each member of a quartet by evenness and Schwarz reality. -/
def quartetFluxJet (c : ℕ → ℂ) : Fin 4 → ℕ → ℂ
  | 0, k => c k
  | 1, k => (-1 : ℂ) ^ k * c k
  | 2, k => (starRingEnd ℂ) (c k)
  | 3, k => (-1 : ℂ) ^ k * (starRingEnd ℂ) (c k)

/-- Every finite completed-flux passport with forced residue `-1` is realized on its full
quartet orbit. Every quartet point is a simple zero, and every quartet jet is the exact
even/Schwarz transport of the freely prescribed primary jet. -/
theorem exists_quartet_passport_flux_realizer_of_full_finite_jet_passport
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (α : J → ℂ) (N : J → ℕ) (c : J → ℕ → ℂ)
    (hc0 : ∀ j, c j 0 = -1)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetPoint (α i.1) i.2)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ B : Polynomial ℂ,
      0 < B.degree ∧
      (∀ z : ℂ, quartetRealizer a₀ B (-z) = quartetRealizer a₀ B z) ∧
      (∀ z : ℂ, quartetRealizer a₀ B ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (quartetRealizer a₀ B z)) ∧
      (∀ y : ℝ, quartetRealizer a₀ B ((y : ℂ) * Complex.I) ≠ 0) ∧
      (∀ h : ℂ, Function.Periodic (quartetRealizer a₀ B) h → h = 0) ∧
      (∃ Kupper Klower R : ℝ,
        0 < Kupper ∧ 0 < Klower ∧
        (∀ z : ℂ, ‖quartetRealizer a₀ B z‖ ≤
          Kupper * (1 + ‖z‖) ^ B.natDegree * Real.exp (2 * ‖z‖)) ∧
        ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤ ‖quartetRealizer a₀ B (x : ℂ)‖) ∧
      (∀ i : J × Fin 4,
        quartetRealizer a₀ B (quartetPoint (α i.1) i.2) = 0 ∧
        deriv (quartetRealizer a₀ B) (quartetPoint (α i.1) i.2) ≠ 0) ∧
      ∀ (j : J) (q : Fin 4) (k : ℕ), k ≤ N j →
        iteratedDeriv k
          (fluxGerm (quartetRealizer a₀ B) (quartetPoint (α j) q)) 0 =
            quartetFluxJet (c j) q k := by
  obtain ⟨a₀, ha₀, B, hdeg, heven, hreal, haxis, hperiod, horder, hsimple, hflux⟩ :=
    exists_quartet_passport_flux_realizer_of_finite_jet_passport α N c hc0 hαre hinj
  have hf : ∀ z, AnalyticAt ℂ (quartetRealizer a₀ B) z :=
    quartetRealizer_analyticAt a₀ B
  have hord (j : J) : analyticOrderAt (quartetRealizer a₀ B) (α j) = (1 : ℕ) :=
    (hf (α j)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (hsimple j).1 (hsimple j).2
  refine ⟨a₀, ha₀, B, hdeg, heven, hreal, haxis, hperiod, horder, ?_, ?_⟩
  · rintro ⟨j, q⟩
    fin_cases q
    · simpa [quartetPoint] using hsimple j
    · constructor
      · simpa [quartetPoint] using (heven (α j)).trans (hsimple j).1
      · simpa [quartetPoint, deriv_neg_of_even heven] using
          (neg_ne_zero.mpr (hsimple j).2)
    · constructor
      · simp [quartetPoint, hreal, (hsimple j).1]
      · simpa [quartetPoint, deriv_conj_of_conjEquivariant hreal] using
          ((map_ne_zero (starRingEnd ℂ)).mpr (hsimple j).2)
    · constructor
      · simp [quartetPoint, heven, hreal, (hsimple j).1]
      · simpa [quartetPoint, deriv_neg_of_even heven,
          deriv_conj_of_conjEquivariant hreal] using
          (neg_ne_zero.mpr ((map_ne_zero (starRingEnd ℂ)).mpr (hsimple j).2))
  · intro j q k hk
    have hprimary := hflux j k hk
    fin_cases q
    · simpa [quartetPoint, quartetFluxJet] using hprimary
    · have hneg := iteratedDeriv_fluxGerm_neg_of_even
          heven hf (hord j) k
      simpa [quartetPoint, quartetFluxJet, hprimary] using hneg
    · have hordconj :
          analyticOrderAt (quartetRealizer a₀ B) ((starRingEnd ℂ) (α j)) =
            analyticOrderAt (quartetRealizer a₀ B) (α j) :=
        analyticOrderAt_conj_of_conjEquivariant hreal
          (hf (α j)) (hf ((starRingEnd ℂ) (α j)))
      have hconj := iteratedDeriv_fluxGerm_conj_of_conjEquivariant hreal hordconj k
      simpa [quartetPoint, quartetFluxJet, hprimary] using hconj
    · have hnegconj :=
          iteratedDeriv_fluxGerm_neg_conj_of_even_conjEquivariant
            heven hreal hf (hord j) k
      simpa [quartetPoint, quartetFluxJet, hprimary] using hnegconj

end RHTower
