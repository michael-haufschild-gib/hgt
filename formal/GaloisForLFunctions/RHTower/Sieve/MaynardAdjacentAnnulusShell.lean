import GaloisForLFunctions.RHTower.Sieve.MaynardOrdinateShellReparameterization

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- **Annulus-to-canonical-shell bridge.** Reflection chooses a positive central or outer wing;
the ordinate telescope then chooses a comparable shell and canonically resets the Heath--Brown
height without changing the aggregate. Endpoint power bounds keep the new exponent in the full
Route-T range. -/
theorem exists_reparametrized_comparable_ordinate_shell_of_adjacent_annulus
    (L X k : ℕ) {T₀ mu₀ N H R B U T V : ℝ}
    (hX : 1 ≤ X) (hT₀ : 1 < T₀) (hX₀ : T₀ ^ mu₀ = X)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hU : 1 < U) (hUT : U ≤ T) (hTV : T ≤ V)
    (hmuLo : V ^ (4 / 3 : ℝ) ≤ X) (hmuHi : (X : ℝ) ≤ U ^ (8 : ℝ))
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) N
            ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖) :
    ∃ A C : ℝ,
      ((A = U ∧ C = T) ∨ (A = T ∧ C = V)) ∧
      U ≤ A ∧ A ≤ C ∧ C ≤ V ∧
      ∃ J : ℕ, 0 < J ∧
        (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ C / A ∧
        C / A < (((2 ^ J : ℕ) : ℝ)) ∧
        ∃ j ∈ Finset.range J,
          let T₁ := routeTComparableWidthLadder A C (j + 1)
          let mu₁ := routeTExactCutoffExponent T₁ X
          T₁ ∈ Set.Icc A C ∧
          routeTComparableWidthLadder A C j ≤ 2 * T₁ ∧
          T₁ ^ mu₁ = X ∧
          mu₁ ∈ Set.Icc (4 / 3 : ℝ) 8 ∧
          (B / 4) / (J : ℝ) ≤ ‖∫ y in T₁..routeTComparableWidthLadder A C j,
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) N
                ((1 : ℂ) + (y : ℝ) * I) *
              (routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * I))‖ := by
  have hwing := exists_positive_interval_norm_ge_quarter_of_adjacent_annulus
    L X k T₀ (mu₀ / 120) hN hH hR (by linarith) hUT hTV hB
  obtain ⟨A, C, hchoice, hUA, hAC, hCV, hlarge⟩ :
      ∃ A C : ℝ,
        ((A = U ∧ C = T) ∨ (A = T ∧ C = V)) ∧
        U ≤ A ∧ A ≤ C ∧ C ≤ V ∧
        B / 4 ≤ ‖∫ y in A..C,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) N
              ((1 : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ := by
    rcases hwing with hcentral | houter
    · exact ⟨U, T, Or.inl ⟨rfl, rfl⟩, le_rfl, hUT, hTV, hcentral⟩
    · exact ⟨T, V, Or.inr ⟨rfl, rfl⟩, hUT, hTV, le_rfl, houter⟩
  have hA : 1 < A := hU.trans_le hUA
  obtain ⟨J, hJ, hbelow, habove, j, hj, hTmem, hcomp, hX₁, hshell⟩ :=
    exists_reparametrized_comparable_ordinate_shell_integral_norm_ge
      L X k hX hT₀ hX₀ hN hH hR (by norm_num : (0 : ℝ) < 1)
        hA hAC hlarge
  let T₁ : ℝ := routeTComparableWidthLadder A C (j + 1)
  let mu₁ : ℝ := routeTExactCutoffExponent T₁ X
  have hTglobal : T₁ ∈ Set.Icc U V :=
    ⟨hUA.trans hTmem.1, hTmem.2.trans hCV⟩
  have hmurange : mu₁ ∈ Set.Icc (4 / 3 : ℝ) 8 :=
    routeTExactCutoffExponent_mem_fourThird_eight_of_ordinate_interval
      hX hU hTglobal hmuLo hmuHi
  refine ⟨A, C, hchoice, hUA, hAC, hCV, J, hJ, hbelow, habove,
    j, hj, ?_⟩
  dsimp only
  exact ⟨hTmem, hcomp, hX₁, hmurange, hshell⟩

end RHTower.Sieve
