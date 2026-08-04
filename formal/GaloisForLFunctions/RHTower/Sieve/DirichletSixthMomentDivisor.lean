import GaloisForLFunctions.RHTower.Sieve.DirichletSixthMoment
import GaloisForLFunctions.RHTower.Sieve.CubeFibreDivisorBound

/-!
# The sixth-moment estimate, unconditionally

Feeding the divisor bound on the fibres into `sixthMoment_dirPoly` removes the last hypothesis: for
every `ε > 0` there is an absolute `C` with

    ∑_r |F(λ_r)|⁶ ≤ (T + 4N³(1+log N³))(δ^{-1} + 2log N³) · C N^ε · (∑_n |a_n|²)³

for every Dirichlet polynomial of length `N` and every `δ`-separated family of frequencies in
`[δ/2, T−δ/2]`.  Dividing by `V⁶` caps the number of frequencies where `|F| ≥ V`.

The `N^ε` is the divisor bound and is unavoidable in this form; it is negligible against the powers
of `N` already present.
-/

namespace RHTower.Sieve

open Finset

/-- **The sixth moment of a Dirichlet polynomial, with no hypothesis on the fibres.** -/
theorem exists_sixthMoment_dirPoly_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : Fin N → ℂ) (lam : ℕ → ℝ) (δ T : ℝ) (R : ℕ),
      2 ≤ N → 0 < δ → 0 ≤ T → (∀ i, lam i + δ ≤ lam (i + 1)) → δ / 2 ≤ lam 0 →
      lam R + δ / 2 ≤ T →
      ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 6
        ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
            * (1 / δ + 2 * Real.log ((N ^ 3 : ℕ) : ℝ))
            * (C * (N : ℝ) ^ ε * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  obtain ⟨C, hC, hfib⟩ := exists_cubeFibre_card_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro N a lam δ T R hN hδ hT hgap hlow hhigh
  exact sixthMoment_dirPoly N hN a hδ hT hgap hlow R hhigh
    (fun j => hfib N (by omega) j)

/-- **The large-value count, with no hypothesis on the fibres.** -/
theorem exists_card_largeValues_sixth_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : Fin N → ℂ) (lam : ℕ → ℝ) (δ T V : ℝ) (R : ℕ),
      2 ≤ N → 0 < δ → 0 ≤ T → 0 < V → (∀ i, lam i + δ ≤ lam (i + 1)) → δ / 2 ≤ lam 0 →
      lam R + δ / 2 ≤ T →
      (∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) →
      ((R : ℝ) + 1) * V ^ 6
        ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
            * (1 / δ + 2 * Real.log ((N ^ 3 : ℕ) : ℝ))
            * (C * (N : ℝ) ^ ε * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  obtain ⟨C, hC, hfib⟩ := exists_cubeFibre_card_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro N a lam δ T V R hN hδ hT hV hgap hlow hhigh hbig
  exact card_largeValues_sixth_le N hN a hδ hT hV hgap hlow R hhigh
    (fun j => hfib N (by omega) j) hbig

end RHTower.Sieve
