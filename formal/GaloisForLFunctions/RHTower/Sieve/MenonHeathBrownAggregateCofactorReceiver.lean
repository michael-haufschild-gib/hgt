import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownAggregateCofactorCauchy

/-!
# Selected-factor receiver for the full Heath--Brown aggregate with a cofactor

Finite Cauchy first exposes every literal degree-three box.  A distinguished factor in each box
is then bounded pointwise, while fixed-shift Montgomery pays its erase-complement together with
the original unshifted Dirichlet cofactor.  Thus no product length is discarded.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Exact complementary Montgomery cost after pointwise excision of one selected factor. -/
def menonHeathBrownSelectedFactorCofactorCost
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (epsilon C sigma V delta T : ℝ) (M : ℕ) (b : Fin M → ℂ) : ℝ :=
  V ^ 2 *
    ((T + 4 *
          ((groupedDyadicUpper (menonHeathBrownComplementExponent box j)) * M : ℕ) *
          (1 + Real.log
            ((groupedDyadicUpper (menonHeathBrownComplementExponent box j)) * M))) *
      (1 / delta + 2 * Real.log
        ((groupedDyadicUpper (menonHeathBrownComplementExponent box j)) * M)) *
      (C *
        ((((groupedDyadicUpper (menonHeathBrownComplementExponent box j)) * M : ℕ) : ℝ)) ^
            epsilon *
          ((((groupedDyadicLower (menonHeathBrownComplementExponent box j) : ℝ) ^
              (-sigma)) ^ 2 *
            ((groupedDyadicUpper (menonHeathBrownComplementExponent box j) : ℝ) *
              (1 + Real.log
                (groupedDyadicUpper (menonHeathBrownComplementExponent box j) : ℝ)) ^
                (2 * Fintype.card (menonHeathBrownComplementIndex box j) +
                  (2 ^ (2 * Fintype.card (menonHeathBrownComplementIndex box j)) - 1)))) *
            ∑ m : Fin M, ‖b m‖ ^ 2)))

/-- The complete window-relevant degree-three aggregate inherits selected-factor Montgomery
box by box while an arbitrary cofactor remains at every original frequency. -/
theorem exists_sum_normSq_windowRelevantAggregate_mul_dirPoly_le_selectedFactor
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (T0 t N : ℝ) (M : ℕ), 1 ≤ M →
      ∀ (b : Fin M → ℂ) (u : ℝ)
        (j : (box : HeathBrownBoxChoice L X 3) →
          HeathBrownBoxFactorIndex 3 box.m)
        (V : HeathBrownBoxChoice L X 3 → ℝ) {sigma : ℝ},
        0 ≤ sigma → (∀ box, 0 ≤ V box) →
        ∀ {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ},
        0 < delta → 0 ≤ T →
        (∀ i, lam i + delta ≤ lam (i + 1)) →
        (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) →
        (∀ box, ∀ r ∈ S,
          ‖heathBrownBoxFactorValue L X 3 box
            ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) (j box)‖ ≤ V box) →
        ∑ r ∈ S,
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 3 T0 t N
                ((sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I) *
              dirPoly M b (-lam r)‖ ^ 2 ≤
          (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 64 *
            ∑ box : HeathBrownBoxChoice L X 3,
              menonHeathBrownSelectedFactorCofactorCost box (j box)
                epsilon C sigma (V box) delta T M b := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_meanSquare_heathBrownBox_shift_mul_dirPoly_le_selectedFactor hepsilon
  refine ⟨C, hC, ?_⟩
  intro L X T0 t N M hM b u j V sigma hsigma hV S lam delta T hdelta hT hgap hband
    hselected
  have haggregate := sum_normSq_windowRelevantAggregate_mul_le_boxCores
    L X T0 t N S
      (fun r => (sigma : ℂ) + ((u + lam r : ℝ) : ℂ) * Complex.I)
      (fun r => dirPoly M b (-lam r))
  refine haggregate.trans ?_
  gcongr with box
  have hbox := hmean L X 3 box (j box) hsigma (hV box) M hM b u
    hdelta hT hgap hband (hselected box)
  simpa only [menonHeathBrownSelectedFactorCofactorCost] using hbox

end

end RHTower.Sieve
