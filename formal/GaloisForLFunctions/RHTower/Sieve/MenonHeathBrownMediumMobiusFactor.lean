import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSixFactorDichotomy
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusPowerSaving

/-!
# Menon's medium Heath--Brown Mobius factor

A literal Mobius atom selected from the degree-three Heath--Brown packet inherits the corpus's
unconditional Route-T power saving.  The theorem keeps the actual box exponent, truncation cutoff,
ordinate, and contour parameters; no replacement coefficient family or analytic premise is used.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A literal Mobius atom selected from a Heath--Brown box inherits the unconditional Route-T
power saving, with its actual box exponent and truncation cutoff unchanged. -/
theorem exists_norm_heathBrownBoxFactorValue_moebius_le_routeTPower :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
          (i : HeathBrownBoxFactorIndex k box.m) (c tau U : ℝ),
        heathBrownBoxFactorKind k box.m i = .moebius →
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i →
        2 ^ heathBrownBoxFactorExponent box.a box.b box.q i ≤ L →
        0 ≤ c →
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
            (4 : ℕ) ≤ U →
        routeTInverseBaseHeight + U ≤ |tau| →
        ‖heathBrownBoxFactorValue L X k box
            ((c : ℂ) + (tau : ℝ) * Complex.I) i‖ ≤
          2 * routeTMoebiusPowerConstant C C' *
            routeTContourEdgeBound A (|tau| + U) *
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
              (1 - c - routeTContourShift A delta (|tau| + U) / 3) := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hmain⟩ :=
    exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  intro L X k box i c tau U hkind hq hqL hc hU hsep
  rcases i with i | i
  · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
      heathBrownBoxFactorExponent, heathBrownFactorBase] using
      hmain L (box.a i) c tau U hq hqL hc hU hsep
  · rcases i with i | i <;> simp [heathBrownBoxFactorKind] at hkind

end


end RHTower.Sieve
