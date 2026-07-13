import GaloisForLFunctions.HTGeometry.EvaluationIncidenceFiberIndependence
import GaloisForLFunctions.HTGeometry.FiniteFamilyBlockHypersurfaceDimension

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- **Fixed-coefficient incidence-fiber dimension dichotomy.** Every nonzero coefficient tensor
has at least `card row - q` active rows. Either an active equation is a nonzero constant and the
fiber is empty, or the active equations in their independent row blocks cut iterated Krull
dimension by at least the number of active rows. -/
theorem coefficientIncidenceFiber_empty_or_krullDimDrop
    {row κ σ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (σ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (c : κ × Fin (q + 1) → ℂ) (hc : c ≠ 0) :
    Fintype.card row ≤ q + Fintype.card (coefficientGoodRow q z c) ∧
      ((∃ b : coefficientGoodRow q z c,
          ∀ x : σ → ℂ,
            MvPolynomial.eval x (coefficientRowPolynomial q exponent c (z b.1)) ≠ 0) ∨
        ringKrullDim
              (finiteFamilyBlockHypersurfaceRing
                (fun b : coefficientGoodRow q z c =>
                  coefficientRowPolynomial q exponent c (z b.1))) +
            Fintype.card (coefficientGoodRow q z c) ≤
          Fintype.card (coefficientGoodRow q z c) * Nat.card σ) := by
  classical
  refine ⟨coefficientGoodRow_card_lower q z hz c hc, ?_⟩
  by_cases hconst : ∃ b : coefficientGoodRow q z c,
      IsConstantMvPolynomial (coefficientRowPolynomial q exponent c (z b.1))
  · left
    obtain ⟨b, hb⟩ := hconst
    exact ⟨b, coefficientRowPolynomial_eval_ne_zero_of_constant
      q exponent hexponent c (z b.1) b.2 hb⟩
  · right
    apply finiteFamilyBlockHypersurfaceRing_krullDim_add_card_le
    intro b hb
    exact hconst ⟨b, hb⟩

end
end GaloisForLFunctions.HTGeometry
