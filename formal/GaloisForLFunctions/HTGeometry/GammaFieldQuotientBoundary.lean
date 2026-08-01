import GaloisForLFunctions.HTGeometry.GammaFieldShapeConvergence

/-!
# The projective boundary of a quotient in the Gamma field

Every element of `ℂ(s)⟨Γ⟩` is a quotient of two Gamma polynomials over `ℂ(s)⟨ψ⟩`.  Each of them
converges against the Gamma-jet shape of its lowest power, so as soon as the denominator's residue is
nonzero the quotient converges against the ratio of the two shapes — to the quotient of the residues
times that ratio.

This is eq. (23) → (3) for the field rather than the ring.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The projective boundary of a Gamma-field quotient.**  With both numerator and denominator
presented by their Gamma-jet data and the denominator's residue nonzero, the quotient converges
against the ratio of the shapes. -/
theorem tendsto_gammaFieldQuotient (hσ : 0 < σ) {dA dB : ℕ} (A B : ℕ → ℝ → ℂ) (uA uB : ℕ)
    (huA : uA ≤ dA) (huB : uB ≤ dB) (aA dPA bA aB dPB bB : ℕ) (csA csB : ℕ → ℂ)
    (hcB : csB uB ≠ 0)
    (hconvA : ∀ i, Tendsto (fun t : ℝ => A i t / polyJetShape σ aA dPA bA t) atTop (nhds (csA i)))
    (hconvB : ∀ i, Tendsto (fun t : ℝ => B i t / polyJetShape σ aB dPB bB t) atTop (nhds (csB i)))
    (hlowA : ∀ i < uA, A i = fun _ => 0) (hlowB : ∀ i < uB, B i = fun _ => 0)
    {r : ℂ} (hr : Tendsto (fun t : ℝ =>
      gammaJetShape σ uA aA dPA bA t / gammaJetShape σ uB aB dPB bB t) atTop (nhds r)) :
    Tendsto (fun t : ℝ => (∑ i ∈ Finset.range (dA + 1), A i t * gammaLine σ t ^ i)
        / (∑ i ∈ Finset.range (dB + 1), B i t * gammaLine σ t ^ i)) atTop
      (nhds (csA uA * r / csB uB)) := by
  refine tendsto_ratio_of_normalized hcB
    (eventually_gammaJetShape_ne_zero hσ uA aA dPA bA)
    (eventually_gammaJetShape_ne_zero hσ uB aB dPB bB)
    (tendsto_gammaField_div_gammaJetShape hσ A uA huA aA dPA bA csA hconvA hlowA)
    (tendsto_gammaField_div_gammaJetShape hσ B uB huB aB dPB bB csB hconvB hlowB) hr

end GaloisForLFunctions
