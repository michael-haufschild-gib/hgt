import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInteriorPoles

/-!
# The actual logarithmic-polynomial theta defect

The exact residue identity becomes a finite packet with all pole orders retained.
Every interior clearing root lies in the open critical strip and contributes a
nonzero polynomial. Endpoint contributions remain explicit in the finite set.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- One family of polynomials represents all residues, with a sharp removability criterion. -/
theorem exists_poleCleared_residue_polynomials (P : Polynomial ℂ) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) :
    ∃ Q : ℂ → Polynomial ℂ,
      (∀ ρ : ℂ, ∀ x : ℝ, 0 < x →
        laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) ρ (-1) =
          (x : ℂ) ^ (-ρ) * (Q ρ).eval (Real.log x : ℂ)) ∧
      ∀ ρ : ℂ, Q ρ = 0 ↔ 0 ≤ meromorphicOrderAt (poleClearedDegreeTwoCompletion P H) ρ := by
  have h := fun ρ => exists_mellin_residue_polynomial (poleClearedDegreeTwoCompletion_meromorphicAt P hH ρ)
  choose Q hrep hzero using h
  exact ⟨Q, hrep, hzero⟩

/-- The original datum yields the actual finite logarithmic packet or infinitely many deficits. -/
theorem degreeThree_infiniteDeficits_or_logPolynomialDefect {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ) (ε : ℂ) (Q : ℂ → Polynomial ℂ),
        P.Monic ∧ ‖ε‖ = 1 ∧ (∀ s, E (1 - s) = ε * E s) ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        (∀ ρ : ℂ, Q ρ = 0 ↔ 0 ≤ meromorphicOrderAt (poleClearedDegreeTwoCompletion P H) ρ) ∧
        (∀ ρ ∈ P.roots.toFinset, 0 < ρ.re ∧ ρ.re < 1 ∧ Q ρ ≠ 0) ∧
        ∀ x : ℝ, 0 < x →
          MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x -
              ε * ((x : ℂ) ^ (-1 : ℂ) * MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x⁻¹) =
            (1 / 4 : ℂ) * ∑ ρ ∈ degreeTwoPoleSet P,
              (x : ℂ) ^ (-ρ) * (Q ρ).eval (Real.log x : ℂ) := by
  rcases degreeThree_infiniteDeficits_or_poleCleared hD hE1 with hi | ⟨P, H, hm, _, ho, hd, hg, h₁, hf⟩
  · exact Or.inl hi
  · obtain ⟨ε, hε, he⟩ := hD.exists_sign
    obtain ⟨Q, hrep, hzero⟩ := exists_poleCleared_residue_polynomials P hd
    refine Or.inr ⟨P, H, ε, Q, hm, hε, he, ho, hd, hg, h₁, hf, hzero, ?_, ?_⟩
    · intro ρ hρ
      have hp : P.eval ρ = 0 := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hρ)
      have hr := deficitPolynomial_root_re_mem_Ioo P ho hp
      refine ⟨hr.1, hr.2, ?_⟩
      intro hq
      exact (not_le_of_gt (poleClearedDegreeTwoCompletion_order_neg_at_root
        hD.entire hE1 hd h₁ P hf ho hp)) ((hzero ρ).mp hq)
    · intro x hx
      rw [degreeTwoQuotient_theta_defect hD he P hm.ne_zero hd hg hf ho hx]
      congr 1
      exact Finset.sum_congr rfl fun ρ _ => hrep ρ x hx

end RHTower.WeilHigherDenominator
