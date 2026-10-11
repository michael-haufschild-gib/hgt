import GaloisForLFunctions.RHTower.DegreeThreeXiDivisibleConverse
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFiniteDeficit

/-!
# Even cubic data with finitely many `ξ` deficits are multiples of `ζ³`

For an even cubic datum (`E(1 − s) = E(s)`, `E(1) ≠ 0`), either `ξ`'s divisor is contained in
`E`'s at all but infinitely many points, or `L(g) = g(1) ζ³`
(`degreeThree_eq_zetaCube_or_infiniteDeficits_of_even`).  The finite deficit packet in the
Maass inversion defect is removed by the corpus boundary-period argument
(`poissonPacket_eq_zero_of_inversionDefect`); the remaining full divisibility is
`degreeThree_eq_zetaCube_of_xi_le`.  Unlike `degreeThree_eq_vonMangoldt_or_infiniteDeficits`,
no Weil correspondence, real-rootedness or positivity is assumed.
-/

noncomputable section

open Set Complex Polynomial

namespace RHTower.WeilHigherDenominator

open MaassBesselSeries

/-- **Even cubic data: `ζ³` or infinitely many `ξ` deficits.** -/
theorem degreeThree_eq_zetaCube_or_infiniteDeficits_of_even {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (heven : ∀ s, E (1 - s) = E s) :
    (∀ s : ℂ, 1 < s.re → LSeries g s = g 1 * riemannZeta s ^ 3) ∨
      (xiDeficitSupport E).Infinite := by
  classical
  rcases degreeThree_infiniteDeficits_or_spatialDefect hD hE1 with hi |
    ⟨P, H, ε, R, hm, _, he, ho, _, _, _, _, hs, hpacket⟩
  · exact Or.inr hi
  · have hε : ε = 1 := by
      apply mul_right_cancel₀ hE1
      rw [one_mul, ← he 1]
      exact heven 1
    have hzero := poissonPacket_eq_zero_of_inversionDefect P.roots.toFinset R
      (fun ρ hρ => ⟨(hs ρ hρ).1, (hs ρ hρ).2.1⟩)
      (maassFun_add_one (g := degreeTwoQuotientCoeff g)
        (degreeTwoEndpointNumerator E 1) (deriv (degreeTwoEndpointNumerator E) 1))
      (fun z hz => by simpa only [hε, one_mul] using hpacket z hz)
    have hp (z : ℂ) : P.eval z ≠ 0 := by
      intro hz
      have hmz : z ∈ P.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hm.ne_zero).mpr hz)
      exact (hs z hmz).2.2 (hzero z hmz)
    apply Or.inl
    refine (degreeThree_eq_zetaCube_of_xi_le hD hE1 fun z => ?_).2
    have hPA : AnalyticAt ℂ (fun w => P.eval w) z :=
      P.differentiable.differentiableOn.analyticAt Filter.univ_mem
    have hd : xiDeficit E z = 0 := by
      exact_mod_cast (ho z).symm.trans (hPA.analyticOrderAt_eq_zero.mpr (hp z))
    exact Nat.sub_eq_zero_iff_le.mp hd

/-- A non-`ζ³` even cubic datum loses `ξ` multiplicity at infinitely many points. -/
theorem infinite_xiDeficits_of_even_ne_zetaCube {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (heven : ∀ s, E (1 - s) = E s)
    (hne : ∃ s : ℂ, 1 < s.re ∧ LSeries g s ≠ g 1 * riemannZeta s ^ 3) :
    (xiDeficitSupport E).Infinite := by
  rcases degreeThree_eq_zetaCube_or_infiniteDeficits_of_even hD hE1 heven with h | h
  · obtain ⟨s, hs, hne⟩ := hne
    exact (hne (h s hs)).elim
  · exact h

end RHTower.WeilHigherDenominator
