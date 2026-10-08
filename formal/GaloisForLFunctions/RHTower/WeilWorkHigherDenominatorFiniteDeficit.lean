import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBoundaryPeriod
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCentralExclusion
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMultiplicity

/-!
# A nontrivial complete cubic datum has infinitely many xi-multiplicity deficits

The actual spatial packet, its boundary limit and both modular identities remove
every finite nonempty deficit divisor. All inputs are those of the original
degree-three correspondence. The infinite-deficit branch remains open.
-/

noncomputable section

open Set Complex Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

open MaassBesselSeries

/-- The exact complete cubic correspondence leaves no finite nonempty deficit alternative. -/
theorem degreeThree_eq_vonMangoldt_or_infiniteDeficits {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      (xiDeficitSupport E).Infinite := by
  classical
  rcases degreeThree_infiniteDeficits_or_spatialDefect hD hE1 with hi |
    ⟨P, H, ε, R, hm, _, he, ho, _, _, _, _, hs, hpacket⟩
  · exact Or.inr hi
  · have hpos := degreeThree_functional_equation hD hRH hsl hΛ
    have hε : ε = 1 := by
      apply mul_right_cancel₀ hE1
      rw [one_mul, ← he 1]
      exact hpos 1
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
    apply eq_vonMangoldt_of_xi_multiplicity_le hD hRH hsl hΛ
    intro z
    have hPA : AnalyticAt ℂ (fun w => P.eval w) z :=
      P.differentiable.differentiableOn.analyticAt Filter.univ_mem
    have hd : xiDeficit E z = 0 := by
      exact_mod_cast (ho z).symm.trans (hPA.analyticOrderAt_eq_zero.mpr (hp z))
    exact Nat.sub_eq_zero_iff_le.mp hd

/-- Any non-von-Mangoldt complete cubic datum loses zeta multiplicity at infinitely many points. -/
theorem infinite_xiDeficits_of_degreeThree_ne_vonMangoldt {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    (hne : ¬∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) :
    (xiDeficitSupport E).Infinite := by
  rcases degreeThree_eq_vonMangoldt_or_infiniteDeficits hD hE1 hRH hsl hΛ with h | h
  · exact (hne h.1).elim
  · exact h

end RHTower.WeilHigherDenominator
