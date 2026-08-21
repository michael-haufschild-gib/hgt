import GaloisForLFunctions.RHTower.MackeyFlatDivisorSelection
import GaloisForLFunctions.HTGeometry.GlobalRegularInertiaCalkin

/-!
# Global compact-formation selection for the Euler-shell divisor

The local charges of the survival transfer are the strict-right zeta orders.  Compact, Schatten
and determinant-class formation of the global regular inertia packet attached to those charges are
each equivalent to the Riemann hypothesis.
-/

open Complex GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.LpDiagonal

namespace RHTower

noncomputable section

/-- **Corollary 6.1 — global compact-formation selection for the Euler shell.**  Vanishing of the
strict-right divisor, compactness of every local global-inertia packet, Schatten membership of
every such packet, and determinant-class membership of every such packet are each equivalent to
the Riemann hypothesis. -/
theorem riemannHypothesis_tfae_globalInertia :
    List.TFAE
      [ RiemannHypothesis,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → localFormationCharge ρ = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          IsCompactOperator (globalInertiaDefect (localFormationCharge ρ)),
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          ∃ p : ℝ, 0 < p ∧ MemSchattenClass p (globalInertiaDefect (localFormationCharge ρ)),
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          MemSchattenClass 1 (globalInertiaDefect (localFormationCharge ρ)) ] := by
  tfae_have 1 → 2 := by
    intro hrh ρ hρ hρ1
    exact (localFormationCharge_eq_zero_iff hρ1).2
      (riemannHypothesis_iff_zetaZeroFreeRight.1 hrh ρ hρ hρ1)
  tfae_have 2 → 3 := fun h ρ hρ hρ1 =>
    ((globalInertia_tfae (localFormationCharge ρ)).out 0 2).1 (h ρ hρ hρ1)
  tfae_have 3 → 4 := fun h ρ hρ hρ1 =>
    ((globalInertia_tfae (localFormationCharge ρ)).out 2 3).1 (h ρ hρ hρ1)
  tfae_have 4 → 5 := fun h ρ hρ hρ1 =>
    ((globalInertia_tfae (localFormationCharge ρ)).out 3 4).1 (h ρ hρ hρ1)
  tfae_have 5 → 1 := by
    intro h
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 => ?_
    refine (localFormationCharge_eq_zero_iff hρ1).1 ?_
    exact ((globalInertia_tfae (localFormationCharge ρ)).out 4 0).1 (h ρ hρ hρ1)
  tfae_finish

/-- **The global inertia mark is faithful on the strict-right divisor.**  Two points whose global
inertia unitaries differ by a compact operator carry the same local order. -/
theorem localFormationCharge_eq_of_isCompactOperator_sub {ρ σ : ℂ}
    (h : IsCompactOperator
      (globalInertiaCLM (localFormationCharge ρ) - globalInertiaCLM (localFormationCharge σ))) :
    localFormationCharge ρ = localFormationCharge σ :=
  globalInertiaCLM_eq_of_isCompactOperator_sub h

/-- **No compact repair of a zeta zero.**  At a strict-right zero of zeta the global inertia
defect stays at essential distance two from the compact operators. -/
theorem two_le_norm_globalInertiaDefect_sub_of_zetaZero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0)
    {K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex} (hK : IsCompactOperator K) :
    2 ≤ ‖globalInertiaDefect (localFormationCharge ρ) - K‖ := by
  refine two_le_norm_globalInertiaDefect_sub (fun hc => ?_) hK
  exact ((localFormationCharge_eq_zero_iff hρ1).1 hc) hzero

end

end RHTower
