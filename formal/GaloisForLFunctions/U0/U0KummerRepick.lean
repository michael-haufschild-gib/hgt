/-
# u₀ ⟂ φ_b via the Kummer **re-pick** route (tower-free), transcendence discharged

The Böttcher agent's `Bottcher.noRelation_of_kummer_repick` proves `NoRelation K F G` from a *per-degree*
Kummer carrier — re-picking a single finite radical extension `M = AdjoinRoot(X^{2ⁿ}−a)` deep enough to
kill each fixed-degree relation, with **no infinite tower**. It is generic in the fixed base element `G`,
so the u₀ case `(F = φ_b, G = u₀)` reuses it directly.

This file performs that instantiation for u₀ at the genuine carrier `meroField U` (`U` a deep ball in
`Ext ∩ escapeOpen b`), discharging the `Transcendental ℂ(z) u₀` conjunct of the `data` from the committed
`U0MeroCarrier.u0Mero_transcendental` (pulled back along the injective descent `ψ`). The result reduces
`NoRelation ℂ(z) φ_b u₀` to **exactly** the φ_b carrier `data` (the radicand `a = φ_b∘f^[k]`, the
irreducibility of `X^{2ⁿ}−a`, the descent `ψ`, and the Kummer deck `σ`) — the parallel Böttcher
construction. No tower, no monodromy hypothesis: the lone remaining input is the φ_b radical data.
-/
import GaloisForLFunctions.U0.U0MeroCarrier
import GaloisForLFunctions.Bottcher.KummerDeck

open Polynomial Filter Topology Bottcher U0MeroCarrier

namespace U0KummerRepick

variable {U : Set ℂ}

/-- **u₀ ⟂ φ_b — the tower-free Kummer re-pick closure (transcendence discharged).** Given, for each
relation degree `d`, a finite Kummer carrier `M` with an injective `ℂ(z)`-algebra descent `ψ : M → meroField U`
sending the root to `φ_b` and a base element to `u₀`, a deck `σ` of order `> d` scaling the root and fixing
`u₀`, this yields `NoRelation ℂ(z) φ_b u₀` — via `noRelation_of_kummer_repick`. The `Transcendental ℂ(z) u₀`
the abstract lemma asks for is supplied here from `u0Mero_transcendental` (transcendence pulls back along the
injective `ψ`), so the `data` hypothesis carries only the φ_b radical structure. -/
theorem u0_phib_noRelation_repick (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (data : ∀ d : ℕ,
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∃ (M : Type) (_ : Field M) (_ : Algebra (RatFunc ℂ) M)
        (ψ : M →ₐ[RatFunc ℂ] meroField U) (Fk Gk ζ : M) (σ : M ≃ₐ[RatFunc ℂ] M),
        Function.Injective ψ ∧ ψ Fk = phiMero b hU_esc ∧
        ψ Gk = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) ∧
        Fk ≠ 0 ∧ d < orderOf ζ ∧ σ Gk = Gk ∧ σ ζ = ζ ∧ σ Fk = ζ * Fk) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hGtr := u0Mero_transcendental hUo hUc hUne hUinf hU_ext
  apply noRelation_of_kummer_repick
  intro d
  obtain ⟨M, fM, aM, ψ, Fk, Gk, ζ, σ, hinj, hF, hG, hFk, hd, hσG, hσζ, hσF⟩ := data d
  refine ⟨M, fM, aM, ψ, Fk, Gk, ζ, σ, hinj, hF, hG, ?_, hFk, hd, hσG, hσζ, hσF⟩
  intro halg
  obtain ⟨p, hp, hpeval⟩ := halg
  exact hGtr ⟨p, hp, by rw [← hG, Polynomial.aeval_algHom_apply, hpeval, map_zero]⟩

end U0KummerRepick
