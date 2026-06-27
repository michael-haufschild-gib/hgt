/-
# hRigid via the single-point repelling route, with the functional equation derived

A streamlined producer of the E–vS rigidity input `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` on the
genuine carrier `M = meroField U`, using the **single-point** repelling obstruction
(`BasinColimit.false_of_repelling_branch_global`). Unlike `RelativeRigidityCapstone.hrig_phiMero_of_repelling`,
the Böttcher functional equation `β(f^[p]z)=(βz)^{2^p}` is **no longer a hypothesis** of the per-relation
datum: it is derived once and for all from the global single-valued basin branch `β` (analytic on
`(K_{c₁})ᶜ`, `= bottcherCoord c₁` on `escapeOpen c₁`) via the identity theorem
(`BasinColimit.bottcherFE_iterate_of_global_branch`). The branch `β` is supplied a single time at top
level rather than re-existentially-quantified per relation.

This shrinks the connected-case dynamical residue to: the global single-valued branch `β` (the connected
Böttcher uniformization), plus, per cleared relation, a non-resonant repelling periodic point
`z₀ ∈ J_{c₁}∖K_{c₂}` (`ha` forces `z₀` into `c₂`'s basin) that is a simple root of the relation fibre,
with its basin boundary limit. The functional equation — previously an opaque input — is now a theorem.

New file (hRigid / connected lane, single-point route with the FE discharged).
-/
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.RelativeRigidityCapstone

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation via the single-point repelling route, FE derived from the global branch.** The branch
`β` (analytic on `(K_{c₁})ᶜ`, `= bottcherCoord c₁` on `escapeOpen c₁`) is supplied once; per cleared
relation, a non-resonant repelling period-`p` point `z₀ ∈ J_{c₁}∖K_{c₂}` with the simple-root and basin
boundary-limit datum suffices — `false_of_repelling_branch_global` supplies the functional equation
internally. -/
theorem noRelation_phiMero_of_repelling_global
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z₀) ∧
          (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w ^ i) d w₀ ∧ d ≠ 0 ∧
          w₀ ≠ 0 ∧ z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨z₀, w₀, d, lam, p, ha, hroot, hpartial, hd, hw₀, hz₀, hNeBot,
    hβlim, hβrel, hβne, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  exact false_of_repelling_branch_global hβan hβesc ha hroot hpartial hd hw₀ hz₀ hNeBot
    hβlim hβrel hβne hFz hlam hres

/-- **The hRigid connected-case input, single-point route, FE derived.** Composes
`noRelation_phiMero_of_repelling_global` with `transcendentalOverAdjoin_of_noRelation`: the rigidity
input `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` follows from `φ_{c₂}` transcendence (`hG`), the global
single-valued basin branch `β`, and, per cleared relation, the non-resonant repelling-cycle datum. The
Böttcher functional equation is no longer assumed — it is a proven consequence of `β` being a
single-valued branch (`bottcherFE_iterate_of_global_branch`). -/
theorem hrig_phiMero_of_repelling_global
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z₀) ∧
          (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w ^ i) d w₀ ∧ d ≠ 0 ∧
          w₀ ≠ 0 ∧ z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hinput)

/-- **hRigid reduced to per-level roots + the per-relation repelling datum.** Threads the whole built
chain: a coherent family of per-level single-valued `2ⁿ`-th roots `βlev n` (analytic, nonzero, anchored
to `bottcherCoord c₁` on `escapeOpen c₁`) assembles into the global branch `β`
(`BasinColimit.exists_global_branch_of_level_roots`); the Böttcher functional equation is then automatic
(`bottcherFE_iterate_of_global_branch`, inside `hrig_phiMero_of_repelling_global`); and the per-relation
non-resonant repelling-cycle datum about that `β` closes each relation. The output is the E–vS rigidity
input `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}`. The remaining inputs are now exactly: the per-level
roots (the connected Böttcher uniformization, modulo the cut-match winding identification) and, per
relation, a non-resonant repelling `z₀ ∈ J_{c₁}∖K_{c₂}` simple-root with its basin boundary limit. -/
theorem hrig_phiMero_of_level_roots
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z₀) ∧
          (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z₀) (bottcherCoord c₂ z₀)) * w ^ i) d w₀ ∧ d ≠ 0 ∧
          w₀ ≠ 0 ∧ z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc⟩ :=
    exists_global_branch_of_level_roots c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc
    (hinput β hβan hβesc)

end Bottcher
