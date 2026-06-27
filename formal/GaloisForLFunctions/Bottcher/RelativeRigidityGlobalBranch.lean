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

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation via the global-branch repelling route, with boundary nonzero derived from modulus.**
Compared with `noRelation_phiMero_of_repelling_global`, the per-relation datum no longer carries
`w₀ ≠ 0`; it follows from the global branch modulus and the basin-side boundary limit. -/
theorem noRelation_phiMero_of_repelling_global_modulus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
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
  obtain ⟨z₀, w₀, d, lam, p, ha, hroot, hpartial, hd, hz₀, hNeBot,
    hβlim, hβrel, hβne, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  exact false_of_repelling_branch_global_modulus hβan hβesc hβmod ha hroot hpartial hd hz₀ hNeBot
    hβlim hβrel hβne hFz hlam hres

/-- **The hRigid input via a modulus-carrying global branch.** This repackages
`noRelation_phiMero_of_repelling_global_modulus` as the exact `TranscendentalOverAdjoin` input consumed by
`q62_both_connected`, while deriving the boundary nonzero datum internally. -/
theorem hrig_phiMero_of_repelling_global_modulus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
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
    (noRelation_phiMero_of_repelling_global_modulus hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β
      hβan hβesc hβmod hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **hRigid from level roots with boundary nonzero eliminated.** The level-root family now assembles
into a global branch carrying both nonvanishing and the Böttcher modulus on the whole basin
(`exists_global_branch_of_level_roots_modulus`). Hence the per-relation repelling datum no longer needs
`w₀ ≠ 0`: it is derived from the basin-side modulus and boundary limit inside
`hrig_phiMero_of_repelling_global_modulus`. -/
theorem hrig_phiMero_of_level_roots_modulus
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
        (∀ z ∈ (filledJulia c₁)ᶜ, β z ≠ 0) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
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
  obtain ⟨β, hβan, hβesc, hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β
    hβan hβesc hβmod (hinput β hβan hβesc hβ0 hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation via a modulus-carrying global branch, with `β ≠ w₀` also derived.** Compared with
`noRelation_phiMero_of_repelling_global_modulus`, the per-relation datum no longer supplies the
frequent non-constancy condition `∃ᶠ z, β z ≠ w₀`; the basin-wide modulus and boundary limit force it. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_ne
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨z₀, w₀, d, lam, p, ha, hroot, hpartial, hd, hz₀, hNeBot,
    hβlim, hβrel, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  exact false_of_repelling_branch_global_modulus_auto_ne hβan hβesc hβmod ha hroot hpartial hd
    hz₀ hNeBot hβlim hβrel hFz hlam hres

/-- **The hRigid input via a modulus-carrying global branch, with all boundary side conditions derived.**
The per-relation repelling datum only supplies the simple-root, boundary-limit, relation, periodicity, and
non-resonance facts; `w₀ ≠ 0` and `∃ᶠ z, β z ≠ w₀` are consequences of the modulus. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_ne
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_ne hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β
      hβan hβesc hβmod hinput)

/-- **hRigid from level roots with all modulus-derived boundary side conditions eliminated.** The level
roots produce a global branch with nonvanishing and basin-wide modulus; the modulus then supplies both
`w₀ ≠ 0` and `∃ᶠ z, β z ≠ w₀` for every boundary-limit datum. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_ne
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
        (∀ z ∈ (filledJulia c₁)ᶜ, β z ≠ 0) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * (β z) ^ i = 0) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc, hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_ne hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β
    hβan hβesc hβmod (hinput β hβan hβesc hβ0 hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with the relation filter derived from analytic coefficient continuation.** In the
modulus-carrying global-branch route, the per-relation datum no longer needs to supply the basin-side
relation filter. It is enough to provide analytic continuations `a i` of the cleared coefficients on the
`c₁` basin that match the original coefficients on the carrier `U`; the open-witness identity theorem
spreads the relation from `U` to the whole basin. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, z₀, w₀, d, lam, p, ha, ha_z₀, hmatch, hroot, hpartial, hd, hz₀, hNeBot,
    hβlim, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc
      ∑ i ∈ s, a i z * (β z) ^ i
          = ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    relation_eq_zero_basin_analytic_of_open hUo hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
  have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
  exact false_of_repelling_branch_global_modulus_auto_ne hβan hβesc hβmod ha_z₀ hroot hpartial hd
    hz₀ hNeBot hβlim hβrel hFz hlam hres

/-- **hRigid via a modulus branch and analytic coefficient continuations.** This packages
`noRelation_phiMero_of_repelling_global_modulus_auto_relation` as the `TranscendentalOverAdjoin` input:
the relation filter, the nonzero boundary value, and the frequent boundary exclusion are all derived
internally. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      hG β hβan hβesc hβmod hinput)

/-- **hRigid from level roots and analytic coefficient continuations.** The level roots produce the
modulus-carrying global branch; analytic coefficient continuations matching the original cleared
coefficients on `U` then make the relation filter automatic. This is the current strongest hRigid
level-root interface. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_relation
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
        (∀ z ∈ (filledJulia c₁)ᶜ, β z ≠ 0) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc, hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG β hβan hβesc hβmod (hinput β hβan hβesc hβ0 hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with coefficient smoothness derived from `AnalyticAt`.** This strengthens
`noRelation_phiMero_of_repelling_global_modulus_auto_relation`: the per-relation datum supplies analytic
coefficient continuations on the basin and `AnalyticAt` at the boundary point; the `ContDiffAt` input
needed by the local algebraic-branch obstruction is derived by `AnalyticAt.contDiffAt`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, d, lam, p, ha, ha_z₀, hmatch, hroot, hpartial, hd, hz₀, hNeBot,
        hβlim, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
      exact ⟨a, z₀, w₀, d, lam, p, ha, (fun i hi => (ha_z₀ i hi).contDiffAt), hmatch, hroot,
        hpartial, hd, hz₀, hNeBot, hβlim, hFz, hlam, hres⟩)

/-- **hRigid with coefficient smoothness derived from `AnalyticAt`.** The relation filter, boundary
nonzero, frequent boundary exclusion, and `ContDiffAt` coefficient datum are all internal consequences of
the supplied analytic continuations and branch modulus. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_analyticAt
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with coefficient smoothness derived from `AnalyticAt`.** This is the strongest
current level-root hRigid interface: level roots give the global modulus branch; analytic coefficient
continuations matching on `U` give the relation filter; `AnalyticAt` gives the local smoothness input. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_analyticAt
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
        (∀ z ∈ (filledJulia c₁)ᶜ, β z ≠ 0) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc, hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_analyticAt hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG β hβan hβesc hβmod (hinput β hβan hβesc hβ0 hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Level-root hRigid with minimal branch data passed to the callback.** Compared with
`hrig_phiMero_of_level_roots_modulus_auto_analyticAt`, the callback no longer receives a separate
nonvanishing proof for `β`; if it needs that fact it follows from `branch_ne_zero_of_modulus` and the
modulus argument already passed here. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_analyticAt_minBranch
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_analyticAt hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc _hβ0 hβmod
      exact hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with the fibre derivative computed internally.** Compared with
`noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt`, the per-relation datum supplies only
nonvanishing of the canonical fibre derivative. The `HasDerivAt` witness is exactly
`relation_hasDerivAt_w_analytic`, so no separate derivative proof or auxiliary `d` is part of the
interface. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_fibreDerivative
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hroot, hderiv, hz₀, hNeBot,
        hβlim, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
      exact ⟨a, z₀, w₀, (fibrePoly a s z₀).derivative.eval w₀, lam, p,
        ha, ha_z₀, hmatch, hroot, relation_hasDerivAt_w_analytic a s z₀ w₀, hderiv,
        hz₀, hNeBot, hβlim, hFz, hlam, hres⟩)

/-- **hRigid with the fibre derivative computed internally.** This is the `TranscendentalOverAdjoin`
form of `noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_fibreDerivative`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_analyticAt_fibreDerivative
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_fibreDerivative
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with minimal branch data and canonical fibre derivative input.** This is the
current smallest hRigid callback in this file: level roots produce the global modulus branch, the callback
receives no branch nonvanishing proof, and it supplies only nonvanishing of the canonical fibre derivative
instead of an auxiliary derivative witness. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_analyticAt_minBranch_fibreDerivative
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_analyticAt_minBranch hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc hβmod Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hroot, hderiv, hz₀, hNeBot,
        hβlim, hFz, hlam, hres⟩ := hinput β hβan hβesc hβmod Q s hnt hEqOn
      exact ⟨a, z₀, w₀, (fibrePoly a s z₀).derivative.eval w₀, lam, p,
        ha, ha_z₀, hmatch, hroot, relation_hasDerivAt_w_analytic a s z₀ w₀, hderiv,
        hz₀, hNeBot, hβlim, hFz, hlam, hres⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Boundary fibre equation from an eventual basin relation.** If the analytic-coefficient relation holds
eventually along the basin side of `z₀`, the coefficients tend to their boundary values, and `β` tends to
`w₀`, then the limiting fibre equation at `(z₀,w₀)` follows. -/
theorem relation_boundary_root_of_tendsto {c : ℂ} {β : ℂ → ℂ} {a : ℕ → ℂ → ℂ}
    {s : Finset ℕ} {z₀ w₀ : ℂ}
    (ha : ∀ i ∈ s, ContinuousAt (a i) z₀)
    (hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 := by
  haveI := hNeBot
  have hlim : Tendsto (fun z => ∑ i ∈ s, a i z * (β z) ^ i) (𝓝[(filledJulia c)ᶜ] z₀)
      (𝓝 (∑ i ∈ s, a i z₀ * w₀ ^ i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (((ha i hi).tendsto).mono_left nhdsWithin_le_nhds).mul (hβlim.pow i)
  have hev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[(filledJulia c)ᶜ] z₀]
      fun z => ∑ i ∈ s, a i z * (β z) ^ i := by
    filter_upwards [hβrel] with z hz
    exact hz.symm
  have hzero : Tendsto (fun z => ∑ i ∈ s, a i z * (β z) ^ i) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 0) := by
    exact tendsto_const_nhds.congr' hev
  exact tendsto_nhds_unique hlim hzero

/-- **NoRelation with boundary root and fibre derivative computed internally.** The callback supplies the
coefficient continuations, their match on the carrier, a boundary limit `β → w₀`, the canonical derivative
nonvanishing, and the repelling-cycle data. The basin relation filter, boundary fibre equation, derivative
witness, boundary nonzero value, and frequent boundary exclusion are derived internally. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_boundaryRoot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hz₀, hNeBot,
    hβlim, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc
      ∑ i ∈ s, a i z * (β z) ^ i
          = ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    relation_eq_zero_basin_analytic_of_open hUo hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
  have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
  have hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 :=
    relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
      (fun i hi => (ha_z₀ i hi).continuousAt) hNeBot hβlim hβrel
  exact false_of_repelling_branch_global_modulus_auto_ne hβan hβesc hβmod
    (fun i hi => (ha_z₀ i hi).contDiffAt) hroot (relation_hasDerivAt_w_analytic a s z₀ w₀)
    hderiv hz₀ hNeBot hβlim hβrel hFz hlam hres

/-- **hRigid with boundary root and fibre derivative computed internally.** This is the
`TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_boundaryRoot`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_analyticAt_boundaryRoot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_analyticAt_boundaryRoot
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with minimal branch data, auto boundary root, and canonical derivative input.**
This strengthens `hrig_phiMero_of_level_roots_modulus_auto_analyticAt_minBranch_fibreDerivative` by
removing the callback's explicit boundary fibre equation. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_analyticAt_minBranch_boundaryRoot
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, AnalyticAt ℂ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_analyticAt_boundaryRoot
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod
    (hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with only boundary `ContDiffAt` coefficient input.** This is the weakest local
coefficient regularity currently needed by the hRigid single-point obstruction: `AnalyticOnNhd` on the
basin still spreads the relation, while `ContDiffAt` at `z₀` gives both the boundary continuity used to
compute the limiting root and the local smoothness needed for the simple-root branch obstruction. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hz₀, hNeBot,
    hβlim, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc
      ∑ i ∈ s, a i z * (β z) ^ i
          = ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    relation_eq_zero_basin_analytic_of_open hUo hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
  have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
  have hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 :=
    relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
      (fun i hi => (ha_z₀ i hi).continuousAt) hNeBot hβlim hβrel
  exact false_of_repelling_branch_global_modulus_auto_ne hβan hβesc hβmod ha_z₀ hroot
    (relation_hasDerivAt_w_analytic a s z₀ w₀) hderiv hz₀ hNeBot hβlim hβrel hFz hlam hres

/-- **hRigid with only boundary `ContDiffAt` coefficient input.** This packages
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot` as the hRigid
`TranscendentalOverAdjoin` output. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with minimal branch data and only boundary `ContDiffAt` coefficient input.** The
callback receives the global branch, far-field anchor, and modulus, but no branch nonvanishing proof; its
per-relation work is reduced to coefficient continuation/matching, canonical fibre-derivative
nonvanishing, the boundary limit, and the repelling-cycle data. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_boundaryRoot
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod
    (hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A point on the frontier of the filled Julia set belongs to the filled Julia set. -/
theorem mem_filledJulia_of_mem_frontier {c z₀ : ℂ}
    (hz : z₀ ∈ frontier (filledJulia c)) : z₀ ∈ filledJulia c := by
  rw [(isClosed_filledJulia c).frontier_eq] at hz
  exact hz.1

/-- A point on the frontier of `K_c` has a nontrivial basin-side neighbourhood filter. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_mem_frontier {c z₀ : ℂ}
    (hz : z₀ ∈ frontier (filledJulia c)) : (𝓝[(filledJulia c)ᶜ] z₀).NeBot := by
  have hz' : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  exact mem_closure_iff_nhdsWithin_neBot.mp hz'

/-- **NoRelation with frontier boundary input.** This further shrinks the `ContDiffAt` hRigid interface:
the callback supplies the natural Julia-frontier statement `z₀ ∈ frontier K_{c₁}`, and the filled-Julia
membership plus nontrivial basin-side filter are derived internally. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_boundaryRoot hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim,
        hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
      exact ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv,
        mem_filledJulia_of_mem_frontier hfront,
        nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront,
        hβlim, hFz, hlam, hres⟩)

/-- **hRigid with frontier boundary input.** This is the `TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with frontier boundary input.** This is the current smallest level-root hRigid
interface in this file: the callback provides coefficient continuation/matching, boundary `ContDiffAt`,
canonical fibre-derivative nonvanishing, a Julia-frontier point with basin-side branch limit, and the
repelling-cycle nonresonance data. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_boundaryRoot
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc hβmod Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim,
        hFz, hlam, hres⟩ := hinput β hβan hβesc hβmod Q s hnt hEqOn
      exact ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv,
        mem_filledJulia_of_mem_frontier hfront,
        nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront,
        hβlim, hFz, hlam, hres⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with strongly-repelling norm input.** This replaces the explicit nonresonance predicate
`∀ m ≥ 1, λ^m ≠ 2^p` in the frontier hRigid interface by the single modulus inequality
`(2^p : ℝ) < ‖λ‖`, using `nonresonant_of_norm_gt`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_norm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim,
        hFz, hlam, hnorm⟩ := hinput Q s hnt hEqOn
      exact ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hlam,
        nonresonant_of_norm_gt hnorm⟩)

/-- **hRigid with strongly-repelling norm input.** This is the `TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_norm`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_norm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_norm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with strongly-repelling norm input.** This is the current smallest level-root
hRigid interface in this file: nonresonance is derived from `(2^p : ℝ) < ‖λ‖`, and the remaining callback
data are coefficient continuation/matching, boundary `ContDiffAt`, canonical fibre-derivative
nonvanishing, a frontier point, and the basin-side branch limit. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier_norm
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ lam : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc hβmod Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim,
        hFz, hlam, hnorm⟩ := hinput β hβan hβesc hβmod Q s hnt hEqOn
      exact ⟨a, z₀, w₀, lam, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hlam,
        nonresonant_of_norm_gt hnorm⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- The canonical derivative witness for an iterate of the quadratic map. -/
theorem hasDerivAt_quadratic_iterate_deriv (c z₀ : ℂ) (p : ℕ) :
    HasDerivAt ((quadratic c)^[p]) (deriv ((quadratic c)^[p]) z₀) z₀ := by
  exact (analyticOnNhd_quadratic_iterate c p z₀ (mem_univ z₀)).differentiableAt.hasDerivAt

/-- **NoRelation with canonical multiplier derivative.** This removes the callback's auxiliary multiplier
`λ` and its `HasDerivAt` proof: the multiplier is the canonical derivative
`deriv ((quadratic c₁)^[p]) z₀`, and analyticity of the iterate supplies the derivative witness. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖deriv ((quadratic c₁)^[p]) z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_norm hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm⟩ :=
        hinput Q s hnt hEqOn
      exact ⟨a, z₀, w₀, deriv ((quadratic c₁)^[p]) z₀, p, ha, ha_z₀, hmatch, hderiv,
        hfront, hβlim, hFz, hasDerivAt_quadratic_iterate_deriv c₁ z₀ p, hnorm⟩)

/-- **hRigid with canonical multiplier derivative.** This is the `TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖deriv ((quadratic c₁)^[p]) z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with canonical multiplier derivative.** This is the current smallest level-root
hRigid interface in this file: the callback no longer supplies a multiplier value or derivative proof;
it only proves the strongly-repelling inequality for the canonical derivative of the iterate. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier_derivNorm
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖deriv ((quadratic c₁)^[p]) z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier_norm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc hβmod Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm⟩ :=
        hinput β hβan hβesc hβmod Q s hnt hEqOn
      exact ⟨a, z₀, w₀, deriv ((quadratic c₁)^[p]) z₀, p, ha, ha_z₀, hmatch, hderiv,
        hfront, hβlim, hFz, hasDerivAt_quadratic_iterate_deriv c₁ z₀ p, hnorm⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- The derivative of an iterate of the quadratic map is the product of orbit multipliers. -/
theorem deriv_quadratic_iterate_eq_orbitProduct (c z₀ : ℂ) (p : ℕ) :
    deriv ((quadratic c)^[p]) z₀ = ∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀ := by
  exact (hasDerivAt_quadratic_iterate c z₀ p).deriv

/-- **NoRelation with orbit-product expansion input.** This rewrites the canonical derivative norm in
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm` as the explicit
product of quadratic orbit multipliers. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_derivNorm hUo hUc hUne hUinf
    c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm⟩ :=
        hinput Q s hnt hEqOn
      have hnorm' : (2 ^ p : ℝ) < ‖deriv ((quadratic c₁)^[p]) z₀‖ := by
        rwa [deriv_quadratic_iterate_eq_orbitProduct]
      exact ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm'⟩)

/-- **hRigid with orbit-product expansion input.** This is the `TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_orbitNorm`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_orbitNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod hinput)

/-- **Level-root hRigid with orbit-product expansion input.** This is currently the most geometric
level-root hRigid interface in this file: the repelling/nonresonance datum is expressed directly as the
orbit-multiplier product bound. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier_orbitNorm
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
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∀ i ∈ s, ∀ z ∈ U,
            a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) ∧
          (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact hrig_phiMero_of_level_roots_modulus_auto_contDiffAt_minBranch_frontier_derivNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc (by
      intro β hβan hβesc hβmod Q s hnt hEqOn
      obtain ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm⟩ :=
        hinput β hβan hβesc hβmod Q s hnt hEqOn
      have hnorm' : (2 ^ p : ℝ) < ‖deriv ((quadratic c₁)^[p]) z₀‖ := by
        rwa [deriv_quadratic_iterate_eq_orbitProduct]
      exact ⟨a, z₀, w₀, p, ha, ha_z₀, hmatch, hderiv, hfront, hβlim, hFz, hnorm'⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with a single continued coefficient branch.** The caller supplies one analytic basin
continuation `γ` of `φ_{c₂}` along the `c₁` basin, rather than a separate coefficient family `a`.  The
coefficient family needed by the orbit-product hRigid theorem is constructed internally as
`aᵢ(z) = Qᵢ(z, γ z)`, and its analyticity is derived from
`analyticOnNhd_eval₂_of_analyticOnNhd`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) z₀) ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier_orbitNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, w₀, p, hcont, hderiv, hfront, hβlim, hFz, hnorm⟩ := hinput Q s hnt hEqOn
      refine ⟨fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z), z₀, w₀, p, ?_, ?_, ?_, hderiv,
        hfront, hβlim, hFz, hnorm⟩
      · intro i _hi
        exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
      · exact hcont
      · intro i _hi z hz
        simpa using congrArg (fun w => (Q i).eval₂ (Polynomial.evalRingHom z) w) (hγmatch z hz))

/-- **hRigid with a single continued coefficient branch.** This is the
`TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) z₀) ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch hinput)

/-- **Level-root hRigid with a single continued coefficient branch.** Per-level roots still assemble
into the global `c₁` branch `β`; the `c₂` side is now supplied as one analytic continuation `γ`, from
which all relation coefficients are built internally. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_minBranch_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) z₀) ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch
    (hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A bivariate polynomial evaluated along an analytic germ `g` is analytic at the base point.  This is
the local analogue of `analyticOnNhd_eval₂_of_analyticOnNhd`; it is used at frontier points where the
continued `γ` branch is only known locally across the boundary point. -/
theorem analyticAt_eval₂_of_analyticAt {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (R : Polynomial (Polynomial ℂ)) :
    AnalyticAt ℂ (fun z => R.eval₂ (Polynomial.evalRingHom z) (g z)) z₀ := by
  have hfun : (fun z => R.eval₂ (Polynomial.evalRingHom z) (g z))
      = (fun z => ∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).eval z * (g z) ^ i) := by
    funext z; rw [eval₂_eq_sum_range]; rfl
  rw [hfun]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (analyticAt_id.aeval_polynomial (R.coeff i)).mul (hg.pow i)

/-- **NoRelation with a single continued coefficient branch, local smoothness derived.** Compared with
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm`, the callback no longer
proves `ContDiffAt` for every coefficient `Qᵢ(z, γ z)`: it only proves that `γ` is analytic at the chosen
frontier point.  The coefficient smoothness is derived by `analyticAt_eval₂_of_analyticAt`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontier_orbitNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, w₀, p, hγAt, hderiv, hfront, hβlim, hFz, hnorm⟩ := hinput Q s hnt hEqOn
      refine ⟨z₀, w₀, p, ?_, hderiv, hfront, hβlim, hFz, hnorm⟩
      intro i _hi
      exact (analyticAt_eval₂_of_analyticAt hγAt (Q i)).contDiffAt)

/-- **hRigid with a single continued coefficient branch, local smoothness derived.** This is the
`TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch hinput)

/-- **Level-root hRigid with a single continued coefficient branch, local smoothness derived.** This is
currently the smallest level-root hRigid interface in the γ-continuation route: the `c₁` branch comes from
level roots, the `c₂` branch is one continued `γ`, and the callback only supplies local analyticity of `γ`
at the chosen frontier point plus the simple-fibre and repelling orbit-product data. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_analyticAt_minBranch_frontier_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).derivative.eval w₀ ≠ 0 ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch
    (hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with γ continuation and separable boundary fibre.** This removes the callback's direct
simple-derivative proof from
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm`.  The boundary
root is derived by propagating the relation through the basin and taking the basin-side limit; separability
of the boundary fibre then gives the nonzero fibre derivative. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, w₀, p, hγAt, hsep, hfront, hβlim, hFz, hnorm⟩ := hinput Q s hnt hEqOn
      let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
      have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ := by
        intro i _hi
        exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
      have haAt : ∀ i ∈ s, AnalyticAt ℂ (a i) z₀ := by
        intro i _hi
        exact analyticAt_eval₂_of_analyticAt hγAt (Q i)
      have hmatch : ∀ i ∈ s, ∀ z ∈ U,
          a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
        intro i _hi z hz
        dsimp [a]
        simpa using congrArg (fun w => (Q i).eval₂ (Polynomial.evalRingHom z) w) (hγmatch z hz)
      have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
        intro z hz
        calc
          ∑ i ∈ s, a i z * (β z) ^ i
              = ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                    (bottcherCoord c₁ z) ^ i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
          _ = 0 := hEqOn hz
      have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
        relation_eq_zero_basin_analytic_of_open hUo hUne
          (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
      have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
        Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
      have hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
        nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront
      have hrootSum : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 :=
        relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
          (fun i hi => (haAt i hi).continuousAt) hNeBot hβlim hβrel
      have hrootPoly : (fibrePoly a s z₀).eval w₀ = 0 := by
        rwa [eval_fibrePoly]
      have hderiv : (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 :=
        eval_derivative_ne_zero_of_separable (by simpa [a] using hsep) hrootPoly
      refine ⟨z₀, w₀, p, hγAt, ?_, hfront, hβlim, hFz, hnorm⟩
      simpa [a] using hderiv)

/-- **hRigid with γ continuation and separable boundary fibre.** This is the
`TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch hinput)

/-- **Level-root hRigid with γ continuation and separable boundary fibre.** This is now the smallest
level-root hRigid interface in the γ-continuation route: the callback supplies local analyticity of `γ`,
separability of the boundary fibre, a frontier basin limit, and the orbit-product repelling inequality. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_analyticAt_minBranch_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch
    (hinput β hβan hβesc hβmod)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Concrete `NoRelation` from level roots, γ continuation, and separable boundary fibres.** This is the
level-root `NoRelation` endpoint of the γ/separable hRigid route: the level-root tower assembles the global
`c₁` Böttcher branch, and the γ/separable callback closes every cleared relation directly. -/
theorem noRelation_phiMero_of_level_roots_modulus_auto_gamma_analyticAt_minBranch_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch
    (hinput β hβan hβesc hβmod)

/-- **Connected-case `q62` endpoint from the level-root γ/separable hRigid route.** This composes the
strongest level-root hRigid producer in this file with `q62_independence_connected_of_inputs`, yielding the
concrete connected-case independence for distinct nonexceptional parameters from the same γ/separable
frontier data. -/
theorem q62_independence_connected_of_level_roots_modulus_auto_gamma_analyticAt_minBranch_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          AnalyticAt ℂ γ z₀ ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_level_roots_modulus_auto_gamma_analyticAt_minBranch_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan hγmatch hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with frontier-analytic γ.** Compared with the γ/separable frontier theorem, local
analyticity of `γ` at each selected frontier point is no longer relation data: it is supplied once as
`AnalyticOnNhd γ (frontier K_{c₁})`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_gamma_analyticAt_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, w₀, p, hsep, hfront, hβlim, hFz, hnorm⟩ := hinput Q s hnt hEqOn
      exact ⟨z₀, w₀, p, hγfront z₀ hfront, hsep, hfront, hβlim, hFz, hnorm⟩)

/-- **hRigid with frontier-analytic γ.** This is the `TranscendentalOverAdjoin` form of
`noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγfront hγmatch hinput)

/-- **Level-root hRigid with frontier-analytic γ.** The level-root tower still supplies the global `c₁`
branch; frontier analyticity of `γ` is now a global input rather than a per-relation callback field. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hanalytic hpow hne hanchorEsc
  exact hrig_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγfront hγmatch
    (hinput β hβan hβesc hβmod)

/-- **Connected-case `q62` endpoint with frontier-analytic γ.** This is the strongest connected endpoint
currently exposed by the γ/separable hRigid route: the per-relation callback no longer carries local
analyticity of `γ`; it supplies only separability, frontier limit, periodicity, and repelling orbit product. -/
theorem q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan hγfront hγmatch hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected hRigid endpoint with `φ_{c₂}` transcendence produced internally.** This removes the
abstract terminal hypothesis `Transcendental (RatFunc ℂ) (phiMero c₂ hU₂)` from the strongest
frontier-analytic γ endpoint by deriving it via `phiMero_transcendental_of_repelling_input`.  The remaining
`c₂` input is explicit dynamical/simple-root data, not a field-theoretic placeholder. -/
theorem q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n, (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne_params hx₁ hx₂ hG βlev hanalytic hpow hne hanchorEsc
    γ hγan hγfront hγmatch hinput

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with frontier-analytic β and γ.**  This is the boundary-limit-free form of the
frontier-analytic γ route: if the global basin branch `β` itself has a frontier analytic continuation, then
`w₀` and `Tendsto β (𝓝[Kᶜ] z₀) (𝓝 w₀)` are no longer relation data.  The callback only chooses a separable
strongly-repelling frontier fibre; the boundary value is forced to be `β z₀`. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  noRelation_phiMero_of_repelling_global_modulus_auto_gamma_frontierAnalytic_frontier_orbitNorm_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan hγfront hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, p, hsep, hfront, hFz, hnorm⟩ := hinput Q s hnt hEqOn
      refine ⟨z₀, β z₀, p, hsep, hfront, ?_, hFz, hnorm⟩
      exact ((hβfront z₀ hfront).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)

/-- **hRigid with frontier-analytic β and γ.** This packages the boundary-limit-free NoRelation wrapper as
`TranscendentalOverAdjoin`: once `β` is analytic at the frontier, the per-relation datum only chooses a
separable strongly-repelling frontier fibre. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_orbitNorm_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput)

/-- **Connected q62 endpoint with β/γ frontier analyticity and `φ_{c₂}` transcendence produced internally.**
The ad hoc boundary-limit witness is gone: `w₀` is `β z₀`, and `Tendsto β` follows from `hβfront`. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_orbitNorm_separable_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput)

end Bottcher
namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with frontier-analytic β/γ and canonical nonresonance.**  The branch boundary value is
forced to be `β z₀`, and the periodic multiplier is the canonical derivative of the iterate.  The caller
only selects a separable frontier periodic fibre and proves the genuine nonresonance condition for that
canonical multiplier. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (∀ m : ℕ, 1 ≤ m →
            (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_repelling_global_modulus_auto_contDiffAt_frontier
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β hβan hβesc hβmod (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, p, hsep, hfront, hFz, hres⟩ := hinput Q s hnt hEqOn
      let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
      have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ := by
        intro i _hi
        exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
      have hγAt : AnalyticAt ℂ γ z₀ := hγfront z₀ hfront
      have haAt : ∀ i ∈ s, AnalyticAt ℂ (a i) z₀ := by
        intro i _hi
        exact analyticAt_eval₂_of_analyticAt hγAt (Q i)
      have hmatch : ∀ i ∈ s, ∀ z ∈ U,
          a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
        intro i _hi z hz
        dsimp [a]
        simpa using congrArg (fun w => (Q i).eval₂ (Polynomial.evalRingHom z) w) (hγmatch z hz)
      have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
        intro z hz
        calc
          ∑ i ∈ s, a i z * (β z) ^ i
              = ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                    (bottcherCoord c₁ z) ^ i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
          _ = 0 := hEqOn hz
      have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
        relation_eq_zero_basin_analytic_of_open hUo hUne
          (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
      have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
        Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
      have hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
        nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront
      have hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 (β z₀)) :=
        ((hβfront z₀ hfront).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      have hrootSum : ∑ i ∈ s, a i z₀ * (β z₀) ^ i = 0 :=
        relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
          (fun i hi => (haAt i hi).continuousAt) hNeBot hβlim hβrel
      have hrootPoly : (fibrePoly a s z₀).eval (β z₀) = 0 := by
        rwa [eval_fibrePoly]
      have hderiv : (fibrePoly a s z₀).derivative.eval (β z₀) ≠ 0 :=
        eval_derivative_ne_zero_of_separable (by simpa [a] using hsep) hrootPoly
      refine ⟨a, z₀, β z₀, deriv ((quadratic c₁)^[p]) z₀, p, ha,
        (fun i hi => (haAt i hi).contDiffAt), hmatch, ?_, hfront, hβlim, hFz,
        hasDerivAt_quadratic_iterate_deriv c₁ z₀ p, hres⟩
      simpa [a] using hderiv)

/-- **hRigid with frontier-analytic β/γ and canonical nonresonance.** -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (∀ m : ℕ, 1 ≤ m →
            (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput)

/-- **Connected q62 endpoint with β/γ frontier analyticity and canonical nonresonance.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (∀ m : ℕ, 1 ≤ m →
            (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput)

end Bottcher
