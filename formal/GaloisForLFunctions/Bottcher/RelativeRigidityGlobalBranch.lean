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
