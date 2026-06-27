/-
# hRigid capstone: the connected-case independence reduced to the shared dynamical datum

The end-to-end wiring of the `hRigid` (Eremenko–van Strien rigidity) lane on the genuine carrier
`M = meroField U`. The previously *floating* E–vS input `hrig = TranscendentalOverAdjoin φ_{c₁} φ_{c₂}`
is here produced by a theorem — no longer assumed — from two function-level inputs that both bottom out
at one dynamical datum (a dendrite Julia point of `J_{c₁}` with a basin Böttcher branch):

* `hG`  — `φ_{c₂}` transcendental over `ℂ(z)`  (the `hGtr` input; reduces, via
  `phiMero_transcendental_of_no_function_relation`, to its own absolute dendrite no-relation);
* `hno` — the bivariate dendrite no-relation: no nonzero cleared relation
  `∑ᵢ Qᵢ(z, φ_{c₂}(z))·φ_{c₁}(z)ⁱ` vanishes on `U`  (discharged by
  `RelativeNaturalBoundary.false_of_basin_branch_dendrite_analytic`).

`transcendentalOverAdjoin_phiMero_of_dynamical_inputs` composes
`noRelation_phiMero_of_no_function_relation` (the bivariate core) with
`transcendentalOverAdjoin_of_noRelation` (the pure-algebra reduction) to build `hrig`;
`q62_independence_connected_of_dynamical` then threads `hG` (as `hGtr`) and the produced `hrig`
through `q62_independence_connected_of_inputs`, yielding the concrete connected-case independence
`NoRelation ℂ(z) φ_{c₁} φ_{c₂}` from the single shared datum. This closes the mechanical assembly of
the connected case down to the one remaining dynamical input.
-/
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge
import GaloisForLFunctions.Bottcher.RelativeNaturalBoundary
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.RelativeBasinBranch
import GaloisForLFunctions.Bottcher.Q62ConnectedAssembly

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **The `hrig` producer (E–vS rigidity input, no longer floating).** From the two shared dynamical
inputs — `φ_{c₂}` transcendental over `ℂ(z)` (`hG`) and the bivariate dendrite no-relation (`hno`) —
the rigidity input `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` is produced by composing
`noRelation_phiMero_of_no_function_relation` with `transcendentalOverAdjoin_of_noRelation`. -/
theorem transcendentalOverAdjoin_phiMero_of_dynamical_inputs
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hno : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        ¬ Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hno)

/-- **q62 connected/connected, reduced to the shared dynamical datum.** The genuine connected-case
independence `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` over the meromorphic field, for distinct nonexceptional
`c₁,c₂`, follows from exactly the two function-level inputs that both bottom out at the dendrite
Böttcher-branch datum: `hG` (transcendence of `φ_{c₂}`) and `hno` (the bivariate dendrite no-relation).
This routes `hG` to `hGtr` and the produced `hrig` through `q62_independence_connected_of_inputs`. -/
theorem q62_independence_connected_of_dynamical
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hno : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        ¬ Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_phiMero_of_dynamical_inputs
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hno)

/-- **hno from the dendrite simple-root basin-branch datum (the single #24 interface).** The bivariate
no-relation `hno` reduces to one existence statement: for every nonzero cleared relation vanishing on
`U`, there is a continued coefficient family `a` (analytic at the dendrite point — the continuation of
`(Q i)(·, φ_{c₂})` past the far field, since `J_{c₁}` is bounded and `escapeOpen c₂` is only the far
field), a dendrite Julia point `z₀∈J_{c₁}` with empty nearby filled-Julia interior, a simple root
`(z₀,w₀)` of the relation, and a basin Böttcher branch `β` carrying the relation with the genuine
modulus `‖β‖=exp(G_{c₁})`. Then `RelativeNaturalBoundary.false_of_basin_branch_dendrite_analytic`
closes it. This isolates exactly the dynamical datum the multi-month Montel→Julia lane (#24) must
construct; everything upstream of it is now proven and axiom-clean. -/
theorem noRelation_phiMero_of_dendrite_input
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d : ℂ) (r : ℝ) (β : ℂ → ℂ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧ ball z₀ r ∩ interior (filledJulia c₁) = ∅ ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, z₀, w₀, d, r, β, ha, hr, hz₀, hempty, hroot, hpartial, hd, hβlim, hβrel, hβmod⟩ :=
    hinput Q s hnt hEqOn
  exact false_of_basin_branch_dendrite_analytic ha hr hz₀ hempty hroot hpartial hd hβlim hβrel hβmod

/-- **hno from the basin-branch + dendrite-tip datum (the refined #24 interface).** The bivariate
no-relation `hno` reduces to: for every nonzero cleared relation vanishing on `U`, a continued analytic
coefficient family `a` with separable nondegenerate fibre at a dendrite tip `z₀∈J_{c₁}` (`hempty`/`htip`),
and a basin Böttcher branch `β` carrying the relation and the genuine modulus `‖β‖=exp(G_{c₁})` on the
basin sector `ball z₀ r ∩ Ω_{c₁}`. `false_of_global_basin_branch_analytic` does the rest (branch family,
branch-following, simple-root boundary limit, natural-boundary obstruction — all now internal). This is
strictly weaker dynamical data than `noRelation_phiMero_of_dendrite_input`: it asks only for the *basin
branch* and the *dendrite tip*, not the pre-digested simple-root boundary value. The remaining #24 content
is exactly the construction of `β` (the basin-wide continuation of `φ_{c₁}` — input B/#22) and the dendrite
tip with empty filled-Julia interior (input D/#23), with `a` the continuation of `(Qᵢ)(·,φ_{c₂})`. -/
theorem noRelation_phiMero_of_basin_branch
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (N : ℕ) (z₀ : ℂ) (r : ℝ) (β : ℂ → ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧ ball z₀ r ∩ interior (filledJulia c₁) = ∅ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) ∧
          ContinuousOn β (ball z₀ r ∩ (filledJulia c₁)ᶜ) ∧
          (∀ z ∈ ball z₀ r ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
          (∀ z ∈ ball z₀ r ∩ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, N, z₀, r, β, hsupp, hN, hN1, ha, hlead, hsep, hr, hz₀, hempty, htip,
    hβc, hβrel, hβmod⟩ := hinput Q s hnt hEqOn
  exact false_of_global_basin_branch_analytic hsupp hN hN1 ha hlead hsep hr hz₀ hempty htip
    hβc hβrel hβmod

/-- **hno from an ω-primitive on the common-basin region (the deepest #24 interface).** For each nonzero
cleared relation vanishing on `U`, given a preconnected basin region `V ⊆ Ω_{c₁}` carrying the continued
coefficients `a` analytically (so `V ⊆ Ω_{c₂}` too — the common basin), a far-field anchor `E ⊆ V` where
the relation in `bottcherCoord c₁` holds, a primitive `F` of `ω = greenLogDeriv c₁` on `V`, a dendrite tip
`z₀∈J_{c₁}` whose basin sector sits inside `V`, and the fibre nondegeneracy at `z₀`, the relation is
impossible. Builds the basin branch `β` from the primitive (`exists_relativeBranch_of_primitive`) and feeds
the dendrite obstruction (`noRelation_phiMero_of_basin_branch`). This reduces the entire connected-case
`NoRelation` to `hG` + an **ω-primitive on the common-basin region** (the simply-connected/Poincaré content
— the tree's `exists_primitive_glue_chain` targets it) plus the dendrite/common-basin geometry. -/
theorem noRelation_phiMero_of_primitive
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (N : ℕ) (z₀ e₀ : ℂ) (r : ℝ) (V E : Set ℂ) (F : ℂ → ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) V) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable ∧
          IsOpen V ∧ IsPreconnected V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          (∀ z ∈ V, HasDerivAt F (greenLogDeriv c₁ z) z) ∧
          E ⊆ V ∧ E ⊆ escapeOpen c₁ ∩ Complex.slitPlane ∧ IsOpen E ∧ IsPreconnected E ∧ e₀ ∈ E ∧
          (∀ z ∈ E, ∑ i ∈ s, a i z * (bottcherCoord c₁ z) ^ i = 0) ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧ ball z₀ r ∩ interior (filledJulia c₁) = ∅ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) ∧
          ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_basin_branch hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, N, z₀, e₀, r, V, E, F, hsupp, hN, hN1, haV, ha_z₀, hlead, hsep,
    hVo, hVc, hVb, hF, hEV, hEesc, hEo, hEc, he₀, hrelE, hr, hz₀, hempty, htip, hsectorV⟩ :=
    hinput Q s hnt hEqOn
  obtain ⟨β, hβan, hβ0, hβmod, hβrel⟩ :=
    exists_relativeBranch_of_primitive hVo hVc hVb hF haV hEV hEesc hEo hEc he₀ hrelE
  refine ⟨a, N, z₀, r, β, hsupp, hN, hN1, ha_z₀, hlead, hsep, hr, hz₀, hempty, htip, ?_, ?_, ?_⟩
  · exact hβan.continuousOn.mono hsectorV
  · exact fun z hz => hβrel z (hsectorV hz)
  · exact fun z hz => hβmod z (hsectorV hz)

/-- A ball-chain (balls with connected prefix-overlaps) has preconnected union. -/
theorem isPreconnected_ballChain (B : ℕ → Set ℂ)
    (hball : ∀ i, ∃ a r, B i = Metric.ball a r)
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), B j) ∩ B (i + 1))) (k : ℕ) :
    IsPreconnected (⋃ j ∈ Finset.range (k + 1), B j) := by
  induction k with
  | zero =>
    obtain ⟨a, r, heq⟩ := hball 0
    have : (⋃ j ∈ Finset.range 1, B j) = B 0 := by simp [Finset.range_one]
    rw [this, heq]; exact (convex_ball a r).isPreconnected
  | succ n ih =>
    have hunion : (⋃ j ∈ Finset.range (n + 1 + 1), B j)
        = (⋃ j ∈ Finset.range (n + 1), B j) ∪ B (n + 1) := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert]; exact Set.union_comm _ _
    rw [hunion]
    obtain ⟨x, hx⟩ := (hconn n).nonempty
    obtain ⟨a, r, heq⟩ := hball (n + 1)
    refine IsPreconnected.union x hx.1 hx.2 ih ?_
    rw [heq]; exact (convex_ball a r).isPreconnected

/-- **hno from a basin ball-chain (the fully geometric #24 interface).** The ω-primitive is now constructed
internally by `exists_primitive_greenLogDeriv_chain`; `hinput` supplies only the ball-chain *geometry*:
balls `B j` in the basin `Ω_{c₁}` with connected prefix-overlaps whose union carries the continued
coefficients analytically (so the union `⊆ Ω_{c₂}`), a far-field anchor `E`, and a dendrite tip `z₀∈J_{c₁}`
with its basin sector inside the union. This reduces the connected-case `NoRelation` to point-set/dynamical
data only — a simple arc (ball chain) from the far field to a dendrite Julia point in the common basin, the
dendrite tip (empty filled-Julia interior + preconnected punctured sectors), and the generic fibre
nondegeneracy. No analytic frontier theorem remains anywhere in the chain. -/
theorem noRelation_phiMero_of_ballchain
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (N : ℕ) (z₀ e₀ : ℂ) (r : ℝ) (E : Set ℂ) (B : ℕ → Set ℂ) (k : ℕ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (∀ i, ∃ a' r', B i = Metric.ball a' r') ∧
          (∀ i, B i ⊆ (filledJulia c₁)ᶜ) ∧
          (∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), B j) ∩ B (i + 1))) ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (⋃ j ∈ Finset.range (k + 1), B j)) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable ∧
          E ⊆ (⋃ j ∈ Finset.range (k + 1), B j) ∧
          E ⊆ escapeOpen c₁ ∩ Complex.slitPlane ∧ IsOpen E ∧ IsPreconnected E ∧ e₀ ∈ E ∧
          (∀ z ∈ E, ∑ i ∈ s, a i z * (bottcherCoord c₁ z) ^ i = 0) ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧ ball z₀ r ∩ interior (filledJulia c₁) = ∅ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) ∧
          ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ (⋃ j ∈ Finset.range (k + 1), B j)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_primitive hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, N, z₀, e₀, r, E, B, k, hsupp, hN, hN1, hball, hsub, hconn, haV, ha_z₀, hlead, hsep,
    hEV, hEesc, hEo, hEc, he₀, hrelE, hr, hz₀, hempty, htip, hsectorV⟩ := hinput Q s hnt hEqOn
  obtain ⟨F, hF⟩ := exists_primitive_greenLogDeriv_chain B hball hsub hconn k
  have hVo : IsOpen (⋃ j ∈ Finset.range (k + 1), B j) := by
    apply isOpen_biUnion; intro i _; obtain ⟨a', r', heq⟩ := hball i; rw [heq]; exact isOpen_ball
  have hVc : IsPreconnected (⋃ j ∈ Finset.range (k + 1), B j) :=
    isPreconnected_ballChain B hball hconn k
  have hVb : (⋃ j ∈ Finset.range (k + 1), B j) ⊆ (filledJulia c₁)ᶜ := by
    apply Set.iUnion₂_subset; intro i _; exact hsub i
  exact ⟨a, N, z₀, e₀, r, _, E, F, hsupp, hN, hN1, haV, ha_z₀, hlead, hsep,
    hVo, hVc, hVb, hF, hEV, hEesc, hEo, hEc, he₀, hrelE, hr, hz₀, hempty, htip, hsectorV⟩

/-- **hno for a dendrite parameter.** When `J_{c₁}` is a dendrite (`interior(filledJulia c₁) = ∅`, the
defining property of dendrite/Misiurewicz Julia sets) the per-relation empty-interior condition is automatic
(`ball z₀ r ∩ ∅ = ∅`), so the ball-chain interface simplifies: for each nonzero cleared relation vanishing
on `U`, supply a dendrite tip `z₀∈J_{c₁}∖filledJulia c₂` (with `htip` preconnected punctured sectors), a
ball-chain through the common basin to its sector, the continued coefficients (analytic on the chain +
`ContDiffAt` at `z₀`), the far-field anchor, and the generic fibre nondegeneracy. This is the cleanest
interface for the dendrite/Misiurewicz sub-range of the connected case, where the natural-boundary
obstruction applies directly (the quasicircle/hyperbolic sub-range, where `filledJulia` has interior, needs
a distinct obstruction — the genuine remaining frontier). -/
theorem noRelation_phiMero_of_dendrite_param
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hdend : interior (filledJulia c₁) = ∅)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (N : ℕ) (z₀ e₀ : ℂ) (r : ℝ) (E : Set ℂ) (B : ℕ → Set ℂ) (k : ℕ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (∀ i, ∃ a' r', B i = Metric.ball a' r') ∧
          (∀ i, B i ⊆ (filledJulia c₁)ᶜ) ∧
          (∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), B j) ∩ B (i + 1))) ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ (a i) (⋃ j ∈ Finset.range (k + 1), B j)) ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable ∧
          E ⊆ (⋃ j ∈ Finset.range (k + 1), B j) ∧
          E ⊆ escapeOpen c₁ ∩ Complex.slitPlane ∧ IsOpen E ∧ IsPreconnected E ∧ e₀ ∈ E ∧
          (∀ z ∈ E, ∑ i ∈ s, a i z * (bottcherCoord c₁ z) ^ i = 0) ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) ∧
          ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ (⋃ j ∈ Finset.range (k + 1), B j)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_ballchain hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, N, z₀, e₀, r, E, B, k, hsupp, hN, hN1, hball, hsub, hconn, haV, ha_z₀, hlead, hsep,
    hEV, hEesc, hEo, hEc, he₀, hrelE, hr, hz₀, htip, hsectorV⟩ := hinput Q s hnt hEqOn
  have hempty : ball z₀ r ∩ interior (filledJulia c₁) = ∅ := by rw [hdend, inter_empty]
  exact ⟨a, N, z₀, e₀, r, E, B, k, hsupp, hN, hN1, hball, hsub, hconn, haV, ha_z₀, hlead, hsep,
    hEV, hEesc, hEo, hEc, he₀, hrelE, hr, hz₀, hempty, htip, hsectorV⟩

/-- **NoRelation via the GENERAL repelling route (all connected Julia — no dendrite restriction).** The
second, more general route to the connected-case independence: `hno` reduces to a NON-RESONANT repelling
periodic point `z₀∈J_{c₁}∖filledJulia c₂` that is a simple root of the relation, reached by a basin Böttcher
branch `β` carrying the relation and the Böttcher functional equation `β(f^[p]z)=(βz)^{2^p}` (non-constant
on the basin side). `false_of_repelling_branch_analytic` closes it via the resonance finisher — needing NO
empty-interior/dendrite condition, so this covers the quasicircle/hyperbolic connected parameters that the
dendrite route cannot. Repelling periodic points are dense in every `J_{c₁}`, so this is the route to the
*full* nonexceptional connected range. -/
theorem noRelation_phiMero_of_repelling
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ) (β : ℂ → ℂ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          w₀ ≠ 0 ∧ z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β ((quadratic c₁)^[p] z) = (β z) ^ (2 ^ p)) ∧
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
  obtain ⟨a, z₀, w₀, d, lam, p, β, ha, hroot, hpartial, hd, hw₀, hz₀, hNeBot,
    hβlim, hβrel, hβfe, hβne, hFz, hlam, hres⟩ := hinput Q s hnt hEqOn
  exact false_of_repelling_branch_analytic ha hroot hpartial hd hw₀ hz₀ hNeBot
    hβlim hβrel hβfe hβne hFz hlam hres

/-- **`hrig` produced from the repelling-cycle datum (hRigid reduced to one classical input).** Composing
`noRelation_phiMero_of_repelling` (the general all-connected-Julia obstruction) with
`transcendentalOverAdjoin_of_noRelation` (the pure-algebra reduction) yields the E–vS rigidity input
`hrig = TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` directly from: `φ_{c₂}` transcendence (`hG`) and, per cleared
relation, a non-resonant repelling periodic point of `f_{c₁}` in `J_{c₁}∖filledJulia c₂` with the basin
branch carrying the relation + the Böttcher functional equation. Every analytic/algebraic step is proven and
axiom-clean; the sole remaining input is the *existence* of such a repelling cycle — Fatou's classical
density of repelling periodic points in the Julia set, the dynamical residue shared with the absolute
transcendence lane. This is the cleanest machine-checked statement of "the connected-case hRigid path,
reduced to one classical dynamical theorem." -/
theorem hrig_phiMero_of_repelling
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (z₀ w₀ d lam : ℂ) (p : ℕ) (β : ℂ → ℂ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          w₀ ≠ 0 ∧ z₀ ∈ filledJulia c₁ ∧ (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
          (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β ((quadratic c₁)^[p] z) = (β z) ^ (2 ^ p)) ∧
          (∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₁)^[p]) lam z₀ ∧
          (∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hinput)

end Bottcher
