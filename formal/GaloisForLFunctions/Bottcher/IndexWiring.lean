/-
# Wiring the index-formula obstruction to an actual relation

The index-route endpoint `IndexResonance.false_of_branches_repelling_fixed` consumes, at each period-`p`
cycle point off the exceptional set, a *branch tuple*: an analytic `g` with `g z₀ = ζ ≠ 0`, the Böttcher
functional equation `g ∘ f^[p] =ᶠ g^{2^p}`, and `deriv g z₀ ≠ 0`. This file produces the branch and the
functional equation from an actual minimal relation `P` (the same spine that
`ConnectedTranscendence.false_of_periodic_simpleroot` runs on, extracted as a reusable producer):

* the local algebraic branch `g` of `P` at a simple root `(z₀, w₀)` (`exists_analyticAt_branch_poly`);
* the Böttcher functional equation, via the divisibility gateway
  `divides_relation_up_to_denom` → `funEq_hdiv_of_divides` → `funEq_of_branch`.

`exists_branch_with_FE` packages exactly that. The two clauses still to be matched to the index tuple are
purely *local genericity at the cycle point*: `w₀ ≠ 0` (nonzero Böttcher value) and `deriv g z₀ ≠ 0` (the
branch is non-constant to first order — `n = 1`), both of which hold off the finite branch/critical locus of
`P`, so for a large prime period `p` they hold at every period-exactly-`p` point.

New file (hRigid / connected lane, the relation→branch wiring). Consumes the existing branch + functional
equation spine.
-/
import GaloisForLFunctions.Bottcher.ConnectedTranscendence
import GaloisForLFunctions.Bottcher.IndexResonance

open Polynomial Filter Topology Set

namespace Bottcher

/-- **Branch + Böttcher functional equation from a relation, at a simple root over a period-`p` point.**
Given a minimal relation `P` (vanishing on `U`, with its `f^[p]`-composite `compRelPoly c p P` also
vanishing) and a period-`p` point `z₀` that is a simple root `(z₀, w₀)` of the fibre with `w₀^{2^p} = w₀`,
the local algebraic branch `g` of `P` exists, is analytic at `z₀` with `g z₀ = w₀`, satisfies the relation
near `z₀`, and satisfies the **Böttcher functional equation** `g(f^[p] z) = (g z)^{2^p}` near `z₀`. This is
the spine of `false_of_periodic_simpleroot` (branch + divisibility gateway + `funEq_of_branch`), extracted
so the index route can consume the branch and the functional equation directly. -/
theorem exists_branch_with_FE {U : Set ℂ} (c : ℂ) (p : ℕ) {w₀ d z₀ : ℂ}
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
        ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hFz : (quadratic c)^[p] z₀ = z₀) (hw₀ : w₀ ^ (2 ^ p) = w₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧
      (∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0) ∧
      (∀ᶠ z in 𝓝 z₀, g ((quadratic c)^[p] z) = (g z) ^ (2 ^ p)) := by
  obtain ⟨g, hgAt, hgz, hgrel⟩ := exists_analyticAt_branch_poly P hroot hpartial hd
  obtain ⟨e, S, he0, hPS⟩ :=
    divides_relation_up_to_denom c P (compRelPoly c p P) hP0 hPmin hPrel hQrel
  have hdiv := funEq_hdiv_of_divides c p P he0 hPS hgAt.continuousAt hgrel
  have hF : ContinuousAt ((quadratic c)^[p]) z₀ :=
    (analyticOnNhd_quadratic_iterate c p z₀ (mem_univ _)).continuousAt
  have heq : ∀ᶠ z in 𝓝 z₀, g ((quadratic c)^[p] z) = (g z) ^ (2 ^ p) :=
    funEq_of_branch P hpartial hd hgAt hgz hgrel hF hFz hw₀ hdiv
  exact ⟨g, hgAt, hgz, hgrel, heq⟩

/-- **The index branch tuple from a relation, given the local genericity.** Packages
`exists_branch_with_FE` into exactly the shape `IndexResonance.false_of_branches_repelling_fixed` consumes:
the existential `∃ g ζ, AnalyticAt g z₀ ∧ g z₀ = ζ ∧ ζ ≠ 0 ∧ (Böttcher FE) ∧ deriv g z₀ ≠ 0`. The two
genericity inputs `w₀ ≠ 0` and `deriv g z₀ ≠ 0` are taken on the constructed branch; both hold off the
finite branch/critical locus of `P`, hence at every period-exactly-`p` point for a large prime `p`. The
functional equation form here is the `=ᶠ` between the two functions that the endpoint expects. -/
theorem exists_index_branch_tuple {U : Set ℂ} (c : ℂ) (p : ℕ) {w₀ d z₀ : ℂ}
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
        ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hroot : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hFz : (quadratic c)^[p] z₀ = z₀) (hw₀ : w₀ ^ (2 ^ p) = w₀) (hw0ne : w₀ ≠ 0)
    (hgen : ∀ g : ℂ → ℂ, AnalyticAt ℂ g z₀ → g z₀ = w₀ →
        (∀ᶠ z in 𝓝 z₀, ∑ i ∈ P.support, (P.coeff i).aeval z * (g z) ^ i = 0) → deriv g z₀ ≠ 0) :
    ∃ (g : ℂ → ℂ) (ζ : ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ = ζ ∧ ζ ≠ 0 ∧
      (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z₀] (fun y => g y ^ (2 ^ p)) ∧
      deriv g z₀ ≠ 0 := by
  obtain ⟨g, hgAt, hgz, hgrel, heq⟩ :=
    exists_branch_with_FE c p P hP0 hPmin hPrel hQrel hroot hpartial hd hFz hw₀
  exact ⟨g, w₀, hgAt, hgz, hw0ne, heq, hgen g hgAt hgz hgrel⟩

/-- **The connected-case obstruction from a minimal relation (no-attracting-fixed-point parameters).**
The full connector: a minimal relation `P` (with its `f^[p]`-composite also vanishing) cannot coexist with
* `B` a set of **repelling fixed points** of `f_c` (the exceptional set; needs no attracting fixed point),
* at every period-`p` cycle point off `B`, the **squaring-fixed simple-root datum** — a nonzero `w₀` with
  `w₀^{2^p} = w₀`, a simple root of the fibre, and the branch non-constant (`hgen`: the constructed branch
  has nonzero derivative), and
* the exceptional mass small (`hsmall`, automatic for large `p`).

`exists_index_branch_tuple` turns each bulk datum into the index branch tuple, then
`false_of_branches_repelling_fixed` (the index-formula obstruction) closes it. This reduces the connected
obstruction, end-to-end and machine-checked, to: a minimal relation `P` + the squaring-fixed simple-root
structure on the period-`p` cycle (the dynamical residue shared with the absolute-transcendence spine,
`exists_pow_fixed_root`) + the repelling fixed-point geometry. -/
theorem false_of_relation_bulk_branches {U : Set ℂ} (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
        ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (B : Finset ℂ) (hBfix : ∀ z ∈ B, quadratic c z = z) (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖)
    (hbulk : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B, ∃ (w₀ d : ℂ),
        (∑ i ∈ P.support, (P.coeff i).aeval z * w₀ ^ i = 0) ∧
        HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i) d w₀ ∧ d ≠ 0 ∧
        w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
        (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
          (∀ᶠ y in 𝓝 z, ∑ i ∈ P.support, (P.coeff i).aeval y * (g y) ^ i = 0) → deriv g z ≠ 0))
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False := by
  refine false_of_branches_repelling_fixed c hp hsep B hBfix hBrep ?_ hsmall
  intro z hz
  obtain ⟨w₀, d, hroot, hpartial, hd, hw₀, hw0ne, hgen⟩ := hbulk z hz
  have hFz : (quadratic c)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp
      (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1)
  exact exists_index_branch_tuple c p P hP0 hPmin hPrel hQrel hroot hpartial hd hFz hw₀ hw0ne hgen

/-- **Connected-case `φ_c`-transcendence via the index route (top-level entry).** The index analogue of
`ConnectedTranscendence.phiMero_transcendental_of_periodic_input`: `φ_c = phiMero c` is transcendental over
`ℂ(z)` provided that, for each minimal relation `P`, one can supply the **index-route dynamical data** — a
period `p ≥ 1` with `f_c^[p] - X` separable, a finite set `B` of repelling fixed points of `f_c` (the
no-attracting-fixed-point exceptional set), the squaring-fixed simple-root datum at every period-`p` cycle
point off `B`, and the small exceptional mass. The minimal relation is extracted by
`phiMero_transcendental_of_no_minimal_relation_min`; its `f^[p]`-composite vanishes by
`relation_vanishes_escapeOpen` + `relation_iterate_eq_zero`; `false_of_relation_bulk_branches` then closes
it through the index-formula obstruction. This is the index route carried end-to-end to the genuine carrier,
with the residual purely the per-cycle squaring-fixed root structure + the repelling fixed-point geometry. -/
theorem phiMero_transcendental_via_index {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (B : Finset ℂ), 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
          (∀ z ∈ B, quadratic c z = z) ∧ (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B, ∃ (w₀ d : ℂ),
            (∑ i ∈ P.support, (P.coeff i).aeval z * w₀ ^ i = 0) ∧
            HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i) d w₀ ∧ d ≠ 0 ∧
            w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
            (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
              (∀ᶠ y in 𝓝 z, ∑ i ∈ P.support, (P.coeff i).aeval y * (g y) ^ i = 0) → deriv g z ≠ 0)) ∧
          ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
            < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_minimal_relation_min hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, B, hp, hsep, hBfix, hBrep, hbulk, hsmall⟩ := hinput P hP0 hdeg hPrel hPmin hcount
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  exact false_of_relation_bulk_branches c hp hsep P hP0 hPmin hPrel hQrel B hBfix hBrep hbulk hsmall

/-- **Connected-case `φ_c`-transcendence via the index route, with smallness chosen internally.**
This variant removes the explicit exceptional-mass inequality from `phiMero_transcendental_via_index`.
For each minimal relation, the caller supplies one finite exceptional set of repelling fixed points and
eventual separability/bulk branch data.  Lean then chooses a sufficiently large period using
`eventually_exceptional_mass_small_roots` and closes with `false_of_relation_bulk_branches`. -/
theorem phiMero_transcendental_via_index_eventual {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ B : Finset ℂ,
          (∀ z ∈ B, quadratic c z = z) ∧
          (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
            B ⊆ (fixedPointPoly c p).roots.toFinset ∧
            (∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B, ∃ (w₀ d : ℂ),
              (∑ i ∈ P.support, (P.coeff i).aeval z * w₀ ^ i = 0) ∧
              HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i) d w₀ ∧
              d ≠ 0 ∧ w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
              (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
                (∀ᶠ y in 𝓝 z,
                  ∑ i ∈ P.support, (P.coeff i).aeval y * (g y) ^ i = 0) →
                deriv g z ≠ 0)))) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_minimal_relation_min hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨B, hBfix, hBrep, heventual⟩ := hinput P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, hpdata, hsmallRoot⟩ :=
    (heventual.and (eventually_exceptional_mass_small_roots c B hBrep)).exists
  rcases hpdata with ⟨hp, hsep, hBsub, hbulk⟩
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  exact false_of_relation_bulk_branches c hp hsep P hP0 hPmin hPrel hQrel B hBfix hBrep
    hbulk (hsmallRoot hp hsep hBsub)

/-- **Connected-case `φ_c`-transcendence via the index route, with fixed exceptional roots derived.**
This strengthens `phiMero_transcendental_via_index_eventual`: the caller only supplies a fixed finite
exceptional set of repelling fixed points and eventual bulk branch data.  The inclusion
`B ⊆ roots (f_c^[p] - X)` is derived internally from fixedness and `1 ≤ p`, while the exceptional-mass
smallness period is still chosen internally. -/
theorem phiMero_transcendental_via_index_eventual_fixedB {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ B : Finset ℂ,
          (∀ z ∈ B, quadratic c z = z) ∧
          (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable ∧
            (∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B, ∃ (w₀ d : ℂ),
              (∑ i ∈ P.support, (P.coeff i).aeval z * w₀ ^ i = 0) ∧
              HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z * w ^ i) d w₀ ∧
              d ≠ 0 ∧ w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧
              (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
                (∀ᶠ y in 𝓝 z,
                  ∑ i ∈ P.support, (P.coeff i).aeval y * (g y) ^ i = 0) →
                deriv g z ≠ 0)))) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_minimal_relation_min hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨B, hBfix, hBrep, heventual⟩ := hinput P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, hpdata, hsmallRoot⟩ :=
    (heventual.and (eventually_exceptional_mass_small_roots c B hBrep)).exists
  rcases hpdata with ⟨hp, hsep, hbulk⟩
  have hBsub : B ⊆ (fixedPointPoly c p).roots.toFinset := by
    intro z hz
    exact fixed_mem_fixedPointPoly_roots hp (hBfix z hz)
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  exact false_of_relation_bulk_branches c hp hsep P hP0 hPmin hPrel hQrel B hBfix hBrep
    hbulk (hsmallRoot hp hsep hBsub)

end Bottcher
