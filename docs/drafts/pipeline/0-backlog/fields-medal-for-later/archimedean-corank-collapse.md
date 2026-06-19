# The archimedean corank collapse — is the missing single Frobenius exactly ∂_s? (the lead bet)

- **ID:** archimedean-corank-collapse
- **Stage:** 0-backlog
- **Type:** CONJECTURE (falsifiable lead — decides the whole archimedean-generator program)
- **Priority:** FIELDS MEDAL
- **Source:** ../../door/bucket-archimedean-generator.md (§X9·NEW — the one part of that bucket **not**
  already in the corpus); resolves `../2-fully-proven/corank-transcendence-continuation-bridge.md` and
  `../0-backlog/corank-seam-invariant.md` (#125) constructively; builds on
  `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121, `corank=1` over `F_q`); connects
  the already-mined operator (`∂_s = −Σ(log p)θ_p` = Connes op, #88 §7 / #90 §1) and the already-mined
  "FE = product formula, places = primes ∪ {∞}" (#70) and "two hypertranscendence sources: Γ-place + the
  infinite base" (#90 §64.4) to the **new** corank trilogy;
  ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #121, #122, #123, #125
- **Statement (to shape).** Over ℚ the finite-prime relation lattice is `Λ_{M_ζ} = {m : Σ_p m_p log p = 0}
  = 0`, so `corank = ∞` (no relation among the multipliers `1/p`). The **product formula**
  `∏_v |x|_v = 1` (already identified as the FE / the `0↔∞` base-swap, #70 / #90 §64.3) is the one missing
  relation, and in operator form it **is** the archimedean generator `∂_s = −Σ_p (log p) θ_p` (the
  archimedean Euler operator = Connes' scaling operator `D` of #88 §7 / #90 §1, = minus the weighted sum
  of the finite ones).
  **Conjecture (lead bet):** in the **enriched** lattice `Λ⁺` of the completed module `M_Λ ∈ 𝓜⁺` (which
  includes the `∂_s`-direction), `corank(Λ⁺) = 1`, the lone relation being `∂_s` (the product formula).
  Hence **the "missing single Frobenius" of the seam is exactly `∂_s`**, and the seam gap
  `corank(Λ_ℚ) − corank(Λ_ff) = ∞ − 1` reads literally **"`∞` finite primes, `1` archimedean relation."**

  **One sentence:** the infinite corank over ℚ is an artifact of writing the archimedean (differential)
  datum in finite-difference language; restore the generator `∂_s` and the corank collapses to the same
  `1` that `F_q` enjoys — with `∂_s` playing the role `F_q`'s single Frobenius `q` plays there.

## Goal
This is the **decision card** for the whole archimedean-generator program. If the collapse holds, the
seam is *named and located* (`= ∂_s`) and every corank-∞ face (G1 non-holonomicity, G2 transcendence, G4
weight torus) acquires a single finite archimedean explanation. If it **fails** — if `Λ⁺` still has
infinite corank — that is itself a sharp result: the archimedean corank is a genuinely new infinite
invariant not reducible to one relation, and the seam is *worse* than "one missing Frobenius." Either way
the bet is falsifiable and worth settling first.

## The mechanism to test (and the honest subtlety)
- `Λ` (existing) records **multiplicative** relations among the multipliers `g_p = 1/p`. `∂_s` adds a
  relation among the **flows/derivations**, not directly among the multipliers — so "does `∂_s` reduce
  `corank`?" is **not** automatic. The card's first job is to define `Λ⁺` precisely: the relation lattice
  of the enriched multiplier datum `{g_p} ∪ {archimedean datum of ∇_s}`, and to decide whether the
  product-formula identity `∂_s = −Σ(log p)θ_p` is a **relation in `Λ⁺`** (collapse) or a **new
  generator** (no collapse).
- **Concrete test object.** The Stieltjes constants `γ_n` are `∂_s`-data (Taylor coefficients in `s`).
  Currently (`corank-transcendence-continuation-bridge` §2) they are forced through `{log p}`, producing
  `∞` transcendentals. Test prediction: in `𝓜⁺` the `γ_n` are **one derivation's** data, so the
  enriched continuation-transcendence is `trdeg = 1` *in the `∂_s`-direction* — the archimedean analogue
  of `F_q`'s lone `ln q`. Compare to the FF computation (`trdeg = corank = 1`, #122) as the template.
- **`F_q` control.** Over `F_q(C)`, `corank = 1` already and `∂_s` ↦ a Frobenius place; the enriched
  lattice must stay `corank = 1` (no double-counting). A required consistency anchor.

## Door passport
- **Door-2:** if the collapse holds via an *essential* use of the uniform infinite-prime weighting
  `Σ(log p)θ_p` (no finite-base parent has it), the statement is **NATIVE/C5** — the first one. If it
  reduces to single-prime/finite data, BRIDGE. The card is designed to expose which.
- **Door-5:** the `F_q` anchor (`corank=1` recovered) is the recovery check.
- **Couples to** `completed-connection-category` (needs `Λ⁺` defined there) and to
  [[bucket-the-seam-archimedean-obstruction]] (#125 corank face).

## Approach
1. **Define `Λ⁺`** for `M_Λ ∈ 𝓜⁺` (depends on `completed-connection-category`’s axioms).
2. **Adjudicate the product-formula identity** `∂_s = −Σ(log p)θ_p`: relation in `Λ⁺` (collapse to 1) or
   new generator (no collapse)? This is the crux — settle it with the operator algebra, not heuristics.
3. **Stieltjes test.** Recompute the continuation transcendence of `Λ` *with* `∂_s` primitive; predict
   `trdeg = 1` in the `∂_s`-direction; archive any numerical pre-certification in `computations/`.
4. **`F_q` consistency** (Door-5) and the verdict (Door-2 native vs bridge).

## Gates
- [ ] 0 → 1  in-progress: `Λ⁺` defined; the collapse-vs-new-generator dichotomy stated as a precise
  operator-algebra question; Stieltjes test-prediction written; `F_q` anchor pinned; Door passport
- [ ] 1 → 2  fully-proven: the product-formula identity adjudicated in `Λ⁺` (collapse `∞→1` proven, or
  the infinite-corank alternative proven); Door-2 verdict; `F_q` recovery checked
- [ ] 2 → 3  formalized: Lean — the product-formula operator identity and (if collapse) `corank(Λ⁺)=1`,
  reusing `linearIndependent_log_primes` and #121's `Λ_ff = ker deg`
- [ ] 3 → 4  publication-ready: "the missing single Frobenius is `∂_s`" (or its falsification)

## Notes / risk
- **Not claimed proven.** The mechanism (whether `∂_s` is a relation or a generator in `Λ⁺`) is the open
  crux; both outcomes are informative. No RH consequence asserted.
- Possible collision: `corank-seam-invariant` (#125, the ℚ lower-bound realization) and
  `baker-for-stieltjes` (the analytic Stieltjes instance). This card supplies the **constructive
  `∂_s` resolution**; those supply the difference-language realization. Flag to the seam thread.

## Cross-references
- `../../door/bucket-archimedean-generator.md` (§X9·NEW) — parent.
- `completed-connection-category.md` — defines `𝓜⁺`/`Λ⁺` (dependency).
- `../0-backlog/corank-seam-invariant.md` (#125), `../2-fully-proven/corank-transcendence-continuation-bridge.md`
  (#122), `../1-in-progress/baker-for-stieltjes.md` — the difference-language corank faces this card
  resolves constructively. **Do not duplicate their analysis.**

## Log
- 2026-06-19 — created in 0-backlog from §X9·NEW. The falsifiable lead bet of the archimedean-generator
  program: `∂_s` = the product-formula relation collapses ℚ-corank `∞→1`, naming the missing single
  Frobenius `= ∂_s`. Stated the honest crux (relation-in-`Λ⁺` vs new-generator) and the Stieltjes test
  (`trdeg=1` in the `∂_s`-direction). First step = define `Λ⁺` and adjudicate the product-formula identity.
</content>
