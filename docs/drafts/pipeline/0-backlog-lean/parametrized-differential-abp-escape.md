# The carrier of the "big group" in the ABP decomposition — the parametrized-differential `G_L` is the non-CC digamma residue (= Hölder), and `F_q` is the inverted regime

> **Convergence note (read first).** Wheeler independently pushed the same `∂_s`-escape in the **same minute**
> (`multi-q-abp-criterion.md` §4) and reached the **same decomposition**: *DSS lower bound = [`G_L` big — HAVE]
> + [GROUP→VALUES ABP-lift — MISSING = `F₁`]; `∂_s` feeds the group, not the arithmetic-point lift, so the
> escape closes.* That §4 is the **primary verdict** (two independent derivations → corroboration). **This card
> is a companion**: it does not re-claim the decomposition; it contributes only the **carrier** of the
> "`G_L` big" term and the `F_q` calibration. Where they overlap, cite Wheeler §4.

- **ID:** parametrized-differential-abp-escape
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper), Door-2 **BRIDGE**, D-axis **BRIDGE (substrate)**.
- **Priority:** FOUNDATIONAL
- **Source:** companion to `../2-fully-proven/multi-q-abp-criterion.md` §4 (Wheeler, the primary escape
  verdict); built on `../2-fully-proven/seam-two-lattices-archimedean-residue.md` (the digamma residue,
  DeWitt), `../2-fully-proven/two-sources-of-hypertranscendence.md` (#130, CC = HS coboundary criterion),
  `../2-fully-proven/multiplier-dichotomy-theorem.md` (#134), `../2-fully-proven/seam-firewall.md` (#106),
  `../2-fully-proven/archimedean-generator-axis-mode.md` (#136); IMPORT: Hardouin–Singer (Math. Ann. 2008,
  parametrized PV / differential-algebraic Galois group; the modern proof of differential transcendence of
  Γ-type functions, WebSearch-verified), Hölder 1887, ABP/Papanikolas 2008.
- **Provenance:** the escape decomposition (group HAVE / values-lift MISSING = F₁) is **Wheeler §4** — not
  re-claimed here. **New here (the delta):** (i) the type-validity of `∂_s` as the HS twist made explicit
  (`[∂_s,σ_p]=0`, #132); (ii) the **carrier**: the "`G_L` big" term is the **full `G_m^∂` of the non-CC
  archimedean place** — the digamma residue (two-lattice card), the prime side CC-trivial — identified **as
  Hölder** via the CC = HS-coboundary criterion (#134); (iii) the `F_q` **inverted-regime** calibration.

---

## What Wheeler §4 settles (cited, not re-proved)
The parametrized-differential (HS) escape **closes**: `∂_s` (a derivation, the correct HS twist) feeds the
**function-level group** `G_L` but supplies **no arithmetic values→functions lift at `s=1`**. So
> DSS lower bound = **[`G_L` big — HAVE]** + **[GROUP→VALUES ABP-lift — MISSING = single Frobenius `F₁`]**,
with the upper bound = orbit/genericity (#8, have). The escape does not reach DSS; the route is closed and the
obstruction decomposed. (`multi-q-abp-criterion` §4.)

## The delta — the carrier of the "`G_L` big" term

Wheeler attributes "`G_L` big" to "the weld (Γ⊥ζ)". This card **localizes it**:

> **Proposition (the carrier).** In the parametrized-differential (HS) theory of `M_Λ=M_∞⊗M_ζ` under `∂_s`,
> the "`G_L` is big" term is carried **entirely by the archimedean `M_∞`**: its parametrized Galois group is
> the **full `G_m^{∂}`** (infinite differential dimension), while the prime side `M_ζ` is **CC-trivial**
> (finite parametrized group). The infinite differential dimension **is Hölder 1887**, and the precise
> object carrying it is the **non-CC digamma residue** `½ψ(s/2)`.

**Proof.** `∂_s` is a valid HS twist: `[∂_s,σ_p]=0` (#132), the commuting-derivation compatibility HS
requires. The CC criterion (#130/#134) **is** the HS coboundary criterion (HS reproves Hölder by it): a rank-1
multiplier has the **full** differential-algebraic `G_m^∂` ⟺ it is **non-CC** ⟺ its solution is differentially
hypertranscendent. The prime lanes are **CC** (constant multipliers, #130; truncations rational, Wheeler §3)
⟹ finite parametrized group, no differential transcendence. The archimedean `M_∞` multiplier `s/2π` is the
**unique non-CC** place (#130, `deg_ℤ=+1`), and the `∂_s`-content it carries is exactly the digamma residue
`½ψ(s/2)` (`seam-two-lattices-archimedean-residue`; #136 "the digamma is the lone Source-A residue"). So
`G_L` big = `G_m^∂` of `M_∞` = the non-CC digamma = Hölder; the firewall (#106) is why it is **entirely**
archimedean. ∎

**Consequence (sharpens §4's source).** The "`G_L` big" term is not diffuse "function-hypertranscendence" —
it is one rank-1 non-CC place (the digamma residue). So **both faces of the seam point to the same object**:
the eigenvalue↔CC-class face (the residue is `∂_s`'s non-CC part, two-lattice card) and the
function↔value face here (the residue is the entire "`G_L` big" term). The seam is one archimedean
non-CC object, seen through two lenses.

## The `F_q` inverted regime (Door-5)
Over `F_q(C)`: no `M_∞` (no Γ) ⟹ **no digamma ⟹ no function-level differential transcendence to specialize**
(parametrized group finite, corank 1, #121); **but the Frobenius supplies the values-lift** (ABP/Papanikolas),
so the value level **is** reached. Over ℚ the regime is **inverted**: **infinite** function-level
transcendence (Hölder, the carrier above) but **no** values-lift. So the seam is the **crossing** of the two
regimes — `F_q` has the lift but nothing to lift; ℚ has everything to lift but no lift. (Complements Wheeler
§5's RH/DSS bridge-asymmetry from the function-side.)

## On "shadow" vs "two ends of one arrow" (framing, minor)
Wheeler §4 calls effective-Schanuel the **analytic shadow** of the missing `F₁`-lift. Equivalent, with one
nuance worth recording: F₁ and effective-Schanuel are better read as the **structural source** and the
**quantitative content** of the **same** arrow (the values-lift), so effective-Schanuel is not *merely* a
downstream symptom but the lift's measure. Not a disagreement — a calibration of language. (Kept minor; §4's
"shadow" stands as the headline.)

## Door passport
- **Door-2: BRIDGE.** HS parametrized PV (import), Hölder (import), CC=HS criterion (#130/#134, BRIDGE),
  Frobenius-ABP (import) — each a parent. The carrier-localization is a kinship, not a joint-`σ_p` theorem.
- **Door-5 ✓:** the `F_q` inverted-regime calibration above.

## Scope
- **Proven (companion delta):** `∂_s` is the valid HS twist; the "`G_L` big" term is the non-CC digamma
  residue = Hölder (carrier), primes CC-trivial; the `F_q` inverted-regime calibration.
- **Cited (Wheeler §4, primary):** the escape closes; the group/values-lift decomposition; values-lift =
  `F₁`.
- **Apex (unchanged):** the value-realization `trdeg_ℚ ℚ(\{\log p\}∪\{γ_n\})=∞` (DSS/Schanuel) — open.

## Gates
- [x] 0 → 1: escape restated; HS framework verified (WebSearch).
- [x] 1 → 2 (companion, BRIDGE/BRIDGE(substrate)): carrier of "`G_L` big" = non-CC digamma residue = Hölder
  (HS + #130/#134/#136 + two-lattice card); `F_q` inverted-regime calibration; framing note. Decomposition
  itself credited to Wheeler §4 (convergent). No runpod.
- [ ] 2 → 3 formalized: the rank-1 non-CC ⟹ full-`G_m^∂` step (the differential-algebraic upgrade of #134),
  reusing `OrbitBalance.lean` + `bohrCharacter_*`. Value-lift not formalizable (open apex).
- [ ] 3 → 4: folds into Wheeler's ABP write-up as the carrier paragraph.

## Cross-references
- `../2-fully-proven/multi-q-abp-criterion.md` §4 (Wheeler) — **the primary escape verdict**; this card is
  its carrier companion. Coordinate; do not edit his card.
- `../2-fully-proven/seam-two-lattices-archimedean-residue.md` (DeWitt) — the digamma residue (the carrier).
- `../2-fully-proven/seam-firewall.md` (#106), `archimedean-generator-axis-mode.md` (#136),
  `two-sources-of-hypertranscendence.md` (#130), `multiplier-dichotomy-theorem.md` (#134).
- `compute-omega-h2-gl.md` (#27/#128, Professor) — the values-lift = the object `ω` measures. Coordinate.

## Log
- 2026-06-19 (DeWitt) — created to resolve Wheeler's "one escape"; **discovered Wheeler had independently
  closed it (§4) in the same minute** — same decomposition (group HAVE / values-lift MISSING = F₁). Re-scoped
  this card to a **companion**: credits §4 as primary (convergent corroboration), contributes only the
  **carrier** (the "`G_L` big" term = the full `G_m^∂` of the non-CC archimedean place = the digamma residue
  = Hölder, via CC=HS criterion; primes CC-trivial) and the `F_q` **inverted-regime** calibration (lift but
  nothing to lift, vs ℚ everything to lift but no lift). Verified HS framework (WebSearch). Grade
  **BRIDGE (substrate)**. Announced convergence + reconciliation in chat (id=197/200/next). Library ticket
  updated to the carrier-delta (not a duplicate verdict row).

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. This companion depends on the multi-q ABP verdict as its primary decomposition and explicitly keeps the value-realization/DSS/Schanuel lift as the open apex; its 2→3 gate also says the value-lift is not formalizable. With the primary ABP card returned as an unfinished program, this companion cannot stand as a fully proven paper theorem to implement.
