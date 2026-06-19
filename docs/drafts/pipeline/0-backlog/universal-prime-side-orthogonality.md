# Universal orthogonality — no prime-side positivity is equivalent to RH

- **ID:** universal-prime-side-orthogonality
- **Stage:** 0-backlog
- **Type:** CONJECTURE (the open residual of the orthogonality meta-theorem)
- **Priority:** FOUNDATIONAL (it would close whether any purely-prime route to RH exists)
- **Source:** split from `../2-fully-proven/orthogonality-meta-theorem.md` §6 (the universal residual, explicitly
  not banked there); `../../door/bucket-realization-and-fake-family.md`, `../../door/bucket-the-seam-archimedean-obstruction.md`;
  00-status row #137
- **Statement.**
  > **Conjecture (universal orthogonality).** There is no positive-definite polarization on any object of the
  > completed category `𝓜` whose positivity is **equivalent to RH** and which is definable from the
  > **Source-B / prime-lattice** structure alone (Euler / Satake λ-ring / `σ_p`), without the archimedean
  > completion.

  The meta-theorem (`orthogonality-meta-theorem.md`) proves the **located** form: the *canonical* RH-positivity
  (Weil, and every known equivalent — Li, Herglotz/`κ₋=0`, Bombieri) is the **archimedean** polarization, hence
  not Source-B-definable (§§1–3, robust under §2). This card is the **universal** generalization from
  "every known criterion" to "every possible criterion": that **no** prime-side positivity expression of RH
  exists at all.

## Goal
Closes the structural question the BRIDGE monoculture raises. A proof upgrades "every proven Source-B result is
RH-blind" from an empirical pattern + a located theorem to a **no-go**: the prime wing cannot carry RH under any
formulation, so RH-bearing C5 *must* use the archimedean weld (`archimedean-prime-cross-term`). It is the
sharp, falsifiable form of the field's central diagnosis (the seam = the sole RH obstruction). A
**counterexample** — a prime-side positive form whose positivity ⟺ RH — would refute it and reopen Source B as
an RH route (none found in 150 years; cf. the realization fakes that pass positivity, #82/#84).

## Door passport
- **Door-2.** The *located* theorem is BRIDGE (imports Weil + Tannakian duality). The *universal* claim, if
  ruling out all prime-side formulations genuinely requires the no-single-Frobenius / `corank=∞` obstruction
  (no `√q`-weight self-duality over ℚ, vs `F_q`'s `corank=1`), is the **negative/substrate** dual of C5 — "an
  obstruction every parent sees and none resolves" (D4). Grade to be decided by whether the proof is parent-
  reachable or needs the native apparatus.
- **Door-4.** Lives at the seam: the archimedean ⊥ prime decomposition (`faces-orthogonality` §5′, unconditional
  via #132/#133). The claim is precisely that the prime side of that decomposition is RH-positivity-free.
- **Door-5.** Over `F_q` the conjecture is **false on purpose** — the single Frobenius supplies the `√q`-weight
  polarization (`LocalFactorDuality`), so Source B *does* carry RH = Weil. The universal claim is therefore a
  **number-field-only** statement; its hypothesis (no single Frobenius) is exactly the ℚ/`F_q` separator.

## Gates
- [ ] 0 → 1  in-progress: state the quantifier precisely (define "Source-B-definable polarization" / the
  category `𝓜_B`); fix the witness/counterexample shape; Door passport sketch
- [ ] 1 → 2  fully-proven: either a no-go (every RH-equivalent positive form on `𝓜_B` reduces to the
  archimedean polarization) or a counterexample; grade Door-2
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Generalize the rank-1 orthogonality lemma (`orthogonality-meta-theorem` §1: `g_p^∨ = g_p^{-1}`, no
`g_p = g_p^{-1}` for a non-unit multiplier) from one object to the whole Source-B subcategory: show any
self-duality on a prime-lattice object forces the trivial (unit) multiplier, so no nontrivial `s↔1−s`
polarization exists without the archimedean factor. Equivalent operator face: the Satake λ-ring `𝓜=ℚ[p_m]`
(#79) carries no RH-equivalent positive form because its `∞`-prime Koszul complex is acyclic (`H(t)E(−t)=1`,
`compute-omega-h2-gl` §R) — the multiplicative wing has no archimedean content. The hard part is the universal
quantifier over *all* polarizations, not the witnessed ones; the lever is the `corank=∞`/no-`√q`-weight
obstruction (`corank-seam-invariant`, #125).

## Cross-references
- `../2-fully-proven/orthogonality-meta-theorem.md` (#137) — the located theorem this generalizes (its §6 residual).
- `../0-backlog-lean/faces-orthogonality.md` (#54) — Face A ⊥ Face B logical independence (the disjoint-wings input).
- `../2-fully-proven/archimedean-prime-cross-term.md` (#134) — the weld where RH-bearing C5 must live if this holds.
- `realization-problem.md` (#84), `intrinsic-rh-locus-pure-polarized.md` (#98) — fakes pass positivity / which objects have RH.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the seam = the polarization = the missing Frobenius.

## Log
- 2026-06-19 — created in 0-backlog. Split from `orthogonality-meta-theorem.md` §6: the meta-theorem proves the
  located archimedean-positivity statement and explicitly leaves the universal "no prime-side RH-positivity at
  all" conjecture unbanked. Logged here so the open residual is tracked rather than orphaned in the proof card.
