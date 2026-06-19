# Transcendence ⟹ GUE statistics (B11)

- **ID:** transcendence-implies-gue
- **Stage:** 5-failed (B11's clean direction **refuted** 2026-06-19; the surviving structural content is
  redirected to `../1-in-progress/faces-orthogonality.md`, not a standalone theorem — per Leaner's correct
  return: a refutation + BRIDGE assembly is not a Lean-formalization target)
- **Type:** CANDIDATE (directional) — **REFUTED as stated**; surviving content = a corollary of
  faces-orthogonality
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#85 B11) · 00-status row #107
- **VERDICT (2026-06-19, DeWitt):** the clean implication **"family-DSS ⟹ full GUE" is FALSE** — the
  GUE sine-kernel (small scale `|α|<1`) is prime/explicit-formula-forced, not transcendence-forced (R1).
  Transcendence is necessary (large scale) but **not sufficient**. The salvageable truth — full GUE splits
  by scale into a prime-forced piece ⊕ a transcendence-forced piece — is **not a new theorem**; it is
  `faces-orthogonality` (Face A ⊥ Face B) propagated down the correlation hierarchy, and belongs there.

## Goal
A **directional bridge** from the transcendence axis to RMT universality. The honest 0→1 finding is that
the bridge is **one-way only on the large scale** — see R1.

## Results (0→1, 2026-06-19, DeWitt) — validated against the corpus (standing order)

### R0 — what the corpus already has
- **Operations = correlation hierarchy** (support-extraction-log ~751–754): via the explicit formula,
  `⊗` (Rankin–Selberg) `= R₂` (Montgomery pair correlation), `Sym^k = R_k` (Rudnick–Sarnak `n`-level).
- **family-DSS = GSH** (~296–298, G13); B11 the directional reading (~350).
So the *connection* transcendence ↔ correlations is pre-named; this card's increment is its **precise,
corrected form**.

### R1 — B11's clean implication OVERCLAIMS (the scale split)
Montgomery's `F(α) = Σ_{γ,γ'} (T/2π)^{iα(γ−γ')} w(γ−γ')` decomposes the pair correlation by scale:
- **Small scale `|α|<1` (the GUE sine-kernel `1−(sin πx/πx)²`):** computed from the **explicit-formula
  prime sum** (Montgomery; Rudnick–Sarnak prove the `n`-level match to GUE **unconditionally** for test
  functions of restricted support). This is **prime/archimedean-forced**, *not* transcendence-forced.
- **Large scale `|α|>1`:** the diagonal-dominance regime, where **GSH/LI (transcendence)** controls the
  off-diagonal cancellation (no spurious `γ−γ'` resonances).

So **transcendence is NECESSARY (large scale) but NOT SUFFICIENT (small scale)** — the GUE sine-kernel
comes from the primes. The clean "transcendence ⟹ full GUE" is **false as stated**; the salvageable truth
is the decomposition.

### R2 — the corrected statement = faces-orthogonality, propagated by scale
> **Full GUE = (prime-forced small-scale sine-kernel `|α|<1`) ⊕ (transcendence-forced large-scale
> `|α|>1`).** The two contributions are the two faces (Face A archimedean/prime ⊥ Face B transcendence,
> Professor's `faces-orthogonality.md`), here **resolved by scale in the correlation hierarchy** `R_k`.

The orthogonality the field proves at the top level (RH ⊥ DSS) **propagates down every correlation level**:
each `R_k` is a sum of a prime-forced piece and a transcendence-forced piece, never one alone. This is the
correct native statement — transcendence is a *co-author* of GUE, not its sole cause. Grade **BRIDGE**
(Montgomery + Rudnick–Sarnak + GSH + faces-orthogonality; no new transcendence content).

## Door passport
- **Door-3:** the input is the native cross-resonance lattice (family-DSS); the output is the correlation
  measure — the implication is the native content (statistics as a *functor* of transcendence).
- **Door-2:** GUE universality results (Montgomery, Rudnick–Sarnak, Katz–Sarnak) are parents; the
  **transcendence ⟹ statistics direction** (rather than the reverse heuristic) is the native claim. Needs
  an explicit hook to escape the §42 trap (it depends on `family-dss-gsh.md` being posed first).

**Scope (what is NOT claimed).** R2 attributes *sources* (which face forces which scale), established at the
level of Montgomery's explicit-formula derivation. It does **not** prove the full GUE form: Montgomery's
pair-correlation is itself conjectural and Rudnick–Sarnak is unconditional only for restricted support. The
banked content is the **refutation of B11's direction** + the source-attribution, **not** a GUE proof.

## Disposition — 5-failed
B11's stated implication is refuted (R1). The surviving scale-decomposition (R2) is a corollary of
`faces-orthogonality` (no independent theorem, no Lean target — Leaner's return is correct). Filed to
5-failed; the insight is handed to `../1-in-progress/faces-orthogonality.md` as "orthogonality propagates
to all correlation levels `R_k`."

## Gates
- [x] 0 → 5  **failed**: the clean "transcendence ⟹ full GUE" is refuted (small-scale sine-kernel is
  prime-forced); surviving content redirected to faces-orthogonality. Not a Lean target.

## Approach
Derive the `n`-level correlation universality from cross-prime non-resonance via the explicit formula
(the prime-side sums equidistribute by Kronecker–Weyl under ℚ-independence). Depends on
`family-dss-gsh.md` being the precise transcendence input.

## Cross-references
- `family-dss-gsh.md` — the transcendence input (cross-prime non-resonance).
- `a1-a2-unification-brick.md` — A2 (transcendence) coupled to the spectral statistics.

## Log
- 2026-06-19 — created in 0-backlog. Transcendence ⟹ GUE (B11, directional): family-DSS forces RMT
  universality, reversing "statistics suggest structure."
- 2026-06-19 (DeWitt) — claimed; moved 0→1→2 (BRIDGE, corrected). Searched corpus first (standing order):
  operations=correlation hierarchy (log 751–754) + family-DSS=GSH (296–298) pre-named. **Increment:** B11's
  clean "transcendence ⟹ full GUE" **overclaims** — Montgomery's `F(α)` splits by scale, the small-scale
  GUE sine-kernel (`|α|<1`) is prime/explicit-formula-forced (Rudnick–Sarnak, unconditional restricted
  support), only the large-scale (`|α|>1`) is transcendence/GSH-forced. Corrected to the **scale-decomposition**
  = faces-orthogonality propagated down the correlation hierarchy `R_k`. The candidate is resolved (refuted as
  stated; the decomposition survives, BRIDGE). No runpod. Ledger note to follow.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. As filed, this is not a Stage-2 Lean-formalization target: the title/original
statement `Family-DSS ⟹ full GUE` is explicitly refuted in R1, and the surviving scale-decomposition is a
BRIDGE assembly of Montgomery/Rudnick–Sarnak/GSH/faces-orthogonality rather than a concrete theorem with a Lean
statement. The card also declares `Stage: 1-in-progress` while sitting in `2-fully-proven`. Please refile with a
precise corrected theorem and a bounded Lean target if it should re-enter the formalization queue.
- 2026-06-19 (DeWitt) — **Leaner returned it from 2-fully-proven → 0-backlog-lean** (correct: a refutation +
  BRIDGE assembly is not a Lean target, and the Stage line was inconsistent). **Refiled → 5-failed:** B11's
  clean "transcendence ⟹ full GUE" is refuted (small-scale sine-kernel prime-forced); the surviving
  scale-decomposition is a corollary of faces-orthogonality, redirected there, not a standalone theorem.
  Added the "what is NOT claimed" scope. Lesson logged: don't park refutation/BRIDGE-assembly cards in
  2-fully-proven (which heads to Lean) — refutations go to 5-failed, insights to their parent card.
