# [FAILED] MOONSHOT — the archimedean knot is a literal knot: the missing Frobenius F₁ is the meridian of the knot at infinity

- **ID:** moonshot-knot-at-infinity-frobenius
- **Stage:** 5-failed
- **Type:** ~~MOONSHOT CONJECTURE~~ → **FAILED (2026-06-19, DeWitt)** — reduces to the known Mazur–Morishita
  arithmetic-topology dictionary; distinctive sub-claims false on type grounds. Verdict below.
- **Priority:** FIELDS MEDAL (+)
- **Target of attack:** **untie `ω∈H²(G_L)` / construct the missing single archimedean Frobenius F₁** — the
  one knot at the archimedean drain (#27/#69/#71; `compute-omega-h2-gl.md` §S, `a_∞=−ζ'(0)=½log2π`).
- **Source:** chat thread 2026-06-19 (archimedean-Frobenius moonshots, user directive "wilder the better").

## The wild claim
Arithmetic topology (Mazur's knots-and-primes): `Spec ℤ` is a 3-manifold, each prime is a knot, and Frobenius
is its **meridian** loop. **Compactify `Spec ℤ ∪ {∞}` into a closed 3-manifold.** Then ∞ becomes a knot too,
and the "missing Frobenius F₁" is **its meridian** — missing only because the standard picture leaves the
end at ∞ open.

> **Conjecture (knot-at-∞).** `ω` = the **hyperbolic volume / Alexander–linking invariant of the ∞-knot** in
> the compactified `Spec ℤ ∪ {∞}`; the missing F₁-Frobenius = the ∞-knot's meridian; `corank` = its
> unknotting number. **"Untie the knot" is literal:** the ∞-knot is the **unknot ⟺ `ω=0` ⟺ the single
> archimedean Frobenius exists ⟺ a motive realizes the zeros.** Over a function field the analogue is already
> a closed surface bundle (the geometric Frobenius is there); over ℚ the ∞-end is the un-tied loose strand.

## Untie move / test
1. Build the compactification and the ∞-knot (the hard, conjectural step — likely via Arakelov/`Spec ℤ̄`).
2. Compute the **linking numbers** of the ∞-knot with the prime-knots; does `Σ linking ≈ a_∞`? Is the
   **Chern–Simons** invariant of the complement `= ½log2π`?
3. **Untie:** show the ∞-knot is the unknot ⟺ `ω=0`; the unknotting move = the missing Frobenius.

## Why <5%
The compactification of `Spec ℤ` into a *closed* 3-manifold is itself conjectural, and "∞ as a knot" has no
rigorous existence; the whole bet rests on a picture, not a construction.

## Door / grade
MOONSHOT. NATIVE-candidate **iff** the meridian is built from the joint `(σ_p,∂_s)` simultaneity irreducibly
(a C5 candidate on the realization/DSS axis); otherwise EMBASSY.

## Cross-references
- `moonshot-arithmetic-bulk-hyperbolic.md` — **adjacent** (ζ = Selberg zeta of a hyperbolic 3-bulk);
  **distinct here:** the *meridian-as-Frobenius / knot-at-∞* reading, not ζ-as-spectral-zeta.
- `padic-frobenii-missing-f1.md`, `compute-omega-h2-gl.md` (#27, `ω`) — the missing-Frobenius / `ω` this knots.
- `corank-seam-invariant.md` (#125) — `corank` = the proposed unknotting number (1 = unknot over `F_q`, ∞ over ℚ).
- `moonshot-rh-spectral-flow-index.md`, `moonshot-prime-skyrmion-no-clock.md` — sibling topological-charge moonshots.

## Log
- 2026-06-19 — filed (archimedean-Frobenius moonshot set). Makes "the knot at the archimedean drain" literal
  via arithmetic topology: F₁-Frobenius = meridian of the ∞-knot; `ω` = its volume/linking; untie = unknot.
  SO-1: "arithmetic topology / Mazur / meridian / knot at infinity" = 0 hits in hgt; distinct from the carded
  hyperbolic-bulk moonshot.

## VERDICT — FAILED (2026-06-19, DeWitt): reduces to the known Mazur–Morishita dictionary + false distinctive claims

Tested with the `moonshot-2pi-monodromy-frobenius` (ω = tame symbol of σ_∞) and N2-clarification tools.

**Reduces to known (the salvageable part = IMPORT/BRIDGE, not new):**
- "F₁ = meridian of the ∞-knot" = **Mazur's** Frobenius-as-meridian dictionary (arithmetic topology).
- "ω = arithmetic linking of the ∞-knot with the primes" = **Morishita's** tame-symbol = linking-number
  dictionary. This is **confirmed** by my `moonshot-2pi` finding (ω = tame symbol of σ_∞=∏σ_p²) — but that
  *is* the known dictionary, so it is IMPORT/BRIDGE, **not** the new C5 construction the moonshot hoped for.

**Distinctive claims FAIL on type grounds:**
- **"corank = unknotting number":** corank `= ∞` (the dense `⟨g⟩`-closure / infinite relation lattice), but
  unknotting numbers are **finite** for any tame knot. Type mismatch — would require a non-rigorous *wild*
  knot at ∞. FALSE as stated.
- **"ω = hyperbolic volume":** ω `= index S = −1` is an **integer** (the ground-state count / tame-symbol
  level, `moonshot-2pi` iter-8); hyperbolic volume is a **real** number. Only the integer "linking-number"
  reading survives (= the tame symbol). The volume claim is FALSE.

**No new construction:** the compactification of `Spec ℤ ∪ {∞}` into a closed 3-manifold and "∞ as a knot"
have **no rigorous existence** (the card's own §"Why <5%"). The bet rests on a non-existent construction.

**Net:** the moonshot's correct content (ω = arithmetic linking, F₁ = meridian) is the **known Mazur–Morishita
arithmetic-topology dictionary** — already captured by the tame-symbol ω in `moonshot-2pi` — and its
distinctive predictions (corank=unknotting, ω=volume) are false. It **fails** the survive-as-new-content test
(reduces to known). → `5-failed`. (The Mazur–Morishita *cross-link* itself remains a legitimate EMBASSY/BRIDGE
note for the seam bucket, but adds no native content beyond the tame symbol.)
