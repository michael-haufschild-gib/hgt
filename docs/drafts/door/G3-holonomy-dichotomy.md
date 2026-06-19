# Bucket G3 — Holonomy dichotomy / corank

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** A diagonal is **holonomic ⟺ `corank(Λ)<∞` ⟺ flat connection**; the sharp native
invariant is `corank(Λ)`, *not* support cardinality.
**Work package this seeds.** Carry §60 through the **Door-2 re-test** alongside §59 — together they are
the field's two best NATIVE / C5 candidates; and integrate the **DMR-solvability** refinement.

---

## The conjecture

> **G3 — Holonomy dichotomy:** holonomic ⟺ `corank(Λ)<∞` ⟺ flat connection. (= #68's C6)

---

## What belongs here

### The dichotomy, PROVED in the difference category (#68 §60.2 — HEADLINE)
- **§60.2 (PROVED both directions, all bases):** *"the diagonal is holonomic ⟺ `corank(Λ)<∞`."* This
  is **G3 verbatim**, via the Galois-dimension argument `dim⟨g⟩-closure = corank(Λ)` (the same engine
  as §59 / [[G1-difference-holder]]). **G3 is essentially DONE** in the difference category. The sharp
  invariant is `corank(Λ)`, not support cardinality. *(Caveat §61.3: difference-category.)*
- Arithmetic `Λ=0` ⟹ corank `∞` ⟹ difference-hypertranscendental — i.e. §60 *feeds* G1.
- #101 §60: was a leading C5 candidate. **Door-2 re-test (2026-06-19): BRIDGE** — (⟹) is §59's argument
  (single shift + Kronecker–Weyl on `𝕋^∞` + unique factorization); (⟸) is §49.2 + Lipshitz 1988
  (import); and `corank(Λ)` is a renamed torus-closure dimension, so it **also fails Door-3.** See
  [[door-C5-irreducibility-and-door-2-retest]].
- #101 §43.2 (P3 solved): closed subgroups ↔ relation sublattices, `dim = corank`, arithmetic = the
  `Λ=0` full-torus vertex. (the pro-torus inverse problem)

### The free/hard table (#67 Brick #3)
- The free/hard split *is* the corank dichotomy in action: the flow (corank-trivial part) is FREE; the
  zeros (corank-`∞` part) are HARD. The "holonomic ⟺ flat" face = the multiplicative wing being the
  *solved/flat* half.

### The DMR refinement — solvability, not abelianness (#87 §10)
- **§10 DMR-solvable (PROVED HERE, self-correction #5):** the Lyapunov line is
  **SOLVABILITY/REDUCIBILITY, not abelianness** — `G_M` solvable ⟺ cocycle reducible (Lie–Kolchin) ⟺
  `L=0`; non-solvable ⟺ irreducible ⟺ `L>0`. The Borel extension (non-abelian solvable) has `L=0`,
  **correcting #68 §11's "abelian ⟺ integrable."** *Refines G3: the right invariant on the dynamics
  side is solvability.* (→ [[bucket-time-and-non-holonomic-time]] for the cocycle/dynamics reading)

### The completed-connection / two-Galois-class gap (#91 §3)
- §3 the Galois-class gap: q-difference Galois (prime lanes) vs shift/difference Galois (∞-lane, Γ,
  van der Put–Singer) are genuinely **different categories**; the seam = a single Tannakian category
  holding both, welded by the FE = `G_L`. The diagonal picture (shift = weighted prime flow) is the
  guide; the Γ-weight is a **connection term**, not a separate module. (→ [[G4-multi-q-picard-vessiot-and-langlands-group]], [[G5-unitarity-gatekeeper]] §4)

---

## Status ledger for this bucket

| Piece | Tier / grade | Source |
|---|---|---|
| holonomic ⟺ `corank(Λ)<∞` (difference cat.) | **`[PROVED HERE]`** | #68 §60.2 |
| pro-torus inverse problem `dim=corank` (P3) | **`[PROVED HERE]`** | #68 §43.2 |
| solvability (not abelianness) = `L=0` (DMR) | **`[PROVED HERE]`** (self-correction #5) | #87 §10 |
| §60 Door-2 grade (re-tested 2026-06-19) | **BRIDGE** (also fails Door-3); not C5 | — |
| the completed (primes+∞) connection / `G_L` | conjecture / Tier C | #91 §3 |

## Open core / the work package
1. **Door-2 re-test of §60 — DONE: BRIDGE** (also fails Door-3). See
   [[door-C5-irreducibility-and-door-2-retest]]. C5 remains open.
2. **Build the single Tannakian category** holding both Galois classes (prime-lane q-difference +
   ∞-lane shift/Γ), welded by the FE — this is `G_L` itself and overlaps
   [[G4-multi-q-picard-vessiot-and-langlands-group]].

## Cross-references
- [[G1-difference-holder]] — §59 is G3's structural twin (same Galois-dimension argument).
- [[door-C5-irreducibility-and-door-2-retest]] — the NATIVE-grade verdict.
- [[bucket-time-and-non-holonomic-time]] — the holonomy/integrability dichotomy *is* the boundary
  cocycle's reducibility (Avila/DMR).
