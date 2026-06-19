# The realization problem — is "Euler product ⟺ two-faces" an IFF? (#7)

- **ID:** realization-problem
- **Stage:** 0-backlog
- **Type:** CONJECTURE (native)
- **Priority:** FIELDS MEDAL
- **Source:** ../../door/bucket-realization-and-fake-family.md (#85 SEED-V, #75, #84, #98) · 00-status rows #84, #86
- **Statement:** Is the organizing law **`Euler product ⟺ two-faces (positivity ∧ genericity ∧ FE)`** an
  **IFF**? The field's **First Theorem** gives the forward direction (Euler product ⟹ the two-faces
  structure, `EulerProduct.lean`). The **converse** (SEED-V / B26): does `(Face-A positivity ∧ Face-B
  genericity ∧ FE) ⟹ Euler-realized`? Equivalently `∃ source-built g with g ⋆ g* = Ω_∞ − prime-comb`;
  equivalently (#98) does the prime-deformed LP family's limit **identify** with ξ. Includes **G17
  (overdetermination = genuineness, #84):** RH-bearing objects = the zero-side = prime-side
  **overdetermined locus** ∩ (E) ∧ (A), with the explicit formula as its equation system.

## Goal
The **converse of the field's only theorem** and the A1/A2 unification stated as **existence-of-`g`**.
The governing lesson of the bucket: **genuineness is the Euler cut (A), not the positivity cut (P)** —
the three cuts (E) realizability / (A) arithmeticity / (P) positivity are **independent**, and the fakes
(Davenport–Heilbronn) live in `(E) ∧ ¬(A)` with Hankel-positivity yet no Euler product. So every
"RH ⟺ positive/unitary" criterion (G5, no-margin) **must be conjoined with (A)** or it passes a fake.
The realization problem asks whether positivity + genericity + FE is enough to *force* (A).

## Door passport
- **Door-1:** built on the native First Theorem (Euler ⟺ Bohr-lift factorization) and the source-pure
  carrier; the converse is an existence statement about a source-built `g`.
- **Door-2:** the finite Spectral-Torelli / symmetric-function half is likely IMPORT; the **infinite
  resolvent/Hadamard passage** (does the LP-limit land on ξ) is the native Tier-B content.
- **Fake filter:** any candidate `g` must **reject** Davenport–Heilbronn / Epstein (the discipline).

## Gates
- [ ] 0 → 1  in-progress: the IFF stated; the three cuts (E)/(A)/(P) and G17 overdetermination pinned;
  the LP-limit identification route scoped; the fake-rejection requirement written
- [ ] 1 → 2  fully-proven: the converse decided (IFF proved, or a counterexample / obstruction located)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Two routes, cross-checking: (i) **LP-limit identification** (#98) — RH ⟺ ξ ∈ LP ⟺ ξ is an LP-limit;
positivity is automatic along the prime-deformed LP family (each step a Pólya–Schur multiplier `e^{x/p}`,
`MultiplierScaling`/`sigmaScale_splits`), so the content is that the *arithmetic* limit identifies with
ξ — a **closedness/identification** problem, not a positivity one. (ii) **Overdetermination** (G17) —
characterize the locus where the zero-side `Σ_ρ ρ^{−m}` and prime-side (`−ξ'/ξ`) computations of each
`s_m` agree for all `m` (image thin, infinite-codimension), intersected with (E) ∧ (A).

## Cross-references
- `a1-a2-unification-brick.md` — realization = "∃ g realizing both faces."
- `weil-positivity-operator.md`, `carrier-herglotz-rh.md` — the positivity criteria that need the (A) cut.
- `compute-omega-h2-gl.md` — `ω=0` / motive-existence is the realization's algebraic shadow.
- `../../door/bucket-realization-and-fake-family.md` — the fake-family filter discipline.

## Log
- 2026-06-19 — created in 0-backlog. The realization problem (grand conjecture #7): the converse of the
  First Theorem and the A1/A2 unification as existence-of-`g`; folds in G17 overdetermination.
