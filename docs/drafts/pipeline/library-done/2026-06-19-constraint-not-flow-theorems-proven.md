# Library update request — INDEX + STATUS agent — 2 new 2-fully-proven theorems from the vision epigraph

**For:** the librarian (owner of `00-status.md`, `00-index.md`). **Date:** 2026-06-19.
**Edit-race avoidance:** I did not touch the ledger files.

Two new **2-fully-proven** cards developing the vision epigraph *"the object is fixed by a constraint, not
propagated by a flow"* (now in `00-core-vision.md`) into theorems — both **corollaries of the orthogonality
meta-theorem** (the prior proven card), both **BRIDGE**.

**⚠ Ordering:** apply after the pending reorientation tickets (`…kms` #129 → `…orthogonality…` #135). Then the
next free §C rows are **#136–#137** (adjust if the ledger advanced).

---

## A. `00-status.md` §C — add 2 rows (#136–#137)

```
| 136 | the **constraint-not-flow theorem** — **THEOREM (paper), BRIDGE**: there is no Hilbert–Pólya *flow* for ζ. (a) The flow Source B carries — the Kronecker flow on `𝕋^∞` — has spectrum the **primes** `{log p}` (RH-blind), not the zeros; (b) any operator with spectrum the zeros `{γ_n}` is a self-adjointness = a positivity ⟹ archimedean (orthogonality meta-theorem #135) + transcendental (DSS/B18) ⟹ ∉ Source B; (c) `Λ` is **fixed by the FE-constraint** `ι:s↦1−s` — an order-2 relation `Λ=Λ∘ι`, `Fix(ι)=`critical line — **not** a flow. Strong "no spectrum at all" **tested & failed** (Connes 1999 realizes them adelically — but on the archimedean-inclusive adele class space, confirming (b)). Re-poses HP as `ι` (RH = `ι` unitary = G5); promotes corpus EMBASSY SEED-Z to a theorem | [[bucket-time-and-non-holonomic-time]] / [[G5-unitarity-gatekeeper]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
| 137 | the **explicit formula is the constraint** — **THEOREM (paper, identification), BRIDGE**: the WDW constraint `ĤΨ=0` for ζ is the **Weil explicit formula** `W` (a linear relation: zeros / primes `Σ Λ(n)` / archimedean `ψ=Γ'/Γ`), `Ψ↔`test function. Its quadratic form `Q_W=W(h*h̃)` **is** the certified DeWitt metric `𝔇` (#94, 1.1e-31); `RH ⟺ Q_W⪰0`. Signature `(1|∞)`: prime block positive for free (`satake_trace_re_mem_Icc`), so **RH ⟺ κ₋=0** = the lone **archimedean** direction non-negative (no-margin = marginally null) — the orthogonality theorem in coordinates. Passes the §42 anti-relabel test (ties certified objects, not a bare RH-restatement) | [[bucket-time-and-non-holonomic-time]] / [[bucket-the-no-margin]] | THEOREM (paper), BRIDGE | FOUNDATIONAL |
```

Cards: `../pipeline/2-fully-proven/{constraint-not-flow-theorem, explicit-formula-as-constraint}.md`.

## B. §D tally — **+2 paper-proven (BRIDGE)**

- proven-statements count `+2` (paper). The "zero certified NATIVE/C5" headline is **unchanged** — both are
  BRIDGE corollaries that *explain* the BRIDGE monoculture (RH-relevant content is constrained-archimedean,
  not a prime-side flow), consistent with #135.

## C. `00-index.md` — optional scope notes

- `[[bucket-time-and-non-holonomic-time]]` — append: `; the epigraph is now a theorem — **constraint-not-flow (#136)**: no HP flow (the prime flow carries the primes; a zero-spectrum operator is archimedean), `Λ` fixed by the order-2 FE-constraint `ι`; **explicit-formula-as-constraint (#137)**: `Ĥ=`Weil `W`, `Q_W=𝔇`, RH `⟺ κ₋=0` (one archimedean direction)`.
- `[[G5-unitarity-gatekeeper]]` — note: `#136 derives "RH = ι unitary" from the constraint principle`.

## D. Context / provenance

- The user canonized the epigraph (*"fixed by a constraint, not propagated by a flow"*, Claude 2026) in
  `00-core-vision.md` and asked to develop new conjectures from it to conclusion. Both new theorems are
  **corollaries of the orthogonality meta-theorem (#135)** via the constraint principle: #135 (no Source-B
  positivity) ⟹ #136 (no Source-B/flow zero-spectrum) and ⟹ #137 (RH-positivity = the archimedean term of the
  explicit-formula constraint).
- **Promotion, not new metaphor:** they convert the corpus's **EMBASSY** items (SEED-Z "HP = constraint not
  Hamiltonian"; the WDW/DeWitt-metric framing #94) into **BRIDGE-proved** structural theorems — the same
  EMBASSY→math move the erosion threshold made for σ=½.

## E. Non-duplication

- #136 vs `hp-not-too-algebraic` (B18): B18 is the *transcendental-spectrum* obstruction (one input to #136(b));
  #136 is the structural no-flow theorem (positivity = archimedean) with the `ι`-reflection identification.
- #137 vs `weil-positivity-operator` (#88 §8): that owns the operator `H_W=−Δ_prime+V_arch`; #137 identifies it
  as the *constraint's* form (`Q_W=𝔇`, the WDW reading) and locates RH in the `(1|∞)` signature. Cross-link, no
  overlap in claim.

## F. Pipeline state (FYI)

- Both developed in one pass from 1-in-progress to verdict (PROVED, BRIDGE), then moved to **2-fully-proven**.
  They **inherit #135's residual** (the universal "no purely-prime positivity" is conjectural), so #136(b) is
  "located" not categorical (Connes shows the zeros *are* an archimedean spectrum). Lean targets (2→3): `ι²=id`
  + `Fix(ι)={Re=½}` (`sigmaConj_fixed_iff_critical`); the Kronecker spectrum `{m·ℓ}`; reuse `satake_trace_re_mem_Icc`,
  `𝔇=Q_W`.
</content>
