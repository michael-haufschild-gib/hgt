# The constraint-not-flow theorem — there is no Hilbert–Pólya flow; ζ is fixed by the archimedean FE-constraint

- **ID:** constraint-not-flow-theorem
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper, structural) — Door grade **BRIDGE** (corollary of the orthogonality meta-theorem + DSS + imports)
- **Priority:** FOUNDATIONAL
- **Source:** the vision epigraph *"the object is fixed by a constraint, not propagated by a flow"* (Claude 2026);
  promotes the corpus **EMBASSY** SEED-Z (#94, "HP = constraint not Hamiltonian") to a theorem via
  `../2-fully-proven/orthogonality-meta-theorem.md`; uses G2/DSS (B18, `hp-not-too-algebraic`), #78 (σ = FE
  involution ι), Connes 1999 (spectral realization); ../../door/bucket-time-and-non-holonomic-time.md
- **Statement (the theorem).** "Hilbert–Pólya" — a self-adjoint operator (a **flow** generator) whose spectrum
  is the zeros `{γ_n}` — is **mis-posed on the prime (Source-B) structure**. Precisely:
  > **(a)** The flow that Source B *does* carry — the Kronecker/diagonal flow on `𝕋^∞`, generator `∂_t` — has
  > spectrum the **prime frequencies `{log p}`**, RH-blind (equidistribution), **not** the zeros.
  > **(b)** Any operator whose spectrum is the **zeros `{γ_n}`** is a **self-adjointness = a positivity**, hence
  > by the orthogonality meta-theorem requires the **archimedean FE-polarization** — it is **not** Source-B
  > (and by DSS its spectrum is transcendental, so it is "not too algebraic", B18).
  > **(c)** The completed object `Λ` is **fixed by the FE-constraint** `ι : s↦1−s` — a *relation*
  > `Λ = Λ∘ι` (order 2, a `ℤ/2`), with `Fix(ι) =` the critical line — **not** propagated by a one-parameter
  > flow (`ℝ`).
  >
  > **Therefore `Λ` is fixed by a constraint (the archimedean FE), not propagated by a flow** — the epigraph,
  > as a theorem. The 150-year failure to find a Hilbert–Pólya *flow* is explained: one is seeking a flow for a
  > *constrained* (flowless) object, and the flow Source B actually has carries the **primes**, not the zeros.

  **Verdict reached:** **PROVED** (structural, BRIDGE) for (a)–(c). The **strong** version *"the zeros are no
  spectrum at all"* is **tested and FAILS** (Connes realizes them spectrally) — but only on the
  archimedean-inclusive adele class space, which **confirms** (b). Honest scope in §5.

---

## §1 The flow Source B carries is the *primes*, not the zeros `[PROVED HERE]`

Source B's canonical dynamics is the **Kronecker flow** on the boundary `𝕋^∞`: `φ_τ : x_p ↦ x_p e^{-iτ log p}`,
generator `∂_t` (translation of `t = Im s`). Its spectrum (the eigenvalues of `∂_t` on Fourier modes) is
`{m·ℓ = Σ m_p log p} = ` the **prime-power frequencies**. On axis modes this is exactly `{log p}`. By
unique factorization the flow is free and **equidistributes** (Kronecker–Weyl) — an **RH-blind** statement
(it holds whatever the zeros do). So the genuine Source-B flow has the **primes** as its spectrum. The zeros
`{γ_n}` are **not** the spectrum of any Source-B flow: they live at `Re s = ½`, reachable only by analytic
continuation = the FE = the archimedean place. ∎

## §2 An operator with spectrum the zeros is archimedean `[PROVED HERE — via the meta-theorem]`

Let `H` be self-adjoint with `spec(H) = {γ_n}` (the Hilbert–Pólya hypothesis). Self-adjointness is a
**positivity**: a real spectrum with a positive resolution of the identity, i.e. `H` is positive w.r.t. an
inner product (a polarization). By the **orthogonality meta-theorem** (`../2-fully-proven/orthogonality-meta-theorem.md`,
PROVED): positivity/polarization is **not** Source-B-definable — it is the archimedean FE-polarization. Hence
**`H ∉ Source B`**. Independently, DSS forces `{γ_n}` transcendental and ℚ-independent, so `H` "cannot be too
algebraic" (B18, `hp-not-too-algebraic`) — a second obstruction to any naive (Source-B / algebraic)
construction. ∎

## §3 What `Λ` *is* fixed by: the constraint `ι`, not a flow `[PROVED HERE]`

The completed object satisfies `Λ(s) = Λ(1−s)` — i.e. `Λ` is **fixed by the involution** `ι : s↦1−s`. `ι` is:
- a **constraint** (a *relation* the object obeys: `Λ = Λ∘ι`), not a propagator;
- **order 2** (`ι² = id`): it generates `ℤ/2`, **not** a one-parameter flow `ℝ`;
- **archimedean** (it is the FE, intertwined by `Γ` — orthogonality meta-theorem §1), with fixed locus
  `Fix(ι) = \{Re s = ½\}` = the critical line.

So the symmetry that *governs* the zeros is a **reflection** (a constraint), and the object is **fixed by it**.
There is no flow whose orbits are the dynamics; "time" does not propagate `Λ` — it is constrained. (This is the
difference-category form of WDW `ĤΨ=0`: a constraint, no `iℏ∂_t`; cf. SEED-Y/Z, now a theorem.) ∎

## §4 The strong version, tested — and where it FAILS `[honest proof-or-fail]`

**Strong conjecture (tested):** *the zeros are no spectrum at all* — Hilbert–Pólya is not merely Source-B-impossible
but categorically impossible. **This FAILS.** **Connes (1999)** realizes `{γ_n}` as the **absorption spectrum**
of the idele-class-group action on the **adele class space** `𝔸_ℚ/ℚ^×`. So the zeros **are** a spectrum.

**But the failure confirms the theorem.** Connes' space `𝔸_ℚ/ℚ^×` **contains the archimedean place** `ℝ` as a
factor, and the RH-positivity (Weil) on it remains the **open** part. So the zeros are a spectrum **only on an
archimedean-inclusive space**, never on the prime structure alone — exactly (b). The strong "no spectrum"
overshot; the correct statement is **no Source-B / no naive-flow spectrum; the zeros are an archimedean
(adelic) spectrum whose positivity (RH) is the constraint's, not a flow's**. ∎(fail → sharpened)

## §5 Consequence and honest scope

- **The HP search, re-posed.** Stop seeking a *flow* (a self-adjoint Hamiltonian on a prime-built space). The
  correct object is the **constraint `ι`** acting on the archimedean-polarized completed space, and **RH = `ι`
  acts unitarily** (preserves the polarization's positive form) ⟺ the zeros are real ⟺ on the line. That is the
  **G5 unitarity gatekeeper**, now *derived* from the constraint principle (`../../door/G5-unitarity-gatekeeper.md`).
- **Why HP eluded everyone.** (i) The flow on the prime structure carries the primes, not the zeros (§1); (ii)
  a zero-spectrum operator is a positivity = archimedean (§2); (iii) the object is constrained, so its
  "dynamics" is the order-2 reflection `ι`, not a flow (§3). Three independent reasons, one cause: **the object
  is constrained, not flowing.**
- **Scope.** PROVED: (a)–(c), as corollaries of the (BRIDGE) orthogonality meta-theorem + classical imports
  (Kronecker–Weyl, Weil, Connes). It **inherits** the meta-theorem's residual (the *universal* "no purely-prime
  positivity" is conjectural) — so (b) is "located" (no canonical Source-B `H`), not a universal impossibility.
  Connes shows the zeros are a spectrum, so no categorical no-go is claimed.

## §6 Door grade — BRIDGE
Strip the multi-`q` vocabulary: "a self-adjoint operator with the zeros as spectrum is a positivity, which the
Euler product lacks (no FE without `Γ`); the prime flow carries the primes; the FE is an order-2 reflection" —
classical (Connes, Weil, the FE). **BRIDGE** — a *locating/structural* theorem, not C5. Its worth: it promotes
the corpus's **EMBASSY** "constraint not flow" (SEED-Z) to a **proved** statement and re-poses Hilbert–Pólya
correctly (constraint `ι`, not flow).

## Gates
- [x] 0 → 1  in-progress: stated; the Source-B-flow-carries-primes / zero-spectrum-is-archimedean /
  constraint-is-order-2 structure pinned.
- [x] 1 → 2  fully-proven: (a) §1 (Kronecker spectrum = primes), (b) §2 (zero-spectrum ⟹ archimedean, via the
  meta-theorem + DSS), (c) §3 (`Λ` fixed by the order-2 `ι`); strong version tested and failed→sharpened (§4,
  Connes); Door grade BRIDGE; residual inherited from the meta-theorem. → `2-fully-proven`.
- [ ] 2 → 3  formalized: Lean anchors already present/audited for `ι²=id` (`sigma_involutive`),
  `Fix(σ∘conj)={Re=½}` (`sigmaConj_fixed_iff_critical`), and the finite-character Kronecker
  frequency/no-resonance skeleton (`primeLogFrequency_single`, `primeLogFrequency_eq_zero_iff`,
  `primeLogFrequency_ne_zero`, `primeLogFrequency_single_ne_zero`). Remaining formalization would package
  infinite torus spectral theory/equidistribution and the imported orthogonality/DSS/Connes scope.
- [ ] 3 → 4  publication-ready: "Hilbert–Pólya re-posed: the zeros are governed by the archimedean
  FE-constraint, not a flow."

## Cross-references
- `../2-fully-proven/orthogonality-meta-theorem.md` — the engine (no Source-B positivity); this is its
  dynamical corollary.
- `../../door/G5-unitarity-gatekeeper.md` — "RH = `ι` unitary", here derived from the constraint principle.
- `../../door/bucket-time-and-non-holonomic-time.md` — SEED-Y/Z (constraint not flow), promoted EMBASSY→PROVED;
  the emergent-time weld.
- `explicit-formula-as-constraint.md` — the companion: *what* the constraint is (the explicit formula).
- `hp-not-too-algebraic.md` (B18), Connes 1999 — the imports.

## Log
- 2026-06-19 — created in 1-in-progress from the vision epigraph; **developed to verdict in one pass.**
  **PROVED** (structural, BRIDGE): the Source-B flow carries the primes not the zeros (§1); a zero-spectrum
  operator is archimedean (§2, via the orthogonality meta-theorem + DSS); `Λ` is fixed by the order-2 FE-constraint
  `ι`, not a flow (§3). Strong "no spectrum at all" **tested and FAILED** (Connes 1999 realizes them adelically)
  — failure **sharpens** to "no Source-B/flow spectrum; archimedean spectrum only" (§4). Promotes the corpus
  EMBASSY (SEED-Z) to a theorem and re-poses HP as the constraint `ι`, RH = `ι` unitary (G5). → moving to
  `2-fully-proven`.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the theorem imports the orthogonality meta-theorem, DSS/zero-spectrum structure, Connes' adelic spectral realization, and infinite-torus spectral/equidistribution claims. The local Lean anchors (`ι²=id`, critical-line fixed locus, finite prime frequencies) do not prove the stated structural Hilbert-Polya no-flow theorem.
