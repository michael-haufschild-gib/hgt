# HB generic mixed-Casimir source landing

- **ID:** HB-C-A.9x-f
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB surviving corrected scalar-normalization branch
- **Statement:** On every packed strict repeated-leg unfolding chamber point
  `1 < Re P`, `2 Re P < Re Q`, the literal nonconstant Whittaker source equals
  `Λ(2P+Q-1) Λ(Q)^2 Λ(Q-2P+1)`; its forced rank-three mixed-Casimir dressing equals
  the canonical entire four-Xi scalar vertex and closes the balanced C-A.9u landing.

## Goal and discharged chain

This removes fixed-point-only calibration from the HB scalar-normalization burden:

`literal generic Whittaker/Bessel/Ramanujan source`
`→ rank-three mixed-Casimir pole fill`
`→ canonical entire scalar family`
`→ C-A.9u balanced source`
`→ negative BM → left QNM → HC94 clock/source cocycle → RH`.

It discharges the first four links for every strict-chamber parameter.  Later BM/QNM/HC94/cocycle
construction remains open.

## Gates

- [x] 0 → 1 in-progress: source-pure chamber statement, exact proof chain, hostile audit
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and independent novelty review

## Theorem and proof

For packed `P,Q`, define

```text
u=P-1/2,  a=1-2P,  w=Q-2P+1,
A=2P+Q-1, C=2P-Q=1-w.
```

The literal source is

```text
S(P,Q)=8 Λ(2Q)(2π)^(-Q)
       · ∫₀∞ x^(Q-1)K_u(x)^2 dx
       · L(σ_aσ_a,w).
```

Ramanujan gives

```text
L(σ_aσ_a,w)=ζ(w)ζ(Q)^2ζ(A)/ζ(2Q).
```

Two-K Mellin gives

```text
∫₀∞ x^(Q-1)K_u(x)^2 dx
=2^(Q-3)/Γ(Q) · Γ(A/2)Γ(Q/2)^2Γ(w/2).
```

Exact complex-cpow cancellation then yields

```text
S(P,Q)=Λ(A)Λ(Q)^2Λ(w).
```

The fourth canonical channel is `C`, but entire Xi reflection sends it to `w=1-C`; moreover
`c(C)=c(w)` for `c(s)=s(s-1)/2`.  Therefore

```text
V_Xi(P,Q)=c(A)c(Q)^2c(C)·S(P,Q)=K(P,Q)·S(P,Q).
```

All convergence and nonvanishing conditions follow from packed chamber fields.  No hypothesis or
analytic-continuation axiom is introduced.

## Hostile audit and novelty

- Wrong Whittaker exponent, omitted `ζ(2Q)`, two-K chamber failure, complex-cpow branch failure,
  raw `Λ(C)` evaluation, and centered-channel mismatch were each checked and excluded.
- Zagier already proved the regularized triple-Eisenstein four-completed-zeta formula.  That
  identity is `[LITERATURE]`, not new.
- New survivor is narrower: corpus's literal Whittaker/Bessel/Dirichlet source is welded to the
  exact rank-three mixed-Casimir pole-fill normalization over the complete strict chamber.  Search
  found no such source-side theorem in corpus or literature as of 2026-08-30.
- Key structural insight: source argument is `w=1-C`; functional equation belongs inside pole
  filling, not as permission to evaluate raw completed Lambda at a negative trivial-zero channel.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinGenericMixedCasimirSourceLanding`
- Main theorems:
  - `D4BMStrictTripleUnfoldingParameters.actualUnfoldedScalarSource_eq_positiveLambdaProduct`
  - `D4BMStrictTripleUnfoldingParameters.canonicalScalarVertex_eq_mixedCasimir_mul_positiveLambdaProduct`
  - `D4BMStrictTripleUnfoldingParameters.mixedCasimir_mul_actualUnfoldedScalarSource_eq_canonical`
  - `D4BMStrictTripleUnfoldingParameters.mixedCasimirCorrectedActualUnfoldedSource_balanced_eq_canonical`
- Specialization theorem:
  `D4BMStrictTripleUnfoldingParameters.actualUnfoldedScalarSource_twoFive_eq`
- Direct `lake env lean` check: PASS.
- Targeted `lake build` of module: PASS.
- `#print axioms` for all four main theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import: `GaloisForLFunctions/RHTower.lean`.
- Global lint remains red only for unrelated concurrently unwired modules; this module is wired and
  contains no forbidden declaration.

## Log

- 2026-08-30 — created in stage 1 after corpus/literature audit; frontier map left read-only.
- 2026-08-30 — paper proof closed after hostile loop; Lean proof and full-chamber balanced landing
  audited; promoted to stage 3.
