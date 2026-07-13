# A multivariate lift marker retains the full prime-word support

- **ID:** `prime-support-multivariate-lift-marker`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[POSITIVE SUCCESSOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`
- **Parent no-go:** `binary-lift-parity-prime-support-blindness.md`
- **Consumer:** `../../1-in-progress/prime-source-ramanujan-lift-ihara-limit-rh.md`

## Theorem

For a finite prime word `w`, define its squarefree multivariate marker

```text
B_w(X)=prod_(p in supp(w)) X_p.
```

Lean proves that `B_w` is exactly the monomial whose exponent is the indicator of the distinct
letter support and that this exponent has support precisely `supp(w)`.  Under a specialization
`X_p -> sigma_p`,

```text
B_w(sigma)=prod_(p in supp(w)) sigma_p.
```

This specialization occurs after the support has been retained; it is not the parity character of
the original multiplicity packet.

For the parity-blind pair

```text
w=[0],       w'=[0,1,1],
```

every binary lift character identifies the two multiplicity packets, but Lean proves

```text
B_w != B_w'.
```

Thus the multivariate marker is a faithful finite carrier of the distinct-support datum needed by
the prime-support boundary jets.

## Route consequence

An ordinary signed `2`-lift is too small, but the graph route has a precise positive replacement:

```text
edge-labelled nonbacktracking words
  -> multivariate edge-zeta determinant or trace-monoid series
  -> squarefree support marker B_w
  -> marked normal boundary jets
  -> only then specialize to a lift-character packet
  -> conditional interlacing / Ramanujan bound.
```

The next open theorem is to construct this marked multivariate Ihara object and prove that the
support projection is compatible with its determinant/cycle expansion.  Coefficient cancellation
between different multiplicity vectors having the same support must remain visible; a scalar
Booleanization is not enough.

## Formal certificate

The module proves:

- `primeWordSquarefreeMarker_eq_monomial`;
- `primeWordSquarefreeMarker_exponent_support`;
- `eval_primeWordSquarefreeMarker`;
- `primeWordSquarefreeMarker_separates_parityBlindWords`;
- `multivariateMarker_repairs_binaryLift_support_blindness`.

The exact module builds.  Axiom audit of the capstone reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] canonical squarefree support marker defined
- [x] exact exponent support proved
- [x] specialization law proved
- [x] parity-blind pair separated
- [x] exact Lean build
- [x] accepted-axiom audit

