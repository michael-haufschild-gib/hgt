# Deninger v4 literature-to-Lean parity audit

- **ID:** `deninger-v4-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE AUDIT
- **Route:** L — Deninger/Hodge/cohomological realization
- **Primary source:** Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400v4 (7 February 2024).
- **Scope:** exact results in §§6–12 used by Route L's rational-Witt source, topology,
  leafwise degree zero, generalized functions, and divisor support.

## Counting rule

A literature theorem counts as formalized only when Lean contains a closed declaration about the
constructed arithmetic object.  A structure field carrying the cited conclusion, an abstract
implication waiting for arithmetic instantiation, or a paper citation does not count.

## Primary-source theorem inventory

Current v4 contains the following results in the Route-L source range:

- §6: Theorem 6.1.
- §7: Lemmas 7.1–7.3; Propositions 7.4–7.7; Corollaries 7.8–7.9; Theorem 7.10.
- §8: Theorem 8.2; Lemma 8.3.
- §9: Proposition 9.1; Theorems 9.2, 9.3, 9.6, 9.8; Lemma 9.4; Corollary 9.7.
- §10: Theorem 10.2; Proposition 10.3.
- §11: Lemmas 11.1–11.2; Propositions 11.5–11.7.
- §12: Proposition 12.1.

Exact statements and dependencies are being transcribed from v4 source before formalization.

## Confirmed false-positive coverage

### Corollary 7.9 and Theorem 7.10

The Stage-3 card `deninger-prime-packet-topology-haar-retraction` formalizes the internal
profinite packet, Frobenius quotient, mapping torus, and compact-to-Hausdorff upgrade.  Its own
remaining-work section states that Lean lacks Deninger's external map from the mapping torus into
the rational-Witt packet.  Therefore Corollary 7.9 and Theorem 7.10 are not yet formalized.

### Theorem 10.2

`DeningerRegularH0.lean` computes coinvariants and group homology of a regular representation.
`DeningerArithmeticEndpointPurity.lean` proves consequences of a trivial bottom generator and a
perfect endpoint pairing.  Neither constructs Deninger's leafwise sheaf on the four v4 dynamical
spaces or proves that its degree-zero sections are constants with trivial flow/Galois action.
Therefore Theorem 10.2 is not yet formalized.

### Proposition 11.7

`DeningerGeneralizedDivisorSupport.lean` places the identity
`gdiv u = pr⁻¹(div u)` in the field `DeningerGeneralizedDivisorLaw.pullback_law` and derives prime
support from that field.  The cited proposition is assumed, not proved.  Therefore Proposition
11.7 is not yet formalized.

## Formalization order

1. Build the literal `Spec ℤ` geometric-character/root source and arithmetic projection used by
   the rational-Witt specialization.
2. Prove Proposition 11.7 from residue-field evaluation; remove the assumed law from formal
   credit.
3. Build the v4 inductive-limit/Frobenius source packet and its suspension map; prove Corollary
   7.9 and Theorem 7.10 on that source.
4. Build the locally-leaf-constant sheaf/degree-zero section object and prove Theorem 10.2 and
   Proposition 10.3.
5. Close all remaining §§6–12 statements in dependency order, then repeat the parity audit for
   the Route-L-relevant Meyer, Burnol, and Connes primary sources.

## Log

- 2026-08-11 — audited v4 rather than the older arXiv numbering; found 28 Route-L source results.
  Demoted four locally claimed results from formal coverage because existing Lean supplies only
  internal factors, consequences, or an assumed interface.
