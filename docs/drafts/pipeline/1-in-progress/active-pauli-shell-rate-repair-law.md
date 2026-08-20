# Active Pauli shell rate-repair law

- **ID:** `active-pauli-shell-rate-repair-law`
- **Stage:** 1 -- in progress
- **Type:** no-go / ensemble correction / fixed-rate foundation
- **Parent:** `../2-fully-proven/fixed-shell-angular-dephasing-static-local-plateau-law.md`
- **Status:** `[NO-GO PAPER-PROVED] [POSITIVE REPAIR PAPER-PROVED] [LEAN NEXT] [NOVELTY NOT CLAIMED]`
- **Date:** 2026-08-21

## Exact defect

The current shell law samples a unit vector in the full `4^n`-dimensional Pauli coefficient
space and then sets every coefficient outside the nonidentity weight-at-most-`q` dictionary to
zero.  This does not fix the Hamiltonian interaction rate.  In particular, the identity label is
always inactive.  The unit coefficient vector supported on that label produces the zero
Hamiltonian, whereas a unit coefficient vector supported on any active Pauli label produces one
Pauli word and has squared Hilbert--Schmidt norm `2^n`.

Thus the current fixed-shell measure contains an implicit random active radius.  The claimed
removal of Gaussian radial mixing is invalid on that measure.

## Positive repair

Let

```text
A_(n,q) = {P : Pauli label | P != I and weight(P) <= q}.
```

Sample `J` from the unit sphere in `R^(A_(n,q))` and define

```text
H(J) = sum_(P in A_(n,q)) J_P P.
```

Pauli Hilbert--Schmidt orthogonality gives the exact identity

```text
||H(J)||_HS^2 = 2^n sum_(P in A_(n,q)) J_P^2 = 2^n.
```

This active shell, not the full coefficient shell with zero weights, is the correct fixed-rate
ordinary `q`-local ensemble.  Product Clifford conjugation preserves support and Pauli weight, so
it acts on `A_(n,q)` by a signed permutation and preserves this shell.  The prior Clifford second
moment therefore has a valid route to the corrected ensemble, but it must be restated there before
Theorem C can be used.

## Proof

For the no-go, take the two full coefficient vectors `e_I` and `e_P`, where `P` is active.  Both
have Euclidean norm one.  Since the weight of `I` is zero, `H(e_I)=0`.  Since the weight of `P` is
one, `H(e_P)=P`, and Pauli orthogonality gives `||P||_HS^2=2^n`.

For the repair, expand the Gram square of `H(J)`.  Distinct Pauli words are orthogonal and every
Pauli word has squared Hilbert--Schmidt norm `2^n`; hence all cross terms vanish and the displayed
identity follows.  A product Clifford maps each active word to a sign times another word with the
same support, so the active shell is invariant.

## No-go closure

- **Exact killing mechanism:** inactive coefficient directions carry unit-shell mass while
  producing no Hamiltonian interaction.
- **Strongest positive survivor:** restriction to the active Pauli dictionary fixes interaction
  rate exactly and retains product-Clifford invariance.
- **New insight:** fixed coefficient norm is physical only after quotienting coefficient-kernel
  directions; otherwise angular dephasing secretly uses radial mixing.
- **Status:** paper proof dependency-closed; Lean formalization next.  No external novelty claim.

## Brown frontier

This repair validates a plateau input only.  It proves no initial linear growth, no first return to
the polynomial circuit set, and no complete same-draw Brown--Susskind theorem.
