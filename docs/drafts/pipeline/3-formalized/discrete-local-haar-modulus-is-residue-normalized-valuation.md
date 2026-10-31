# Discrete local Haar modulus is residue-normalized valuation

- **Stage:** 3-formalized
- **Parent:** [Actual elliptic moduli](elliptic-local-haar-moduli-equal-normalized-magnitudes.md).
- **Statement:** For a nontrivially integer-valued field with compact integer
  ring and `exp(-1)` in its valuation range, additive Haar modulus of every
  unit equals its residue-normalized valuation.

## Proof

Let `Q` be residue cardinality. Choose an irreducible element `π` of the
discrete valuation ring. It generates the maximal ideal, hence is a
uniformizer. Since `exp(-1)` occurs, its valuation is exactly `exp(-1)`.
The audited residue-index formula gives Haar modulus `Q^(-1)` for `π`.

For a field unit `u`, write `v(u)=exp(m)` and set `b=uπ^m`. Then `v(b)=1`.
Both multiplication by `b` and its inverse preserve the integer ball. That
ball has normalized Haar mass one, so the Haar modulus of `b` is one.
The decomposition `u=bπ^(-m)` now gives modulus `Q^m`, exactly the
residue-normalized valuation of `u`.

The valuation-range condition fixes the integer scale. It is discharged by
actual uniformizers in the elliptic specialization.

## Lean

`HTGeometry/LoopEisenstein/DiscreteHaarMagnitude.lean`:
`distribHaarChar_eq_residueMagnitude`. Direct Lean and transitive axiom audits passed; dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
