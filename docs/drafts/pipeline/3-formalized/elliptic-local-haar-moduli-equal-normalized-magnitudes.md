# Elliptic local Haar moduli equal normalized magnitudes

- **Stage:** 3-formalized
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** At every actual finite completion and at infinity, the additive
  Haar character of each unit equals its previously defined normalized magnitude.

## Proof

A uniformizer has Haar character equal to inverse residue cardinality.
Valuation-one units preserve the integral ball, whose normalized mass is one.
Write an arbitrary unit as a valuation-one unit times an integer power of a
uniformizer. The valuation and Haar character then give the same residue power.

The actual finite valuations contain `exp(-1)` by the proved place uniformizer;
the infinity parameter supplies the same value. Completed residue fields are
already identified with the actual prime residue rings and with `F₃` at infinity.
These discharge normalization rather than assume it.

The [general uniformizer decomposition](../3-formalized/discrete-local-haar-modulus-is-residue-normalized-valuation.md)
gives modulus `Q^m` when valuation is `exp(m)`. At a finite place the dense
field embedding preserves the actual place uniformizer valuation. At infinity,
the embedded parameter `x/y` has valuation `exp(-1)`. The completed residue
equivalences give exactly the cardinalities defining `finiteCompletionMagnitude`
and `infinityCompletionMagnitude`. Substitution proves both identities.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticLocalHaarMagnitude.lean`:
`finiteCompletion_distribHaarChar`, `infinityCompletion_distribHaarChar`.
Direct Lean audit passed. Both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
