# Explicit fifth-order witness for joint Euler deletion

**Stage:** 3-formalized finite identities. **RH implication:** none. **Novelty:** not certified.

In six-by-six complex coefficient arrays, set `X=E_01+E_12` and
`Y=E_23+E_34+E_45`. Lean proves that the actual moduli-two-and-three exponential
block satisfies the exact identity

`B(z)=1-(z^5/60)E_05`.

The proof constructs every power through degree five, proves the sixth power zero for every
linear combination of `X,Y`, and identifies the actual exponential with its finite polynomial.
Symbolic multiplication then proves the block identity. The actual deletion coefficients are
connected to these generators explicitly. Every block with arbitrary within-block weights
absorbs `E_05` on both sides; `E_05^2=0` and its `(0,5)` entry is one.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointNilpotentWitness.lean`.
Namespace: `RHTower.DeletionJointSharpness`.
Audited theorems: `chain_sixth`, `exp_chain`, `frozen_source_exact`, `topWord_entry`,
`variableBlock_absorbs_topWord`.

`lake env lean /tmp/hgt-joint-polygon-17TZsg/WitnessAudit.lean` passed; all five axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`. Production matches
the audited scratch body. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionJointNilpotentWitness` passed.
The umbrella import is wired; no umbrella build ran. No numerical experiment or external
certificate was used. Repository-wide lint will be rerun with the continuing sharpness module.

These finite identities alone do not prove divergence of the original varying-weight product.
The [exact paper proof](../2-fully-proven/euler-deletion-joint-product-one-fifth.md) removes
this coordinate, proves the remaining block errors summable, and derives actual-product
divergence. Formalization of that last argument remains in progress.
