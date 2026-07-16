# A commutator kernel must annihilate the terminal horizon symbol

- **ID:** `horizon-kernel-spencer-prolongation`
- **Stage:** 3-formalized
- **Type:** THEOREM / PRINCIPAL SYMBOL / SPENCER PROLONGATION / LIE KERNEL
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [NOVELTY PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.HorizonKernelSpencerProlongation`

## The theorem

Let `delta_i` be finitely many derivations of a field `L/K`.  Suppose one boundary state has
terminal principal symbol

```text
delta_i z = sum_j a_(i,j) y_j.                                       (1)
```

Let `q=(q_(i,k))` be any matrix of coefficients satisfying the derivation relation

```text
sum_(i,k) q_(i,k) [delta_i,delta_k] = 0.                              (2)
```

Then applying `(2)` to `z` forces the first Spencer identity

```text
sum_(i,k) q_(i,k)
  (sum_j a_(k,j) delta_i y_j - sum_j a_(i,j) delta_k y_j) = 0.        (3)
```

If the first descendant packet `{delta_i y_j}` is linearly independent, every coefficient in
`(3)` vanishes.  If in addition `q` is skew and `K` has characteristic zero, this becomes the
matrix equation

```text
q a = 0.                                                             (4)
```

## Meaning

The projective line-contact theorem constrains which decomposable bivectors may lie in the
commutator kernel.  Equation `(4)` is the next compatibility layer: a kernel relation must also be
a syzygy of the terminal principal symbol.  The exterior kernel and the horizon equation cannot
be specified independently.

For a free Fock-like first descendant layer, `(4)` is unavoidable.  Therefore any proposed
minimal-rank realization whose symbol is not annihilated by its kernel must introduce correlated
descendants.  Ward identities, gauge relations, equations of motion, or a non-free prolongation
module are not optional physical decoration; they are the exact algebraic data missing from the
free construction.

## Novelty and parent gate

Cross-derivative and Spencer compatibility are classical, and the theorem is not claimed as a new
origin for formal integrability.  The fully commuting special case was already formalized in the
project as the free-tail obstruction.  The new theorem handles an arbitrary linear relation in
the commutator image and extracts its explicit matrix action on the terminal symbol.

Exact searches found no external source coupling this partial commutator-kernel equation to a
varying-direction complete hypertranscendence horizon or to the minimal commutator-rank invariant.
This is an absence-of-hit result, not a priority certificate.  The first-prolongation law is
infrastructure; the significant open theorem is whether its full higher prolongation tower is
sufficient for sharp realization.

Relevant parent theories include Spencer cohomology, Janet--Riquier completion, differential
fields with several commuting derivations, and module rank/support varieties.

## QFT reading

`[CONJECTURE -- PHYSICAL IDENTIFICATION]` A pretemporal QFT realization supplies the correlated
descendant module through Ward identities or gauge constraints.  The horizon fixes admissible
commutator kernels at projective degree two, while `(3)--(4)` are the first consistency equations
on the descendant sector.  No specific QFT is shown to realize these data.

## RH impact

The theorem is a new source filter, not an RH proof.  An arithmetic model that lowers commutator
rank by imposing relations among its law derivations must exhibit terminal symbol columns and
descendant syzygies satisfying `(3)--(4)`.  The current completed-`L` constructions do not supply
such a module.

## Lean verification

Lean proves the general obstruction identity, its expansion as a free-tail linear combination,
coefficientwise vanishing under linear independence, and the skew characteristic-zero equation
`q a=0`.  The module direct-checks, its narrow build target passes, formal lint passes, and axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
