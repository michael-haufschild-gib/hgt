# Scalar prime-factor relabelling supplies no new zero relation

- **ID:** RH-PRSA-20260906
- **Stage:** 5-failed
- **Status:** scalar candidate rejected; classical positive identities closed in Lean
- **Proposed RH chain:** a zeta zero forces a new relation among prime-factor relabelling
  defects; actual integer cutoff geometry contradicts that relation off the critical line; RH.
  The scalar comparison below is identically zero without a zero input, so it does not supply
  the first new relation. No qualifying successor or RH implication was established.

For a permutation `pi` of the actual primes, extend unique factorization to the positive-integer
bijection `E_pi(product p^a_p)=product pi(p)^a_p`. Its scalar candidate is the difference between
`sum E_pi(n)^(-s)` and `sum n^(-s)`. Finite prefixes retain the actual integer cutoff, so this
does not assume that relabelling preserves numerical size.

## First test: exact scalar collapse

Unique factorization gives `E_pi` by mapping the prime multiset and taking its product. Mapping
by `pi^(-1)` is its inverse, and multiset union proves complete multiplicativity. In particular,
it sends each actual prime `p` to `pi(p)`; this is an integer-valued construction, not an
assigned parameter model.

For `Re(s)>1`, absolute reindexing proves

```
sum_(n>=1) E_pi(n)^(-s) = sum_(n>=1) n^(-s) = zeta(s).
```

Thus comparing any two such scalar functions gives zero at every point of that half-plane.
Continuing this same scalar analytic identity cannot create a new zero-specific relation:
uniqueness retains the same zeta germ and the zero difference. The Lean leaf states the exact
ordinary, norm-summable half-plane identity; its total `tsum` definition outside that region
must not be read as an asserted continuation or a conditionally convergent series.

## Second pass: retain the actual cutoff

For a finite set `F` of positive integers and any complex observation `f`, define

```
D(e,F,f) = sum_(n in F) f(e(n)) - sum_(n in F) f(n).
```

Finite reindexing and cancellation give the exact positive survivor:

```
D(e,F,f) = sum_(n in e(F) minus F) f(n)
           - sum_(n in F minus e(F)) f(n),

D(e o d,F,f) = D(e,d(F),f) + D(d,F,f).
```

For the first identity, use the bijection from `F` onto `e(F)` and cancel the common
intersection. For the second, add and subtract the sum on `d(F)`; the remaining image is
`e(d(F))`. Both are proved for every permutation of the positive integers, so apply in
particular to prime-factor relabellings. They retain the entering and exiting integers and
the transported cutoff exactly. Neither requires or implies a zeta zero.

This second pass does not prove that the finite boundary vanishes, has a chosen sign, or obeys
any new law at a zeta zero. It does not rule out every construction using permutations or
nonlinear observations of the finite boundary. Such a construction would need a specified
new arithmetic relation and its proof; it is not an established survivor here.

## Corpus and literature audit

The current corpus provided `PNat.factorMultisetEquiv` and `PrimeMultiset.prod` in mathlib;
`PrimeOccupationCompletionProduct.occupationEquivPNat` identifies the same integer source.
The scalar argument is classical absolute reindexing, explicitly described in
[Keith Conrad's zeta-series handout, Convergence Theorem 3](https://kconrad.math.uconn.edu/promys2000/tech2.pdf).
The ordinary zeta series and Euler product are recorded by [DLMF §25.2](https://dlmf.nist.gov/25.2).
The finite boundary and composition identities are finite-sum cancellation, not new mathematics.
Searches for multiplicative bijections and prime permutations found no exact packaged RH
architecture; those misses establish no absence or novelty claim.

The preceding discovery pass used 30 corpus searches, with current AND/phrase semantics, and
`rg` on the exact sources. [Query scope](../1-in-progress/rh-corpus-architecture-audit-2026-09-06-prime-permutation-searches.tsv)
records caps and exclusions. This is not an exhaustive reading of the Lean corpus.

Other concrete sources checked before selecting the relabelling test:

| Source read | What its statement actually supplies | Missing arithmetic relation |
|---|---|---|
| `ArithmeticSecondOrderObstruction` in full; `ArithmeticInteractionScaleLaw` through the all-pair return theorem | Exact rigidity of a specified Leibniz deformation with a controlled second-order lift; bounded returns classify zero interaction. | No literal zero-derived lift or return bound; already recorded in `STATUS.md` F20b–F20c. |
| `AllScaleIntegralConformalTraceRigidity` through the integral-curvature setup | Explicit paired powers and an assumption that their trace is integral at every integer scale. | No construction forcing that integrality from a zeta zero. Its reflected model was not adopted. |
| `PrimeSparseCoherenceSaturation` in full | Arbitrary finite Boolean families embed in an arbitrarily small weighted prime neighborhood while remaining differentially independent. | This selects sparse prime coordinates for prescribed data; it imposes no relation on the literal all-one sequence. |
| `SubdirectConstraintWitnesses` in full; `PrimeConstraintJoining` definitions and final dichotomy | A chosen enumeration of prime slots realizes prescribed countable correlations. | Relabelling a countable set supplies no constraint from the numerical prime values. |
| `PrimeWordSupportSelector` in full; `PrimeWordSynchronizedCluster` through support recovery | A scalar support selector kills mixed words; the cluster example explicitly uses a published aligned-spin partition block. | No source factorization into those blocks; the partition-function route was not adopted. |

## Lean scope and validation

[PrimeRelabellingScalarAudit.lean](../../../../formal/GaloisForLFunctions/RHTower/PrimeRelabellingScalarAudit.lean)
contains the actual prime-factor bijection, its multiplication and prime-value laws, norm
summability and equality to zeta on `Re(s)>1`, the exact finite boundary and transported
composition law, and the premise-free `scalar_comparison_closed` capstone. This is a closed
classical audit, not an RH proof.

Scratch and direct production checks passed with `lake env lean <file>`. The final serialized
leaf audit passed with
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.PrimeRelabellingScalarAudit`;
only this leaf was rebuilt against cached dependencies. All eight public theorems passed an
imported scratch axiom audit, reporting only `propext`, `Classical.choice`, and `Quot.sound`.
Repository formal lint passed with large-file warnings. The module is wired into `RHTower.lean`;
no full or umbrella build ran. No admitted proof, added axiom, or computational certificate is used.

**NO POSITIVE SALVAGE FOUND as a new RH producer.** The strongest exact positive survivors
above are formalized but classical. The full goal remains active, with the new zero-forced
relation and the off-line contradiction still missing. No new `STATUS.md` mathematical entry
is warranted by these reindexing identities; its existing constraints remain applicable.

No new mathematical computation is required. No experiment or Runpod job has been started.
