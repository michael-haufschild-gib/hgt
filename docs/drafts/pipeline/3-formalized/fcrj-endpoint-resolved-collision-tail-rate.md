# FCRJ endpoint phase-resolution collision tail rate

- **ID:** FCRJ-RCTR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-formalized)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 61
- **Statement:** Replace singular inverse-chord collision cost by exact frequency-resolution
  saturation at chord scale `1/N`.

## Goal

For distinct unit modes `z_i`, coefficients `c_i`,

```text
U_n = sum_i c_i z_i^n,
J   = sum_i |c_i|^2,
R_N = sum_(i!=j) |c_i||c_j|
        min(1, 2N/(|1-conj(z_i)z_j|(N+1)^2)),
```

prove for every `N>=1`

```text
|N sum_(n>N)|U_n|^2/n^2-J| <= J/(N+1)+R_N.           (RCR1)
```

Specialize to physical prime-log endpoint jumps and multiply by exact aperture factor
`A^2/(4 pi^2)` for raw FCRJ amplitudes.

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. `norm_tsum_unitPhase_invSqTail_le` gives oscillatory cost
   `2/(|1-w|(N+1)^2)`.
2. `tsum_shift_rpow_le` also gives nonoscillatory absolute tail `1/N` for `N>=1`.
3. `norm_natCast_mul_finiteExponentialPencilInvSqTail_sub_energy_le` sums only first bound and
   therefore becomes arbitrarily large at unresolved chords.
4. Corpus has prime-log separation and endpoint-mesh laws, but no frequency-saturated finite
   Wiener collision budget and no physical FCRJ specialization.

## External frontier `[LITERATURE]`

Quantitative and subsequential Wiener lemmas are classical; Cuny--Eisner--Farkas,
*Wiener's lemma along primes and other subsequences*, arXiv:1701.00101, and Schulte,
*On Wiener's lemma for locally compact abelian groups*, arXiv:2005.05212, are parent references.
Targeted search found no inverse-square atomic-tail theorem with pairwise resolution kernel
`min(1,const/(N|1-w|))`, and no clipped physical prime-log specialization.  Novelty claim is
restricted to exact phase-resolution budget and its source interpretation.

## Conjecture loop A — raw inverse-chord cost

`[FAILED AS FRONTIER INVARIANT]` The loop-60 budget is correct but singular at near collisions,
even though the actual scaled pair kernel stays bounded.  It confuses unresolved pairs with large
error and cannot exploit small total mass inside a collision cluster.

## Conjecture loop B — saturated phase-resolution kernel

`[CONJECTURE] [FROZEN 2026-08-27]` `(RCR1)` holds with `R_N` above.

### Paper proof plan

For `|w|=1`, the absolute tail and loop-60 Abel bound give

```text
|sum_(n>N) w^n/n^2|
 <= min(1/N, 2/(|1-w|(N+1)^2)).                       (RCR2)
```

After multiplying by `N`, the ordered `(i,j)` off-diagonal contribution is at most

```text
|c_i||c_j| min(1, 2N/(|1-conj(z_i)z_j|(N+1)^2)).
```

The diagonal error remains at most `J/(N+1)`.  Finite expansion and triangle inequality prove
`(RCR1)`; endpoint differentiation supplies physical amplitude factor.

### Hostile audit

- Kernel is bounded by one, so exact and near collisions cannot create artificial blow-up.
- For resolved chords `N|1-w| >> 1`, it recovers loop-60 inverse-chord decay.
- For unresolved chords `N|1-w| << 1`, it charges pair mass, matching scalar kernel scale.
- Singleton packets have zero off-diagonal budget.
- Bound remains absolute and may miss cancellation among three or more near-colliding signed
  nodes; this is next possible sharpening, not a defect in statement.
- No arithmetic smallness is asserted.  New moving-packet core is weighted unresolved-pair mass
  plus resolved inverse-chord mass, rather than divergent minimum separation.

Verdict: `PROVED ON PAPER`.  Generic minimum of two classical scalar estimates is
infrastructure; source-specific physical resolution budget and revised route obstruction are
candidate-new.

## Open core

Lean formalization is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointPhaseCollisionTailRate.lean`.
Direct checking, targeted module build, `#print axioms` audits, and global formal lint pass;
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Next audit: whether physical signed endpoint clusters admit a source-derived cancellation
invariant beyond absolute resolved pair mass.
