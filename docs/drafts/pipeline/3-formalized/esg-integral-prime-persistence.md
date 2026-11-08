# Natural integral barcode of prime-product homology

- **ID:** esg-integral-prime-persistence
- **Stage:** 3-formalized
- **Type:** INTEGRAL HOMOLOGY PERSISTENCE

## Exact theorem

For every commutative ring `R`, actual augmented prime-product homology
persistence is naturally the direct sum of intervals `[m,2m)`, indexed by
odd squarefree integers `m`. The summand lies in exterior degree `ω(m)`,
or reduced topological degree `ω(m)−1`. The empty face supplies `[1,2)`.
Every height map retains each coefficient until its interval ends.

The integral comparison commutes with canonical coefficient extension.
The actual map induced by extending integer chains preserves each surviving
basis class. There is a natural linear equivalence

`R ⊗[ℤ] H_k(C(N);ℤ) ≃ H_k(C(N);R)`,

sending `r⊗x` to `r·H(ℤ→R)(x)`. At every odd-squarefree interval label,
the coefficient after extension is the image in `R` of the integer coefficient.
No flatness hypothesis on `R` is required.

## Proof

Increasing prime supports form the exterior-chain basis. The prime-product
cutoff is their coordinate span. In positive degree, forgetting prime two
identifies cycles with odd chains of the same cutoff; its inverse is
`S ↦ d(2∧S)`. Boundaries at height `N` are exactly cycles at `⌊N/2⌋`.
The augmented empty degree has the corresponding boundary identity.

Projection onto odd supports of product `m≤N<2m` therefore has exactly the
actual boundary kernel. The quotient comparison sends actual cycle classes
to their surviving coefficients. Literal inclusions retain these coefficients,
so the comparison is natural. Prime-support product gives the degree-preserving
bijection with odd squarefree labels.

The exterior universal property extends integer chains canonically to `R`.
Deletion and coning commute with this map. It descends through the actual
boundary quotient, sends `[c]` to `[c_R]`, and commutes with height inclusions.
Each surviving representative `d(2∧S)` is preserved, as is the empty chain.
Thus the induced map preserves the actual homology basis. The base-changed
integral basis proves the tensor equivalence and its naturality. Reindexing
by squarefree product changes no coefficients.

## Lean realization

Namespace `GaloisForLFunctions.EffectiveScalingGeometry`:

- [PrimeAugmentedHomology.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeAugmentedHomology.lean):
  `primeHomologyCriticalIso`.
- [PrimeArithmeticPersistence.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeArithmeticPersistence.lean):
  `primeHomologySquarefreeIntervalIso`.
- [PrimeHomologyCoefficientMap.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyCoefficientMap.lean):
  `primeIntegralHomologyMap_class`, `primeIntegralHomologyMap_natural`.
- [PrimeHomologyBaseChange.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeHomologyBaseChange.lean):
  `primeHomologyBaseChange_tmul`, `primeHomologyBaseChange_natural`.
- [PrimeArithmeticBaseChange.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeArithmeticBaseChange.lean):
  `primeHomologySquarefreeIntervalIso_integral`.

Direct `lake --old env lean` audits pass. Printed capstones use exactly
`[propext, Classical.choice, Quot.sound]`. Modules are wired into the programme
umbrella; no umbrella build is used.

## Existing theory and scope

[Björner, Theorem 3.1](https://arxiv.org/abs/1101.5704) gives the classical
Betti-rank formula using odd squarefree numbers in `(N/2,N]`. No priority claim
is made for that formula or the individual wedge decomposition. This theorem
realizes the actual natural persistence isomorphism and canonical coefficient
maps in Lean. It supplies no Euler-cancellation estimate or global effectivity.

Complex Dirichlet weights are covered by the separate
[chain-gauge equivalence](esg-dirichlet-persistence-equivalence.md).
Integral nonunit weights and analytic completion require different arguments.
