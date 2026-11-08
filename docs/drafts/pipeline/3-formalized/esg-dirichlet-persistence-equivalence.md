# Dirichlet weighting preserves prime-height homology persistence

- **ID:** esg-dirichlet-persistence-equivalence
- **Stage:** 3-formalized
- **Type:** NATURAL CHAIN ISOMORPHISM

## Exact theorem

At every prime-product cutoff `N`, the augmented exterior-chain complex over
`ℂ` with boundary weights `p^(−s)` is isomorphic to the unweighted complex.
The isomorphisms commute with all height inclusions, for every complex `s`.
Consequently the actual homology persistence functors are naturally isomorphic
in every degree, including the empty augmented face.

The unweighted and weighted complexes are built from the spans of prime tuples
whose products are at most `N`; they are not abstract modules assigned the
expected ranks or interval labels.

## Paper proof

Let `g_s(e_p)=p^s e_p` on the free prime module and `G_s=∧g_s` on exterior
chains. Since prime bases are nonzero, `g_s g_t=g_(s+t)` and `G_s` has inverse
`G_(−s)`. Every atom is scaled by the product of its vertex factors, so both
maps preserve its product cutoff.

The weighted augmentation composed with `g_s` is the ordinary augmentation:
`p^s p^(−s)=1`. Naturality of exterior contraction therefore gives
`d_s G_s=G_s d_0`. Restricting yields the cutoff chain isomorphism. Height
inclusions are literal inclusions of the same chains, so they commute with the
gauge. Applying the homology functor yields the natural persistence isomorphism.

## Lean realization

Namespace `GaloisForLFunctions.EffectiveScalingGeometry`.

- [DirichletChainGauge.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/DirichletChainGauge.lean):
  `dirichletChainGauge_boundary`, `dirichletCutoffGaugeEquiv`.
- [PrimeCutoffComplex.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeCutoffComplex.lean):
  `primeCutoffComplex`, `primeCutoffPersistence`, `primeCutoffHomology`.
- [DirichletPersistenceEquivalence.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/DirichletPersistenceEquivalence.lean):
  `dirichletCutoffComplexIso`, `dirichletPersistenceIso`,
  `dirichletHomologyPersistenceIso`.

All three modules pass direct `lake --old env lean <module>` audits.
Their printed capstone dependencies are exactly
`[propext, Classical.choice, Quot.sound]`. The programme umbrella imports all
three; no umbrella build is used.

## Contribution and boundary

The corpus already supplies exterior chains, contraction naturality and
fillings after doubling. This result constructs the cutoff complexes and
homology functors and identifies their entire Dirichlet persistence systems.
Product-weighted homology is classical; see
[Ren–Wu–Wu, Definition 2.5 and §4](https://arxiv.org/abs/1708.06722).
No priority claim is made for diagonal gauge equivalence in general.

Finite complex Dirichlet weights therefore preserve algebraic persistence.
This theorem does not identify an analytic completion, control a norm, or
establish cancellation. Integral nonunit weights are outside its conclusion.
The exact integral barcode and its canonical coefficient compatibility are proved in
[the persistence card](esg-integral-prime-persistence.md).
