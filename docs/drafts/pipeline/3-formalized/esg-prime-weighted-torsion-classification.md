# Integral prime-weighted homology and its arithmetic persistence

- **ID:** esg-prime-weighted-torsion-classification
- **Stage:** 3-formalized
- **Type:** INTEGRAL ARITHMETIC PERSISTENCE

## Theorem

Give vertex `p` boundary coefficient `p` in the augmented exterior complex of
prime faces with product at most `N`. In every exterior degree `k`, its actual
integral homology is naturally the pair of finitely supported coefficient
spaces with labels

| Coefficients | Label | Height window |
|---|---|---|
| `ℤ` | Odd squarefree `m`, `ω(m)=k` | `m≤N<2m` |
| `ℤ/2` | Squarefree `m` coprime to six, `ω(m)=k` | `2m≤N<3m` |

For `N≤M`, the free part restricts the old free coefficients to the new free
window. The parity part restricts `cast₂(old free)+old parity` to the new torsion
window. Thus a label coprime to six has the block

`ℤ[m,2m) → ℤ/2[2m,3m) → 0`,

with reduction modulo two at the transition. Odd labels containing three have
only `ℤ[m,2m)`. The statement includes the empty support in augmented degree
zero and describes the original complex's homology maps.

The canonical free quotient has no natural section already in empty degree.
More generally, a face omitting two and three has a free birth generator whose
coefficient becomes one modulo two at double height, for every possible lift
of that free generator. The objectwise free-plus-torsion decomposition therefore
does not split the persistence functor.

## Proof

Put `u=e₃−e₂`. The actual integral cycle coordinates are
`P(y)=d(u∧y)` and `Q(x)=O(x)+e₃∧δ₂(x)` in positive degree, and the identity in
empty degree. For a weighted cycle, the equation `d(Ox)+2δ₂x=0` and saturation
of the coordinate cutoff place `δ₂x` below `⌊N/3⌋`. Both inverse maps preserve
height and commute with all inclusions.

In odd coordinates, actual boundaries at `N` are exactly

`Dₖ(N)=Oₖ(⌊N/3⌋)+2Oₖ(⌊N/2⌋)+(Oₖ(⌊N/2⌋)∩ker(e₃∧·))`.

Splitting a filling into its odd and two-cone parts gives the forward
containment. The Bézout cone, the two-cone of a projected cycle, and the negative
two-cone of a chain annihilated by adjoining three fill the three summands.
The last summand consists of faces containing three; it is zero in empty degree.

Projection onto the free and parity windows is surjective, with kernel `D`.
For the kernel, expand a half-height chain in the exterior basis. Every term
is low, contains three, or has an even coefficient in the torsion window.
For surjectivity, lift finitely supported parity coefficients to integers;
the free and parity windows are disjoint. The first isomorphism theorem then
descends these coordinates through the actual homology class quotient.

The coefficient transition formula commutes with literal chain inclusions.
At a target torsion label, a born source coefficient lies either below its
doubled birth height or in its torsion window, so exactly one source component
contributes. The product of the prime support identifies the labels with
squarefree integers, and omitting two and three is equivalent to coprimality
with six.

For nonsplitting, the free birth generator dies in the free quotient at double
height. Every lift still has parity coefficient one there, since that label
has no torsion coordinate at its birth height. Naturality of a section would
force the same transition to be zero. The empty face supplies an unconditional
counterexample, and the actual homology isomorphism transports the obstruction.

## Lean and audit

- [PrimeWeightedAugmentedHomology.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedAugmentedHomology.lean):
  `primeValueHomologyCoordinateIso`, including the actual cycle-class comparison.
- [PrimeWeightedArithmeticPersistence.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedArithmeticPersistence.lean):
  `primeValueHomologyArithmeticIso`, `squarefreeValueMap_free`,
  `squarefreeValueMap_torsion`.
- [PrimeWeightedPersistenceExtension.lean](../../../../formal/GaloisForLFunctions/EffectiveScalingGeometry/PrimeWeightedPersistenceExtension.lean):
  `primeValueCoordinateMap_double_ne_zero`, `primeValueFreeProjection_no_section`,
  `primeValueActualFreeProjection_zero_no_section`.
- [Boundary and coefficient theorem](esg-prime-weighted-boundary-lattice.md):
  supporting lattice, parity and reindexing declarations.

All listed modules pass direct `lake --old env lean` audits. Printed capstones
use exactly `[propext, Classical.choice, Quot.sound]`.

## Existing theory and scope

Weighted simplicial homology is classical [Ren–Wu–Wu](https://arxiv.org/abs/1708.06722).
General weighted torsion structure over formal power-series discrete valuation
rings is developed by [Li–Reidys](https://arxiv.org/abs/2205.03435) and
[Bura–Dutta–Li–Reidys](https://arxiv.org/abs/2206.04612). No priority claim is made
for weighted homology or its general structure theory. The arithmetic result
here is the explicit integral prime-product classification with actual height
maps and its nonsplitting.

The [all-coefficient filtered normal form](esg-two-prime-weighted-normal-form.md)
now gives the actual two-prime chain isomorphism and natural core/tag block
coordinates with exact differential matrices. Its arbitrary-coefficient homology comparison remains
open, as do Euler cancellation, arithmetic heights and scaling-surface effectivity.
