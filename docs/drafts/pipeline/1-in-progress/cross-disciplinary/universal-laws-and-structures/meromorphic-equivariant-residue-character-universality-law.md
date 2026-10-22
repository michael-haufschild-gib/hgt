# Meromorphic equivariant residue-character universality law

## Status

Theorem-first survivor. Paper proof complete; exact Lean module check passed warning-free on
2026-07-22.

## Lean-generated inputs

- `RHTower/EquivariantAnalyticOrderCyclicSpectrumUniversalityLaw.lean`: for analytic germs,
  arbitrary self-map equivariance forces multiplier-to-order equality with the scalar character.
- `HTGeometry/LogarithmicResidueQuantization.lean`: the logarithmic derivative residue is the
  signed integer meromorphic order, including poles.
- `RHTower/CCMMeromorphicCuspBoundaryNoGo.lean`: corpus already uses Laurent normal form for
  arbitrary integer meromorphic charge along a punctured analytic arc.
- `HTGeometry/RamificationPoleFixedPoint.lean`: signed order, rather than analytic nonnegative
  order, is the natural local coordinate for pole/zero rigidity.

## Candidate survivor

Let `f` be meromorphic at `c`, with signed order `n : ℤ`. Let analytic `τ` fix `c` with nonzero
multiplier. If `f(τ(s)) = χ f(s)` near `c`, then

`(τ'(c)) ^ n = χ`.

The same `n` is the punctured limit of `(s-c) logDeriv f(s)`. Thus local meromorphic
semi-equivariance has one signed charge simultaneously visible as a multiplicative character and
an additive logarithmic residue. Law271 is its nonnegative analytic face; logarithmic poles are its
negative face.

## Formal targets

- `GaloisForLFunctions.HTGeometry.multiplier_zpow_meromorphicOrder_eq_character`
- `GaloisForLFunctions.HTGeometry.meromorphicEquivariant_residueCharacterLaw`

## Novelty audit

Post-proof primary-source searches covered meromorphic semi-invariants, equivariant divisors,
local Laurent characters, logarithmic derivatives, and residue/divisor correspondences. Adjacent
literature includes Noguchi's logarithmic-derivative/divisor residue framework
([Project Euclid](https://projecteuclid.org/journals/nagoya-mathematical-journal/volume-83/issue-none/Lemma-on-logarithmic-derivatives-and-holomorphic-curves-in-algebraic-varieties/nmj/1118786486.pdf))
and Chiang--Feng's meromorphic logarithmic difference/derivative theory
([arXiv:math/0610480](https://arxiv.org/abs/math/0610480)). No source found states the exact joint
local law for a vector-valued meromorphic germ, arbitrary analytic self-map with nonzero
multiplier, nontrivial scalar character, signed Laurent order, and the scalar residue corollary.
Novelty claim is limited to that joint formulation and Lean formalization; Laurent factorization
and the integer residue of `dlog` are classical.

## Verification

```text
cd formal
lake env lean GaloisForLFunctions/HTGeometry/MeromorphicEquivariantResidueCharacterUniversalityLaw.lean
```

Passed with exit code 0 and no warnings on 2026-07-22.
