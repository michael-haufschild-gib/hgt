# Finite divisor/head/tail shadow universality law

## Status

Law 251; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/FiniteDivisorPrefixNonselection.lean`
- `RHTower/CombinedShadowBlindness.lean`
- `RHTower/TailBlindness.lean`

## Theorem-first derivation

Finite-divisor nonselection constructs an exact critical-line divisor prefix with a finite Euler
head and a fresh fixed orbit. Combined shadow blindness proves that multiplication by a free
reflection-orbit quartic preserves both finite Euler class and logarithmic-derivative tail. The
quartic is nonzero at every critical-line point, so the two interfaces compose without changing
any prescribed prefix multiplicity.

## Universal law

For every finite positive critical-line divisor with arbitrary multiplicities, every finite Euler
head, and every fresh fixed orbit, adjoining an arbitrary generic free off-line orbit preserves:

- the same finite Euler class;
- the exact full prescribed divisor prefix;
- the fresh fixed orbit with order one;
- eventual nonvanishing and the original asymptotic logarithmic-derivative tail.

The resulting carrier has order one and nontrivial level-one charge at the free off-line point.
Thus finite divisor data, finite exact Euler data, and the asymptotic tail are simultaneously blind
on one carrier.

## Paper proof

1. Use `finiteDivisorPrefix_orbitNonselection` for the fixed extension's finite Euler membership,
   prescribed multiplicities, and fresh order-one fixed orbit.
2. The fixed extension is eventually nonzero on a sufficiently far right half-plane: the Euler
   bundle is eventually nonzero and all critical-line factors are nonzero off `Re s = 1/2`.
3. Multiply it by `orbitQuartic ρ`. Apply `eventuallyNonvanishing_orbitQuartic_mul` and
   `dlogTail_orbitQuartic_mul`; absorb the quartic into the FE/Schwarz residual factor.
4. At old critical-line points and the fresh fixed point the quartic has order zero, so analytic
   order is unchanged.
5. At `ρ`, the fixed extension is nonzero and the quartic has simple order one, hence the new
   carrier has order one and level-one charge `-1`.

No numerical pre-certification applies: proof is exact divisor arithmetic and asymptotic-tail
invariance.

## Lean target

- Module: `GaloisForLFunctions.RHTower.FiniteDivisorHeadTailShadowUniversalityLaw`
- Capstone: `RHTower.finiteDivisorHeadTail_freeOrbitShadowUniversality`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/FiniteDivisorHeadTailShadowUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
