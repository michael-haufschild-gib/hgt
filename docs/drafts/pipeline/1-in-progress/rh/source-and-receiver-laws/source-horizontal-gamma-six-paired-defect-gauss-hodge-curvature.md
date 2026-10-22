# Source-horizontal Gamma-six paired-defect / Gauss-Hodge curvature

- **Status:** FORMAL THEOREM PACKAGE; PRODUCER STILL OPEN
- **Lean:** `formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature.lean`
- **Route seam:** L cyclic descent + R resolved antidiagonal + C1/CCM Gauss-Hodge virial

## Result

Let `B=t-1` be the literal Deninger infinite-cyclic boundary and let

```text
r_a(Bf) = (exp(a)-1) r_a(f)
```

be the already constructed physical-character defect. Pair the two retained orientations before
scalar collapse:

```text
K_a(f,g) = -r_a(Bf) r_{-a}(Bg).
```

Lean now proves the exact coefficient-faithful identity

```text
K_a(f,g)
  = 2 r_a(f) r_{-a}(g) (cosh(a)-1).
```

For the canonical unit primitive this has three simultaneous forms:

```text
K(a)
  = 2(cosh(a)-1)
  = (exp(a)-1) + (exp(-a)-1)
  = -(exp(a)-1)(exp(-a)-1).
```

Thus opposite transport is multiplicatively flat, but its deviation from the identity has a
strictly positive additive codiagonal away from `a=0`. The codiagonal has zero first neutral jet
and universal second jet `2`; linear antidiagonal cancellation is exactly the shadow that hid the
nonlinear obstruction.

After prime-clock substitution `a=log(p)t` and multiplication by the literal Gauss residue/Fisher
weight, the Euler derivative is exactly `gaussHodgeMassCurrent`. This identifies Gauss Hodge mass
as the nonlinear second-order curvature left over when the resolved Green antidiagonal is
exponentiated.

## Heavy conjecture loop

### C1 — contragredient diagonal descent kills paired defects

**Conjecture.** Since the two characters have parameters `a` and `-a`, simultaneous generator
translation is invisible; perhaps diagonal cyclicity kills their paired boundary value.

**Failure.** Lean proves diagonal character product is exactly one for every `a`, while paired
boundary curvature is positive iff `a != 0`. Multiplicative inverse transport gives
`exp(a)exp(-a)=1`; it does not give `exp(a)+exp(-a)=2`.

**Positive survivor.** The missing law is now finite and additive: force the two *deviations from
identity* to have zero codiagonal. At prime clock this condition is exactly critical-line
placement, with prime label and both orientations retained.

### C2 — square-zero DGA/Bianchi packaging kills the product

**Conjecture.** Place the two defects on odd generators of an exterior DGA and use `d^2=0` to make
their product an exact two-cell whose scalar readout vanishes.

**Failure.** Every algebra map from an exterior algebra over `R` to `R` kills every odd generator:
the generator squares to zero and `R` has no nonzero nilpotents. Lean proves no scalar algebra
character can carry the two nonzero physical defects at nonneutral `a`. A Sullivan primitive alone
therefore cannot justify the required scalar Stokes law.

**Positive survivor.** Required target is genuinely nonmultiplicative: a trace/current on a
resolved two-cell, with an independently proved Stokes property. Ordinary scalar character
extension is formally excluded.

### C3 — paired cyclic curvature is the missing Gauss virial

**Conjecture.** The surviving second-order defect may coincide with the positive Gauss-Hodge
receiver rather than define another obstruction.

**Proof.** Lean proves its prime-clock weighted Euler response is exactly
`gaussHodgeMassCurrent`. This is an exact L/R/C1 seam, not analogy.

## Formal declarations

- `sourceHorizontalGammaSixOppositeBoundaryCurvature_eq_splitEnergy`
- `sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_curvature`
- `sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects`
- `sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff`
- `hasDerivAt_sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_zero`
- `sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_secondJet`
- `gaussHodgeMassCurrent_eq_euler_gaussGammaSixPairedBoundaryEnergy`
- `sourceHorizontalGammaSixOppositeCharacter_diagonalGenerator_flat`
- `sourceHorizontalGammaSix_diagonalFlat_but_pairedCurvature_pos_iff`
- `exteriorAlgebraRealCharacter_generator_eq_zero`
- `not_exists_exteriorCharacter_carrying_oppositePhysicalDefects`
- `sourceHorizontalGammaSixPrimePhysicalBoundaryDefects_add_eq_zero_iff`

## Open producer

Construct, from actual Xi source rather than divisor-selected scalar data, a nonmultiplicative
resolved trace/current satisfying finite additive codiagonal conservation for the forward and
reciprocal cyclic boundary defects. Multiplicative contragredience, first-order Green cancellation,
ordinary cyclic descent, and exterior-DGA scalarization cannot supply this law.

No RH claim is made. External novelty is unaudited; internal cross-corpus identity and no-go are
unconditional Lean theorems.
