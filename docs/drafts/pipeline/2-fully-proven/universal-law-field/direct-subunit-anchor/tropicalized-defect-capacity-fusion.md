# Tropicalized defect-capacity fusion

- **ID:** ULF-DSA-002
- **Stage:** 2-fully-proven
- **Status:** exact three-organ fusion proved; source/completion ownership remains open
- **Lean:** `RHTower.DirectSubunitEscapeCapacityFusion`

## Big picture

Direct subunit selection does not need a new integral lattice or a winding.  The corpus already
contains the integer: a nonzero horizontal formation grade tropicalizes to one unsigned harmonic
escape unit.  It also contains a coercive real lift of that unit and a literal source capacity
strictly below one unit.

The resulting law is

```text
continuous nonneutral grade
  -> integer escape support I = 1
  -> cubic completed energy E >= (115/108) I
  while literal Euler source capacity B < 115/108.
```

This is the Ferrero--Washington shape: a discrete obstruction and a direct strict subunit budget,
with no tensor power, repeated scale, or density amplification.

## Corpus audit

1. `HedenmalmThetaKakutaniBalancedIndexNoGo` defines
   `thetaKakutaniEscapeMultiplicity : XiZeroCopy -> Nat`.  It is zero on neutral copies and one on
   nonneutral copies.  Reflection preserves it; signed Fredholm index cancels, unsigned defect does
   not.
2. `XiFormationEscapePrincipalClassLaw` reconstructs the same 0/1 class from Gamma-six boundary
   jets, Mobius prime-normal energy, resolved Green codiagonal, and Kakutani polarization.
3. `XiWardCubicReflectionLoewnerCodiagonalIncidence` proves that each strict-right divisor support
   has integrated cubic landing at least `115/108`, multiplicity included.
4. `RoutePPrimitiveCollisionSubquantum` proves the complete primitive Euler collision budget is
   strictly below `115/108`.
5. `RoutePPrimitiveCollisionCapacityTerminal` proves that asserting target trace capacity directly
   is RH-equivalent.  The missing edge must therefore arise from a source-defined completion, not
   be assumed as a target inequality.

## Theorem

For every `q : XiRightZeroCopy`, put

```text
I(q) = thetaKakutaniEscapeMultiplicity(q) in Nat,
E(q) = integral of xiWardCubicReflectionLoewnerCodiagonalLanding(q).
```

Then unconditionally

```text
I(q) = 1,
B_Euler < (115/108) I(q) <= E(q).
```

### Proof

Strict-rightness says `Re(rho)-1/2 > 0`, hence centered modular rate is nonzero.  The exact
flux/rate zero-locus theorem makes theta boundary flux nonzero, so quantized escape multiplicity is
one.  Substitute this equality into the proved Euler subquantum bound.  The cubic Loewner quantum
theorem gives the second inequality.  No new assumption enters.

`[PROVED HERE]`

## Exact RH closure still missing

One theorem remains:

> Construct, before divisor specialization, the anomaly-subtracted relative completion of the
> literal Euler collision synthesis and prove that every completed Loewner residue vector is its
> contractive boundary image.

Its trace consequence would be `E(q) <= B_Euler`.  Combined with the proved fusion,

```text
B_Euler < (115/108) I(q) <= E(q) <= B_Euler,
```

so no `XiRightZeroCopy` exists; functional equation gives RH.

The completion theorem must define the source operator, subtraction, domain, and contraction
without `XiRightZeroCopy`, `analyticOrderAt xi`, or an RH-equivalent target-capacity premise.
Residues may be read only after the source construction exists.

## No-gos fixed by the fusion

- Signed index is wrong: functional-equation reflection cancels it.  Integer is unsigned escape
  multiplicity.
- Dyadic ghost integrality and integral frames are unnecessary and RH-equivalent as premises.
- Completed-SEM winding is unnecessary; its global vanishing is already an RH receiver and no
  same-boundary subunit estimate exists.
- Finite normalized Kakutani energies below one do not help: they converge to one off line.  The
  direct strict gap comes from the independent cubic Euler capacity.
- Literal Laurent coefficient integrality does not make physical evaluation integer-valued.
- Stating `E <= B_Euler` on divisor packets is forbidden: P-G176 proves that statement is already
  RH-equivalent.  It must be a consequence of pre-divisor completion properness.

## Interpretation

The higher mechanism is **tropicalized defect capacity**: completion turns every nonzero continuous
grade into one indivisible support unit; a coercive energy represents that unit; arithmetic
formation has less than one unit of total capacity.  RH becomes the assertion that literal Euler
formation owns its completed boundary energy after universal anomaly subtraction.

