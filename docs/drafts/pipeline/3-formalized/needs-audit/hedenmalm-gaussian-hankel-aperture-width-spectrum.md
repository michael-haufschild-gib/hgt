# Hedenmalm Gaussian Hankel aperture--width spectrum

- **ID:** `hedenmalm-gaussian-hankel-aperture-width-spectrum`
- **Stage:** 3-formalized
- **Type:** EXACT SUPPORT / COMPLETE-HANKEL PHASE LAW
- **Scientific status:** `[PROVED ON PAPER] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  - `complete-hankel-sign-cone-hedenmalm-rh.md`
  - `../not_new_scientific_knowledge/hedenmalm-exterior-complete-gaussian-hankel-phase-law.md`
  - `../ccm-quantitative-source-divisor-energy-spectrum.md`

## Statement

For `alpha >= 0`, let

```text
Z(alpha) : every zero rho of xi satisfies Re rho <= 1/2 + alpha.
```

Fix one Gaussian temperature `tau > 0`.  Let `H_tau(alpha)` assert that for every aperture

```text
alpha < a < 1
```

the complete Gaussian-windowed Hankel tower of the actual Hedenmalm center-mixed Fourier current
`J_a` is positive semidefinite.  Then

```text
H_tau(alpha)  <->  Z(alpha).                                      (1)
```

Equivalently, the positivity threshold of the complete Hedenmalm Gaussian Hankel family is exactly
the horizontal support radius of the Xi divisor.  In particular:

```text
alpha = 1/2 : the exterior phase is unconditional;
alpha = 0   : the endpoint is RH.
```

The theorem is independent of the chosen positive Gaussian temperature.  It is an exact phase
law, not an estimate and not a finite-section statement.

## Proof

Write the centered Xi spectral point attached to a zero `rho=beta+i gamma` as

```text
lambda = gamma + i(1/2-beta).
```

The functional equation and Schwarz reflection pair `lambda` with its complex conjugate.  At the
lower point `z=b-ia`, the imaginary part of the paired relative-resolvent atom is

```text
  2a ((b-Re lambda)^2 + a^2 - (Im lambda)^2)
  -----------------------------------------------------.           (2)
  (((b-Re lambda)^2+(a+Im lambda)^2)
   ((b-Re lambda)^2+(a-Im lambda)^2))
```

The denominator is positive away from the paired poles.  Under `Z(alpha)`, reflection gives the
two-sided bound

```text
|Im lambda| = |beta-1/2| <= alpha.
```

Hence `(2)` is nonnegative whenever `a>alpha`.  The same strict inequality shows that the line
`Im z=-a` contains no Xi zero.  The relative-resolvent series is absolutely summable there; pairing
and reindexing by conjugation therefore yields

```text
Im (XiC'/XiC)(b-ia) >= 0.                                        (3)
```

The exact Hedenmalm current identity is

```text
J_a(b)
 = d/da |XiC(b-ia)|^2
 = 2 |XiC(b-ia)|^2 Im (XiC'/XiC)(b-ia).                           (4)
```

Thus `J_a(b)>=0` for every `b` and every `alpha<a<1`.  At one positive Gaussian temperature, the
complete weighted Hankel sign-cone theorem says that all Hankel sections are positive semidefinite
if and only if the continuous multiplier `J_a` is pointwise nonnegative.  This proves
`Z(alpha) -> H_tau(alpha)`.

Conversely assume `H_tau(alpha)` and suppose that a zero `rho` satisfies

```text
d := Re rho - 1/2 > alpha.
```

The open-strip theorem gives `d<1/2`.  Put `b=Im rho`.  Then

```text
XiC(b-id)=0.                                                      (5)
```

The complete Hankel sign-cone theorem turns `H_tau(alpha)` into `J_a(b)>=0` at every
`alpha<a<1`.  By `(4)`, the nonnegative function

```text
U(a)=|XiC(b-ia)|^2
```

has nonnegative derivative throughout every compact interval contained in `(alpha,1)`, and is
therefore nondecreasing there.  Since `XiC` is entire and nonzero, its zero at `b-id` is isolated.
Choose `c` with `alpha<c<d`, sufficiently close to `d`, so that `XiC(b-ic) != 0`.  Monotonicity
and `(5)` give

```text
0 < U(c) <= U(d)=0,
```

a contradiction.  Therefore no such `rho` exists, proving `Z(alpha)`.

The argument uses the complete tower only through its exact recovery of the multiplier sign.  No
finite Hankel section can replace it.

## Research consequence

The law identifies the remaining RH-bearing theorem without hiding it in a finite positivity
claim.  The open source problem is now exactly a downward propagation theorem carrying the
unconditional exterior phase from threshold `1/2` to threshold `0`.  Any proposed mechanism must
decrease the actual divisor-width invariant; reformulating the same invariant in a new positive
carrier does not discharge that obligation.

## Formalization plan

- [x] generalize the conjugate-pair resolvent sign from exterior width `1/2` to an arbitrary
      half-plane bound `alpha`;
- [x] sum the paired atoms and transfer the trace sign to the Hedenmalm current;
- [x] define the complete Gaussian tail cone above `alpha`;
- [x] prove `Z(alpha) -> H_tau(alpha)`;
- [x] prove the reverse implication using the exact aperture derivative and isolated zeros;
- [x] add the quantitative phase law to the RHTower index and run the exact source and module
      audits.

## Lean theorem surface

The unconditional formalization is
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmGaussianHankelApertureWidthSpectrum.lean`.
Its capstones are:

```text
hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
hedenmalmGaussianHankelTailCone_temperature_iff
hedenmalmGaussianHankelTailCone_zero_iff_riemannHypothesis
```

The exact source check and exact module build both succeed.  The capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`; the formal lint gate passes.

## Novelty boundary

The horizontal-modulus monotonicity mechanism is classical (Sondow--Dumitrescu), and the divisor
half-plane spectrum already occurs elsewhere in the local corpus.  Possible novelty attaches only
to the exact complete-Hankel threshold synthesis.  No priority claim is made before a dedicated
literature audit.
