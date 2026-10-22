# Ramified differential orientation law

- **ID:** `ramified-differential-orientation-law`
- **Stage:** 1-in-progress
- **Type:** `[PAPER-PROVED CORE] [FORMAL CORE] [UNCONDITIONAL] [RH-FACING]`
  `[CANDIDATE NEW SYNTHESIS] [NOVELTY UNDER PRIMARY-LITERATURE AUDIT]`
- **Supersedes as headline:** `oriented-reflection-quotient-law.md`
- **Uses:** `positive-source-reflection-symmetry-fracture-law.md`;
  `first-moment-quadratic-zero-free-law.md`.

## The universal reinterpretation

The repeated obstruction is not insufficient differential complexity. It is loss of one scalar
amplitude under an invariant quotient.

Let `q` be a nonzero hypertranscendental element of a differential field and put

```text
j = q'/q.
```

The scalar reconstruction and torsor theorems in the corpus prove, under their displayed
constant-field and generation hypotheses,

```text
F<q> = F<j>(q)                                           (R1)
Aut_d(F<q> / F<j>) = G_m                                 (R2)
Aut_d(F<q> / F<q^N>) = mu_N.                             (R3)
```

Moreover,

```text
q hypertranscendental  =>  q^N hypertranscendental,      (R4)
dlog(q^N) = N dlog(q),                                  (R5)
F<dlog(q^N)> = F<dlog(q)>.                              (R6)
```

Thus a positive power retains the complete logarithmic differential current and maximal
differential complexity. What it loses is exactly a finite scalar phase. For `N=2`, that phase is
orientation:

```text
q and -q have the same square and the same logarithmic-current field.
```

This is the **differential orientation torsor**.

Now let `q` also be a local analytic coordinate. At a zero `p`,

```text
ord_p(q^N) = N ord_p(q).                                (R7)
```

The map `q -> q^N` is free away from the divisor and ramified on it. Every analytic reader
invariant under `q -> -q` factors through `q^2`; its first jet at `q=0` vanishes. The logarithmic
current remains singular there and records multiplicity, but not the choice of sheet.

This gives the master law:

> **Ramified differential orientation law.** Invariant scalarization conserves differential
> complexity, logarithmic current, divisor support, and multiplicity up to the covering degree.
> It discards exactly the finite orientation torsor. The discarded datum becomes indispensable
> precisely on the divisor, where the quotient ramifies. Consequently invariant currents can
> count a collision, but a regular one-sided exclusion law must live on an oriented lift.

The law is not the classical observation that an even function depends on a square. Its content
is the simultaneous exact conservation theorem `(R1)`--`(R7)`, the scalar differential Galois
classification, and the source-selected Riemann--Xi realization below.

## Reflected analytic channels

For an ordered analytic pair `(A,B)`, put

```text
R = B/A,
J = (A+B)/(A-B).
```

Channel exchange sends

```text
R -> 1/R,
J -> -J.
```

The symmetric collision `A+B=0` is `J=0` whenever the local denominator is regular. Hence the
reflection quotient is the `N=2` orientation torsor of the master law.

The ordered lift carries a canonical division-free dynamics:

```text
W = B' A - B A',
V = A^2 conjugate(W),
R' V = |W|^2.                                           (R8)
```

Every affine collision `alpha A + beta B=0` is the projective level
`R=-alpha/beta`. The Wronskian is therefore the regular first-order orientation discarded by
every even reader. Affine zero motion, boundary normal velocity, and projective monotonicity are
three readings of `(R8)`.

## Source-selected Riemann--Xi realization

The completed theta density selects

```text
E(z)  = (z^2+1/4)F(z)-1/4,
E#(z) = (z^2+1/4)F(-z)-1/4.
```

The universal first-moment quadratic stability theorem proves the source mechanism behind the
unconditional chart

```text
E(z) != 0  for Im(z)>0.                                 (R9)
```

The exact reflection identity is

```text
E+E# = 4 z^2 XiC.                                       (R10)
```

At every noncentral Xi zero in the upper theta strip, `E#=-E`, so `E-E#=2E!=0`. Therefore the
odd coordinate

```text
J=(E+E#)/(E-E#)
```

is regular there and

```text
XiC(z)=0  iff  J(z)=0.                                  (R11)
```

The Xi divisor is thus the ramification locus of the reflection-orientation quotient, not a
failure of the positive source chart.

At a collision,

```text
W = 4 z^2 XiC'(z) E(z).                                 (R12)
```

At a positive simple real collision, the source boundary value fixes the exact signed normal
velocity. The affine-pencil ejection theorem is the same unsquared orientation in deformation
coordinates.

No RH conclusion is asserted. The closed result is a classification: it identifies exactly
which datum survives every invariant differential reader, exactly which datum is lost, and
exactly where that loss becomes singular for the actual completed theta realization.

## Exact shadow theorem, not analogy

Rows below are admitted only with the stated theorem-level implication.

| Corpus theorem | Exact specialization of the master law |
|---|---|
| Scalar logarithmic-current reconstruction | `(R1)`: a full HT scalar adds one amplitude to its current field |
| Scalar differential torsor | `(R2)`: current readers quotient the full scalar amplitude group |
| Finite scalar differential torsor | `(R3)`: power readers leave exactly `mu_N`; sign for `N=2` |
| Power HT and log-current field invariance | `(R4)`--`(R6)`: squaring loses no Kolchin complexity or current |
| Even-entire square factorization | global analytic `N=2` invariant descent |
| Even-reader first-jet theorem | regular first-order orientation vanishes at branch locus |
| Analytic order of a power | `(R7)`: divisor multiplicity is multiplied, not erased |
| Completed-theta transverse Pick theorem | `(R9)`: positive source constructs a zero-free oriented chart |
| Completed-theta reflection identity | `(R10)`--`(R11)`: Xi divisor is reflection ramification |
| Projective Wronskian flow | `(R8)`: canonical unsquared orientation before quotient |
| Affine simple-zero ejection | local oriented lift can enter a forbidden half-plane although endpoint is zero-free |
| Ward `8 pi` quartet theorem | reflection--Schwarz orbit pushforward counts four local divisor charges; it does not orient exclusion |
| Escaping quartet/Kolchin blindness | invariant finite differential fingerprints can retain HT while divisor charge escapes to a noncompact marked current |
| Isodivisorial HT-free frames | projective differential complexity and a common divisor are independent coordinates |
| Pairwise common-mode theorem | additive analogue: invariant differences lose one HT translation torsor |
| Theta spectral-form classification | symmetric positive forms live on divisor measures and are nonclosable in ordinary `L2` unless zero |

Claims about all Hilbert--Polya, CCM, Weil, Gram, or explicit-formula methods are prohibited.
Only a method whose reader is proved to factor through the relevant invariant quotient is covered.

## New deductions

### 1. Hypertranscendence is conserved across orientation loss

Squaring cannot be diagnosed as a loss of differential complexity:

```text
q HT  =>  q^2 HT,
F<dlog(q^2)> = F<dlog(q)>.
```

Hence the missing RH datum cannot be recovered by proving a stronger hypertranscendence statement
about the squared or logarithmic-current carrier. The missing datum is finite Galois data, not
Kolchin rank.

### 2. Divisor charge is the ramified residue of a free amplitude

Away from zeros, orientation is a free scalar torsor. At a zero, the power quotient ramifies and
the logarithmic current acquires its divisor pole. Winding, Ward mass, and negative index are
pushforwards of this local valuation. They are expected to count defects because counting is the
information the quotient preserves.

### 3. The correct RH-grade object is a source-oriented divisor current

The source theorem provides the chart, the Wronskian provides first-order orientation, and the
logarithmic current provides divisor charge. None alone contains all three. The minimal object is
their compatible lift:

```text
(zero-free source section, projective Wronskian orientation, divisor valuation).
```

This is an oriented meromorphic incidence current, not another scalar positivity criterion.

### 4. Relative differential independence and a shared divisor are compatible by design

Relative independence concerns generic projective directions after a common amplitude has been
removed. A shared divisor is local valuation data of that amplitude. Their coexistence is not
paradoxical and cannot imply zero exclusion without a theorem coupling projective direction to
oriented valuation.

## Hostile falsifiers

1. Any equation `(R1)`--`(R8)` fails under the hypotheses stated in the manuscript.
2. The finite torsor theorem requires hypotheses not discharged in a claimed Xi specialization.
3. `J` is asserted hypertranscendental without a theorem.
4. The actual theta sharp involution fails to exchange the two channels.
5. A claimed Xi zero lies where `E-E#=0`, invalidating the local odd coordinate.
6. The `8 pi` law is presented as a consequence of square descent rather than the proved
   reflection--Schwarz quartet current.
7. A field/matroid/Gram no-go is generalized beyond its exact invariant-reader class.
8. Prior literature already combines scalar differential torsor conservation, ramification,
   source-selected theta completion, and the Xi projective current.
9. The paper implies terminal capture, zero exclusion, or RH.

Hits 1--5 or 8 retire the headline. Hits 6--7 narrow the shadow map. Hit 9 blocks publication.

## Formal theorem surface

- `HTGeometry.differentialAdjoin_eq_logCurrentOrdinaryExtension`;
- `HTGeometry.scalarDifferentialGaloisGroupEquiv`;
- `HTGeometry.scalarFiniteDifferentialGaloisGroupEquiv`;
- `HTGeometry.hypertranscendentalOver_pow_of_pos`;
- `HTGeometry.differential_logDeriv_pow`;
- `HTGeometry.differentialAdjoin_logDeriv_pow_eq`;
- `HTGeometry.differentialAdjoin_pow_eq_logCurrentOrdinaryExtension`;
- `GaloisForLFunctions.HTGeometry.evenEntireSquareFactor_sq`;
- `HTGeometry.evenReader_firstJet_zero`;
- `analyticOrderAt_pow`;
- `HTGeometry.reflectedChannelOddCoordinate_swap`;
- `HTGeometry.reflectedChannelProjectiveDerivative_mul_flow`;
- `HTGeometry.reflectedAffineCollision_iff_projectiveLevel`;
- `HTGeometry.firstMomentQuadraticCompletion_ne_zero`;
- completed-theta zero-free chart, reflection, collision, projective Wronskian, boundary-velocity,
  and affine-ejection theorems;
- Xi hypertranscendence and the exact Ward/Kolchin/isodivisorial theorem surfaces listed in
  existing publication claim audits.

## Closure ledger

- [x] scalar current reconstruction and `G_m` torsor;
- [x] finite power-coordinate `mu_N` torsor;
- [x] power hypertranscendence and log-current conservation;
- [x] global even-entire square descent;
- [x] local invariant first-jet blindness;
- [x] analytic divisor-order multiplication;
- [x] universal projective flow and affine-level law;
- [x] universal positive-source quadratic stability;
- [x] exact theta zero-free chart and Xi collision realization;
- [x] exact theta Wronskian and conditional signed ejection;
- [ ] exact theta odd-coordinate sharp wrapper and local Xi-zero regularity theorem;
- [ ] Xi upper-end square/current-field conservation capstone;
- [ ] narrow Ward, Kolchin, isodivisorial, and spectral-form corollaries to exact declarations;
- [ ] primary-literature novelty audit;
- [ ] publication manuscript, claim trace, and hostile referee report.
