# Suzuki bicausal no-free-splice classification

- **ID:** `suzuki-bicausal-no-free-splice-classification`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-bicausal-no-free-splice-classification-formalized.md`
- **Type:** UNIVERSAL TRANSPORT CLASSIFICATION / SHARP NO-GO SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOT RH]`
  `[APPLICATION NOVELTY UNVERIFIED]`
- **Parent:** `suzuki-bicausal-displacement-overlap-conservation.md`
- **Failed inference:**
  `../../5-failed/suzuki-continuum-two-flank-surplus-pays-bicausal-seam.md`
- **RH used:** no
- **Computation used:** no

## Frontier attacked

The sharp log-Haar construction transports increasing-side mass forward by one fixed displacement
and decreasing-side mass without that displacement.  The two aggregate targets overlap on a seam
whose width equals the displacement.  A proposed repair used the fact that the critical tilted
tent has total apex deficit larger than the seam width.

That comparison uses the wrong quantity.  Total apex deficit is not the one-sided transport slack.
The theorem below classifies the splice exactly and shows that, after duplicate capacity is
removed, its residual is the original continuous-minus-atomic quadrature deficit.  Bicausal
splicing alone neither weakens nor strengthens the RH-bearing inequality.

## Setup

Let `h>0`, `a<=s`, and `s+h<=b`.  For an interval-integrable real profile `Phi`, put

```text
M(Phi)=integral_a^(s+h) Phi + integral_s^b Phi,  mixed target mass,
O(Phi)=integral_s^(s+h) Phi,                     duplicate seam mass,
U(Phi)=integral_a^b Phi.                         capacity-one target mass.
```

Let `Q` be any real source quadrature.  In the Suzuki application,

```text
Q=sum_n 2 Lambda(n)/n * A_a(2 log n)
```

over the corresponding finite sharp support.

## Theorem A: no-free-splice identity

For every `Phi` and every `Q`,

```text
M(Phi)=U(Phi)+O(Phi),                                  (1)

[M(Phi)-Q]-O(Phi)=U(Phi)-Q.                            (2)
```

Consequently,

```text
M(Phi)-Q >= O(Phi)  iff  U(Phi) >= Q,                  (3)
M(Phi)-Q =  O(Phi)  iff  U(Phi) =  Q.                  (4)
```

Thus the statement that accumulated one-sided monotonicity slack pays the duplicated seam is
*exactly* the original capacity-one quadrature inequality.

### Proof

Additivity of interval integrals gives

```text
integral_a^(s+h) Phi
 =integral_a^s Phi+integral_s^(s+h) Phi,

integral_s^b Phi
 =integral_s^(s+h) Phi+integral_(s+h)^b Phi.
```

Adding and regrouping yields

```text
M(Phi)
 =integral_a^s Phi+2 integral_s^(s+h) Phi+integral_(s+h)^b Phi
 =U(Phi)+O(Phi),
```

which is `(1)`.  Subtract `Q+O(Phi)` to obtain `(2)`.  The order and equality equivalences
`(3)--(4)` follow by substitution.  No monotonicity, positivity, arithmetic input, or limiting
argument is used.  Square.

## Theorem B: continuum splice is exactly critical, never supercritical

Take as source quadrature the capacity-one continuum mass itself, `Q=U(Phi)`.  Then

```text
M(Phi)-Q=O(Phi).                                        (5)
```

Hence every common-displacement continuum splice has zero capacity-corrected margin, for every
profile.  This remains true when the profile has arbitrarily large total apex deficit.

In particular the proved critical tilted-tent inequality

```text
D(1/2,2)=16-8 cosh(1)>2
```

does not supply a strict splice margin.  `D` measures total deficit from the apex over the whole
two-flank support; `(5)` concerns displacement slack after target multiplicity is corrected.  The
two quantities are not interchangeable.

### Proof

Substitute `Q=U(Phi)` into `(2)`.  Square.

## Sharp Suzuki consequence

Let `Q_a` be the exact finite Mangoldt quadrature and `U_a` the completed positive lag mass before
the fixed Gamma charge.  Any proof using only:

1. future cells on the increasing branch;
2. past cells on the decreasing branch;
3. common-displacement overlap bookkeeping; and
4. subtraction of the duplicated seam,

must prove

```text
M_a-Q_a >= O_a.
```

By `(3)`, this is equivalent to `U_a>=Q_a`, the original RH-bearing positive-lag quadrature
inequality.  Therefore the cell splice is bookkeeping, not a producer.  A genuine proof needs
additional arithmetic or operator structure that gives an independent lower bound for the
capacity-corrected residual.

The unique surviving scalar is

```text
R_a=U_a-Q_a.                                             (6)
```

In cumulative-mass language it is the displacement-fluctuation commutator between actual
Mangoldt quantile map and constant continuum displacement.  Under first-order weighted Mangoldt
weak convergence that commutator tends to zero, not to the positive tilted-tent apex deficit.
Its sign is therefore a second-order arithmetic problem, consistent with the exact RH connector.
No asymptotic sign is claimed here.

## Hostile audit

1. **Not another RH criterion.**  The theorem proves a universal identity and uses it to reject a
   proposed producer; it does not advertise `(6)` as progress by renaming it.
2. **No pointwise-cell repetition.**  The result concerns every aggregate common-displacement
   splice, not only individual apex cells.
3. **No contradiction with positive two-flank deficit.**  The deficit theorem remains true; its
   claimed payment interpretation is what fails.
4. **No capacity-only overclaim.**  Actual arithmetic blocks can still help if their source
   structure proves a lower bound for `(6)` independently.  The theorem says common-shift
   bookkeeping cannot do so.
5. **No RH input or computation.**  Proof is interval additivity and ordered-field algebra.

## Novelty boundary

Interval inclusion--exclusion and integral additivity are classical bridges.  Targeted search
found no use of the exact no-free-splice equivalence `(3)` in Suzuki's screw-function program or
the Mangoldt log-Haar transport literature.  Candidate new content is the source-specific
classification and correction of the proposed RH route, not the elementary integral identity.
Independent priority audit remains required.

## Gates

- [x] exact newest-corpus frontier audited
- [x] complete paper proof
- [x] false continuum-surplus inference isolated
- [x] strongest positive classification extracted
- [ ] source-independent lower bound for arithmetic displacement commutator
- [ ] RH
