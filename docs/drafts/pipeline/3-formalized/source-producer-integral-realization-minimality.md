# Source production and integral realization are independent HT information channels

- **ID:** `source-producer-integral-realization-minimality`
- **Stage:** 3-formalized
- **Type:** GENERAL HT MINIMALITY THEOREM / NO-GOS WITH POSITIVE SUCCESSOR
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [FOUNDATIONAL SIGNIFICANCE PASS]`
  `[NOVELTY PROVISIONAL FOR THE SIX-CHANNEL HT CONSEQUENCE] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MinimalHTCompletionArchitecture.lean`
- **Parents:**
  - `hypertranscendental-minimal-polarized-critical-completion-architecture.md`
  - `../2-fully-proven/not_new_scientific_knowledge/determinant-line-trivialization-zero-divisor-blindness.md`
  - `../1-in-progress/hypertranscendental-constraint-hodge-duality.md`
- **Statement:** Even the previously forced source action, polarization, critical product
  bornology, and complete controlled transport germ do not determine either a source-produced
  divisor or integral divisibility.  Two further independent channels are necessary: a
  distinguished source-effective section and an integral/ramified realization.

## The first new channel: the carrier does not determine the section

Let `L=R x R` be the trivial real line over the real axis.  For every finite reduced divisor
`S subset R`, the polynomial section

```text
e_S(t)=product_(a in S)(t-a)                                  (1)
```

has zero set exactly `S`.  The carrier `L`, its topology, its orientation, and its homotopy type
are unchanged while the divisor is arbitrary.

> **[THEOREM -- SOURCE-SECTION BLINDNESS]** Forgetting the distinguished section is
> nonconservative for divisor and nonvanishing predicates, even on one fixed trivial analytic
> line.

This strengthens the determinant-line no-go from an interval argument to a formally certified
universal finite-zero-set realization.

> **Positive successor.** A source theory expected to produce spectral or divisor information
> must retain a distinguished section or morphism constructed from the source.  Triviality of its
> carrier, determinant line, derived support, or orientation is insufficient.

## The second new channel: realification does not determine integral divisibility

Consider the integral operators

```text
A_Z(x,y)=(2x,4y),
B_Z(x,y)=(-8y,x+6y).                                         (2)
```

After extension of scalars to `R`, put

```text
P_R(x,y)=(-4x-2y,x+y),
P_R^(-1)(u,v)=(-u/2-v,u/2+2v).                              (3)
```

Direct multiplication gives

```text
B_R P_R=P_R A_R,                                             (4)
```

and `(3)` proves that `P_R` is invertible.  Thus the real operators are conjugate: every invariant
of the real analytic conjugacy class agrees.

Their integral images have different exponent behaviour.  The image of `A_Z` is
four-saturated in the sense

```text
for every v in Z^2, 4v lies in image(A_Z),                   (5)
```

because `4(x,y)=A_Z(2x,y)`.  The analogous statement fails for `B_Z`: if
`4(1,0)=B_Z(x,y)`, then `-8y=4`, impossible over `Z`.

> **[THEOREM -- INTEGRAL REALIFICATION BLINDNESS]** Two integral operators can have isomorphic
> real analytic realizations while their integral cokernels have different exponent predicates.

The example is stronger than comparing multiplication by two on `Z` and `R`: it holds after the
entire real operator, including its conjugacy class, has been identified.

> **Positive successor.** A conservative source theory expected to detect multiplicity,
> divisibility, Kummer parity, ramification, or arithmetic rigidity must retain an integral or
> adelic lattice and its comparison maps.  No real or complex completion can reconstruct this
> channel in general.

## Six-channel minimality theorem

The parent theorem already forces four kinds of retained data:

```text
(i)   external source constraint groupoid;
(ii)  signed Hermitian/Krein polarization;
(iii) critical Gevrey product bornology on the full source x observable cone;
(iv)  complete controlled nonabelian transport germ.                         (6)
```

Equations `(1)`--`(5)` force two further kinds:

```text
(v)   a distinguished source-generated effective section or realization morphism;
(vi)  an integral/ramified lattice with its source comparison maps.           (7)
```

> **[THEOREM -- SIX-CHANNEL LOWER BOUND]** Any proposed HT field theory conservative for source
> identity, polarization, critical multiscale boundedness, complete transport, divisor
> nonvanishing, and integral divisibility must retain all six information channels `(6)`--`(7)`
> or an equivalent conservative object.

This is a necessity theorem, not a completeness theorem.  The witnesses show nonconservativity of
the relevant forgetful theories; they do not assert that the six retained channels reconstruct
every HT source.

## The unified object forced by the obstruction report

The six channels divide naturally into kinematics and effectivity.  Let

```text
Kin_HT = (source action, polarization, critical bornology,
          controlled transport, integral/ramified realization),

pi_eff : Eff_HT -> Kin_HT.                                  (8)
```

An object of `Eff_HT` above a kinematic object is not another decoration.  It is a source-pure
lift supplying the distinguished global section or realization morphism and all required typed
comparison maps.  For a constrained HT source with kinematic point `k_F`, define its producer
space by the homotopy fibre

```text
Prod_HT(F)=hofib_(k_F)(pi_eff).                              (9)
```

This corrects two weaker candidates.

- A topology, derived support, or constraint spectrum sees only part of `Kin_HT` and cannot see
  either `(1)` or `(5)`.
- A determinant or spectral object stores one realization of a lift but does not prove that it
  was produced source-purely or that an integral lift exists.

The common object is therefore a **space of source-effective lifts**, not a common scalar
obstruction and not a static topology.

## Seven reported obstruction classes as faces of one producer space

The obstruction classes in `docs/reports/rh-proof-chains-and-obstructions-2026-07-16.md` map to
`(8)`--`(9)` as follows.

| Report class | Required face of the producer theory |
|---|---|
| `O1` sign/orientation | positive real/polarized locus of `Prod_HT(F)` |
| `O2` critical all-scale estimate | critical product bornology and extension of the lift over the full scale cone |
| `O3` source spectral realization | perfect spectral/determinant realization of the distinguished lift |
| `O4` multiplicity/root/divisibility | integral/ramified lift and its cokernel data |
| `O5` non-circular comparison | source-purity of the lift: it factors from source data, not from the target divisor |
| `O6` missing typed bridge | an actual comparison morphism inside the effective lift |
| `O7` algebraicity/integrality/rigidity | arithmetic essential-image condition on the integral lift |

The claim is not that these predicates are equivalent.  It is that each is a different failure
mode of existence, extension, uniqueness, positivity, or arithmetic effectivity of one lift.

## Fields-scale conjecture: source-effectivity equivalence

> **[CONJECTURE -- HT SOURCE-EFFECTIVITY EQUIVALENCE]** There is a differential-birationally
> invariant category `Eff_HT^(max,thin)` of source-pure effective lifts such that
>
> ```text
> regular source-minimal constrained HT germs
>     ~= Eff_HT^(max,thin).                                  (10)
> ```
>
> Here `max` means maximal Kolchin growth of the vertical observable tower, while `thin` means
> finite generation or perfect amplitude transverse to the source-operator algebra, not finite
> cohomological height.  The observation functor reconstructs the analytic germ from its effective
> lift; the germ itself is not included as part of the lift data.  Analytic, monodromy, spectral,
> polarized, and integral realization functors are jointly conservative on the essential image.

Equation `(10)` is the exact form of “infinite algebraic capacity concentrated on a thin
constraint boundary.”  Capacity is maximal in the vertical observable direction; thinness is a
source-relative finite-generation condition; effectivity selects the special source among the
universally realizable kinematic objects.

### Falsifiers

Retire or enlarge `(10)` if any of the following occurs.

1. Two inequivalent source-minimal HT germs have equivalent complete effective lifts.
2. The lift can be defined only by storing the analytic germ or its divisor, making reconstruction
   circular.
3. A natural source class requires a seventh information channel independent of `(6)`--`(7)`.
4. Two source-matched obstruction realizations admit no common effective refinement.
5. The six-channel essential image is merely a standard motivic or Tannakian realization category
   with no HT-specific reconstruction theorem.

Every falsifier has a positive successor: construct the missing channel explicitly, prove the
maximal conservative subcategory, or narrow the equivalence to the largest source class on which
reconstruction is faithful.

## External novelty and anti-theatre gate

The ingredients are parent mathematics and are not claimed as discoveries:

- derived Tannakization and automorphism groups of realization functors;
- de Rham--Betti objects, comparison torsors, and systems of realizations;
- motives with integral coefficients and real/Betti realization;
- integral versus rational or real matrix conjugacy;
- determinant lines, sections, and divisor theory.

Primary parent checks include:

- Iwanari, *Tannakization in derived algebraic geometry*, https://arxiv.org/abs/1112.1761;
- Kreutz--Shen--Vial, *Around the de Rham--Betti conjecture*,
  https://arxiv.org/abs/2206.08618;
- Yang, *A Note on Systems of Realizations on Shimura Varieties*,
  https://arxiv.org/abs/2304.10751;
- Afandi, *Conjugacy of Integral Matrices over Algebraic Extensions*,
  https://arxiv.org/abs/2109.02130.

The explicit polynomial and lattice witnesses are elementary parent consequences.  The
candidate-new theorem is the **HT six-channel minimality consequence** obtained by combining them
with the five existing nonconservativity witnesses.  Targeted searches found no source stating
this lower bound for constrained hypertranscendental analytic functions.  This is a provisional
novelty pass, not a specialist certificate.

- `[ANTI-THEATRE -- PASS]` The effective-lift language earns its place by two new exact deletion
  tests and the report-wide obstruction factorization; it is not promoted as a theorem of
  reconstruction.
- `[PAPER VERDICT]` The six-channel lower bound is a substantive section of the foundational HT
  minimal-architecture paper, not by itself a separate major paper.
- `[FIELDS VERDICT]` The lower bound is not Fields-scale.  The equivalence `(10)`, with one new
  analytic theorem transferred between genuinely different realizations, is Fields-scale.
- `[RH BOUNDARY]` The report is evidence for which realization faces must exist.  No zeta source
  lift, critical-zero identification, positivity theorem, or RH conclusion is asserted.

## Lean certificate

Lean formalizes:

- every finite reduced zero set as the exact zero set of a polynomial section of one trivial
  line;
- the explicit real conjugacy `(3)`--`(4)`;
- four-saturation of `image(A_Z)`;
- failure of four-saturation for `image(B_Z)`;
- their combined source-section/integral-realization lower-bound certificate.

New declarations:

- `prescribedFiniteZeroSection`;
- `prescribedFiniteZeroSection_eq_zero_iff`;
- `sourceSectionDivisorBlindness`;
- `realLatticeComparison_bijective`;
- `realLatticeComparison_intertwines`;
- `splitIntegralLatticeOperator_fourSaturated`;
- `coupledIntegralLatticeOperator_not_fourSaturated`;
- `integralRealificationBlindness`;
- `sourceProducerIntegralLowerBound`.

## Gates

- [x] source-section deletion killed by arbitrary finite zero sets
- [x] realification deletion killed after full real conjugacy, not only scalar invertibility
- [x] both exact witnesses Lean-formalized
- [x] each no-go paired with a positive retained channel
- [x] all seven report obstruction classes mapped to typed faces
- [x] parent realization and integral-conjugacy theories identified
- [x] anti-theatre distinction between lower bound and reconstruction conjecture made explicit
- [ ] construct `Eff_HT` for the height-one triptic class without storing the source germ
- [ ] prove its observation functor reconstructs that class modulo DA
- [ ] construct a nonlinear nonabelian effective lift
- [ ] prove two genuinely different realization functors jointly conservative
- [ ] obtain independent specialist novelty review
