# The physical defect product has an exact reversal anomaly

- **ID:** `physical-defect-orientation-anomaly`
- **Stage:** 3-formalized
- **Type:** PHYSICAL-CHARACTER REVERSAL LAW / ORIENTATION NO-GO WITH POSITIVE COCYCLE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CANDIDATE NEW HT CONSEQUENCE]`
  `[PARENT FORMULA SEPARATED] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/PhysicalDefectOrientationAnomaly.lean`
- **Normalization no-go and exact gate:**
  - `formal/GaloisForLFunctions/HTGeometry/GammaPointedSourceNonEffectivity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/JointSourceRealizationConservativity.lean`
- **Unified parent:**
  `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`

## Exact theorem `[PROVED]`

For a finite source family `tau=(tau_i)_(i in S)`, define its complete physical defect product

```text
G_tau(z)=product_(i in S)(exp(tau_i z)-1).                 (1)
```

Let

```text
r=|S|,
sigma_1(tau)=sum_(i in S) tau_i.                           (2)
```

Lean proves the full reversal law

```text
G_(-tau)(z)=(-1)^r exp(-sigma_1(tau) z) G_tau(z).          (3)
```

The multiplier

```text
A_tau(z)=(-1)^r exp(-sigma_1(tau) z)                       (4)
```

is an involutive cocycle:

```text
A_(-tau)(z) A_tau(z)=1.                                   (5)
```

Thus the orientation defect under full source reversal is exactly classified by rank parity and
the first source moment.  It is not an unspecified sign problem.

The theorem now holds for the complete componentwise sign-surgery group.  For a Boolean mask
`epsilon`, let `epsilon*tau` reverse exactly the selected source components and define

```text
A_epsilon(tau;z)
 =product_i [ -exp(-tau_i z), if epsilon_i=1;
               1,              if epsilon_i=0 ].           (5a)
```

Lean proves

```text
G_(epsilon*tau)=A_epsilon(tau;z)G_tau,                     (5b)
A_(epsilon xor eta)(tau;z)
 =A_epsilon(eta*tau;z) A_eta(tau;z).                       (5c)
```

Thus `(4)` is the full-reversal specialization of a genuine source-groupoid cocycle, not merely a
one-off functional equation.

## Midpoint polarization split `[PROVED]`

The elementary identity

```text
exp(a z)-1=exp(a z/2) 2 sinh(a z/2)                        (6)
```

gives the canonical factorization

```text
G_tau(z)
 =exp(sigma_1(tau) z/2)
  product_(i in S) 2 sinh(tau_i z/2).                     (7)
```

Equation `(7)` separates two source roles:

1. `exp(sigma_1 z/2)` is the oriented first-moment character;
2. the centered `sinh` product is the self-dual curvature factor and transforms only by rank
   parity under full reversal.

This is an exact polarization split of the physical boundary, not a temporal evolution and not a
metaphorical decomposition.

## Complete orientation-blind locus `[PROVED]`

If

```text
r is even,
sigma_1(tau)=0,                                           (8)
```

then `(3)` reduces to

```text
G_(-tau)=G_tau.                                           (9)
```

The two oppositely oriented sources have the same complete analytic physical-character germ.
Therefore they also have the same:

- reduced support;
- multiplicities and all Taylor jets;
- contact filtration;
- analytic local ring quotient;
- Koszul or other functorial derived object built from `(1)`;
- topology and any invariant functorially extracted from that derived object.

This strengthens the earlier orientation-surgery no-go.  On the balanced even locus, no refinement
of the unlabelled physical defect germ can recover orientation because the analytic inputs are
literally equal.

## No-go and positive successor

```text
[NO-GO]
Orientation, source sign, or a positivity choice can be reconstructed from the unlabelled physical
defect germ, its full derived topology, or its contact filtration.
```

```text
[POSITIVE]
Full reversal carries the explicit anomaly cocycle A_tau.  A conservative theory must retain the
source orientation cover and a source-effectively normalized trivialization or polarized section
whose reporter family kills the normalized joint-fixed gauge.      (10)
```

The positive object is not “more topology.”  It is a lift of the physical germ to its source
groupoid together with equivariance under `(4)`--`(5)`.  The midpoint split `(7)` gives its first
canonical local chart.

## Bare-source correction `[PROVED NO-GO + EXACT POSITIVE CRITERION]`

The bare source does **not** canonically choose the trivialization in `(10)`.  The Gamma collision

```text
Gamma(z),  exp(2 pi i z) Gamma(z)                          (10a)
```

gives two distinct HT meromorphic germs satisfying the same unit-shift equation and the same value
at `z=1`; periodic gauges can preserve every prescribed finite jet.  Hence polarization,
completion, transport, or integral data derived only from that bare source cannot recover the
forgotten gauge.

The exact positive theorem is the joint-conservativity criterion.  For additive reporters `R_r`,

```text
Obs_R is injective
  iff K^S intersect intersection_r ker(R_r)={0}.            (10b)
```

A nonzero element of the right side is an explicit nonconservativity witness.  Multiplicatively,
the normalized solution fibre is a torsor under the source-fixed gauges preserving the chosen
normalization, and reconstruction holds exactly when that torsor is nonempty with trivial
stabilizer.

Therefore the anomaly cocycle supplies a line/torsor, not a canonical point of it.  A conservative
polarization exists only on the **source-effectively normalized stratum** where the chosen
reporters or asymptotic/positivity conditions kill the residual fixed gauge.  See
`../../5-failed/universal-bare-source-effectivity-reconstruction.md` and
`../not_new_scientific_knowledge/joint-source-realization-common-kernel-criterion.md`.

## Meaning for any potential RH proof

This theorem does not assert that the zeta source lies on the balanced even locus.  It gives a hard
conservativity test.

Any RH strategy whose sign or positivity conclusion factors only through a determinant, zero set,
derived characteristic object, spectral support, or completed topology built functorially from an
unlabelled physical defect germ cannot distinguish reversal twins satisfying `(8)`.  Such a
strategy must do all of the following additional work:

1. prove source-purely that the zeta realization avoids the blind locus and compute its anomaly;
2. construct an independently meaningful normalization/reporter family, not data functorially
   derived from the same bare source;
3. calculate its joint-fixed common kernel and prove criterion `(10b)`;
4. construct the distinguished polarized section only on the resulting normalized stratum.

Critical zeros alone cannot supply that choice: a degeneracy support is invariant data, whereas
orientation is equivariant lift data.  Therefore a sign-sensitive RH argument cannot be completed
by topology or spectral support alone, even if that topology is fully derived.

## Bold conjecture

> **[CONJECTURE -- NORMALIZED POLARIZATION AS ANOMALY TRIVIALIZATION.]**  Every
> source-effectively normalized constrained hypertranscendental system carries an anomaly torsor
> over its source constraint groupoid.  A reporter family `R` cuts out the normalized stratum, and
> polarization is a coherent trivialization of the anomaly torsor precisely when the typed
> analogue of `K^S intersect intersection ker R={0}` holds.  Positivity is a distinguished
> effective section in the positive real form of that trivialized line.  Monodromy and
> noncanonical boundary-condition obstructions are failures of the normalized local
> trivializations to glue; bornological nonattainment is failure of the glued section to lie in
> the critical effective image.

The conjecture makes no universal bare-source reconstruction claim.  It is falsified if a natural
normalized HT source satisfies the common-kernel gate but still has inequivalent compatible
polarized lifts, or if a claimed conservative realization leaves a nonzero joint-fixed gauge
invisible.

For a future zeta realization, critical zeros would be the self-dual degeneracy support of the
distinguished anomaly-trivialized section.  This is a research hypothesis, not an RH theorem.

## Where to look next

1. **Normalized anomaly torsor.**  Build the line/torsor classified by the proved componentwise
   cocycle `(5c)` over the source-effectively normalized stratum.  Its objects are reporter-compatible
   trivializations, not a bare-source canonical choice.
2. **All-degree cumulant spectrum.**  Divide `(7)` by its leading monomial and compute the logarithm
   of the centered factor.  The predicted jet spectrum consists of the first moment and even power
   sums, with odd moments above degree one absent.
3. **Blindness classification.**  Classify exactly when two finite source multisets have identical
   physical defect germs.  The expected finite invariant is product, first moment, and the multiset
   of squared source weights.
4. **Polarized lift and kernel gate.**  Construct the anomaly torsor inside the six-channel
   fracture object, compute the reporters on its joint-fixed gauge, prove their common kernel
   trivial, and only then compare the normalized lift with the osculation/effectivity bifiltration.
5. **Natural HT realization.**  Compute `(4)` for irrational elliptic Gamma, Barnes/multiple-sine,
   and theta/Fay source systems before using it as a zeta pressure test.

## Novelty and anti-theatre gate

The identity `(6)`, reflection parity of `sinh`, finite-difference symbols, and exponential
polynomial functional equations are parent mathematics.  Dowker's central-difference treatment
(`https://arxiv.org/abs/1305.0500`) is adjacent evidence that the `sinh` factorization itself is not
a novelty claim.

The candidate-new content is the HT consequence: the complete physical-character germ has a
source-reversal cocycle with an exact blind locus, forcing polarization to live as normalized
source-equivariant lift data outside every functorial derived refinement of the germ.  The Gamma
collision forbids promoting this lift to a bare-source canonical choice.  Targeted searches found
central-difference and exponential-polynomial parent theories but no equivalent HT source theorem.
This is negative search evidence, not priority certification.  Fields-scale significance requires
the source-groupoid extension and a natural special-function realization.

## Lean certificate

Lean proves unconditionally:

- the midpoint factorization `(6)`;
- the complete finite-product split `(7)`;
- the exact reversal anomaly `(3)`;
- the involutive cocycle identity `(5)`;
- parity reduction for balanced sources;
- complete reversal blindness on the balanced even locus.

Companion Lean modules prove the concrete Gamma source/pointing collision and the exact additive
joint-fixed common-kernel criterion `(10b)`.

The exact-module build passed while the object was missing, and direct touched-file checks pass
after the strengthened midpoint/cocycle additions.  No full build was run.

## Gates

- [x] exact analytic reversal law proved
- [x] strong no-go paired with explicit positive cocycle
- [x] complete blind locus isolated
- [x] midpoint polarization split proved
- [x] cocycle identity proved
- [x] componentwise sign-surgery action proved
- [x] full source-groupoid cocycle law proved
- [x] bare-source canonical-trivialization claim rejected
- [x] exact joint-fixed common-kernel gate incorporated
- [x] Lean formalization unconditional
- [x] parent formula separated from HT consequence
- [x] RH kept as pressure test only
- [ ] full physical-germ equality classification proved
- [ ] normalized anomaly torsor and reporter action constructed
- [ ] natural HT special-function realization computed
- [ ] independent external priority audit completed
