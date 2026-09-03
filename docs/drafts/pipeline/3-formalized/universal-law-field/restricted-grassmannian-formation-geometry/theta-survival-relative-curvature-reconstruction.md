# Theta-survival relative curvature reconstruction

- **ID:** ULF-TSRC-001
- **Stage:** 3-formalized
- **Type:** unconditional pre-divisor relative-metric and reconstruction theorem
- **Parents:** ULF-TM6H-001, ULF-PHSF-001, ULF-PHIN-001
- **Surviving RH edge:** identify this source-formed relative curvature with the completed Xi
  boundary curvature by one pre-divisor same-boundary law; scalar trace comparison is insufficient.

## 1. Higher-law interpretation

The universal metric anomaly is not one divergent scalar to subtract. Literal theta formation
produces one open transport `C`, hence two canonical defect metrics: the metric lost when history
enters `C` and the metric lost when it leaves `C`. Each metric has infinite trace. Their relative
displacement is nevertheless positive, nuclear, integral, and equivalent to the full exit history
of the prime-mixed object `mathsf T`.

Thus completion data live naturally as a **pair of non-nuclear metrics with nuclear relative
curvature**, not as one absolute trace-class operator. This is the source-side mechanism required
by the relative-completion programme; no zero, divisor, ordinate, or RH premise occurs.

## 2. Forced incoming and outgoing metrics

By ULF-TM6H-001 and ULF-PHSF-001,

```text
m_n=105/[(2n+3)(2n+5)(2n+7)],
r_n=m_(n+1)/m_n=(2n+3)/(2n+9),
C e_n=sqrt(r_n)e_(n+1).                              (TSRC.1)
```

Define on `ell2(Nat)`

```text
A_minus=I-C* C,
A_plus =I-C C*,
K=A_plus-A_minus=C* C-C C*=[C*,C].                  (TSRC.2)
```

These are not chosen regulators. `A_minus` and `A_plus` are the two defect metrics canonically
attached to the same theta-formed one-sided transport.

On the standard basis,

```text
A_minus e_n = 6/(2n+9) e_n,
A_plus  e_0 = e_0,
A_plus  e_n = 6/(2n+7) e_n       (n>=1).             (TSRC.3)
```

Both operators are positive and compact because their diagonal coefficients are nonnegative and
tend to zero. Neither is Schatten-one because each tail contains a positive constant multiple of
the harmonic series.

## 3. Relative curvature theorem

**Theorem TSRC-A.** `K` is positive and Schatten-one, with diagonal curvature law

```text
kappa_0=1/3,
kappa_n=12/[(2n+7)(2n+9)]          (n>=1),
K e_n=kappa_n e_n.                                  (TSRC.4)
```

Moreover

```text
Tr K=sum_n kappa_n=1,
||K||_1=1,
||K||=1/3,
Tr K=-ind C=Tr mathsf T.                             (TSRC.5)
```

**Proof.** At grade zero, `C C* e_0=0` and `C* C e_0=r_0e_0`, so
`kappa_0=r_0=1/3`. For `n>=1`,

```text
kappa_n=r_n-r_(n-1)
 = (2n+3)/(2n+9)-(2n+1)/(2n+7)
 = 12/[(2n+7)(2n+9)]>0.
```

Hence `K>=0`. Partial traces telescope:

```text
sum_(n=0)^N kappa_n=r_N -> 1.
```

Therefore `K` is positive Schatten-one with trace and trace norm one. Formula `(TSRC.4)` is
strictly decreasing after its zeroth term, so its operator norm is `1/3`. ULF-PHSF-001 gives
`ind C=-1`; ULF-PHIN-001 gives `Tr mathsf T=1`. This proves `(TSRC.5)`. QED.

The key point is relative: `Tr A_minus=Tr A_plus=infinity`, but their canonically paired
difference has finite integral trace. No scalar counterterm was inserted.

## 4. Flux--curvature reconstruction

Write the exit law carried by `mathsf T` as

```text
w_n=m_n-m_(n+1),
sum_n w_n=1.                                         (TSRC.6)
```

**Theorem TSRC-B.** The probability laws `w=(w_n)` and `kappa=(kappa_n)` determine each other
exactly.

From exit flux to relative curvature,

```text
m_n=sum_(j>=n) w_j,
r_n=m_(n+1)/m_n,
kappa_0=r_0,
kappa_n=r_n-r_(n-1)             (n>=1).              (TSRC.7)
```

From relative curvature to exit flux,

```text
r_n=sum_(j=0)^n kappa_j,
m_0=1,
m_n=product_(j<n) r_j,
w_n=m_n(1-r_n).                                      (TSRC.8)
```

**Proof.** The first line of `(TSRC.7)` is the exit telescope. The second is the definition of
the survival ratio, and `(TSRC.4)` is its first difference. Conversely, telescoping `(TSRC.4)`
gives the first line of `(TSRC.8)`. Iterating `m_(n+1)=r_nm_n` gives the product formula, and
`m_n-m_(n+1)=m_n(1-r_n)` gives `w_n`. QED.

Consequently additive transgression `w=-Delta m` and multiplicative relative curvature
`kappa=Delta(m_(n+1)/m_n)` are two lossless gauges of one theta survival law. Equality of their
total mass is only the degree-zero shadow; `(TSRC.7)--(TSRC.8)` retain every history grade.

## 5. Prime-mixed lift

Let `A_form` be the positive unit-aperture prime formation operator from ULF-PHIN-001, with
`Tr A_form=1` and every cross-prime entry nonzero. Put

```text
mathcal A_minus=A_minus tensor A_form,
mathcal A_plus =A_plus  tensor A_form,
mathcal K      =K       tensor A_form.               (TSRC.9)
```

Then `mathcal A_minus` and `mathcal A_plus` are compact but non-Schatten-one, whereas

```text
mathcal A_plus-mathcal A_minus=mathcal K,
mathcal K>=0,
mathcal K is Schatten-one,
Tr mathcal K=1,
||mathcal K||=||K|| ||A_form||<=1/3.                 (TSRC.10)
```

Every same-history cross-prime entry of `mathcal K` is nonzero. Its history marginal is `K`; the
history marginal of `mathsf T` is `Phi=diag(w_n)`. The reconstruction laws therefore lift to

```text
mathcal K <--> K <--> kappa <--> w <--> Phi <--> mathsf T,  (TSRC.11)
```

with prime kernel unchanged throughout. This is joint reconstruction, not equality after taking
one scalar trace.

## 6. Prediction and exact RH limitation

The theorem predicts the form of any correct completion law:

1. it must compare incoming and outgoing non-nuclear metrics before taking a trace;
2. its finite remainder must preserve cumulative filtration `r_n=sum_(j<=n)kappa_j`, not only
   total mass one;
3. it must act on prime-mixed lift `mathcal K`, because scalarization discards formation;
4. completed residual-boundary vanishing must follow from this relative comparison, not be assumed
   at a divisor.

The corpus's completed cubic formation law already has the predicted shape: two non-summable
primewise metric terms have a summable unsquared-source difference. TSRC-A explains why such
subtraction is source-native rather than an ad hoc renormalization. It does **not** identify source
curvature with cubic Xi energy. Corpus theorem
`routePPrimitiveCollisionTraceCapacityLaw_iff_riemannHypothesis` proves that demanding only the
resulting scalar capacity bound is exactly RH. A generic cyclic trace pairing or positive channel
therefore adds nothing.

The surviving theorem must construct, from literal integer/Poisson self-duality alone, a
same-boundary morphism carrying the entire filtered pair `(mathcal A_plus,mathcal A_minus)` to the
completed pair and preserving `(TSRC.7)--(TSRC.8)`. If its completed relative curvature acquired
one strict-right rank-one horizon, exhaustion of that horizon by completed cumulative reporters
would change at least one reporter. Filtered preservation would contradict that change, closing the
existing horizon endpoint and hence RH. Construction and exhaustion of this morphism remain open.

## 7. Hostile and literature audit

- Self-commutator trace formula for weighted shifts is classical; no novelty is claimed for
  `Tr[C*,C]=1` alone. Recent work extends Berger--Shaw trace formulas to weighted shifts:
  <https://arxiv.org/abs/2508.02896>.
- Traces of relative defect powers are homological indices and admit cyclic/homotopy formulations:
  <https://arxiv.org/abs/1402.0475>. Therefore calling `(TSRC.5)` a cyclic index does not produce
  missing arithmetic morphism.
- Corpus novelty is exact identification and mutual reconstruction of this relative curvature
  with literal theta Mellin-six history, prime-mixed integral--nuclear `mathsf T`, Hodge exit flux,
  and Fredholm boundary charge.
- Pure clock commutators are nonselective; prime lift and marked filtration are mandatory.
- A trace-preserving map may concentrate diffuse mass into a pure state. Total trace conservation
  cannot replace filtered reconstruction.

## 8. Formal status

Fully formalized without project axioms in:

- `GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvatureReconstruction`;
- `GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift`.

The closed capstones are
`RHTower.primeHodgeHistoryRelativeCurvature_closed` and
`RHTower.primeHodgeHistoryRelativeCurvaturePrimeLift_closed`. Together they certify
`(TSRC.2)--(TSRC.11)`: positivity and compactness of both non-Schatten-one metric terms; exact
metric difference and self-commutator identities; trace class, trace `1`, trace norm `1`, and
scalar norm `1/3`; trace/index/integral-nuclear matching; both directions of filtered
flux--curvature reconstruction; the actual normalized Stokes prime lift; nonzero same-history
cross-prime entries; exact history marginals; compact non-Schatten-one lifted metrics; and lifted
curvature norm at most `1/3`.

Verification completed with direct `lake env lean` checks and targeted `lake build` for exactly
these two modules. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
both capstones. The surviving RH edge in Section 6 remains open and is not claimed by either
formal theorem.
