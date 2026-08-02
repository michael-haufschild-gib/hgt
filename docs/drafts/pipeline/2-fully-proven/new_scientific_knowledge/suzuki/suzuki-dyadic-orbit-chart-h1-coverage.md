# The dyadic Suzuki orbit charts cover every finite aperture for \(H^1\)

- **ID:** `suzuki-dyadic-orbit-chart-h1-coverage`
- **Stage:** 2-fully-proven
- **Type:** EXACT GEOMETRIC COVERAGE / LOCAL-TO-GLOBAL SOBOLEV THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Input:** `suzuki-complementary-primitive-flux-derivative-recovery.md`

## 1. Result

Let \(u\) be supported in \([-a,a]\). Suppose the complementary-flux theorem gives

```text
exp(sigma L)F_(v,o)' in L2((0,infinity),dL)             (1)
```

for every realized paired orbit chart, for one \(\sigma>1/2\). Then

```text
u in H1(-a,a).                                          (2)
```

Only the physical endpoint charts are needed when prime \(2\) is invisible. Once prime \(2\) is
visible, finitely many dyadic valuation centers cover the compact interval.

## 2. One weighted chart gives ordinary \(H^1\)

At a center \(x_v\), one oriented chart is

```text
F_(v,+)(L)=w_v[u(x_v+exp(-L))-u(x_v)].                  (3)
```

Put \(r=e^{-L}\). Distributional differentiation gives

```text
F_(v,+)'(L)=-w_v r u'(x_v+r).                           (4)
```

Therefore

```text
integral_0^infinity exp(2sigma L)|F_(v,+)'(L)|^2dL

=w_v^2 integral_0^1
  r^(1-2sigma)|u'(x_v+r)|^2dr.                          (5)
```

Since \(\sigma>1/2\),

```text
r^(1-2sigma)>=1,       0<r<1.                           (6)
```

Thus `(1)` implies \(u'\in L^2((x_v,x_v+1))\). The negative orientation gives
\(u'\in L^2((x_v-1,x_v))\). Every fixed valuation weight \(w_v\) is positive, so division by it
costs only a finite chart-dependent constant.

## 3. Small aperture: one endpoint chart

Prime \(2\) is invisible exactly when

```text
2a<log 2.                                               (7)
```

Since \(\log2<1\), equation `(7)` gives \(2a<1\). The right endpoint center \(x=a\), with its
negative orientation, covers

```text
(a-1,a) superset (-a,a).                                (8)
```

Hence `(5)` at the physical right root already proves `(2)`.

## 4. Visible dyadic prime: lattice coverage

If prime \(2\) is visible, the valuation alphabet contains every \(k e_2\), \(k\in\mathbb Z\).
The right-root coset contains the centers

```text
x_k=a-k log2.                                           (9)
```

Their spacing is

```text
x_k-x_(k+1)=log2<1.                                    (10)
```

The open unit neighborhoods \((x_k-1,x_k+1)\) cover \(\mathbb R\): for every \(x\), choose an
integer \(k\) nearest to \((a-x)/\log2\). Then

```text
|x-x_k|<=log2/2<1.                                     (11)
```

Compactness of \([-a,a]\), or explicitly the finitely many integers satisfying

```text
-1< a-k log2+a,
a-k log2-1<a,                                          (12)
```

selects a finite subcover. Apply Section 2 in those finitely many charts and sum the local
\(L^2\) derivative bounds. This proves `(2)`. `QED`

## 5. Consequence for the finite-recurrence theorem

The earlier “one-prime finite-system interior regularity” gate was artificial. No local
pseudodifferential ellipticity or dense-seam regularity theorem is needed:

```text
full paired-orbit weighted derivative
 -> dyadic unit-chart cover
 -> global H1(-a,a).                                   (13)
```

The physical endpoint values are zero by the completed zero extension, so global \(H^1\) gives
\(H^1_0(-a,a)\).

Combined with complementary primitive-flux derivative recovery, the finite-recurrence
trace-zero theorem is reduced to exactly two source statements:

```text
construct literal completed-source paired orbit equation;
prove its physical-root value/dipole flux charges vanish. (14)
```

## 6. Hostile audit

1. **No density argument.** One visible dyadic direction with spacing \(<1\) suffices.
2. **No infinite norm sum.** Compact interval uses finitely many charts.
3. **No weight-uniformity claim.** Every selected chart has one fixed positive weight.
4. **No pointwise derivative premise.** Equation `(4)` is distributional change of variables;
   weighted \(L^2\) makes the weak derivative an \(L^2\) function.
5. **No small-aperture gap.** When \(2\) is invisible, interval itself has length \(<1\).
6. **No RH claim.** Literal source assembly, root flux matching, recurrence-infinite apertures, and
   Evans injectivity remain.

## 7. Novelty boundary

Interval covers and the logarithmic change of variables are elementary. Candidate-new
source knowledge is their exact removal of Suzuki's compact-middle regularity gate:

```text
dyadic valuation center spacing log2<1
+ unit paired physical windows
+ sigma>1/2 derivative weight
 -> global H1 with no interior regularity theorem.       (15)
```

External priority remains unaudited.

## 8. Lean target

The formal core is the real-line lattice-cover lemma `(11)` and the elementary weight inequality
`(6)`. The Sobolev change of variables requires the analytic chart infrastructure still missing
from the formal tree.

## Gates

- [x] prove one weighted paired chart gives local \(H^1\)
- [x] prove invisible-\(2\) aperture is covered by one endpoint chart
- [x] prove visible dyadic centers give a finite unit-chart cover
- [x] remove one-prime interior regularity gate
- [ ] formalize dyadic lattice-cover core in Lean
- [ ] construct literal paired source equation
- [ ] verify physical-root flux matching
- [ ] pass recurrence-infinite apertures
- [ ] prove raw Evans injectivity or whole-Connes no-go
