# Zero trace does not put Suzuki's Carleman cutoff port in any positive Gamma strip

- **ID:** `suzuki-carleman-flat-port-weighted-strip-barrier`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SHARP COUNTEREXAMPLE / E1--E3 COUPLING THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Input:** `suzuki-wiener-cutoff-closed-graph-relation.md`

## 1. Result

Ordinary closedness of the global Wiener/cutoff relation and vanishing physical half-log trace do
not imply the weighted Carleman estimate needed for spatial \(H^1\).

Let

```text
F(L)=exp(-sqrt(L)),      L>=1,                            (1)
u(s)=F(-log s),          0<s<=exp(-1),                   (2)
```

with a smooth harmless cutoff away from \(s=0\).  Then:

```text
sqrt(L)F(L)->0,                                           (3)
u notin H1(0,1),                                         (4)
```

but \(u\in L^2\) and has zero half-log trace.  Let the one-sided cross-boundary Carleman response be

```text
(S u)(t)=integral_0^1 u(s)/(s+t) ds.                     (5)
```

At \(t=e^{-L}\), after subtracting its unique endpoint constant,

```text
(S u)(e^-L)-integral_0^1 u(s)/s ds
 =-2 sqrt(L)exp(-sqrt(L))(1+o(1)),                       (6)
```

and its logarithmic derivative satisfies

```text
d/dL [(S u)(e^-L)]
 =exp(-sqrt(L))(1+o(1)).                                 (7)
```

Consequently, for every \(\sigma>0\),

```text
exp(sigma L)d/dL[(S u)(e^-L)] notin L2(dL).              (8)
```

In particular no positive Gamma strip, let alone one with \(\sigma>1/2\), follows from:

```text
u in L2
+ zero half-log trace
+ Carleman L2 boundedness
+ subtraction of the low-frequency endpoint constant.                   (9)
```

Applied to the exact cutoff relation, this kills the proposed standalone implication

```text
zero trace -> weighted decay of P a_a(D)(1-P)c.          (10)
```

The remaining theorem must use the full source-return condition:

```text
Ev(c)+u_low=0 on the exterior
+ interior completed zero equation
+ two oriented root ports
 -> weighted Carleman decay.                              (11)
```

Thus `SUZUKI-TRACE-ZERO-H1` and two-port Evans return injectivity are not sequential gates.  They
are one coupled boundary-relation theorem.

## 2. Zero trace and failure of spatial \(H^1\)

Equation `(3)` is immediate.  Since \(s=e^{-L}\),

```text
u'(s)
 =exp(L) exp(-sqrt(L))/(2sqrt(L))                        (12)
```

up to sign.  Therefore

```text
integral_0 |u'(s)|^2 ds
 =1/4 integral^infinity
      exp(L-2sqrt(L))/L dL
 =infinity,                                               (13)
```

proving `(4)`.  On the other hand,

```text
integral_0 |u(s)|^2 ds
 =integral^infinity exp(-2sqrt(L))exp(-L)dL<infinity.    (14)
```

The example is therefore in the ordinary completed boundary class but outside the raw spatial
derivative domain.

## 3. Exact log-coordinate Carleman formula

Put \(t=e^{-L}\), \(s=e^{-v}\).  Ignoring the smooth compact transition at \(v=1\), which
contributes \(O(e^{-L})\) with every \(L\)-derivative, `(5)` becomes

```text
B(L):=(S u)(e^-L)
 =integral_1^infinity
    F(v)/[1+exp(v-L)] dv+O(exp(-L)).                     (15)
```

The endpoint counterterm is

```text
B_infinity
 =integral_1^infinity F(v)dv+constant_from_cutoff.       (16)
```

For the uncut model,

```text
integral_L^infinity exp(-sqrt(v))dv
 =2(sqrt(L)+1)exp(-sqrt(L)).                             (17)
```

Indeed set \(y=\sqrt v\), so the integral is
\(2\int_{\sqrt L}^\infty y e^{-y}dy\).

Now

```text
B_infinity-B(L)
 =integral F(v)
    exp(v-L)/[1+exp(v-L)] dv+O(exp(-L)).                 (18)
```

The range \(v\ge L\) equals the tail `(17)` up to an \(O(F(L))\) logistic transition.  On
\(v<L\), write \(v=L-y\).  The factor in `(18)` is at most \(e^{-y}\), while

```text
F(L-y)/F(L)
 =exp[sqrt(L)-sqrt(L-y)]
 <=exp(C y/sqrt(L))                                      (19)
```

for \(0\le y\le L/2\).  That part is \(O(F(L))\); the remaining \(v\le L/2\) part is
\(O(e^{-L/2})\).  Combining with `(17)` gives `(6)`.

## 4. Derivative asymptotic

Differentiate `(15)`:

```text
B'(L)
 =integral_1^infinity F(v)k(v-L)dv+O(exp(-L)),           (20)

k(y)=exp(y)/[1+exp(y)]^2.                                (21)
```

The logistic kernel is positive, exponentially decreasing at both ends, and

```text
integral_(-infinity)^infinity k(y)dy=1.                 (22)
```

After \(y=v-L\),

```text
B'(L)/F(L)
 =integral_(1-L)^infinity
    [F(L+y)/F(L)]k(y)dy+o(1).                            (23)
```

For fixed \(y\), the ratio in `(23)` tends to one.  On \(|y|\le L/2\), the mean-value theorem gives

```text
F(L+y)/F(L)
 <=exp(C|y|/sqrt(L)),                                    (24)
```

which is dominated by an integrable exponential after increasing \(L\).  The \(y\ge L/2\) tail is
bounded by the positive exponential tail of \(k\).  For \(1-L\le y\le-L/2\), use
\(k(y)\le e^y\); even the maximal ratio \(F(1)/F(L)\) leaves an exponentially small bound.
Dominated convergence in `(23)` and `(22)` prove `(7)`.

For every \(\sigma>0\),

```text
exp(2sigma L)|B'(L)|^2
 =exp(2sigma L-2sqrt(L))(1+o(1)),                        (25)
```

whose integral diverges.  This proves `(8)`.

## 5. Sharp meaning for Suzuki

The principal interior block of the exact cutoff defect

```text
-P log<D>(1-P)c                                         (26)
```

is `(5)` at each endpoint.  The bounded \(q_a(D)\) commutator does not improve `(8)`, and the
low-frequency theorem removes only `(16)`.  Hence Carleman boundedness and the two scalar
counterterms are exactly insufficient at the required scale.

The example does **not** satisfy Suzuki's completed zero equation or exterior support return.
That is the point: any proof of `(10)` which uses only the local trace, operator boundedness, or
the cutoff graph domain is false.  The additional equations in `(11)` are load-bearing.

The correct coupled target is now:

```text
SUZUKI-CLOSED-TWO-PORT-RETURN

Every graph vector in the exact closed Wiener/cutoff relation
which
  (a) evaluates to zero on the exterior after the analytic low port,
  (b) solves the completed zero equation on the interior, and
  (c) has both physical half-log traces zero,
has a Carleman port in some Gamma strip sigma>1/2.        (27)
```

Equation `(27)` implies \(H^1_0\) through the existing weighted Gamma coercivity theorem.  It also
contains the low/high two-port matching data, so it cannot be proved independently of E3.

## 6. Hostile audit

1. **Not a zero-mode counterexample.**  The theorem falsifies a proposed inference, not Suzuki
   injectivity or RH.
2. **Counterterm retained.**  The constant `(16)` is subtracted before `(6)`--`(8)`.
3. **Stronger than inverse-log grades.**  The profile is flat beyond every inverse-log power, so
   no finite or all-order corona coefficient detects it.
4. **Exact physical scale.**  Failure is measured by the required
   `exp(sigma L)d/dL` norm, not unweighted `H1(dL)`.
5. **No carrier theatre.**  The surviving hypothesis `(27)` explicitly uses exterior evaluation
   and completed-source return, the two facts absent from the counterexample.

## 7. Novelty boundary

Slowly varying functions, the Carleman operator, and the logistic approximate identity are
classical.  Candidate-new source knowledge is the exact use of the flat profile to locate the
failure of Suzuki's now-explicit cutoff port:

```text
zero corona trace
+ exact low counterterm
+ Carleman graph boundedness
 does not imply any positive Gamma strip,
so completed regularity and Evans return are one gate.   (28)
```

This is not a restatement of the earlier generic principal-Volterra flat example: `(6)`--`(8)`
compute the response of the literal cross-boundary operator newly isolated by the closed graph
relation.

## 8. Lean status

Formalized unconditionally:

```text
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortProfile.lean
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortChart.lean
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortResponse.lean
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortAsymptotic.lean
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortBarrier.lean
formal/GaloisForLFunctions/RHTower/SuzukiCarlemanFlatPortGap.lean
```

`(3)` is `tendsto_sqrt_mul_flatPortProfile`; `(17)` is `integral_Ioi_flatPortProfile`, from the
closed antiderivative `-2(√v+1)e^{-√v}`; `(14)` and `(13)` are `integrableOn_flatPortValueDensity`
and `not_integrableOn_flatPortDerivativeDensity` (the second because
`L - 2√L - log L → ∞`); `(15)`, `(20)`, `(21)` are `carlemanLogResponse`,
`hasDerivAt_carlemanLogResponse` (differentiation under the integral sign against the `1/4`
majorant) and `logisticKernel`; `(22)` is `integral_logisticKernel`; `(7)` is
`tendsto_carlemanLogResponseDeriv_div`, by dominated convergence in the shifted chart with
majorant `e^{-|y|/2}`; `(6)` is `tendsto_carlemanLogResponse_gap`, from the tail identity
`B_∞ - B(L) = ∫_{M>L} B'` and the tail-ratio comparison; `(8)`/`(25)` is
`not_integrableOn_weighted_carlemanLogResponseDeriv`, for every `σ > 0` and every ray.  Every
theorem audits to `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] construct zero-trace non-`H1` physical profile
- [x] compute exact Carleman log-coordinate formula
- [x] subtract the unique endpoint counterterm
- [x] prove flat Carleman remainder asymptotic
- [x] prove derivative asymptotic by logistic approximate identity
- [x] exclude every positive Gamma strip
- [x] formalize `(3)`, `(6)`--`(8)`, `(13)`--`(14)`, `(17)`, `(20)`--`(22)` unconditionally in Lean 4
- [x] merge trace-zero regularity with exterior two-port return
- [ ] prove `SUZUKI-CLOSED-TWO-PORT-RETURN`
- [ ] prove completed Evans injectivity
- [ ] RH

