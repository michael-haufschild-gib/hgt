# Gamma-sewn synchronized-lcm contraction and causal connected endpoint lift

- **ID:** `gamma-sewn-synchronized-lcm-contraction`
- **Stage:** `1-in-progress`
- **Type:** `NEW SOURCE OPERATOR + POSITIVE THEOREMS + CLOSED NO-GO + RH-BEARING CONJECTURE`
- **Scientific status:** `[CORPUS-NEW] [SEARCH-NONCOLLISION] [NOT A PRIORITY CLAIM] [NOT RH]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnSynchronizedLcmContraction.lean`
- **Canonical current verdict:** `docs/reports/rh-current-state.md`

## Anti-theatre verdict

Known parent theories include Hadamard products, multiplicative Hankel/Hilbert operators,
Dirichlet-series multiplier spaces, Cauchy kernels, and lcm semilattice matrices.  They are not
discoveries here.  Exact corpus and web searches found no occurrence of the combined
Gamma-sewn/common-valuation-depth/Rees/root-density construction, but that is only search
noncollision.

The first proposed RH lift failed its honest response test.  The insertion cocycle was only path
independence of a diagonal weighting; causal prime order is fixed, and the cocycle says nothing
about the joined `delta/beta` response.  Exact physical endpoint recovery at every positive
aperture is false already on singleton supports.

The surviving scientific content is:

1. a canonical all-squarefree common-depth completion interpolating the existing singleton ray and
   pair Gram kernel;
2. a simultaneous all-grade Hilbert--Schmidt Rees boundary;
3. bounded scalar recovery of literal CRT density at the boundary;
4. an exact positive-aperture quadratic response defect;
5. an exact rank separation: the Rees pair layer is Cauchy-full-rank, while scalar recovered
   density is product-rank-one;
6. the forced shape of the next object: a vector-valued connected endpoint fiber that keeps both
   bounded density resolution and the actual hypertranscendental source rank.

## Closed source construction

For prime `p`, aperture `x>0`, and depth `e`, write

```text
B_x(p,e)=C_(x,p)/(p+1) * (1-p^(-x))p^(-xe).
```

For nonempty squarefree support `P`, define

```text
kappa_x(P)=sum_(e>=0)product_(p in P)B_x(p,e)
 =product_(p in P)[C_(x,p)/(p+1)(1-p^(-x))]
    /(1-product_(p in P)p^(-x)).                         (SL1)
```

Then

```text
kappa_x({p})=C_(x,p)/(p+1),
kappa_x({p,q})=the existing Gamma-sewn pair kernel.      (SL2)
```

If `r_x(P)=product_(p in P)p^(-x)`, insertion has gain

```text
g_x(p;P)=C_(x,p)/(p+1)
 *(1-p^(-x))(1-r_x(P))/(1-p^(-x)r_x(P)),                (SL3)
```

and

```text
g_x(p;P)g_x(q;P union {p})
 =g_x(q;P)g_x(p;P union {q}).                            (SL4)
```

`(SL1)`--`(SL4)` are Lean-proved.  The exact module build passes; the principal declaration axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Rees boundary and Hilbert theorem

For `r=|P|>0`,

```text
kappa_x(P)=x^(r-1)(A(P)+o(1)),
A(P)=product_(p in P)[log p/(p+1)] / sum_(p in P)log p.  (SL5)
```

This is a leading asymptotic, not yet an analytic-order theorem through `x=0`.

Define

```text
kappaHat_x(P)=x^(1-r)kappa_x(P),
m(p)=max(1,log p)/(p+1),
M(P)=product_(p in P)m(p).                               (SL6)
```

The dependency-closed paper proof gives

```text
0<kappaHat_x(P)<=M(P)<1,
sum_(P finite, P nonempty)M(P)^2<infinity,               (SL7)
```

uniformly in `x>0`.  Hence the diagonal on nonempty squarefree-support `l2` is uniformly
Hilbert--Schmidt and converges in Hilbert--Schmidt norm to `diag(A(P))`.

Limits of scope:

- the operator is not trace class; singleton absolute sums diverge;
- `D tensor I` on an infinite endpoint/color/jet fiber is not Hilbert--Schmidt;
- the scalar coefficients are differentially algebraic and do not replace
  `XiTransversePrimeSourceHilbertMetric` or Xi-shift hypertranscendence.

## Bounded boundary recovery

For physical root density

```text
theta_h(P)=product_(p in P)nu_h(p)/p,
R_h(P)=sum_(p in P)log p
 *product_(p in P)[nu_h(p)(p+1)/(p log p)],              (SL8)
```

one has

```text
R_h(P)A(P)=theta_h(P),
sup_(h,P nonempty)R_h(P)<infinity.                       (SL9)
```

The identity is Lean-proved.  The uniform bound is paper-proved by a finite-prime/tail split.  It
is bounded recovery of the low density coordinate only; it is not a contraction and does not
recover endpoint cells, aliases, `delta_h`, or `beta_h`.

The Boolean vacuum must be fixed separately because the logarithmic formula gives `R_h(empty)=0`
while `theta_h(empty)=1`.

## Closed no-go 1: positive-aperture exactness

Let

```text
Theta_(x,h)(empty)=1,
Theta_(x,h)(P)=R_h(P)kappaHat_x(P) for P nonempty.       (SL10)
```

On a singleton,

```text
Theta_(x,h)({p})=theta_h({p})C_(x,p),
theta_h({p})-Theta_(x,h)({p})
 =theta_h({p})(1-p^(-x))^2G_(x,p)>0.                    (SL11)
```

Thus no positive aperture reproduces the literal physical low coefficient.  The Lean module proves
the exact defect, its quadratic factorization, and strict positivity on every nonempty finite
singleton packet.

For the honest `{2,3,5}`, `D=5` response packet, the physical cutoff and zero-mode terms cancel and
leave

```text
FCRJ_(x,h)-FCRJ_h
 =J_h sum_(p in {2,3,5})theta_h(p)(C_(x,p)-1).           (SL12)
```

This is nonzero for `x>0` when `J_h>0`.  The former exact finite-aperture conjecture is retired.

## Closed no-go 2: scalar recovery destroys coupled rank

The pair boundary is

```text
A({p,q})=[log p/(p+1)][log q/(q+1)]/(log p+log q).       (SL13)
```

For distinct anchors `p1,p2` and variables `q1,q2`, its `2x2` determinant is a nonzero weighted
Cauchy determinant with numerator

```text
(log p1-log p2)(log q1-log q2).                          (SL14)
```

By contrast,

```text
theta({p,q})=theta({p})theta({q})
```

and every corresponding `2x2` minor is zero.  Lean proves both the exact Cauchy factorization and
the rank-one physical determinant.  Therefore scalar density recovery cannot be the full joined
carrier: it discards precisely the first nonfactorizing squarefree correlation.

**Positive survivor.**  A viable recovery must be vector-valued.  One coordinate supplies the
bounded scalar density `(SL9)`; at least one connected coordinate must retain `(SL14)` and the
actual transverse Xi prime-source evaluation rank.

## Exact surviving response identity

Insert the aperture on the response side, not into the Boolean source vector.  Let
`Omega_(x,h)(e_P)=Theta_(x,h)(P)` and `delta_(x,h)=beta_h-J_h Omega_(x,h)`.  Universal stopped
joining gives

```text
FCRJ_(x,h)-FCRJ_h
 =J_h(Omega_(x,h)-omega_h)(P_Dv_z)
 =J_h sum_(l|Q_z,l<=D)mu(l)[Theta_(x,h)(l)-theta_h(l)].  (SL15)
```

All physical-height middle/high and zero-mode-switch errors cancel.  Hilbert--Schmidt convergence
does not by itself bound `(SL15)` because `P_Dv_z` has growing Boolean support norm.

## Selected conjecture: causal connected Cauchy-fiber gap

Use the literal source fiber

```text
U_(l,h)(k)=S_(l,h)(k)/nu_h(l),
E_(h,H)(l,k)=hat(W)_h(k/l)U_(l,h)(k),                    (SL16)
```

with the existing `k!=0`/`k in Z` switch at `l=H`, the existing causal anchors, and the existing
future Bernoulli weights.

**CCCFG conjecture.**  After complete future dressing and low/high joining, the connected part of
`(SL16)` extends boundedly on the closed causal first-crossing subspace of the synchronized
Cauchy-Rees support space; it retains every nondegenerate pair minor `(SL14)` and contains the
cofinite-deletion transverse Xi shift-jet Hilbert metric.  Its physical amplitude is

```text
O(M^(-1/2)log(M)^B),                                    (SL17)
```

uniformly in height and cutoff, and its response converges locally uniformly to
`continuedPrimeArchSourceRelativeTrace`.

The squared estimate from `(SL17)` gives the required `O(M^(-1)polylog(M))` endpoint energy and
discharges the one-sided FCRJ saturation gate.  The conjecture is source-specific and falsifiable:
its coefficients are fixed by `S`, `W`, causal order, future weights, and the Rees Cauchy metric.
It is not allowed to assume passivity, positivity, or an RH-equivalent endpoint.

## Immediate falsifiers

1. Compute the literal joined pair-fiber minors for two anchors and two future primes.  Rank-one
   factorization kills CCCFG.
2. Recompute `{2,3,5}` with the endpoint-frequency fiber and exact zero-mode switch.  Any extra
   density or vacuum term kills the definition.
3. Test boundedness only on the causal first-crossing subspace.  Coefficientwise boundedness on the
   whole basis is already false because normalized inactive endpoint cells grow like `l/H`.
4. Exhibit the actual Xi transverse shift-jet evaluation packet inside the connected fiber.  A
   scalar DA aperture packet fails this gate.
5. Only after 1--4, attack `(SL17)`.  A loss larger than `M^(-1/2)` in amplitude retires the route.

## Gates

- [x] All-lcm source and geometric collapse.
- [x] Singleton and pair collision with the corpus.
- [x] Flat insertion law.
- [x] Paper proof of the all-grade Hilbert--Schmidt majorant.
- [x] Exact Lean recovery identity.
- [x] Paper proof of uniform scalar recovery.
- [x] Exact positive-aperture singleton no-go in Lean.
- [x] Exact Rees-Cauchy versus product-density rank separation in Lean.
- [x] Honest response-side correction and `{2,3,5}` falsifier on paper.
- [x] Direct leaf check, exact module build, and principal axiom audit.
- [ ] Lean proof of the Rees limit, global square-summability, and uniform recovery bound.
- [ ] Literal connected endpoint-fiber definition and pair-minor falsifier.
- [ ] Causal-subspace boundedness.
- [ ] `M^(-1/2)` connected amplitude estimate.
- [ ] Continued-source convergence.
- [ ] RH.
