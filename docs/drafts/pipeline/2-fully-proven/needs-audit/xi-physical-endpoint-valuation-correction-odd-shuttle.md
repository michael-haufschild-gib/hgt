# Physical-endpoint valuation correction and completed odd shuttle

- **ID:** `xi-physical-endpoint-valuation-correction-odd-shuttle`
- **Stage:** `2-fully-proven`
- **Type:** source-derived object / exact no-go / positive survivor / frontier bridge
- **Scientific status:** `[PAPER-PROVED] [INTERNAL-NONCOLLISION] [NOVELTY UNVERIFIED]`
  `[LEAN-PROVED SOURCE CORE] [NOT RH]`
- **Sources:** `XiAperturePoissonValuationClockShuttle.lean`,
  `XiAperturePhysicalEndpointResponseRenormalization.lean`,
  `XiCompletedApertureReflectionKernel.lean`, and
  `PrimeArchEndpointFrequencyAccretivity.lean`
- **Consumer:** `ContinuedPrimeArchPositiveFrequencyAbove`

## 1. Orientation correction forced by the source

Put `q=1/p` and `k=e+1`.  The actual fine-minus-coarse unit-to-double Poisson coefficient is

```text
rho_(p,e)=q^k-2q^(2k).
```

The existing completed kernel

```text
K_12(t)=2S(2+it)-S(1+it),   S=-xi'/xi,
```

has Euler coefficient `-rho_(p,e)`.  It is therefore the **coarsening** kernel, not the physical
refinement kernel.  Any response identification using `K_12` with the old sign is retired.

The physical endpoint retains only the ordinary-prime mode

```text
pi_(p,e)=q  if e=0,
           0  if e>0.
```

Consequently there is a unique phase-preserving depth correction

```text
eta_(p,e)=pi_(p,e)-rho_(p,e).
```

Explicitly,

```text
eta_(p,0)=2q^2,
eta_(p,e)=-q^(e+1)+2q^(2(e+1))       for e>0.          (PVC1)
```

The coefficientwise reconstruction is exact:

```text
rho_(p,e)+eta_(p,e)=pi_(p,e).                          (PVC2)
```

This is not a scalar remainder chosen after fusion; it preserves every valuation phase.

## 2. Complete fusion and trace-class size

Geometric summation gives

```text
sum_e rho_(p,e)=1/(p+1),
sum_e eta_(p,e)=1/[p(p+1)].                            (PVC3)
```

For `e>0`, `eta_(p,e)<0`; hence

```text
sum_e |eta_(p,e)|
 =2q^2+sum_(k>=2)(q^k-2q^(2k))
 <=4q^2.                                                (PVC4)
```

Therefore

```text
sum_p log(p) sum_e |eta_(p,e)| < infinity.             (PVC5)
```

The correction has an honest translation kernel

```text
E(t)=sum_(p,e) log(p) eta_(p,e)
       exp(-i(e+1)log(p)t).                             (PVC6)
```

and the source-derived physical endpoint completion is

```text
K_end(t)=S(1+it)-2S(2+it)+E(t).                        (PVC7)
```

Its finite Euler spectrum is exactly

```text
sum_p [log(p)/p] exp(-it log p),                        (PVC8)
```

while the fixed Gamma/boundary completion is retained.  At `p=2`, the first two correction
coefficients are `eta_(2,0)=1/2` and `eta_(2,1)=-1/8`; this is the cheapest falsifier for any
claimed lift.

## 3. Bounded depthwise conversion is impossible

For mesh `h`, put `r=p^(-h/2)` and `d_p=1/(p+1)`.  The true-aperture innovation feature and
fine-minus-coarse response layer are

```text
phi_(p,e)^h=d_p(1-r)^2 r^(2e),
rho_(p,e)^h=h r^(e+1)(1/2-r^(e+1)).
```

The unique diagonal multiplier is

```text
m_(p,e)^h=(h/d_p) r^(1-e)(1/2-r^(e+1))/(1-r)^2,
```

which grows as `r^(-e)`.  No bounded depthwise Hilbert intertwiner can create the response from
the positive innovation Gram.  Complete valuation fusion must occur before quadratic
compression.  At `h=2`, all response layers are nonnegative, the unique zero is `(p,e)=(2,0)`,
and their sum is the unsquared damping `1/(p+1)`.

## 4. Exact bridge to the live high-frequency gate

Let

```text
a=1/2-u,   b=1/2+u,   0<u<1/2.
```

Functional-equation reflection and Schwarz reality give

```text
S(a+it)=-conj(S(b+it)).
```

Thus the naturally clock-weighted reflected shuttle satisfies

```text
Re[b S(b+it)-a S(a+it)]
 =Re S(b+it)
 =1/2 Re xiCompletedApertureOddKernel(u,t,0).           (PVC9)
```

At a regular source point `z=t+iu`, the continued source trace obeys the exact source identity

```text
Im continuedPrimeArchSourceRelativeTrace(z)
 =1/2 Re xiCompletedApertureOddKernel(u,t,0).           (PVC10)
```

This identifies the live RH gate with the unique reflection-odd completed aperture sector.  It is
a bridge, not a sign proof.

## 5. Actual frontier conjecture

### `[CONJECTURE] [SOURCE IDENTITY, NOT AN RH REWORDING]` Physical balanced-response identification

For every finite physical prime packet `P`, sample `(PVC7)` at the actual ratio nodes
`t=log(p/q)`, weight its off-diagonal entries by the physical endpoint weights, and force its
diagonal by the physical marginals `log(p)/p`.  The resulting real symmetric balanced coupling is
conjectured to equal, coefficient by coefficient, the unit-to-double specialization of the
corrected joined response `R_M^sharp` in `(AC28)`.

This is falsifiable before any estimate: expand both sides through the finite `h,p,a,r` joining.
The first mismatch retires the conjecture.  A match would construct the previously missing
source-defined off-diagonal prime--Gamma response.

### `[CONJECTURE] [RH-PRODUCING ESTIMATE]` Cofinal signed Dirichlet upper bound

Let `C_P` be the unique balanced completed coupling after the orientation and endpoint correction
above, and let `phi_p` be the actual centered physical aperture vector.  Symmetry and the forced
row marginals `m_p=log(p)/(p+1)` give the exact pointed decomposition

```text
Q_P^ref
 =sum_p m_p ||phi_p||^2 - (1/2) E_P^ref,

E_P^ref
 =sum_(p,q) C_P^ref(p,q) ||phi_p-phi_q||^2.             (PVC11)
```

The distance term alone is forbidden: it loses the common mode identified by HTGeometry.  The
marginal term in `(PVC11)` is the required anchor.

For the actual cofinal physical packets `P_M`, conjecture

```text
E_(P_M)^ref <= C_(A,rho) log(M)^B / M.                  (PVC12)
```

The coupling in `(PVC12)` is indefinite, so this is not positivity or a generic Dirichlet-form
bound.  Subject to the coefficient identification, `(PVC12)` gives the missing reverse response
inequality in `(HGS29c)` because the anchored marginal term already agrees with the physical
baseline up to `(PVC5)`.  This is the exact new analytic estimate to attack; unlike `(PVC10)`, it
is not an RH-equivalent sign copied into new notation.

### `[CONJECTURE] [RH-FACING PRODUCER]` Height-fibered odd-sector conormal domination

After the coefficient identity above is established, form the source-selected three-node
fine-minus-coarse packet before Gram compression and before taking any depth/resolution diagonal.
On every height fiber above the unconditional central band, its completed prime--Gamma
Pontryagin realization is conjectured to have:

1. the canonical Gamma corona conormal as its unique negative line;
2. a positive two-plane obtained contractively from the cubic-normalized true-aperture innovation
   after complete valuation fusion;
3. source-side domination of the positive exterior area by the Gamma conormal square.

Clause 3 is proposed as a mechanism for `(PVC12)`, not as a substitute statement of the target
sign.  If it cannot produce the explicit signed Dirichlet bound, retire it as architecture
theatre.

This conjecture is to be killed unless the Gamma conormal of one explicit finite source packet
matches the packet's unique negative line.  It is also killed by rational-quartet invariance,
finite-prefix determination, a zero joint annihilator, or any construction obtained by factoring
the target matrix after the fact.

## Anti-theatre verdict

- `(PVC1)`--`(PVC10)` are exact source deductions and may be formalized unconditionally.
- Generic Pontryagin factorization, determinant matching, Poisson signatures, and the final
  high-frequency sign are not discoveries by themselves.
- The possible new scientific content is the **distinguished source identification and estimate**:
  the actual joined response must produce the forced correction and satisfy `(PVC12)` before
  target compression.
- Do not claim RH progress until one of those source identifications is proved and the resulting
  inequality reaches `ContinuedPrimeArchPositiveFrequencyAbove`.

## Lean plan

`XiPhysicalEndpointValuationCorrectionOddShuttle.lean` proves `(PVC1)`--`(PVC6)`, the
coefficientwise reconstruction, the clocked fused remainder, absolute convergence on the full
prime-by-valuation diagram, the corrected completed endpoint kernel, and `(PVC9)`--`(PVC10)`.
`XiCompletedBalancedResponseDirichletDecomposition.lean` proves the generic pointed identity and
its source-specific specialization `(PVC11)`.  Both direct leaves pass `lake env lean`.

The two conjectures remain paper-level until their finite source coefficient comparison closes.
