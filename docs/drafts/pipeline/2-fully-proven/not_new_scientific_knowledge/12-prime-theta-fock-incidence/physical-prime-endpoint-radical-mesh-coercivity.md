# Physical prime-endpoint radical and sharp mesh coercivity

- **ID:** `physical-prime-endpoint-radical-mesh-coercivity`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) [SOURCE-SPECIFIC POSITIVE SURVIVOR] [BRIDGE]`
- **Source:** `high-grade-sieve-survivor-one-mode-reduction.md` `(HGS26)`--`(HGS29)` and
  `fcrj-corrected-response-saturation-law.md` `(RS1)`--`(RS8)`
- **Statement:** For the actual clipped ordinary-prime interval source, the prime endpoint
  carrier vanishes exactly when there is no active prime.  Its energy has a sharp local lower
  bound at every endpoint jump, so corrected response saturation is strictly impossible at every
  nonempty finite aperture.

## Goal

Strengthen the generic Hilbert-square survivor from nonnegativity to a theorem using the exact
physical interval source.  The theorem must classify the radical and quantify its local stability
without inserting any zero information or RH-strength estimate.

## Physical packet

Assume

```text
0<c=log(K/M)<A.
```

For every active ordinary prime `p`, put

```text
alpha_p=max(0,log(M/p)),
beta_p=min(A,log(K/p)),
w_p=log(p)/p,

k_p=1_(alpha_p,beta_p]-(beta_p-alpha_p)/A.
```

Thus `0<=alpha_p<beta_p<=A`, and the ordinary-prime endpoint carrier exposed by `(HGS29)` is

```text
P_M=sum_p w_p k_p.                                      (PE1)
```

For `0<=t<=A`, define the centered initial-interval vector

```text
H_t=1_(0,t]-t/A.
```

Then `H_0=H_A=0` and

```text
k_p=H_(beta_p)-H_(alpha_p).                             (PE2)
```

Let `B_M` be the finite set of distinct interior endpoints and define the signed endpoint jump

```text
j_M(t)=sum_(p:beta_p=t)w_p-sum_(p:alpha_p=t)w_p.        (PE3)
```

Equations `(PE1)`--`(PE3)` give

```text
P_M=sum_(t in B_M)j_M(t)H_t.                            (PE4)
```

## Brownian endpoint Gram law

Direct integration gives

```text
<H_s,H_t>=G_A(s,t)=min(s,t)-s t/A,                     (PE5)

||P_M||^2=sum_(s,t in B_M)j_M(s)j_M(t)G_A(s,t).         (PE6)
```

For distinct points in `(0,A)`, the vectors `H_t` are linearly independent: order the points and
read the successive jumps of a linear combination.  Hence the Brownian-bridge Gram matrix in
`(PE5)` is strictly positive definite and

```text
P_M=0  iff  j_M(t)=0 for every t in B_M.                (PE7)
```

The representation `(PE5)` is standard Brownian-bridge parent theory; the physical prime radical
classification below is the source-specific survivor.

## Prime endpoint noncancellation `[PROVED HERE]`

Interior starts are injective in `p`, as are interior ends.  Therefore an endpoint contains at
most one start and at most one end.  If a start of `p` collides with an end of `q`, then

```text
log(M/p)=log(K/q),
q/p=K/M>1,                                              (PE8)
```

so `p!=q`.  The two weights cannot agree.  Indeed

```text
log(p)/p=log(q)/q
```

would imply `q log(p)=p log(q)`, hence `p^q=q^p`, impossible for two distinct primes by unique
factorization.  Thus every interior endpoint belonging to an active packet has nonzero jump.

A nonempty clipped interval has an interior endpoint: if both endpoints were clipped to `0,A`,
its length would be `A`, while its unclipped length is `c<A`.  Consequently

```text
P_M=0  iff  there is no active ordinary prime.           (PE9)
```

Combining `(PE9)` with the corrected-response identity gives the strict finite-aperture law

```text
R_M^sharp<D_M                                           (PE10)
```

whenever at least one active prime exists.  Exact saturation is impossible; the RH checkpoint can
only ask for asymptotic near-saturation.

## Sharp local mesh coercivity `[PROVED HERE]`

Order `B_M union {0,A}`.  For an interior endpoint `t`, let `L_t,R_t>0` be the lengths of the
adjacent left and right cells, and let `a_t,b_t` be the corresponding constant values of `P_M`.
Crossing `t` changes `P_M` by `-j_M(t)`, so

```text
|b_t-a_t|=|j_M(t)|.                                    (PE11)
```

The exact two-cell variance identity is

```text
L a^2+R b^2
 =L R/(L+R)(b-a)^2+(L a+R b)^2/(L+R).                  (PE12)
```

All other cell energies are nonnegative.  Hence for every `t in B_M`,

```text
||P_M||^2>=L_t R_t/(L_t+R_t)|j_M(t)|^2.                (PE13)
```

If `sigma_M` is the smallest mesh-cell length, then

```text
L_t R_t/(L_t+R_t)>=min(L_t,R_t)/2>=sigma_M/2,

||P_M||^2>=(sigma_M/2) max_(t in B_M)|j_M(t)|^2.        (PE14)
```

The constant `1/2` is sharp: one centered half-interval on two equal cells has values
`+j/2,-j/2` and energy `sigma j^2/2`.

Using `D_M-R_M^sharp=||P_M||^2`, `(PE13)`--`(PE14)` become response-saturation deficits.  In the
reverse direction, any upper bound `||P_M||^2<=epsilon` forces the pointwise stability law

```text
|j_M(t)|<=sqrt((L_t+R_t)epsilon/(L_t R_t))              (PE15)
```

at every physical endpoint.

## Significance and no-go boundary

This theorem is more than the generic positivity corollary of `(HGS29)`: it uses clipping,
ordinary-prime weights, unique factorization, and the Brownian endpoint mesh to identify the exact
radical and the sharp local coercivity constant.  It rules out exact low/high cancellation at
every nonempty finite aperture and converts near-saturation into endpoint-jump constraints.

It does **not** prove RH.  The minimum mesh `sigma_M` may collapse, and `(PE13)` is a lower bound
while RH needs the critical upper bound.  The theorem therefore retires exact-cancellation and
source-free correlation stories but leaves open a genuinely quantitative multiscale theorem
coupling endpoint spacing and prime-weight jumps.

Live corpus search found the Brownian kernel and interval coarea ingredients separately, but not
`(PE9)` or `(PE13)`--`(PE15)`.  The finite variance identity and unique-factorization step are
standard parent algebra, so external novelty is unverified and no broad scientific novelty claim
is made.  The result is recorded as new project-local source knowledge and positive salvage.

## Lean status

The current Lean tree formalizes the low/high carrier join, but not the physical logarithmic
endpoints or the Brownian endpoint radical.  Formalization should start with the exact two-cell
identity `(PE12)`, its sharp coercivity/equality classification, and the finite-mesh lift; the
prime-log endpoint noncollision and analytic identification `(PE1)`--`(PE10)` remain separate named
gates and must not be claimed until present in Lean.

## Gates

- [x] 0 -> 1: exact source packet, endpoint invariant, and hostile test stated
- [x] 1 -> 2: dependency-closed proofs of radical classification and sharp mesh coercivity
- [x] exact-cancellation route closed with positive strictness theorem
- [x] corpus audit: source-specific result absent; Brownian parent representation known
- [ ] formalize `(PE12)` and finite-mesh coercivity in one Lean batch
- [ ] formalize prime-log endpoint noncollision and the physical radical `(PE9)`
- [ ] formalize the analytic bridge from `P_M` to the corrected `AC25` response

## Log

- 2026-07-18 — extracted after the one-sided FCRJ correction; paper proof completed without
  numerical computation or web search.

## Lean progress log — 2026-08-22

Corpus audit confirms that `RHTower/PhysicalPrimeEndpointMeshCoercivity.lean` already closes the
generic finite-mesh batch requested by `(PE12)`--`(PE14)`: it proves the exact two-cell variance
identity, the harmonic-mean jump lower bound with equality classification, sharpness of the
one-half constant, finite-mesh coercivity, and strict positive energy from a nonzero jump.  It also
contains the unique-factorization endpoint-weight separation lemma
`physicalPrimeEndpointWeight_ne_of_distinct`.

This is a real partial closure, but not `(PE9)`: clipped physical logarithmic endpoints, the
noncancellation map from active packets to jumps, and the corrected-response identification remain
unformalized.  The card stays at Stage 2.
