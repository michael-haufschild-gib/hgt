# The squarefree Euler line is a thin HT modular-curvature colligation with a corona codiagonal

- **ID:** `squarefree-euler-modular-corona-curvature-colligation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / GENERAL HT REALIZATION / HTGEOMETRY-TO-RHTOWER BRIDGE
- **Scientific status:** `[PROVED HERE] [PROOF-DELIVERY TEST] [NOVELTY GATE BYPASSED BY REQUEST] [NOT RH]`
- **HT parents:**
  - `new_scientific_knowledge/hypertranscendental-clock-normalization-symmetry-anomaly.md`
  - `../3-formalized/finite-observable-conormal-corona.md`
  - `../../1-in-progress/source-anomaly-boundary-colligation-field.md`
  - `../../1-in-progress/pretemporal-horizon-curvature-rigidity.md`
- **RH parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `squarefree-fixed-current-right-half-ward-localization.md`
- **Statement:** Finite squarefree Euler packets form an exact inductive determinant-line
  boundary colligation of uniformly one-dimensional transverse width.  Its logarithmic current has
  Fisher curvature, and its critical curvature is four.  Prime-by-prime the current extends as a
  holomorphic `ell^2` field throughout `Re s>1/2`; all possible strict right-half divisor poles
  occur only after applying the unbounded global codiagonal.  This is an explicit zeta realization
  of the HT conormal-corona and normalization-anomaly mechanisms.

## Finite squarefree determinant line

Let `S` be a finite set of primes, `sigma>1`, and put

```text
q_p=p^(-sigma),
Z_S(sigma)=product_(p in S)(1+q_p).                       (1)
```

In the squarefree tensor space

```text
H_S=tensor_(p in S) C^2,
```

use the unnormalized signed source line and its unit representative

```text
phi_S(sigma)
 =tensor_(p in S)(e_0-sqrt(q_p)e_1),
psi_S=phi_S/sqrt(Z_S).                                   (2)
```

The sign in `(2)` is the Mobius character.  Its Hermitian metric is exactly

```text
||phi_S||^2=Z_S.                                         (3)
```

For a subset `T subset S`, write

```text
H_S(T)=sum_(p in T)log p.
```

The Born law of `psi_S` is the independent squarefree Bernoulli measure with occupation
probability `q_p/(1+q_p)`.

## Fixed current and curvature

The logarithmic metric connection on the real source ray is

```text
J_S(sigma)
 =-partial_sigma log Z_S(sigma)
 =sum_(p in S)(log p)q_p/(1+q_p)
 =E_S H_S.                                                (4)
```

Its real Hessian curvature is

```text
V_S(sigma)
 =-partial_sigma J_S(sigma)
 =partial_sigma^2 log Z_S(sigma)
 =sum_(p in S)(log p)^2 q_p/(1+q_p)^2
 =Var_S(H_S).                                             (5)
```

For `epsilon=sigma-1`, the horizontal source tangent

```text
chi_S=-2epsilon(H_S-E_S H_S)psi_S                         (6)
```

therefore satisfies

```text
||chi_S||^2=4epsilon^2 V_S.                               (7)
```

Thus the squarefree classical Fisher information is literally the real Hessian curvature of the
charged scalar fixed-current line.  It is not a metric attached after the current has been chosen.
For the normalized half-density line, the ordinary projective metric on the parameter derivative
is `V_S/4`; the calibrated tangent `(6)` has squared norm `(7)`.  These normalization factors are
kept explicit below.

## Exact adjacent-prime determinant-line colligation

If `p notin S`, set

```text
v_p=(e_0-sqrt(q_p)e_1)/sqrt(1+q_p),
chi_p=-2epsilon(log p)(N_p-q_p/(1+q_p))v_p.               (8)
```

Then

```text
psi_(S union {p})=psi_S tensor v_p,                       (9)

chi_(S union {p})
 =chi_S tensor v_p+psi_S tensor chi_p.                   (10)
```

The two terms in `(10)` are orthogonal because both `chi_S` and `chi_p` are horizontal.  Hence

```text
||chi_(S union {p})||^2
 =||chi_S||^2+||chi_p||^2,                               (11)

J_(S union {p})=J_S+(log p)q_p/(1+q_p),                  (12)

V_(S union {p})=V_S+(log p)^2q_p/(1+q_p)^2.              (13)
```

Equations `(9)`--`(13)` are a source-canonical finite **boundary-colligation skeleton**: the lower
source line, new boundary self-symbol `v_p`, outgoing tangent `chi_p`, connection, and curvature
all reconstruct the enlarged line.  The transverse tangent width is exactly one at every prime
aperture.

This is not yet the complete HT anomaly colligation
`(T_N,beta_N,delta_N,alpha_N)`: no intrinsic derivative-clock source operation or descent anomaly
`alpha_N` has been identified merely by adding a prime.  Calling `(9)`--`(13)` the full object
would conflate arithmetic aperture with the Kähler--Ore jet clock.

## Actual HT-current comparison and its scope

Use the hypertranscendental zeta amplitude `q=zeta`.  Its logarithmic current

```text
Dq/q=zeta'/zeta=-A                                      (14a)
```

is hypertranscendental by the fixed-current theorem: if it were differentially algebraic, the
linear equation `Dq=(Dq/q)q` would make `q` differentially algebraic.  Thus `C<A>` is a genuine
HT fixed-current field, and the derivatives of `A` form its intrinsic scalar jet clock.

On `Re s>1`, those jets are the prime-power Laplace moments

```text
(-1)^n D^n A(s)
 =sum_(m>=1)Lambda(m)(log m)^n m^(-s).                  (14b)
```

RHTower already formalizes the full von Mangoldt prime-power Laplace channel, its equality with
`A`, and its finite positive Gram packets.  Separately, the existing prime--Laplace
descent-anomaly theorem constructs faithful finite Gamma-jet observations and the omitted Taylor
tail for a weighted time-one **prime slice**.  It does not yet lift that descent anomaly to the
full prime-power channel `(14b)`.  Therefore the comparison morphism from the complete arithmetic
current to the HT jet clock is only half assembled; the finite prime-power Gamma-jet anomaly is
the next exact bridge.

The squarefree current in `(14)` satisfies

```text
J_sq=A(s)-2A(2s).                                       (14c)
```

The second term is holomorphic on `Re s>1/2`.  Therefore the determinant line `(1)`--`(13)` is a
positive metric representative of the same strict anti-causal divisor class as the genuine HT
current `A`, without claiming that the prime-aperture filtration is intrinsically the derivative
filtration or that `J_sq` alone generates the same differential field.

## Critical four-unit boundary

Let `S` increase through all primes.  Then

```text
Z(sigma)=zeta(sigma)/zeta(2sigma),
J(sigma)=A(sigma)-2A(2sigma),
A=-zeta'/zeta.                                           (14)
```

The Laurent expansion at the Euler pole gives

```text
epsilon J(1+epsilon)->1,
epsilon^2 V(1+epsilon)->1.                               (15)
```

Consequently

```text
||chi_(1+epsilon)||^2->4.                                (16)
```

The positive normal boundary becomes singular exactly at the infinite-clock limit: every finite
prime line is normal, while the limiting tangent has norm of order `epsilon^(-1)` before the
critical rescaling.  The four-unit law is the finite residue of this HT normalization anomaly.

## Holomorphic prime current and the corona codiagonal

For complex `s` with `Re s>1/2`, define the prime-coordinate modular current

```text
j(s)_p=(log p)p^(-s)/(1+p^(-s)).                          (17)
```

On every closed half-plane `Re s>=1/2+delta`,

```text
sum_p |j(s)_p|^2
 <=C_delta sum_p (log p)^2p^(-1-2delta)<infinity.         (18)
```

The convergence is locally uniform, so

```text
j:{Re s>1/2}->ell^2(Primes)                              (19)
```

is a holomorphic Hilbert-valued field.  No coordinate of `(19)` has a pole in that half-plane.
The centered local modular character

```text
Delta_p(s)=p^(1/2-s)                                     (20)
```

obeys the exact reflection law

```text
Delta_p(1-s)=Delta_p(s)^(-1),                             (21)
```

so `(19)` is the logarithmic connection of a reflection-reciprocal modular clock.

On `Re s>1`, the algebraic finite-support codiagonal gives

```text
Sigma(j(s))=sum_p j(s)_p
 =J_sq(s)=A(s)-2A(2s).                                   (22)
```

But `Sigma` has no bounded extension to `ell^2(Primes)`: on the normalized indicator of any `N`
prime coordinates its value is `sqrt(N)`.  Meromorphic continuation of the right side of `(22)`
can therefore have poles even though the vector field `(19)` is holomorphic.  Since `A(2s)` is
holomorphic on `Re s>1/2`, every strict right-half zeta zero is precisely a pole created by this
singular global scalarization.

Thus the possible Xi divisor is a **conormal-corona singularity**.  It is not a singularity of any
finite Euler clock or of the Hilbert-valued modular connection.

## Rank-one and curvature-only no-gos

The rank-one principal-symbol theorem concerns an alternating two-law commutator curvature.  The
quantity `(5)` is a symmetric metric Hessian, so using that theorem to force `(5)` to vanish—or to
deduce rank two from its nonvanishing—would be a type error.  The lower-plus-transverse
colligation `(10)` is nevertheless exact, but it is proved directly by tensor factorization.

**Positive HT statement:** alternating integrability curvature and symmetric statistical curvature
are independent invariants of a constrained HT realization.  A rank-one filtered law may be
commutator-flat while its normalized source line has nonzero Fisher curvature.  Any claimed
unification must provide an explicit comparison morphism rather than identify the two by name.

Curvature alone still does not determine the completion.  The unbounded codiagonal in `(22)` is
invisible to `(5)` and can change its meromorphic divisor without changing any finite prime
coordinate.  This is the concrete zeta instance of the general HT theorem that curvature forgets
the boundary self-symbol and source anomaly.

## Direct RH consequence and remaining theorem

Let the Gamma/Sonin framing extend `(9)`--`(13)` to a conservative self-dual boundary colligation.
If its horizontal derivative splits as

```text
completed source tangent
  =causal connection direct_sum anti-causal second fundamental form,
```

with

```text
anti-causal second fundamental form=ell_E,               (23)
```

then the Hilbert-column Gauss--Codazzi/Pythagoras identity for the calibrated tangent and `(16)`
give

```text
||ell_E||_2^2
 <=lim ||chi_(1+epsilon)||^2=4,                           (24)
```

and the existing Cauchy threshold proves RH.

The missing theorem is not positivity of `(5)`; that is exact.  It is the source-framed
identification `(23)`, including continuity of the corona codiagonal through the Gamma/Sonin
rigging.  Any construction that keeps only the Hilbert vector `(19)` cannot see the divisor and is
rejected.

## General HT consequences

1. A source can have a holomorphic normal modular connection in its Hilbert completion while its
   calibrated scalar fixed current lives only in the conormal corona and becomes meromorphic.
2. Persistent divisor data can be singularity of infinite scalarization rather than local
   singularity, finite rank loss, or failure of Hilbert normality.
3. Unbounded arithmetic observable capacity and uniformly thin transverse variation coexist
   explicitly: the number of prime observables grows without bound, while every adjacent boundary
   tangent has width one.  Its promotion to an intrinsic HT capacity statement uses the faithful
   prime--Laplace-to-current-jet comparison, not an identification by vocabulary.
4. A positive self-dual completion does not make the modular clock stationary; it converts the
   divergent infinite tangent into a finite critical curvature residue.

## Gates

- [x] finite signed determinant line constructed
- [x] fixed current equals the determinant-line connection
- [x] Fisher variance equals its curvature
- [x] adjacent-prime determinant-line boundary colligation reconstructed exactly
- [x] uniform transverse width one
- [x] distinction between arithmetic prime aperture and intrinsic HT derivative clock enforced
- [x] genuine zeta fixed-current HT field and full prime-power Laplace channel identified
- [x] time-one prime descent anomaly distinguished from the still-missing prime-power anomaly
- [x] critical curvature residue equals four
- [x] prime-coordinate current extended holomorphically to `Re s>1/2` in `ell^2`
- [x] global codiagonal proved unbounded
- [x] strict right-half divisor localized to corona scalarization
- [x] alternating principal-symbol and symmetric Fisher curvatures separated by type
- [x] curvature-only route rejected positively
- [ ] combine the prime--Laplace descent anomaly with the squarefree determinant-line colligation
- [ ] construct the Gamma/Sonin conservative completion of the resulting full source colligation
- [ ] prove the anti-causal second fundamental form identity `(23)`
- [ ] RH
