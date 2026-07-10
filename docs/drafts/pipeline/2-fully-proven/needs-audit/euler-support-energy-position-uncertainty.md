# Euler support--energy--position uncertainty for off-line divisor motion

- **ID:** euler-support-energy-position-uncertainty
- **Stage:** 2-fully-proven/needs-audit
- **Type:** THEOREM (paper) -- novelty audit open
- **Source:** `euler-support-transverse-divisor-rigidity.md`; user request for a significant global
  constraint on zeros entering the critical line
- **Statement:** `[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]` If two
  completed Euler products differ at primes of convergence dimension `delta`, their logarithmic
  Euler discrepancy has weighted `ell^q` abscissa `sigma_q`, and their nontrivial divisor difference
  contains a point at horizontal distance `a`, then for every `1<=q<=infinity`,

  ```text
  sigma_q + delta/q' >= 1/2+a,       1/q+1/q'=1.
  ```

  Equivalently, their transverse divisor radius is bounded by

  ```text
  r_perp <= max(0, sigma_q+delta/q'-1/2).
  ```

  If the local factors are tempered of uniformly bounded degree, the same position constraint uses
  only the first prime traces: an off-line divisor change at distance `a>0` forces

  ```text
  sigma_q^prime+delta_1/q' >= 1/2+a,
  ```

  where `delta_1` is the convergence dimension of the primes at which the first traces differ. In
  particular, `sigma_2^prime>=a`; square-summable differences of prime traces force equality of the
  complete off-line divisors.

## Goal

Separate two ways an infinite Euler perturbation can be large -- amplitude and prime support -- and
prove that their combined size must pay for the horizontal position of every changed off-line zero.
This is a global infinite-data theorem, not a height bound, local jet condition, or RH equivalent.

## Gates

- [x] 0 -> 1: exact three quantities and interpolation route stated.
- [x] 1 -> 2: full paper proof below.
- [ ] 2 -> 3: formalize the weighted Holder and exponent arithmetic in Lean.
- [ ] 3 -> 4: primary-literature novelty audit and sharpness analysis.

## Setup

Use the class and notation of `euler-support-transverse-divisor-rigidity.md`. Thus

```text
c(p,k)=sum_r alpha_(1,p,r)^k-sum_r alpha_(2,p,r)^k
```

is the logarithmic Euler discrepancy, and

```text
S={p: c(p,k)!=0 for some k>=1},
delta=inf {u>=0: sum_(p in S)p^(-v)<infinity for every v>u}.
```

For `1<=q<infinity`, define

```text
E_q(v)=sum_(p in S) sum_(k>=1) |c(p,k)|^q p^(-kqv)/k,
sigma_q=inf {u in R: E_q(v)<infinity for every v>u}.
```

For `q=infinity`, define

```text
E_infinity(v)=sup_(p in S,k>=1) |c(p,k)|p^(-kv),
sigma_infinity=inf {u in R: E_infinity(v)<infinity for every v>u}.
```

Let `q'` be conjugate to `q`, with `1/infinity=0`. Let `D_nt` be the nontrivial divisor difference
and `a=r_perp(D_nt)`.

For the prime-trace-only version define

```text
c_1(p)=c(p,1),
S_1={p:c_1(p)!=0},
delta_1=inf {u>=0:sum_(p in S_1)p^(-v)<infinity for every v>u},
```

and, for finite `q`,

```text
E_q^prime(v)=sum_(p in S_1)|c_1(p)|^q p^(-qv),
sigma_q^prime=inf {u:E_q^prime(v)<infinity for every v>u},
```

with the analogous supremum definition for `q=infinity`.

## Theorem

For every `1<=q<=infinity`,

```text
sigma_E <= sigma_q+delta/q',                               (H)
r_perp(D_nt) <= max(0,sigma_q+delta/q'-1/2).                (U)
```

If `D_nt` contains a point at distance `a` (in particular if an off-line zero at that distance is
created, removed, or enters the line), then

```text
sigma_q+delta/q' >= 1/2+a.                                 (P)
```

If all local parameters satisfy `|alpha_(j,p,r)|<=1` and the local degrees are bounded, then every
off-line point (`a>0`) satisfies the stronger prime-trace-only inequality

```text
sigma_q^prime+delta_1/q' >= 1/2+a.                         (P_prime)
```

## Paper proof

`[PROVED HERE; NOVELTY UNVERIFIED]`

First take `1<q<infinity`. Fix

```text
v>sigma_q,
w>delta/q'.
```

At `s` with `Re s>v+w`, weighted Holder on the index set of prime powers gives

```text
sum_(p in S) sum_(k>=1) |c(p,k)| p^(-k Re(s))/k

<= (sum_(p in S) sum_(k>=1) |c(p,k)|^q p^(-kqv)/k)^(1/q)
   (sum_(p in S) sum_(k>=1) p^(-kq'w)/k)^(1/q').            (1)
```

The first factor is finite by the definition of `sigma_q`. For the second, `q'w>delta`, and

```text
sum_(k>=1) p^(-kq'w)/k = -log(1-p^(-q'w)) <= C_w p^(-q'w).
```

The sum over `p in S` therefore converges by the definition of `delta`. Hence the logarithmic Euler
discrepancy converges absolutely for every `Re s>v+w`. Letting `v` decrease to `sigma_q` and `w`
decrease to `delta/q'` proves `(H)`.

For `q=1`, the first factor in (1) is already the absolute discrepancy series and the second factor
is a supremum; the same conclusion reads `sigma_E<=sigma_1`. For `q=infinity`, the first factor is
`E_infinity(v)` and the second is the `ell^1` sum over prime powers, giving
`sigma_E<=sigma_infinity+delta`. Thus `(H)` holds at both endpoints.

The relative-strip theorem gives

```text
r_perp(D_nt)<=max(0,sigma_E-1/2).
```

Combining this with `(H)` proves `(U)`. If a point at distance `a` occurs in `D_nt`, the stronger
pointwise form of the relative-strip theorem says `sigma_E>=1/2+a`; together with `(H)` this gives
`(P)`.

For the tempered strengthening, split the logarithmic Euler discrepancy into `k=1` and `k>=2`.
Bounded degree and `|alpha_(j,p,r)|<=1` give `|c(p,k)|<=2d`, hence for every `Re s>1/2`,

```text
sum_p sum_(k>=2) |c(p,k)|p^(-k Re(s))/k
 <= 2d sum_p sum_(k>=2)p^(-k Re(s))/k < infinity.           (2)
```

The prime part obeys the same Holder estimate as (1), now on the index set `S_1` alone, so its
absolute-convergence abscissa is at most `sigma_q^prime+delta_1/q'`. Therefore

```text
sigma_E <= max(1/2, sigma_q^prime+delta_1/q').              (3)
```

An off-line divisor point at distance `a>0` forces `sigma_E>=1/2+a>1/2`. In (3) the second term must
therefore be at least `1/2+a`, proving `(P_prime)`.

## Principal cases

### Square-energy law (`q=2`)

```text
sigma_2+delta/2 >= 1/2+a.                                  (4)
```

If the changed set has full prime exponent `delta=1`, then

```text
sigma_2>=a.                                                  (5)
```

Thus a changed zero at distance `a` forces

```text
sum_p sum_(k>=1) |c(p,k)|^2 p^(-2kv)/k = infinity
```

for every `v<a`. In particular, finite unweighted Euler discrepancy energy (`E_2(0)<infinity`)
forbids every off-line divisor change, even when all primes are allowed to vary.

In the tempered bounded-degree class, the same conclusions hold with the full prime-power energy
replaced by prime traces alone. Since every prime subset has `delta_1<=1`, `(P_prime)` at `q=2`
gives

```text
sigma_2^prime >= 1/2+a-delta_1/2 >= a.                     (6)
```

Thus

```text
sum_p |c_1(p)|^2 < infinity
```

forces equality, with multiplicity, of every off-critical zero and pole of the two functions. No
agreement hypothesis at `p^2,p^3,...` is required for this off-line conclusion.

### Uniform-amplitude law (`q=infinity`)

If `|c(p,k)|<=C p^(ktheta)`, then `sigma_infinity<=theta`, and `(P)` gives

```text
theta+delta>=1/2+a,
```

the support-position theorem.

### Total-variation law (`q=1`)

```text
sigma_1>=1/2+a,
```

equivalent via Cahen's formula to prime-power total variation of growth exponent at least `1/2+a`.

## Deformation consequence

Let `{L_t}` be a family. If for all sufficiently close parameters the changed-prime dimension and
Euler `ell^q` abscissa obey

```text
sigma_q(L_t,L_u)+delta(L_t,L_u)/q' < 1/2,
```

then the nontrivial divisor is locally constant. If an off-line pair at distance `a_n` is removed as
`t_n->t_*`, then necessarily

```text
liminf_n (sigma_q(L_(t_n),L_(t_*))+delta(L_(t_n),L_(t_*))/q') >= 1/2,
```

with the sharper term `1/2+a_n` before taking the limit.

## Sharpness and exact open core

The Holder exponent is sharp at the level of Euler coefficient spaces. If `S_1` has exact
convergence dimension `delta_1` and `|c_1(p)|` has power size `p^theta` on `S_1`, then

```text
sigma_q^prime=theta+delta_1/q,
sigma_q^prime+delta_1/q'=theta+delta_1
```

for every `q`. Thus no interpolation improvement is possible without using more than support and
`ell^q` amplitude.

`[OPEN CORE]` Determine whether the divisor inequality is arithmetically sharp: construct, or rule
out, a pair of genuine completed Euler products for which a changed nontrivial zero satisfies

```text
1/2+a = sigma_q^prime+delta_1/q'.
```

Failure of boundary realizability would be a strictly stronger arithmetic non-entry constraint;
realizability would prove the uncertainty law optimal.

## Novelty and significance audit

- Holder interpolation and convergence abscissae are standard separately.
- Strong multiplicity-one papers use coefficient closeness and thin exceptional prime sets, but the
  searched primary sources did not state a continuum of support--amplitude--zero-position
  inequalities.
- Farmer (2021) is recovered from the tempered prime-trace theorem at `q=infinity`, zero amplitude
  exponent, and `delta_1<1/2`; the new candidate content is the position-sensitive and `ell^q`
  interpolation beyond that endpoint.
- Farmer--Pitale--Ryan--Schmidt (2026) use square-mean closeness of prime coefficients together with
  higher-prime-power or lift hypotheses to prove equality of the functions. The prime-trace-only
  theorem here makes the weaker but unconditional conclusion that the off-line divisors coincide;
  the exact energy-versus-horizontal-distance inequality was not located there.
- The `q=2` energy law is the most significant surviving form: it gives a necessary divergence
  scale for any Euler-side surgery of an off-line zero, even with changes at every prime.
- The theorem remains in `needs-audit`; a standard explicit-formula or Dirichlet-series result
  equivalent to `(P)` would force downgrade.

## Log

- 2026-07-10 -- theorem generated and paper proof completed from the relative-strip result plus
  weighted Holder interpolation.
