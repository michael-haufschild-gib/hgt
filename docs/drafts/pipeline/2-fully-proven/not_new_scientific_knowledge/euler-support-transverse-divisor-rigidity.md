# Half-dimensional Euler support as a transverse-divisor barrier

- **ID:** euler-support-transverse-divisor-rigidity
- **Stage:** 2-fully-proven/needs-audit
- **Type:** THEOREM (paper) -- novelty audit open
- **Source:** user question on the constraint preventing off-line zeros from entering the critical line;
  sparse-prime extension of analytic strong multiplicity one
- **Statement:** `[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Let
  `sigma_E(F,G)` be the absolute-convergence
  abscissa of the logarithmic Euler discrepancy of two order-one completed Euler products with
  standard gamma factors and functional equations centered on `Re s=1/2`. The transverse radius of
  their nontrivial divisor difference `D_nt=(div F-div G)|_(0<Re s<1)` satisfies

  ```text
  r_perp(D_nt) <= max(0, sigma_E(F,G) - 1/2).
  ```

  Hence changing an off-critical zero at horizontal distance `a` requires
  `sigma_E(F,G) >= 1/2 + a`. If the local factors differ only on primes `S` and their parameters are
  bounded by `p^theta`, this forces `delta(S) >= 1/2 + a - theta`.

## Goal

Identify a global, non-height, non-jet constraint on off-critical zeros using the infinite Euler
data itself. The target is not an RH equivalent. It is a quantitative necessary condition for
transverse divisor motion: the farther a changed zero lies from the critical line, the farther right
the logarithmic Euler discrepancy must fail absolute convergence.

## Gates

- [x] 0 -> 1 in-progress: exact analytic class, support exponent, proof mechanism, and falsifiers
  stated.
- [x] 1 -> 2 fully-proven: complete paper proof with every quotient/finite-order step checked.
- [ ] 2 -> 3 formalized: abstract normal-convergence and divisor-reflection theorem in Lean.
- [ ] 3 -> 4 publication-ready: primary-literature novelty audit and standalone theorem.

## Setup

For `j in {1,2}`, let

```text
L_j(s) = product_p product_(r=1)^(d_j(p)) (1 - alpha_(j,p,r) p^(-s))^(-1),
```

initially in a common right half-plane (in the normalized Selberg-class setting, `Re s>1`), with
`d_j(p) <= d` and

```text
|alpha_(j,p,r)| <= p^theta,       theta < 1/2.
```

Assume both functions have meromorphic continuation of finite order at most one and finitely many
poles. Let

```text
Lambda_j(s)=Q_j^s product_m Gamma(lambda_(j,m)s+mu_(j,m)) L_j(s),
```

where `lambda_(j,m)>0` and `Re mu_(j,m)>=0`. The completed functions satisfy functional equations
about `Re s = 1/2`; their conductors, gamma factors, and root numbers may differ. The gamma quotient
has no zero or pole in `Re s>0`, which is the only archimedean fact used for the nontrivial-divisor
bound. Equality of the two functions in the subcritical case will additionally assume identical
conductor and gamma data.

Let

```text
S = {p : L_(1,p) != L_(2,p)},
delta(S) = inf {u >= 0 : sum_(p in S) p^(-v) < infinity for every v > u}.
```

For the logarithmic local discrepancy

```text
c(p,k) = sum_r alpha_(1,p,r)^k - sum_r alpha_(2,p,r)^k,
```

define the intrinsic Euler-discrepancy abscissa

```text
sigma_E(F,G) = inf {u in R :
  sum_p sum_(k>=1) |c(p,k)| p^(-k v)/k < infinity for every v > u}.
```

For a meromorphic divisor `D`, define its transverse radius about the critical line by

```text
r_perp(D) = sup {|Re rho - 1/2| : rho is in supp(D)},
```

with the supremum of the empty set equal to `0`.

Write

```text
D_nt(F,G) = (div L_1-div L_2) restricted to 0<Re s<1.
```

## Candidate theorem

1. The Euler quotient `H = L_1/L_2` is holomorphic and zero-free in `Re s > sigma_E`.
2. The completed quotient `R = Lambda_1/Lambda_2` is zero/pole-free in
   `Re s > max(0,sigma_E)`. Its quotient functional equation reflects this to
   `Re s < 1-max(0,sigma_E)`.
3. Therefore every point `rho` in the nontrivial divisor difference satisfies

   ```text
   1 - sigma_E <= Re rho <= sigma_E,
   |Re rho - 1/2| <= sigma_E - 1/2.
   ```

   If `sigma_E <= 1/2`, the divisor is empty off the critical line. If `sigma_E < 1/2`, it is empty
   everywhere.
4. If the conductor and gamma data agree, then in the last case `R=H` is a nonvanishing entire
   finite-order function, hence
   `R(s)=exp(As+B)`. Since the Euler quotient tends to `1` as `Re s -> +infinity`, `A=0` and
   `exp(B)=1`; thus `L_1=L_2`, and uniqueness of the Euler expansion gives equality of every local
   factor.
5. If local factors differ only at `S`, then

   ```text
   sigma_E(F,G) <= theta + delta(S),
   r_perp(D_nt(F,G)) <= max(0, theta + delta(S) - 1/2).
   ```

   Thus changing a divisor point at horizontal distance `a` forces
   `delta(S) >= 1/2 + a - theta`.
   Consequently, for every `epsilon>0`, the exceptional-prime counting function cannot satisfy

   ```text
   # {p<=x:p in S} = O(x^(1/2+a-theta-epsilon)).
   ```
6. Define the accumulated total variation of the logarithmic Euler discrepancy by

   ```text
   V_E(x) = sum_(p^k <= x) |c(p,k)|/k.
   ```

   If the divisor difference contains a point at horizontal distance `a`, then

   ```text
   limsup_(x->infinity) log V_E(x)/log x >= 1/2+a.
   ```

   Equivalently, for every `epsilon>0`, `V_E(x)` is not `O(x^(1/2+a-epsilon))`.

## Proof mechanism to check

For `sigma > sigma_E`, the defining series converges locally uniformly and gives a holomorphic
logarithm of `R`. In the sparse-support corollary, normal convergence follows for
`sigma > theta + delta(S)` from

```text
sum_(p in S) sum_(k >= 1)
  |sum_r alpha_(1,p,r)^k - sum_r alpha_(2,p,r)^k| / (k p^(k sigma))
  <= 2d sum_(p in S) sum_(k >= 1) p^(-k(sigma-theta))/k.
```

The right side converges locally uniformly. Equality with the meromorphic quotient follows first in
the ordinary Euler half-plane and then by analytic continuation. Reflection by the common completed
functional equation supplies the left half-plane. The intersection of the complements of these two
zero-free half-planes is the closed band `[1-sigma_E, sigma_E]`, giving the divisor-radius inequality.

## Paper proof

`[PROVED BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`

Write `H(s)=L_1(s)/L_2(s)`. In the ordinary Euler half-plane,

```text
log H(s) = sum_p sum_(k>=1) c(p,k) p^(-ks)/k.                 (1)
```

Fix a compact set `K` in `Re s > sigma_E`. Choose `v > sigma_E` below the minimum real part on
`K`. The series of absolute values defining `sigma_E` converges at `v`, so the Weierstrass test makes
(1) locally uniformly convergent on `K`. It defines a holomorphic function `D(s)` there, and
`exp(D(s))` is holomorphic and zero-free. In the common ordinary Euler half-plane it equals `H`.
The meromorphic identity theorem therefore gives

```text
H(s) = exp(D(s)) != 0                    for Re s > sigma_E.  (2)
```

In particular, `H` has neither zeros nor poles in that half-plane.

Now put

```text
A_infinity(s) =
  (Q_1/Q_2)^s product_m Gamma(lambda_(1,m)s+mu_(1,m))
  / product_m Gamma(lambda_(2,m)s+mu_(2,m)),
R(s)=Lambda_1(s)/Lambda_2(s)=A_infinity(s)H(s).
```

Gamma has no zeros, and all poles of every displayed gamma factor have real part at most `0`.
Consequently `A_infinity` has neither a zero nor a pole in `Re s>0`. With
`A=max(0,sigma_E)`, equation (2) gives

```text
R(s) != 0, infinity                                      for Re s>A. (2')
```

Let the completed functional equations be

```text
Lambda_j(s) = epsilon_j conjugate(Lambda_j(1-conjugate(s))).
```

Their quotient satisfies, meromorphically on the plane,

```text
R(s) = eta conjugate(R(1-conjugate(s))),
eta = epsilon_1/epsilon_2,  |eta|=1.                          (3)
```

If `R` had a zero or pole at `s` with `Re s < 1-A`, equation (3) would give a zero or pole of
the same order at `1-conjugate(s)`, whose real part is greater than `A`, contradicting (2').
Thus

```text
R(s) != 0, infinity                       for Re s < 1-A.       (4)
```

Every point `rho` in `supp(div R)` must therefore obey

```text
1-A <= Re rho <= A.                                           (5)
```

Inside `0<Re s<1`, all gamma factors are finite and nonzero, so `supp(div R)` is exactly the
nontrivial divisor difference of `L_1` and `L_2`. If that difference contains an off-line point at
distance `a`, reflection supplies a point on the right at real part `1/2+a`. Equation (5) forces
`A>=1/2+a`. Since this is positive, `A=sigma_E`, and therefore

```text
sigma_E >= 1/2+a.
```

Taking the supremum over the nontrivial divisor support proves

```text
r_perp(D_nt(L_1,L_2)) <= max(0,sigma_E-1/2).                 (6)
```

If `sigma_E = 1/2`, (5) confines the whole nontrivial quotient divisor to the critical line, so all
off-line zeros and poles, including multiplicities, agree. Now additionally suppose the conductor
and gamma data agree. If `sigma_E < 1/2`, the two zero-free half-planes in (2') and (4) overlap and
cover the plane, so `R=H` has no zeros or poles anywhere. The standard
Hadamard quotient theorem for finite-order meromorphic functions gives

```text
R(s)=exp(As+B)
```

because both completed functions have order at most one. On the positive real axis the normalized
Dirichlet series satisfy `L_j(x) -> 1`, hence `R(x) -> 1`. This forces `A=0` and `exp(B)=1`, so
`L_1=L_2`. Uniqueness of Dirichlet coefficients and of normalized polynomial local factors then
gives equality at every prime.

It remains to prove the sparse-support estimate. Pad every local parameter list with zeros to length
`d`. If the local factors agree outside `S`, then `c(p,k)=0` there, while on `S`

```text
|c(p,k)| <= 2d p^(k theta).                                    (7)
```

For every `v > theta+delta(S)`, put `u=v-theta > delta(S)`. From (7),

```text
sum_p sum_(k>=1) |c(p,k)| p^(-kv)/k
 <= 2d sum_(p in S) sum_(k>=1) p^(-ku)/k
 <= C_(d,u) sum_(p in S) p^(-u) < infinity.                   (8)
```

Therefore `sigma_E <= theta+delta(S)`. Combining this with (6), any point of the divisor difference
at horizontal distance `a` satisfies

```text
a <= sigma_E-1/2 <= theta+delta(S)-1/2,
delta(S) >= 1/2+a-theta.                                      (9)
```

If `#S(x)=O(x^q)`, partial summation gives convergence of `sum_(p in S)p^(-v)` for every `v>q`,
so `delta(S)<=q`. The contrapositive of (9) proves the exceptional-prime counting statement. This
proves the candidate theorem.

For the coefficient-mass form, regard the nonnegative terms `|c(p,k)|/k` as the coefficients of an
ordinary Dirichlet series indexed by the prime powers `n=p^k` (summing coincident representations,
which are unique). Since a mismatched divisor point at distance `a` forces
`sigma_E >= 1/2+a > 0`, the Cahen formula for a nonnegative Dirichlet series applies:

```text
sigma_E = limsup_(x->infinity) log V_E(x)/log x.
```

The asserted lower bound follows. Multiplication by `log p` (the coefficients of the logarithmic
derivative) does not reduce the exponent, so the same lower exponent holds for the prime-power mass
`sum_(p^k<=x) |c(p,k)| log p`.

## Deformation corollary

Let `{L_t}` be any family with standard functional equations centered at `1/2`. No differentiability,
zero labeling, or local Taylor expansion is needed. If `sigma_E(L_t,L_u) <= 1/2` for every pair,
then their complete off-critical divisors are identical. Consequently no off-line zero can enter or
leave the critical line anywhere in the family. If the inequalities are strict and the conductor and
gamma data are fixed, the family itself is constant. More quantitatively, an endpoint change involving
a zero at distance `a` forces
`sigma_E(L_t,L_u) >= 1/2+a`.

In particular, suppose an off-line pair at parameter values `t_n`, absent from the divisor at
`t_*`, converges to a critical-line divisor configuration at `t_*`, with horizontal distances
`a_n>0`. Then

```text
sigma_E(L_(t_n),L_(t_*)) >= 1/2+a_n,
liminf_n sigma_E(L_(t_n),L_(t_*)) >= 1/2.
```

Every genuine entry event is therefore an **Euler-discrepancy critical event**. A locally
Euler-thin path (`sigma_E<1/2` for all sufficiently close pairs) cannot meet the collision
discriminant from the off-line side.

## Euler-discrepancy phase trichotomy

The theorem gives a global phase diagram with no zero labels or jets:

```text
sigma_E < 1/2 : no divisor change;
sigma_E = 1/2 : divisor change can be supported only on the critical line;
sigma_E > 1/2 : transverse change is possible only inside
                |Re s-1/2| <= sigma_E-1/2.
```

The functional equation supplies the reflection, but not the barrier. The barrier is the
half-dimensional absolute-convergence threshold of the infinite Euler discrepancy.

## Significance target

Under Ramanujan (`theta=0`), changing one off-critical zero at `beta+i gamma` requires a changed-prime
set `S` with

```text
delta(S) >= 1/2 + |beta-1/2|.
```

Thus the thickness required of the changed Euler data records the horizontal position of the zero,
not its height. Finite, exponentially sparse, and every prime set with convergence exponent at most
`1/2` are incapable of any transverse divisor motion.

For tempered local factors this can be read as a **relative critical-strip theorem**. The ordinary
Euler product uses all primes, whose convergence exponent is `1`, and the standard Euler-plus-FE
argument confines zeros to `[0,1]`. If two Euler products differ only on a set of exponent `delta`,
the same argument confines their *divisor difference* to the narrower strip

```text
1-delta <= Re s <= delta.
```

The standard critical strip is therefore the full-support endpoint of a continuous family of
relative strips. The critical line is the rigidity threshold `delta=1/2`.

## Known-parent audit

- Farmer--Pitale--Ryan--Schmidt prove the finite-`S` version as a simple analytic strong
  multiplicity-one proposition.
- Michael Farmer (2021) already proves that if the exceptional prime set satisfies
  `#S(x) << x^(1/2-delta)`, then the two Selberg-class divisors agree off the critical line. That
  qualitative thin-support result is therefore not new.
- Kaczorowski--Perelli and Soundararajan prove stronger multiplicity-one results from closeness of
  prime coefficients.
- The intrinsic quantitative inequality
  `r_perp <= (sigma_E-1/2)_+` and its position-sensitive support corollary
  `delta(S) >= 1/2 + |beta-1/2| - theta` are useful global formulations, but their proof is a
  direct application of normal Euler-quotient convergence and functional-equation reflection.
  Under the strict scientific-newness criterion they are a bridge, not new scientific knowledge,
  even if this exact notation is absent from the literature.

## Falsifiers and scope

- Functional-equation-preserving perturbations without an Euler product can move zeros on or off
  the line (Gauthier--Xarles), so the Euler hypothesis is essential.
- Standard archimedean data may change: their gamma quotient has no divisor in `Re s>0`, so it cannot
  evade the nontrivial position bound. Nonstandard gamma factors with right-half-plane divisor would
  have to be added to the discrepancy datum.
- The theorem gives a necessary thickness condition, not existence of a deformation when
  `theta + delta(S) > 1/2`, and not RH for any one function.

## Primary sources checked

- P. M. Gauthier and X. Xarles, [Perturbations of L-functions with or without non-trivial zeros off
  the critical line](https://arxiv.org/abs/0911.5135) -- functional-equation symmetry alone permits
  both behaviors.
- M. Farmer, [Strong multiplicity one for the Selberg class](https://arxiv.org/abs/2101.02771) --
  contains the qualitative off-line divisor coincidence theorem for exceptional prime sets of
  counting exponent strictly below `1/2`.
- D. W. Farmer, A. Pitale, N. C. Ryan, and R. Schmidt,
  [Multiplicity one for analytic L-functions and applications](https://doi.org/10.1017/S0305004126102011)
  -- contains the finite-exceptional-set quotient argument and broader coefficient-closeness
  multiplicity-one theorems.
- K. Soundararajan,
  [Strong multiplicity one for the Selberg class](https://arxiv.org/abs/math/0210299), and
  J. Kaczorowski--A. Perelli, *Strong multiplicity one for the Selberg class* (2001) -- checked as
  parent multiplicity-one theory; no position-sensitive relative-strip inequality was located.
- E. Cahen, [Sur la fonction zeta(s) de Riemann et sur des fonctions
  analogues](https://doi.org/10.24033/asens.401) -- parent source for the coefficient-growth formula
  used in the total-variation corollary.

## Log

- 2026-07-10 -- created in progress after the measured-trace detector was killed and the user
  widened the question from a numerical height bound to general constraints on transverse zero
  motion.
