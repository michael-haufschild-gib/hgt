# The diagonal Gamma--Sonin orbit lift erases Mobius sign and has super-four critical energy

- **ID:** `gamma-damped-mobius-clock-critical-amplification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO WITH POSITIVE HT SUCCESSOR
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Source inputs:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`
  - `not_new_scientific_knowledge/gamma-damped-stationary-prime-log-covariance-law.md`
- **Statement:** Every basis-diagonal orbit map intertwining the doubled Mobius clock with Sonin
  reflection consumes the Mobius sign on the invariant Fisher state.  The undamped orbit sum is
  not a Hilbert vector near criticality.  The canonical time-one Gamma damping repairs its domain,
  but the odd Fisher tangent then has the exact critical energy

  ```text
  C_Gamma=6 sqrt(2) Gamma(1/4)/(pi^(3/2) Gamma(3/4))
         =4.5085689807...>4.                                (1)
  ```

  Thus an orbit-only Gamma--Sonin lift is not the missing nonexpansive RH source map.  The
  divisor/floor incidence cocycle must be inserted before the Gamma square and retained in a
  principal-relative trace.

## Doubled source clock and pointed Sonin system

Let `sigma>1`, `epsilon=sigma-1`, and use the squarefree source notation

```text
Z(sigma)=sum_d mu(d)^2d^(-sigma),
psi_sigma(d)=Z(sigma)^(-1/2)mu(d)d^(-sigma/2),
A_sigma=L-E_sigma(log d).                                  (2)
```

On `H_sq direct_sum H_sq`, put

```text
S(f,g)=(J_M g,J_M f),
Psi_sigma=2^(-1/2)(psi_sigma,J_M psi_sigma),
X_sigma=epsilon diag(A_sigma,-A_sigma),                    (3)
```

where `J_M e_d=mu(d)e_d` on squarefree support.  The parent theorem proves

```text
S Psi_sigma=Psi_sigma,
S X_sigma Psi_sigma=-X_sigma Psi_sigma,
||X_sigma Psi_sigma||^2=epsilon^2 Var_sigma(log d)->1.     (4)
```

Let `(K,U,J_infinity,xi)` be the pointed time-one Gamma cyclic representation:

```text
||xi||=1,
J_infinity xi=xi,
J_infinity U_h=U_(-h)J_infinity,
<xi,U_h xi>=phi(h)=(cosh h)^(-1/2).                       (5)
```

The scattering relations in `(5)` are the abstract content of the proved logarithmic Sonin
carrier.

## Forced sign-erasure theorem `[PROVED HERE]`

Consider a basis-diagonal orbit synthesis

```text
W e_d^+=a_d U_(log d)xi,
W e_d^-=b_d U_(-log d)xi.                                 (6)
```

Then

```text
W S=J_infinity W
```

on the algebraic finite-support core if and only if

```text
a_d=mu(d)b_d                                               (7)
```

for every squarefree `d`.

### Proof

The clock sends `e_d^+` to `mu(d)e_d^-`.  Hence the two sides of the intertwining relation on
`e_d^+` are

```text
mu(d)b_d U_(-log d)xi,
a_d J_infinity U_(log d)xi=a_d U_(-log d)xi.              (8)
```

This gives `(7)`; the equation on `e_d^-` is equivalent because `mu(d)^2=1`.  Conversely `(7)`
and `(5)` prove the intertwining on both basis sectors. `QED`

After writing `b_d=b(log d)`, equations `(2)`--`(3)` and `(7)` give

```text
W Psi_sigma
 =1/sqrt(2Z(sigma)) sum_d mu(d)^2d^(-sigma/2)b_d
     (U_(log d)+U_(-log d))xi,                            (9)

W X_sigma Psi_sigma
 =epsilon/sqrt(2Z(sigma)) sum_d mu(d)^2d^(-sigma/2)
     (log d-m_sigma)b_d(U_(log d)-U_(-log d))xi.          (10)
```

Thus the intertwiner necessarily uses the Mobius character to match reflection, and the
character disappears from both descended coefficient sums.  This is not a choice of gauge.

**Positive HT statement.**  In a reflection-constrained source, an arithmetic character can
survive as the grading of the constraint while disappearing from every orbit-diagonal invariant
state.  Character cancellation in the target must then be carried by a non-diagonal incidence
cocycle or a relative angle, not by orbit coefficients alone.

## Undamped orbit-domain no-go `[PROVED HERE]`

Take `b_d=1`.  For every `1<sigma<=2`, the positive even series `(9)` does not converge in `K`.

Indeed, in a dyadic squarefree block `N<=d<=2N`, all logarithmic differences have absolute value
at most `log 2`, and hence

```text
phi(log d-log e)>=phi(log 2)>0.                            (11)
```

Squarefree integers have positive density, so the block contains at least `cN` elements for all
large `N`.  The within-block Gram contribution is bounded below by a positive constant times

```text
(N N^(-sigma/2))^2=N^(2-sigma).                           (12)
```

Summing over disjoint dyadic blocks diverges for `sigma<=2`. `QED`

**Positive HT statement.**  Exact symmetry intertwining does not imply that the distinguished
source state lies in the target Hilbert domain.  In this example the obstruction is cofinal
positive covariance, not failure of any finite clock.

## Canonical Gamma damping

The source-derived damping from the Gamma sum-frequency diagonal is

```text
b_d=d_Gamma(log d)=sqrt(phi(2 log d))
   =2^(1/4)d^(-1/2)(1+d^(-4))^(-1/4).                    (13)
```

For `sigma>1`, the coefficients in `(9)` are absolutely summable after `(13)`, so both `(9)` and
`(10)` define vectors in `K`.  The odd kernel in `(10)` is

```text
K_odd(h,k)=phi(h-k)-phi(h+k).                             (14)
```

It is positive semidefinite because

```text
K_odd(h,k)
 =2 integral sin(hx)sin(kx) dnu_Gamma(x),                (15)
```

where `nu_Gamma` is the probability measure with characteristic function `phi`.

## Exact super-four critical limit `[PROVED HERE]`

Let

```text
Y_sigma=W_(d_Gamma)X_sigma Psi_sigma.                     (16)
```

Then

```text
lim_(sigma->1+)||Y_sigma||^2=C_Gamma,                    (17)
```

with `C_Gamma` as in `(1)`.

### Dirichlet reduction

Put

```text
eta_d=(1+d^(-4))^(-1/4),
F(z)=sum_d mu(d)^2 eta_d d^(-z),
alpha=(sigma+1)/2.                                       (18)
```

Since `eta_d-1=O(d^(-4))`, one has near `z=1`

```text
F(z)=1/(zeta(2)(z-1))+H(z),                              (19)
```

where `H` is holomorphic on a neighborhood of the closed line used below.  If

```text
D_epsilon(x)=-F'(alpha-i x)-m_sigma F(alpha-i x),         (20)
```

the spectral form `(15)` gives the exact identity

```text
||Y_sigma||^2
 =2sqrt(2) epsilon^2/Z(sigma)
   integral (Im D_epsilon(x))^2 dnu_Gamma(x).             (21)
```

### Pole scaling

The squarefree pole gives

```text
Z(1+epsilon)~1/(zeta(2)epsilon),
m_(1+epsilon)=epsilon^(-1)+O(1).                          (22)
```

For `x=epsilon y`, equations `(19)`--`(22)` imply locally uniformly in `y`

```text
epsilon^2D_epsilon(epsilon y)
 ->1/zeta(2) [1/(1/2-i y)^2-1/(1/2-i y)].                (23)
```

Away from the pole window, `(21)` tends to zero.  This follows by subtracting the pole in `(19)`,
using the standard vertical-line bounds for `zeta(z)/zeta(2z)`, and the exponential tail of the
Gamma cyclic density.  On the pole window the rational majorant obtained from `(19)` is square
integrable.  Dominated convergence after `x=epsilon y` is therefore valid.

The Gamma cyclic measure has continuous density `rho_Gamma`, and Fourier inversion gives

```text
rho_Gamma(0)
 =1/(2pi) integral_R (cosh t)^(-1/2)dt
 =Gamma(1/4)/(2sqrt(pi)Gamma(3/4)).                       (24)
```

Finally,

```text
integral_R
 (Im[1/(1/2-i y)^2-1/(1/2-i y)])^2dy=pi.                (25)
```

Combining `(21)`--`(25)` yields

```text
lim ||Y_sigma||^2
 =2sqrt(2)rho_Gamma(0)pi/zeta(2)
 =6sqrt(2)Gamma(1/4)/(pi^(3/2)Gamma(3/4)).                (26)
```

This proves `(17)`.

### The constant is strictly larger than four

For `t>=0`,

```text
cosh t<=(e^t+1)/2.
```

Consequently

```text
integral_R(cosh t)^(-1/2)dt
 >=4sqrt(2)asinh(1).                                     (27)
```

The elementary bounds `asinh(1)>7/8` and `pi^2<10` give

```text
12asinh(1)>pi^2.                                         (28)
```

Equations `(24)`, `(26)`, and `(28)` imply `C_Gamma>4`. `QED`

Numerical evaluation of the exact expression gives

```text
C_Gamma=4.5085689807710507...                             (29)
```

This number was used only to pre-certify the direction of the strict inequality; the proof is
`(27)`--`(28)`.

## No-go and nontrivial positive successor

The source clock has unit critical tangent energy by `(4)`, whereas its canonical diagonal
Gamma--Sonin image has energy `C_Gamma>4`.  Thus this source-fixed orbit lift is not nonexpansive.
Applying it to the completed tangent `chi_sigma=2X_sigma Psi_sigma` would have limiting energy
`4C_Gamma`, not four.

This kills only the **orbit-diagonal** lift.  It proves a stronger positive selection theorem:

```text
source four-unit Fisher tangent
  + Mobius reflection grading
  + time-one Gamma domain repair
  - orbit-diagonal synthesis
  -> finite universal residue-density energy C_Gamma>4.  (30)
```

The excess is a real archimedean covariance invariant, not an arbitrary norm loss.  A surviving
RH construction must use the complementary floor/tail packets before the Gamma square so that
their signed incidence angle contributes to the principal-relative subtraction.  Normalizing
`W_(d_Gamma)` by hand to force energy four is rejected: it would erase the exact Gamma cyclic
normalization and would still not restore the Mobius sign consumed in `(9)`--`(10)`.

**Positive general-HT statement.**  When a Dirichlet source pole is sewn to a continuous
archimedean cyclic measure at the unique exponent which repairs the Hilbert domain, the critical
tangent energy is the product of three local invariants:

```text
Dirichlet pole residue x archimedean spectral density at zero
  x universal centered-pole profile.                     (31)
```

For the squarefree pole and the time-one Gamma measure, `(31)` is exactly `(26)`.  This
residue-density law separates domain repair from metric contraction: the first can hold while the
second fails by a computable universal amount.

## Literature gate

Gamma/Meixner characteristic functions, squarefree Dirichlet series, Fisher scores, and Sonin
reflection are established parent mechanisms.  The project inputs remain admissible sources even
when already proved by other agents.  A targeted literature audit has not located the combined
forced-sign-erasure theorem or the critical constant `(26)`; specialist audit remains open.  No
novelty claim is needed for the route consequence: even if `(26)` has a literature parent, it
still excludes the orbit-only RH lift and selects the incidence-relative successor.

## Gates

- [x] doubled Mobius clock and unit critical Fisher tangent
- [x] characterize every basis-diagonal Sonin orbit intertwiner
- [x] prove forced Mobius sign erasure
- [x] prove failure of the undamped Hilbert domain
- [x] insert the canonical time-one Gamma diagonal
- [x] derive the positive odd Gamma kernel
- [x] prove the exact residue-density critical limit
- [x] prove the constant is strictly larger than four
- [x] isolate the complementary-incidence relative successor
- [ ] independent specialist literature audit
- [ ] formalize the finite clock/intertwiner algebra in Lean
- [ ] construct the incidence-before-Gamma relative lift
- [ ] RH
