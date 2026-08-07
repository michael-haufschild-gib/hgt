# Gamma numerical-range coercivity kills the two Suzuki derivative charges

- **ID:** `suzuki-gamma-weighted-tail-coercivity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-SUPPORTED WEAK REGULARITY
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Inputs:** `suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`,
  `suzuki-support-pruned-selfadjoint-seam-carrier.md`

## 1. Result

The two high-frequency charges found by the frequency-only forced Gamma analysis are genuine for
an arbitrary forced ODE.  They are not free on a physical Suzuki tail.  After exponential
conjugation, the real part of the shifted Gamma multiplier has a finite lower bound.  A cutoff
supported sufficiently far down the positive logarithmic ray makes multiplication by \(2L\)
dominate that lower bound and every bounded self-adjoint prime coupling.  The physical equation
then gives a coercive energy estimate for its derivative.

Precisely, let \(X\) be a complex Hilbert space, \(T=T^*\in\mathcal B(X)\), and

```text
(R F)(L)
 =integral_0^infinity
   [2F(L)-F(L+s)-F(L-s)]/(exp(s)-1) ds.                 (1)
```

Fix \(0<\sigma<1\), define

```text
R_sigma=exp(sigma L) R exp(-sigma L),                   (2)

kappa_sigma
 =2 integral_0^infinity
    [cosh(sigma s)-1]/[exp(s)-1] ds < infinity.         (3)
```

Suppose \(W\) is supported in \([L_0,\infty)\), put

```text
V=exp(sigma L)W,
U=V'-sigma V=exp(sigma L)W',                            (4)
```

and assume, in distributions,

```text
(2L I+R_sigma-T)U+V=G,                                  (5)
```

where \(V,G\in L^2(\mathbb R;X)\).  Then

```text
L_0>(kappa_sigma+||T||)/2
  implies
U in L2,  V in H1,  exp(sigma L)W' in L2.               (6)
```

The theorem is a weak theorem: \(W'\in L^2\) is a conclusion, not a premise.

Applied after the Gamma-wall block Hardy theorem, `(6)` shows that both derivative scattering
charges vanish automatically for every source-supported completed carrier realization.  Thus
`SUZUKI-DERIVATIVE-SCATTERING-ZERO` is no longer an independent arithmetic conjecture.  The live
connector is the literal completed-domain realization of the support-pruned carrier and its
cutoff equation.

## 2. Exact shifted Gamma lower bound

On the shifted Fourier line, \(R_\sigma\) has multiplier

```text
r_sigma(x)=r(x+i sigma),

r(z)=integral_0^infinity
 [2-exp(i z s)-exp(-i z s)]/[exp(s)-1] ds.              (7)
```

The integral is absolutely convergent for \(0<\sigma<1\).  Taking real parts gives

```text
Re r_sigma(x)
 =2 integral_0^infinity
   [1-cosh(sigma s)cos(xs)]/[exp(s)-1] ds.              (8)
```

Since \(\cos(xs)\le1\) and \(\cosh(\sigma s)\ge0\),

```text
1-cosh(sigma s)cos(xs)
 >=1-cosh(sigma s).                                     (9)
```

Near zero the integrand in `(3)` is \(O(s)\).  At infinity it is
\(O(e^{-(1-\sigma)s})\).  Therefore \(\kappa_\sigma<\infty\), and `(8)`--`(9)` imply

```text
Re r_sigma(x)>=-kappa_sigma       for every x in R.      (10)
```

Plancherel consequently gives the exact numerical-range estimate

```text
Re <R_sigma U,U> >= -kappa_sigma ||U||_2^2              (11)
```

on the multiplier domain.  No positivity of the non-self-adjoint shifted operator is asserted;
the finite lower bound `(11)` is the sharp property needed below.

Equivalently,

```text
kappa_sigma
 =-[psi(1-sigma)+psi(1+sigma)+2 EulerGamma],             (12)
```

but the integral form `(3)` makes finiteness and the sign transparent.

## 3. Strong energy estimate

First suppose \(V\) is smooth enough that all terms in `(5)` belong to \(L^2\).  The support
condition also puts \(U\) in \([L_0,\infty)\).  Taking the real part of the \(L^2\) inner product
of `(5)` with \(U\), and using `(11)` and self-adjointness of \(T\), gives

```text
[2L_0-kappa_sigma-||T||]||U||_2^2
 <=Re <G-V,U>
 <=||G-V||_2 ||U||_2.                                  (13)
```

Hence, with

```text
c_sigma=2L_0-kappa_sigma-||T||>0,
```

one has

```text
||U||_2<=c_sigma^(-1)||G-V||_2,                         (14)
||V'||_2<=c_sigma^(-1)||G-V||_2+sigma||V||_2.           (15)
```

Notice that no integration by parts in \(L\) was used.  In particular, there is no circular
boundary term involving an as-yet unproved derivative of \(V\).

## 4. Weak-domain upgrade

It remains to justify `(13)` when \(U=V'-\sigma V\) is only a distribution.  This step is
load-bearing.

Choose a nonnegative compactly supported smooth approximate identity \(\rho_\epsilon\), supported
in \([-\epsilon,\epsilon]\), and write

```text
V_epsilon=rho_epsilon*V,
U_epsilon=rho_epsilon*U
         =V_epsilon'-sigma V_epsilon.                   (16)
```

Translation invariance makes \(R_\sigma\) and \(T\) commute with convolution.  Multiplication by
\(L\) has the exact commutator

```text
rho_epsilon*(L U)
 =L U_epsilon-k_epsilon*U,
k_epsilon(s)=s rho_epsilon(s).                          (17)
```

Convolving `(5)` and using `(17)` yields

```text
(2L I+R_sigma-T)U_epsilon+V_epsilon
 =G_epsilon+2k_epsilon*U.                               (18)
```

The apparent derivative on the last term is harmless:

```text
k_epsilon*U
 =k_epsilon'*V-sigma k_epsilon*V.                       (19)
```

Scaling of the mollifier gives

```text
||k_epsilon'||_1<=C_rho,
||k_epsilon||_1<=C_rho epsilon.                         (20)
```

Thus the right side of `(18)` is bounded in \(L^2\), uniformly for
\(0<\epsilon\le\epsilon_0\).

The Fourier transform of \(U_\epsilon\) is

```text
(i x-sigma) rhohat(epsilon x) Vhat(x).
```

The Schwartz decay of \(\widehat\rho\), together with
\(r_\sigma(x)=O(\log(2+|x|))\), puts \(R_\sigma U_\epsilon\) in \(L^2\).
Equation `(18)` then puts \(L U_\epsilon\) in \(L^2\), so every inner product used in `(13)` is
legitimate.  Moreover

```text
supp U_epsilon subset [L_0-epsilon,infinity).            (21)
```

Choose \(\epsilon_0>0\) so that

```text
c=2(L_0-epsilon_0)-kappa_sigma-||T||>0.                 (22)
```

Applying `(13)` to `(18)` gives a uniform \(L^2\) bound on \(U_\epsilon\).  A weakly convergent
subsequence has an \(L^2\) limit \(U_0\).  Since
\(U_\epsilon\to V'-\sigma V\) in distributions, \(U_0=V'-\sigma V\).  Therefore \(U\in L^2\),
and `(4)` gives \(V\in H^1\).  This proves `(6)`. `QED`

## 5. Source application and charge elimination

Let \(F\) be a realized completed Suzuki carrier tail with zero half-log trace.  Translate a
smooth cutoff far enough down the logarithmic ray and put \(W=\chi F\).  The exact cutoff identity
is

```text
(2L I+R-T)W'+W
 =([R,chi]F)'
  +(2L I+R-T)(chi'F)-[R,chi']F.                         (23)
```

The Gamma-wall block Hardy theorem gives, for every \(0<\sigma<1\),

```text
exp(sigma L)W in L2.                                    (24)
```

The order-minus-one commutator theorem and the compact support of \(\chi'\) put the exponential
conjugate of the right side of `(23)` in \(L^2\).  Apply `(6),` choosing the translated cutoff
past

```text
[kappa_sigma+||T||]/2.
```

Then

```text
exp(sigma L)W' in L2.                                   (25)
```

For \(1/2<\sigma<1\), `(25)` implies the original physical derivative estimate because

```text
integral exp(L)||W'(L)||^2 dL
 <=C integral exp(2sigma L)||W'(L)||^2 dL.              (26)
```

The two derivative charges classify failure of `(25)`.  Hence `(25)` proves

```text
d_+^(sigma)=d_-^(sigma)=0                               (27)
```

for every physical-support solution satisfying the displayed source hypotheses.  The charges
remain useful invariants for arbitrary forced Gamma equations, but they are annihilated by
Suzuki's one-sided physical support and the \(2L\) numerical range.

## 6. Hostile audit

1. **No positivity after vertical shift.**  \(R_\sigma\) is not self-adjoint.  The proof uses the
   exact lower numerical-range bound `(10)`, not a false positivity claim.
2. **No derivative premise.**  Section 4 obtains \(V'\in L^2\) by mollification; it is not used to
   justify the initial test.
3. **No boundary integration by parts.**  The energy test pairs the equation with
   \(U=V'-\sigma V\) and never rewrites \(\operatorname{Re}\langle V,V'\rangle\).
4. **No arbitrary ODE conclusion.**  Physical support and the growing \(2L\) coefficient are
   essential.  Without them the two scattering charges in the general classification need not
   vanish.
5. **No carrier-realization smuggling.**  The theorem applies once the completed zero mode has
   been realized in the support-pruned Hilbert carrier and `(23)` holds there.  That exact
   completed-domain map remains open.
6. **No RH claim.**  Raw Evans injectivity, prolate producer P, and incidence producer I remain
   unresolved.

## 7. Novelty boundary

Numerical-range estimates for shifted Fourier multipliers and Friedrichs mollifiers are standard
ingredients.  Corpus and targeted literature searches found no source-specific theorem combining

```text
vertical Gamma line
 -> exact finite lower numerical range
 -> physical 2L tail coercivity
 -> weak weighted H1 upgrade
 -> automatic annihilation of both derivative scattering charges.       (28)
```

The new content claimed here is this conjunction and its correction of the Route-O frontier.
Priority remains unverified.

## 8. Exact frontier after the theorem

The completed-Evans branch is now

```text
completed zero mode with both half-log traces zero
 -> literal support-pruned carrier realization and cutoff identity
 -> Gamma-wall block Hardy L2
 -> weighted-tail coercivity H1
 -> raw Evans kernel.                                    (29)
```

No independent derivative-scattering conjecture remains between the second and fourth arrows.
The hard open theorem is the first arrow: build the source-domain carrier map, including its
square-summability and exact intertwining with the compressed prime adjacency.

## 9. Lean certificate

The source-bearing finite inequalities are formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiGammaWeightedTailCoercivity.lean
```

The module proves:

```text
neg_suzukiGammaShiftLowerKernel_le_realIntegrand
suzukiGammaShiftLowerKernel_nonneg
suzukiGammaWeightedTailEnergy_norm_le
suzukiGammaWeightedTail_derivative_norm_le
```

The exact pointwise Gamma numerical-range loss, coercive Hilbert energy estimate, and recovery of
the ordinary weighted derivative are therefore kernel-checked.

**`(3)`, `(10)` and the Plancherel step `(11)` are now formal**, in

```text
formal/GaloisForLFunctions/RHTower/SuzukiGammaShiftKappa.lean
```

```text
suzukiGammaShiftLowerKernel_le_one          sigma ≤ 1: majorant ≤ 1 - e^{-s} ≤ 1, via the exact
                                            identity 2(cosh s - 1) = e^{-s}(e^s-1)^2
suzukiGammaShiftLowerKernel_le_exp          s ≥ 1: majorant ≤ 4 e^{-(1-sigma)s}
integrableOn_suzukiGammaShiftLowerKernel    (3): the majorant is integrable on (0,∞) for
                                            0 ≤ sigma < 1
suzukiGammaShiftKappa                       kappa_sigma itself
suzukiGammaShiftKappa_nonneg                kappa_sigma ≥ 0
abs_suzukiGammaShiftRealIntegrand_le        |Re integrand| ≤ majorant + x^2 s^2/(e^s-1)
integrableOn_cosineDefect                   the cosine defect term is integrable
integrableOn_suzukiGammaShiftRealIntegrand  hence so is the exact integrand
neg_suzukiGammaShiftKappa_le_integral       (10): -kappa_sigma ≤ ∫ Re r_sigma, every real x
neg_mul_integral_normSq_le_integral_re_symbol
                                            (11): a multiplication operator whose symbol has real
                                            part ≥ -kappa has quadratic form ≥ -kappa ‖·‖²
```

The mollifier commutator `(17)` is formal too, as reusable geometry, in

```text
formal/GaloisForLFunctions/HTGeometry/MollifierPositionCommutator.lean
  mollify, firstMomentKernel
  mollify_position_eq   (17): rho ⋆ (L·U) = L·(rho ⋆ U) - (k ⋆ U),  k(s) = s rho(s)
  mollify_add, mollify_zero
```

What is still paper mathematics is the *limit* in section 4 — that the mollified equation `(18)`
passes to `(5)` as the mollifier concentrates — together with the identification of `R_sigma` with
multiplication by `r_sigma` on the Fourier side.  Lean does not replace either by an assumed
completed-source map.

## Gates

- [x] derive exact shifted Gamma numerical-range lower bound
- [x] prove weak source-supported weighted derivative estimate
- [x] prove physical tail forces both derivative scattering charges to vanish
- [x] separate arbitrary forced ODE charges from source-supported Suzuki charges
- [x] formalize exact Gamma integrand lower bound
- [x] formalize coercive Hilbert energy estimate
- [ ] construct literal completed support-pruned carrier map
- [ ] apply theorem to every completed trace-zero zero mode
- [ ] identify resulting state with raw Evans kernel
- [ ] prove raw Evans injectivity
- [ ] RH
