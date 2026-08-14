# The paired Suzuki seam turns the Carleman port into a Gamma-subcritical logistic coupling

- **ID:** `suzuki-paired-seam-carleman-logistic-normal-form`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT TWO-ORIENTATION NORMAL FORM / WEIGHTED CROSS-PORT THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-carleman-flat-port-weighted-strip-barrier.md`,
  `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`

## 1. Result

The one-sided Carleman response is not an uncontrolled source at an interior prime seam.  Once
both physical orientations at that seam are retained, it is an exact off-diagonal coupling.  Its
logarithmic derivative is convolution by the logistic density, which is bounded on every
subcritical Gamma-weighted space.

Let \(u\) be bounded on \((-1,1)\), continuous at zero, and first assume its punctured
one-sided profiles are smooth with the difference integrals below convergent.  The identities
extend to the logarithmic form domain in distributions by smooth approximation.  Put

```text
u_0=u(0),
F_+(L)=u(exp(-L))-u_0,
F_-(L)=u(-exp(-L))-u_0,       L>0.                       (1)
```

For the fixed-window logarithmic jump

```text
(J_0u)(x)=integral_(-1)^1 [u(x)-u(y)]/|x-y| dy,          (2)
```

interpreted by the usual difference cancellation at \(y=x\), define

```text
(R F)(L)
 =integral_0^infinity [F(L)-F(L+s)]/(exp(s)-1) ds
  +integral_0^L [F(L)-F(L-s)]/(exp(s)-1) ds,

(C F)(L)
 =integral_0^infinity F(v)/(1+exp(v-L)) dv.              (3)
```

Then, exactly,

```text
(J_0u)( exp(-L))
 =[2L+q(L)]F_+(L)-integral_0^L F_+(t)dt
  +(R F_+)(L)-(C F_-)(L),                               (4+)

(J_0u)(-exp(-L))
 =[2L+q(L)]F_-(L)-integral_0^L F_-(t)dt
  +(R F_-)(L)-(C F_+)(L),                               (4-)

q(L)=log(1+exp(-L)).                                    (5)
```

The exponentially small scalar \(q\) is harmless.  The only cross-orientation term is \(C\).
Distributional differentiation gives

```text
(C F)'(L)=(K F)(L),

(K F)(L)
 =integral_0^infinity F(v) k(v-L)dv,
k(t)=exp(t)/(1+exp(t))^2
    =1/[4 cosh(t/2)^2].                                 (6)
```

After extending \(F\) by zero to the negative half-line, \(K\) is a truncated convolution by
\(k\).  For every \(|\sigma|<1\),

```text
||exp(sigma L) K F||_(L2(R))
 <=m_sigma ||exp(sigma L)F||_(L2(R)),

m_sigma
 =integral_R exp(-sigma t)k(t)dt
 =Gamma(1+sigma)Gamma(1-sigma)
 =pi sigma/sin(pi sigma),                               (7)
```

with \(m_0=1\) by continuity.  Hence the paired cross block is bounded throughout the exact Gamma
strip and has its first singularity at the same height one as Gamma transport.

This changes the local frontier:

```text
one-sided cut:
  Carleman response may carry an arbitrary flat port;   [FALSE ROUTE]

paired interior seam:
  Carleman derivative is a bounded off-diagonal
  logistic coupling and belongs on the operator side;   [PROVED]

physical endpoint:
  opposite orientation is the exact zero exterior,
  so no arbitrary Carleman source remains.               [PROVED LOCALLY]     (8)
```

The flat profile \(e^{-\sqrt L}\) remains a valid counterexample to a one-sided
trace-to-weighted-source inference.  It is not a counterexample to the paired homogeneous system:
its own Carleman response is precisely the opposite-orientation term that `(4+)`--`(4-)` retain.

## 2. Same-side calculation

Take \(x=r=e^{-L}\).  On \(0<y<r\), write \(y=r e^{-s}\).  Then

```text
dy/(r-y)=ds/(exp(s)-1),
```

and the contribution is

```text
integral_0^infinity
 [F_+(L)-F_+(L+s)]/(exp(s)-1) ds.                       (9)
```

On \(r<y<1\), write \(y=r e^s\), \(0<s<L\).  Since

```text
exp(s)/(exp(s)-1)=1+1/(exp(s)-1),
```

this side contributes

```text
L F_+(L)-integral_0^L F_+(t)dt
+integral_0^L
 [F_+(L)-F_+(L-s)]/(exp(s)-1) ds.                       (10)
```

Adding `(9)` and `(10)` gives

```text
L F_+(L)-integral_0^L F_+(t)dt+(R F_+)(L).              (11)
```

The constant \(u_0\) cancels from every difference, so no regularity beyond continuity at the
seam has been inserted.

## 3. Opposite-side calculation

Write \(y=-s\), \(0<s<1\), and then \(s=e^{-v}\).  The opposite-side contribution is

```text
integral_0^1 [F_+(L)-F_-(-log s)]/(e^-L+s) ds

=integral_0^infinity
  [F_+(L)-F_-(v)]/[1+exp(v-L)] dv.                      (12)
```

The scalar integral is exact:

```text
integral_0^infinity dv/[1+exp(v-L)]
 =log(1+exp(L))
 =L+log(1+exp(-L)).                                     (13)
```

Therefore `(12)` equals

```text
[L+q(L)]F_+(L)-(C F_-)(L).                              (14)
```

Adding `(11)` proves `(4+)`.  Reflection proves `(4-)`. `QED`

The fixed window in `(2)` is a local normal choice.  Replacing it by Suzuki's unit-range window
or a smooth physical localization changes `(4+)`--`(4-)` only by kernels smooth at the seam.
After \(r=e^{-L}\), their differentiated profiles are \(O(e^{-L})\), as in the proved polar
remainder theorem.

## 4. Logistic derivative and exact weighted norm

Differentiate the kernel in `(3)`:

```text
d/dL [1/(1+exp(v-L))]
 =exp(v-L)/[1+exp(v-L)]^2
 =k(v-L),                                               (15)
```

which proves `(6)` first for compactly supported smooth \(F\), then distributionally by
approximation.

Conjugation by the physical Gamma weight gives

```text
exp(sigma L)(K F)(L)
 =integral_R
   exp(sigma(L-v))k(v-L)
   [exp(sigma v)F(v)]dv.                                (16)
```

Young's inequality therefore gives `(7)` with the \(L^1\) norm of
\(t\mapsto e^{-\sigma t}k(t)\).  Put \(z=e^t\).  Then

```text
integral_R exp(-sigma t)k(t)dt
 =integral_0^infinity z^(-sigma)/(1+z)^2 dz
 =Beta(1-sigma,1+sigma)
 =Gamma(1-sigma)Gamma(1+sigma).                         (17)
```

The beta integral is finite exactly for \(-1<\sigma<1\).  Euler reflection gives the final
expression in `(7)`. `QED`

## 5. Differentiated paired normal equation

Put

```text
G_+(L)=(J_0u)(exp(-L)),
G_-(L)=(J_0u)(-exp(-L)).                                (18)
```

Differentiating `(4+)`--`(4-)` yields

```text
[2L+q(L)]F_+' +(R F_+)'
 +[1+q'(L)]F_+ -K F_-
 =G_+',                                                  (19+)

[2L+q(L)]F_-' +(R F_-)'
 +[1+q'(L)]F_- -K F_+
 =G_-'.                                                  (19-)
```

Thus \(K\) is a bounded zero-order two-orientation coupling.  In a weighted energy argument its
real part is bounded below by \(-m_\sigma\) times the paired \(L^2\) mass.  Together with a bounded
weighted prime adjacency \(T_{a,\rho}\), the terminal coercive coefficient is

```text
2L-kappa_sigma-m_sigma-||T_(a,rho)||+O(exp(-L)).         (20)
```

It is positive on a sufficiently far ray.  No sign or self-adjointness of \(K\) is required.

Equation `(19)` does not by itself prove weighted \(H^1\).  One must first show that the complete
paired seam state has shifted \(L^2\) and that its only half-log trace coordinates are the two
physical roots.  It proves that the Carleman cross block is not an additional source obstruction
once the correct paired carrier has been realized.

## 6. Implication for the tempered orbit connector

At every interior valuation center

```text
x_nu=+/-a+ell(nu),
```

retain both punctured orientations and subtract their common value \(u(x_\nu)\).
Equations `(4+)`--`(4-)` give the exact local principal block.  Prime translation moves one
oriented center to another and is carried by \(T_{a,\rho}\); the cross-side singular integral is
\(K\); polar and localization remainders are \(O(e^{-L})\).

At a physical endpoint, one orientation is the zero exterior extension.  Therefore the same
formula applies with its opposite component identically zero.  Exact endpoint resonances are
retained as the second oriented root.

The remaining global theorem is now narrower:

```text
assemble all paired local equations in the weighted orbit norm
+ prove no independent half-log trace at an interior center
+ control moving localization radii by R(a)<infinity
 -> shifted L2 paired state
 -> terminal coercivity (20)
 -> trace-zero H1_0.                                    (21)
```

The local Carleman port and its Gamma strip are closed.

## 7. Hostile audit

1. **No one-sided estimate reused.**  Both seam orientations occur explicitly in `(4+)`--`(4-)`.
2. **No false decay of \(C F\).**  \(C F\) may have the flat response proved previously;
   only its derivative is classified as the bounded coupling \(K F\).
3. **No self-adjointness smuggling.**  Weighted boundedness follows from Young's inequality.
4. **No endpoint confusion.**  Physical zero exterior is a genuine zero opposite component;
   an interior artificial cut is not.
5. **No global carrier claim.**  Infinite paired assembly, trace support, and exceptional
   apertures remain open.
6. **No RH claim.**  Nonzero-trace return and raw Evans positivity are untouched.

## 8. Novelty boundary

Carleman kernels, logistic densities, beta integrals, and paired boundary charts are classical
ingredients.  Candidate-new source knowledge is the exact Suzuki correction

```text
literal cutoff Carleman port
 -> retain both oriented seam germs
 -> derivative becomes logistic cross coupling
 -> same sharp strip |sigma|<1 as Gamma
 -> no independent local weighted source obstruction.  (22)
```

Corpus search found the one-sided Carleman response and Gamma wall separately, but not
`(4+)`--`(7)` or the paired interpretation `(8)`.  External priority remains unaudited.

## 9. Lean decision

Faithful formalization needs singular integral cancellation, improper beta integration, weighted
convolution on \(L^2\), and the physical logarithmic chart.  These are absent from the current
formal tree.  An algebraic two-by-two wrapper would not certify `(4+)` or `(7)` and is rejected.
Formalization should start with the actual Carleman/logistic analytic infrastructure when the
global paired carrier theorem is complete.

## Gates

- [x] derive the exact same-orientation Volterra--Gamma block
- [x] derive the exact opposite-orientation Carleman block
- [x] differentiate it to the logistic coupling
- [x] prove exact weighted norm for every `|sigma|<1`
- [x] place the paired cross block on the bounded operator side
- [x] identify physical endpoint as the genuine zero-opposite component
- [ ] assemble the infinite paired orbit equation
- [ ] prove half-log trace is supported only on physical roots
- [ ] prove shifted `L2` for the complete paired state
- [ ] prove trace-zero completed modes enter `H1_0`
- [ ] prove completed Evans injectivity
- [ ] RH or whole-Connes no-go
