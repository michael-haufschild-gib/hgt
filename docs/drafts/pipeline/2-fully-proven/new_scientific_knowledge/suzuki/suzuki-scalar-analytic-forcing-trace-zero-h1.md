# Trace zero forces \(H^1\) for the literal scalar Gamma normal operator with analytic forcing

- **ID:** `suzuki-scalar-analytic-forcing-trace-zero-h1`
- **Stage:** 2-fully-proven
- **Type:** EXACT SOURCE-NORMAL BENCHMARK / SCALE-GAP THEOREM
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-weak-signed-half-log-trace.md`,
  `suzuki-forced-gamma-upper-strip-gluing.md`,
  `suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Theorem

Let \(F:[0,\infty)\to\mathbb C\) be bounded and continuous, extend it by zero to the negative
half-line, and write

```text
P F(L)=2L F(L)-integral_0^L F(t)dt,

(R_full F)(L)
 =integral_0^infinity
   [2F(L)-F(L+s)-F(L-s)]/(exp(s)-1) ds.                 (1)
```

Assume on a terminal half-line

```text
P F+R_full F=G                                           (2)
```

in distributions, and assume:

1. \(\sqrt L\,F(L)\) is bounded;
2. after a compact initial segment, \(G\) is analytic in the physical boundary variable
   \(r=e^{-L}\):

   ```text
   G(L)=sum_(n>=0) a_n exp(-nL),                         (3)
   ```

   with the series and every finite \(L\)-derivative normally convergent for \(L\ge L_0\);
3. the nonconstant part has a positive radius exponent: for some \(\delta>0\),

   ```text
   G(L)-a_0=O(exp(-delta L)),                            (4)
   ```

   with the same estimate after every finite \(L\)-derivative.

Then the signed half-log trace

```text
beta=lim_(L->infinity) sqrt(L)F(L)                       (5)
```

exists.  If \(\beta=0\), then for every

```text
0<sigma<min(1,delta),                                   (6)
```

the terminal profile satisfies

```text
exp(sigma L)F in H1(L_1,infinity).                       (7)
```

In particular, if \(\delta>1/2\), then

```text
u(r)=F(log(1/r)) belongs to H1((0,epsilon)).              (8)
```

The exponent one is sharp for this mechanism: it is the first pole of the exact Gamma transport,
not a guessed regularity scale.

## 2. Trace and differentiated equation

Boundedness of \(G\) follows from `(3)`--`(4)`.  The weak signed-trace theorem applied to `(2)`
therefore gives `(5)`.

Differentiate `(2)` distributionally.  The primitive in \(P\) cancels one copy of \(F\), giving

```text
(2L+R_full)F'+F=G'.                                     (9)
```

The constant \(a_0\) disappears.  Equations `(3)`--`(4)` imply

```text
G'(L)=O(exp(-delta L))                                   (10)
```

with all finite derivatives.  Thus the only possible regular-singular half-log branch in `(9)`
is homogeneous; forcing contributes none.

## 3. Exact Gamma strip

The Fourier multiplier of \(R_{\rm full}\) is

```text
r(z)=psi(1+i z)+psi(1-i z)+2 EulerGamma.                 (11)
```

For the differentiated equation, the frequency ODE is

```text
f'=[-1/(2z)+(i/2)r(z)]f-(i/2)Ghat(z).                    (12)
```

The forced Gamma gluing theorem proves:

```text
beta=0
 -> the positive and negative real-frequency solutions glue
    holomorphically through 0 into 0<Im z<min(1,delta).  (13)
```

Here the forcing transform is holomorphic up to height \(\delta\) by `(10)`, while the homogeneous
propagator is holomorphic only up to the first Gamma pole at height one.  Normal convergence in
`(3)` makes this a literal source statement, not an assumed Hardy continuation.

## 4. Block Hardy estimate

Choose a smooth cutoff \(\chi\) supported on a sufficiently far terminal ray and equal to one
there.  Put \(W=\chi F\).  The exact differentiated cutoff identity is

```text
(2L+R_full)W'+W
 =chi G'
  +([R_full,chi]F)'
  +(2L+R_full)(chi'F)-[R_full,chi']F.                   (14)
```

Terms containing \(\chi'\) are compactly supported.  The Gamma commutator has exponential tails:
at log distance \(d\) from the cutoff it can interact with the transition region only through
\((e^s-1)^{-1}\) with \(s\ge d-O(1)\), hence is \(O(e^{-d})\).  Equation `(10)` supplies rate
\(\delta\) for the physical forcing.

Therefore, for every \(\sigma\) in `(6)`, the right side of `(14)` belongs to the exact block
source space

```text
N_sigma(H)
 =sum_(m in Z) exp(max(0,-m))
   ||exp(sigma L)H||_(L2([m,m+1]))<infinity.             (15)
```

The Gamma-wall block Hardy theorem applied to the glued solution `(13)` gives

```text
exp(sigma L)W in L2.                                    (16)
```

No weighted frequency moment is inferred from strip holomorphy; `(15)` is the quantitative input.

## 5. Weighted derivative and physical \(H^1\)

Conjugate `(14)` by \(e^{\sigma L}\).  The shifted Gamma multiplier has exact lower numerical
range

```text
Re r(x+i sigma)>=-kappa_sigma,

kappa_sigma
 =2 integral_0^infinity
   [cosh(sigma s)-1]/[exp(s)-1] ds<infinity.             (17)
```

Translate the cutoff far enough that \(2L\) dominates \(\kappa_\sigma\).  The weak weighted-tail
coercivity theorem, with scalar prime coupling \(T=0\), applied to `(14)` and `(16)` yields

```text
exp(sigma L)W' in L2.                                   (18)
```

Equations `(16)` and `(18)` prove `(7)`.

Finally,

```text
u'(r)=-F'(L)/r,       dr=exp(-L)dL,
```

so

```text
integral_0^epsilon |u'(r)|^2dr
 =integral_(L_epsilon)^infinity exp(L)|F'(L)|^2dL.       (19)
```

Choose \(1/2<\sigma<\min(1,\delta)\).  Then
\(e^L\le C e^{2\sigma L}\) on the terminal ray, and `(18)` makes `(19)` finite.  Boundedness of
\(u\) gives its \(L^2\) part.  This proves `(8)`. `QED`

## 6. Sharp source consequence

The theorem closes the scale-gap problem for the exact scalar boundary normal operator whenever
the forcing is analytic in \(r\).  In particular, every finite exponential-polynomial
characteristic datum

```text
f(x)=sum_j P_j(x)exp(lambda_j x)
```

has an analytic endpoint germ

```text
f(a-exp(-L))
 =sum_(n>=0) b_n exp(-nL).                              (20)
```

Thus the square-Evans reconstruction forcing itself lies in the closed class.

What is not yet proved is that Suzuki's **complete** lower-order source seen by the scalar endpoint
equation reduces to `(20)`.  Raw prime translations sample the solution at recursively exposed
interior seams; continuity alone does not make those germs analytic.  The new exact boundary is:

```text
analytic/exponentially regular forcing     -> trace-zero H1 [PROVED];
dense prime-seam forcing is Gamma-subcritical
  after exact valuation/Feshbach transport -> [OPEN SOURCE CONNECTOR].       (21)
```

Generic counterexamples such as \(F(L)=e^{-\sqrt L}\) do not contradict the theorem: their induced
forcing is inverse-log-flat but nonanalytic in \(r\), violating `(3)`--`(4)`.

## 7. Hostile audit

1. **No conormal premise on \(F\).**  Only its optimal half-log bound and the exact weak equation
   are assumed.
2. **No bounded-source shortcut.**  Bounded forcing alone is insufficient; `(3)`--`(4)` are
   load-bearing.
3. **No strip-holomorphy-to-\(L^2\) leap.**  Block norm `(15)` supplies the quantitative Hardy
   estimate.
4. **No derivative premise.**  Weighted-tail coercivity proves `(18)` weakly.
5. **No scalar-to-Suzuki overclaim.**  Dense prime-seam regularity remains open in `(21)`.
6. **No RH claim.**  Even a completed trace-zero lift leaves corona no-return and raw Evans
   injectivity.

## 8. Novelty boundary

Logarithmic Dirichlet traces, Gamma variation of constants, strip Hardy estimates, and weighted
energy arguments are classical ingredients.  Targeted searches found no theorem combining the
literal normal form `(1)`, signed trace, first Gamma pole, source block norm, and weak physical
\(H^1\) upgrade under analytic boundary forcing.  Candidate novelty is the exact scale-gap theorem
`(1)`--`(21)` and its identification of dense prime-seam forcing as the remaining Suzuki source
obstruction.  Priority remains unverified.

## 9. Lean status

Unconditional Lean modules already certify the load-bearing algebraic pieces:

```text
SuzukiGammaSkewFrequencyFlux.lean;
SuzukiGammaWallHardyBoundary.lean;
SuzukiGammaWeightedTailCoercivity.lean;
SuzukiPhysicalLogBoundaryMomentLock.lean.
```

The full theorem additionally needs vector-valued Fourier/Paley--Wiener strip translation,
Gamma-ratio modulus, block \(L^2\) convolution estimates, and the weak mollifier passage.  Those
remain paper mathematics in the predecessor modules; adding a theorem that assumes `(7)` or
`(18)` would be circular and is rejected.

## Gates

- [x] exact scalar log-coordinate equation retained
- [x] signed trace obtained in the weak class
- [x] analytic forcing differentiated into a subcritical source
- [x] zero trace glued across the exact Gamma strip
- [x] literal cutoff commutator shown block-subcritical
- [x] shifted block \(L^2\) proved
- [x] weighted derivative and physical \(H^1\) proved
- [x] analytic square-Evans endpoint datum placed in the theorem class
- [ ] prove complete prime-seam/Feshbach forcing is Gamma-subcritical
- [ ] apply to every completed Suzuki trace-zero zero mode
- [ ] prove raw Evans injectivity
- [ ] RH
