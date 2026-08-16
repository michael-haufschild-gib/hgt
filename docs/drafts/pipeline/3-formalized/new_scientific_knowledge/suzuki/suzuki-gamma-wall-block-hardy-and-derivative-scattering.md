# Gamma-wall block Hardy transfer and the derivative scattering obstruction

- **ID:** `suzuki-gamma-wall-block-hardy-and-derivative-scattering`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / FORCED STRIP ESTIMATE + SHARP DERIVATIVE CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Inputs:** `suzuki-forced-gamma-upper-strip-gluing.md`,
  `suzuki-gamma-homogeneous-half-log-scattering-classification.md`,
  `suzuki-support-pruned-selfadjoint-seam-carrier.md`

## 1. Result and correction of the previous frontier

The sufficient source condition

```text
integral_R (1+|x|)^(1/2+sigma)||b(x+i sigma)||dx < infinity
```

in the forced Gamma-gluing theorem is far stronger than the literal cutoff equation supplies.
It also obscures two different questions:

```text
strip Hardy decay:          f(.+i sigma) in L2,
localized physical H1:      x f(.+i sigma) in L2 after tail localization.
```

They are not equivalent.  This card proves:

1. a block Hardy theorem adapted to a physical source with the exact Gamma-wall tails
   `O(exp(-|L|))`;
2. an \(L^2\), rather than weighted-\(L^1\), Hardy criterion for the forced Gamma equation;
3. the order-minus-one commutator theorem which puts a literal smooth cutoff residual in that
   \(L^2\) class;
4. a sharp classification of the remaining derivative obstruction by two high-frequency Gamma
   scattering charges.

Thus the forced strip-decay gate is no longer a frequency-moment conjecture.  The actual remaining
regularity gate is vanishing of two source-defined derivative scattering charges on the completed
support-pruned carrier.

## 2. Exact propagator on a shifted line

Let \(X\) be a complex Hilbert space, \(T=T^*\in\mathcal B(X)\), and

```text
r(z)=psi(1+i z)+psi(1-i z)+2 EulerGamma.
```

On \(0<\operatorname{Im}z<1\), put

```text
H(z)=z^(-1/2) exp(i EulerGamma z)
     [Gamma(1+i z)/Gamma(1-i z)]^(1/2) exp(-i z T/2).
```

Then

```text
H'(z)=i B(z)H(z),
B(z)=(1/2)[r(z)I-T]+i/(2z)I.                            (1)
```

Fix \(0<\sigma<1\), write \(z=x+i\sigma\), and put

```text
p=1/2+sigma.                                             (2)
```

Stirling's formula and the polygamma asymptotics give constants depending only on
\(\sigma\) and \(\|T\|\) such that

```text
||H(x+i sigma)|| <= C(1+|x|)^(-p),
||H(x+i sigma)^(-1)|| <= C(1+|x|)^p,                    (3)

B(x+i sigma)
 =[log(1+|x|)+EulerGamma]I-T/2+O_B(X)((1+|x|)^(-1)),

||d^j/dx^j B(x+i sigma)|| <= C_j(1+|x|)^(-j),
                                                        j=1,2,3.             (4)
```

The \(T\)-factors in \(H(x+i\sigma)H(t+i\sigma)^{-1}\) are unitary because \(x-t\) is
real.  Consequently, on either outward frequency tail,

```text
||H(x+i sigma)H(t+i sigma)^(-1)||
 <=C[(1+|t|)/(1+|x|)]^p
```

whenever \(x,t\) have one sign and \(|x|\ge |t|\).                         `(5)`

No estimate below replaces the Gamma transport by a generic polynomial propagator.  Equations
`(3)`--`(5)` are consequences of its literal Gamma quotient.

## 3. Physical-wall source space

Use the Fourier convention

```text
Ghat(z)=integral_R exp(-i z L)G(L)dL.                    (6)
```

For \(m\in\mathbb Z\), let \(I_m=[m,m+1]\), and define

```text
N_sigma(G)
 =sum_(m in Z) exp(max(0,-m))
    ||exp(sigma L)G(L)||_(L2(I_m;X)).                    (7)
```

This is a physical, not frequency, norm.  It measures the only expanding canonical branch:
negative physical location \(L\sim-m\) meets Gamma frequency at \(|x|\sim e^{-L}\), so that block
has exact transport cost \(e^{-m}\).

If

```text
||G(L)|| <=C exp(-|L|),                                  (8)
```

then `(7)` is finite for every \(0<\sigma<1\).  Indeed, on \(m\ge0\) the summand is
`O(exp(-(1-sigma)m))`; on \(m=-k-1<0\) it is `O(exp(-sigma k))`.

The pointwise hypothesis `(8)` is only a convenient corollary.  The theorem uses the exact block
space `(7)`.

## 4. One-block Gamma Hardy theorem

### Theorem 1

`[PROVED]` Let \(G\in L^2(I_m;X)\) be supported in \(I_m\), and put

```text
b(z)=-(i/2)Ghat(z).                                      (9)
```

Every solution of

```text
f'(z)=iB(z)f(z)+b(z)                                    (10)
```

on the shifted line has

```text
||f(.+i sigma)||_L2
 <=C_sigma,T [
   ||c||+
   exp(max(0,-m))
   ||exp(sigma L)G||_(L2(I_m;X))],                      (11)
```

where \(Hc\) is its homogeneous component.  The constant in `(11)` is independent of \(m\) and
\(G\).

### Proof

Put

```text
g(L)=exp(sigma L)G(L).
```

Then \(b(x+i\sigma)\) is, up to the fixed factor \(-i/2\), the real Fourier transform of \(g\).
Plancherel gives

```text
||b(.+i sigma)||_2=C_F ||g||_2.                          (12)
```

Variation of constants on the horizontal line gives

```text
f(x+i sigma)
 =H(x+i sigma)[c+
   integral_0^x H(t+i sigma)^(-1)b(t+i sigma)dt].        (13)
```

Choose

```text
X_m=C_0 exp(max(0,-m))                                  (14)
```

with \(C_0\) large enough that, for \(|x|\ge X_m\) and \(L\in I_m\),

```text
C(x,L):=B(x+i sigma)+L I
```

is invertible and

```text
||C(x,L)^(-1)||<=C/[log(1+|x|)+L-C].                    (15)
```

This follows from `(4)`: the real part of the scalar part of \(B\) is
\(\log(1+|x|)+O(1)\), while \(T/2\) is self-adjoint and bounded.

On \(|x|\le X_m\), equations `(3)`, `(5)`, and Cauchy--Schwarz give the finite-interval weighted
Hardy estimate

```text
||H(x+i sigma) integral_0^x H(t+i sigma)^(-1)b(t+i sigma)dt
 ||_(L2(|x|<=X_m))
 <=C X_m ||b(.+i sigma)||_2.                            (16)
```

It remains to control the two frequency tails without paying another power of \(X_m\).  For fixed
\(L\in I_m\), put

```text
E(t,L)=H(t+i sigma)^(-1)exp(-itL).
```

By `(1)`,

```text
partial_t E(t,L)=-i E(t,L)C(t,L).                       (17)
```

All operator factors in `(17)` commute: each is a scalar multiple of \(I\) plus a function of
the one self-adjoint operator \(T\).  Two integrations by parts therefore give

```text
integral E(t,L)dt
 = i E C^(-1)
   +E C^(-1)(C^(-1))'
   -integral E A_2(t,L)dt,                              (18)

A_2=[C^(-1)(C^(-1))']'.
```

Equations `(4)` and `(15)` imply

```text
||(C^(-1))'|| <=C/[|t| log(1+|t|)^2],
||C^(-1)(C^(-1))'|| <=C/[|t| log(1+|t|)^3],
||A_2(t,L)|| <=C/|t|^2.                                (19)
```

The first boundary term in `(18)`, after multiplication by \(H(x+i\sigma)\) and integration in
\(L\), is

```text
integral_(I_m) C(x,L)^(-1)exp(-ixL)g(L)dL.              (20)
```

It is \(L^2\)-bounded uniformly on the tail.  To see this without invoking a black-box
pseudodifferential theorem, use the accretive resolvent formula

```text
C(x,L)^(-1)=integral_0^infinity exp(-sB(x+i sigma))exp(-sL)ds.              (21)
```

On \(|x|\ge X_m\), `(14)` makes the product in `(21)` exponentially decreasing in \(s\),
uniformly for \(L\in I_m\).  For each fixed \(s\), Plancherel applied to
`exp(-sL)g(L)` bounds its Fourier transform, while multiplication by
`exp(-sB(x+i sigma))` has the complementary accretive bound.  Minkowski integration in \(s\)
proves

```text
||(20)||_2<=C||g||_2.                                   (22)
```

The same argument, using the higher resolvent powers obtained by differentiating `(21)`, handles
the second boundary term in `(18)`.

For the last integral, `(5)` and `(19)` give, with \(x\ge X_m\),

```text
||H(x+i sigma)
  integral_(X_m)^x H(t+i sigma)^(-1)A_2(t,L)dt||
 <=C (1+x)^(-p)
   integral_(X_m)^x (1+t)^p t^(-2)dt.                  (23)
```

The right side is \(O(x^{-p})\), \(O(x^{-1}\log x)\), or \(O(x^{-1})\), according as
\(p<1\), \(p=1\), or \(p>1\).  Every case is in \(L^2(X_m,\infty)\) because \(p>1/2\).
Since \(I_m\) has length one, \(\|g\|_1\le\|g\|_2\), so `(23)` may be integrated in \(L\).
The negative tail is identical after reflection.

Finally, the boundary value at \(\pm X_m\) propagated by \(H\) has tail norm at most
`C X_m ||g||_2`, by `(5)` and \(p>1/2\).  Combining this with `(12)`, `(16)`, and
`(22)`--`(23)` proves `(11)`. `QED`

## 5. Gamma-wall block Hardy transfer

### Theorem 2

`[PROVED]` If \(N_\sigma(G)<\infty\), then the series of block solutions from Theorem 1 converges
in \(L^2(\mathbb R;X)\).  Every zero-trace solution of `(10)` with

```text
b(z)=-(i/2)Ghat(z)
```

satisfies

```text
f(.+i sigma) in L2(R;X),                                (24)
exp(sigma L)F(L) in L2(R;X),                            (25)
```

where \(F\) is the inverse Fourier distribution of the real boundary value.

### Proof

Write \(G=\sum_m G_m\) with \(G_m=1_{I_m}G\).  Theorem 1 and `(7)` make the sum of the
\(L^2\) norms of the corresponding particular solutions finite.  Hence they converge absolutely
in \(L^2\).  The remaining homogeneous term is in \(L^2\) by `(3)` because
\(p=1/2+\sigma>1/2\).  This proves `(24)`.  Fourier translation and Plancherel give `(25)`.
`QED`

This theorem is strictly stronger for the literal source than the previous weighted-frequency
\(L^1\) criterion.  It uses physical Gamma-wall localization and allows arbitrarily rough
\(L^2\) behavior inside each unit block.

## 6. Literal Gamma cutoff commutator

Let

```text
(R F)(L)
 =integral_0^infinity
   [2F(L)-F(L+s)-F(L-s)]/(exp(s)-1)ds.                  (26)
```

Choose \(\chi\in C^\infty(\mathbb R)\) with

```text
chi=0 on (-infinity,0],       chi=1 on [1,infinity).    (27)
```

### Theorem 3

`[PROVED]` For every bounded \(X\)-valued \(F\),

```text
||[R,chi]F(L)|| <=C_chi ||F||_infinity exp(-|L|)
                                                        for |L|>=2,          (28)
||[R,chi]F||_infinity <=C_chi||F||_infinity.            (29)
```

Consequently

```text
N_sigma([R,chi]F)<infinity                              (30)
```

for every \(0<\sigma<1\).

### Proof

Expanding the commutator in `(26)` gives

```text
[R,chi]F(L)
 =integral_0^infinity k(s)
   [(chi(L)-chi(L+s))F(L+s)
    +(chi(L)-chi(L-s))F(L-s)]ds,                        (31)

k(s)=1/(exp(s)-1).
```

For \(0<s<1\), the Lipschitz bound on \(\chi\) makes each cutoff difference
`O(s)`, while \(s k(s)\) is bounded and integrable.  For \(s\ge1\), \(k(s)\le
C e^{-s}\).  This proves `(29)`.

If \(L\ge2\), only the term containing \(\chi(L-s)\) can be nonzero, and then
`s>=L-1`; hence `(31)` is `O(e^{-L})`.  If \(L\le-2\), only the term containing
\(\chi(L+s)\) can be nonzero, and then `s>=-L`; hence it is `O(e^L)`.  This proves
`(28)`.  Substitution in `(7)` proves `(30)`. `QED`

### Order-minus-one strengthening

`[PROVED]` If \(\chi\in C^\infty\) is constant on each exterior half-line and
\(\chi'\in C^\infty_c\), then

```text
[R,chi]:L2(R;X) -> H1(R;X)                              (32)
```

is bounded.

Indeed, \(R\) has the real multiplier \(r(\eta)\) from Section 2.  In Fourier variables, first
use

```text
i(xi-eta)chihat(xi-eta)=Fourier(chi')(xi-eta).
```

The delta contribution of either exterior constant disappears because it is multiplied by
`r(xi)-r(eta)`.  The remaining kernel is therefore an ordinary Schwartz kernel, and it can be
written as

```text
Fourier([R,chi]F)(xi)
 =integral_R chihat(xi-eta)[r(xi)-r(eta)]Fhat(eta)deta. (33)
```

The exact series

```text
r(eta)=2 sum_(n>=1) eta^2/[n(n^2+eta^2)]
```

and the polygamma asymptotics imply

```text
|r'(eta)|<=C/(1+|eta|),    |r(eta)|<=C log(2+|eta|).    (34)
```

Split `(33)` into

```text
|xi-eta|<= (1+|eta|)/2
```

and its complement.  In the first region, the mean-value theorem and `(34)` give

```text
(1+|xi|)|r(xi)-r(eta)|<=C|xi-eta|.                     (35)
```

In the complement, \(|\xi-\eta|\) controls \(1+|\xi|+|\eta|\); the Schwartz decay of
\(\widehat\chi\) absorbs the logarithm in `(34)` and the factor \(1+|\xi|\).  Schur's test on the
two regions proves

```text
||(1+|xi|)Fourier([R,chi]F)(xi)||_2<=C_chi||F||_2,
```

which is `(32)`. `QED`

The identical proof on the line \(\operatorname{Im}z=\sigma\) uses
`r(xi+i sigma)` in place of `r(xi)`.  Uniform polygamma bounds on every closed substrip give

```text
[R,chi]: exp(-sigma L)L2 -> exp(-sigma L)H1,
                                                        0<sigma<1.          (35a)
```

This is the missing literal source fact: the Gamma jump commutator is not merely exponentially
localized.  It gains one full physical derivative.

## 7. An \(L^2\) Hardy criterion for the forced equation

### Theorem 4

`[PROVED]` Let \(p=1/2+\sigma>1/2\).  If a solution of `(10)` satisfies

```text
x b(x+i sigma) in L2(R;X),                              (36)
```

then

```text
f(.+i sigma) in L2(R;X).                                (37)
```

### Proof

On the positive tail, `(3)` and `(13)` give

```text
||f(x+i sigma)||
 <=C x^(-p)[||c||+
   integral_1^x t^p||b(t+i sigma)||dt].                 (38)
```

Put \(h(t)=t\,b(t+i\sigma)\).  The integral in `(38)` is

```text
integral_1^x t^(p-1)||h(t)||dt.
```

The Hilbert-valued weighted Hardy inequality

```text
integral_1^infinity x^(-2p)
  ||integral_1^x t^(p-1)h(t)dt||^2 dx
 <=[p-1/2]^(-2) integral_1^infinity ||h(t)||^2dt        (39)
```

holds for \(p>1/2\).  It follows either from integration by parts and Cauchy--Schwarz or from the
ordinary Hardy inequality after logarithmic dilation.  Equation `(39)` proves the positive-tail
part of `(37)`; reflection proves the negative tail, and local integrability follows from the ODE.
`QED`

For a cutoff equation whose right side is \(J\), division of the exact Fourier equation by its
factor \(\eta\) gives

```text
b(z)=-Jhat(z)/(2z).                                     (40)
```

Thus `(36)` is exactly the shifted-line \(L^2\) condition on the literal residual \(J\), not a
weighted frequency moment.  The commutator theorem `(32)` is the load-bearing reason a smooth
cutoff produces such a residual.

## 8. The derivative scattering charges

Strip \(L^2\) decay still does not imply physical \(H^1\).  Multiplication by \(x\) in frequency
is physical differentiation, and the homogeneous derivative carrier is

```text
K(z)=zH(z).                                              (41)
```

On \(z=x+i\sigma\),

```text
||K(x+i sigma)v||^2
 asymp |x|^(1-2sigma)||v||^2.                           (42)
```

For every \(1/2<\sigma<1\), `(42)` is not integrable.  Hence derivative regularity requires two
additional cancellations at \(+\infty\) and \(-\infty\).

Suppose the source is in the block class of Theorem 2 and also

```text
x b(x+i sigma) in L2(R;X).                              (43)
```

Raw variation integrals need not converge: their moving endpoint terms are the nonhomogeneous
asymptotic expansion.  Define recursively

```text
D_0(x,L)=C(x,L)^(-1),
D_(j+1)(x,L)=C(x,L)^(-1) partial_x D_j(x,L).             (44)
```

Three integrations by parts give, on either tail,

```text
integral_0^x E(t,L)dt
 =sum_(j=0)^2 i^epsilon_j E(x,L)D_j(x,L)
  +C_0(L)
  +i^epsilon_3 integral_0^x E(t,L)partial_t D_2(t,L)dt, (45)
```

with irrelevant unit complex signs \(i^{\epsilon_j}\).  Since

```text
||partial_t D_2(t,L)||<=C(1+|t|)^(-3)
```

after the nonstationary threshold and \(p<3/2\), the final integrand has norm
`O(|t|^(p-3))` and is absolutely integrable.  Hence the following finite parts exist:

```text
d_+^(sigma)
 =c+FP integral_0^infinity
      H(t+i sigma)^(-1)b(t+i sigma)dt,

d_-^(sigma)
 =c+FP integral_0^(-infinity)
      H(t+i sigma)^(-1)b(t+i sigma)dt.                  (46)
```

Here `FP` means: subtract the three endpoint terms in `(45)` blockwise and then take the ordinary
limit of the absolutely convergent remainder.  The block norm makes the sum of these finite parts
converge.  They are the two **Gamma derivative scattering charges**.

### Theorem 5

`[PROVED]` Under the displayed block and residual hypotheses,

```text
x f(x+i sigma) in L2(R;X)
 iff d_+^(sigma)=0 and d_-^(sigma)=0.                   (47)
```

### Proof

Use the three-term expansion `(45)`.  After multiplication by \(H(x+i\sigma)\), its final tail
is

```text
H(x+i sigma) integral_x^infinity
  E(t,L)partial_tD_2(t,L)dt=O(x^(-2)).                  (48)
```

Thus it remains \(L^2\) after multiplication by \(x\).
The leading nonhomogeneous boundary term is

```text
i [B(x+i sigma)+L]^-1 exp(-ixL)g(L).
```

After multiplication by \(x\), its block sum is \(L^2\) precisely under `(43)`; the resolvent
contributes the harmless factor \(1/\log|x|\).  All later boundary and remainder terms are
\(L^2\) after multiplication by \(x\), by `(4)` and the third integration by parts.

What remains on the positive tail is exactly

```text
xH(x+i sigma)d_+^(sigma),
```

and analogously on the negative tail.  Equation `(42)` shows that this term is in \(L^2\) only
when its coefficient is zero.  This proves necessity.  With both coefficients zero, only the
already established \(L^2\) boundary and remainder terms remain, proving sufficiency. `QED`

The charges in `(46)` are independent of the half-log trace.  The half-log trace is the
regular-singular scattering coefficient at frequency zero; \(d_\pm^{(\sigma)}\) are the two
outgoing charges at infinite frequency.  Conflating them was the previous error in the proposed
`trace zero -> strip decay -> H1` chain.

## 9. Literal Suzuki cutoff identity

Let \(F\) solve the carrier-valued homogeneous tail equation

```text
(2L I+R-T)F'+F=0                                       (50)
```

in distributions, and put \(W=\chi F\).  Since \(R\) commutes with differentiation and \(T\)
commutes with the scalar cutoff,

```text
(2L I+R-T)W'+W
 =([R,chi]F)'
  +(2L I+R-T)(chi'F)-[R,chi']F.                         (51)
```

Identity `(51)` is exact.  It contains no derivative of \(F\) inside a commutator.

Theorem 3 puts the first term in \(L^2\) whenever \(F\in L^2\); all terms with \(\chi'\) are
compactly supported.  On the literal completed source domain, multiplication by a smooth compact
cutoff preserves the logarithmic operator domain, so the remaining \(R(\chi'F)\) term is also in
\(L^2\).  Thus the residual \(J\) in `(51)` satisfies the exact criterion `(40)`--`(43)`.

The undifferentiated regular polar source has a finite limit at an endpoint.  Subtracting that
constant does not change its derivative and leaves an \(O(e^{-L})\) tail.  The zero-extension
Gamma commutator has the two-sided \(O(e^{-|L|})\) wall from `(28)`.  Therefore Theorem 2 closes
the strip-Hardy part of the literal cutoff problem after the already constructed support-pruned
carrier is realized on the completed source.

The general forced ODE still has the two-charge obstruction.  For the physical Suzuki tail,
however, the subsequent theorem
`suzuki-gamma-weighted-tail-coercivity.md` proves

```text
PHYSICAL-SUPPORT-DERIVATIVE-SCATTERING-ZERO:
for every realized trace-zero carrier state and one (equivalently every)
sigma in (1/2,1),
d_+^(sigma)=d_-^(sigma)=0.                              (52)
```

Indeed the shifted Gamma multiplier has a finite lower numerical range, while a cutoff translated
far enough down the positive logarithmic ray makes \(2L\) dominate that loss and
\(\|T\|\).  A weak mollifier energy estimate then puts
\(e^{\sigma L}W'\) in \(L^2\), and Theorem 5 forces both charges to vanish.  Thus `(52)` is no
longer an independent arithmetic conjecture.  The remaining source gate is realization of every
completed trace-zero mode in the support-pruned carrier with the exact cutoff identity.

## 10. Hostile audit

1. **No weighted-\(L^1\) theatre.**  The literal residual is controlled in \(L^2\); Theorems
   1--4 use that class directly.
2. **No decay-to-derivative leap.**  `(24)` and `(25)` do not imply \(H^1\).  The missing
   derivative charges are displayed in `(46)`.
3. **No generic ellipticity claim.**  Order-minus-one smoothing is proved for the exact commutator
   by `(33)`--`(35)`.  The full logarithmic inverse still gains no positive Sobolev order.
4. **No source atom smuggling.**  A physical point mass gives \(b(x)\) of constant size and a
   particular solution of order \(1/\log|x|\), which is not \(L^2\).  The theorem requires the
   actual \(L^2\) cutoff residual.
5. **No hidden RH premise.**  Theorems 1--5 and the subsequent weighted-tail coercivity theorem
   hold for every bounded self-adjoint \(T\).  Arithmetic enters only when identifying the literal
   completed carrier.
6. **No whole-route conclusion.**  Corona no-return, raw Evans injectivity, and producer classes P
   and I remain open.

## 11. Novelty boundary

Weighted Hardy inequalities, commutators of logarithmic Fourier multipliers, and Gamma
asymptotics are classical ingredients.  Corpus and targeted searches found no theorem combining
them into:

```text
literal Gamma wall O(exp(-|L|))
 -> physical block Hardy norm
 -> forced strip H2 without a frequency L1 moment
 -> exact two-charge classification of the H1 obstruction.               (53)
```

The claimed new content is the source-specific conjunction `(7)`--`(53)` and the discovery that
the trace-zero/H1 gap is a high-frequency two-charge problem.  Priority remains unverified.

## 12. Lean decision

The source-bearing formal targets are:

1. the block weight and its exponential-wall summability;
2. the Hilbert-valued weighted Hardy inequality `(39)`;
3. the exact cutoff identity `(47)`;
4. the derivative-carrier integrability boundary `(42)`;
5. the equivalence `(45)` after Bochner/Fourier infrastructure exists.

Formalizing only the scalar algebra in `(44)` would be theatre.  The next Lean module should at
minimum certify `(39)` together with the sharp exponent boundary and reuse
`SuzukiGammaStripCarrierIntegrability.lean` for `(42)`.

`SuzukiGammaWallHardyBoundary.lean` now certifies the exact positive/negative Gamma-wall
summability window and the sharp nonintegrability of the derivative carrier throughout
\(0<\sigma<1\).  `SuzukiGammaWeightedTailCoercivity.lean` certifies the shifted Gamma integrand
lower bound and the coercive Hilbert energy step which annihilates the two charges on a physical
tail.

## Gates

- [x] replace weighted frequency-\(L^1\) condition by exact physical block norm
- [x] prove one-block Gamma Hardy estimate
- [x] prove exponential Gamma-wall sources belong to the block space
- [x] prove literal Gamma cutoff commutator has two-sided exponential wall
- [x] prove exact commutator is order minus one from \(L^2\) to \(H^1\)
- [x] prove shifted \(L^2\) residual implies forced strip \(H^2\)
- [x] identify two derivative scattering charges
- [x] prove their joint vanishing is equivalent to localized frequency first moment
- [x] prove physical support and the exact \(2L\) coefficient force both charges to vanish
- [ ] realize `(51)` on every completed support-pruned Suzuki carrier state
- [x] prove `PHYSICAL-SUPPORT-DERIVATIVE-SCATTERING-ZERO` for every realized carrier state
- [ ] conclude `SUZUKI-TRACE-ZERO-H1`
- [ ] prove corona no-return and raw Evans injectivity
- [ ] RH
