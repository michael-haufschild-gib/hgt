# The semilocal dual-pair connection is exactly the finite Euler logarithmic source

- **ID:** `semilocal-dual-pair-euler-connection-source-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*;
  `semilocal-euler-kernel-chart-differentiability.md`;
  `connes-semilocal-finite-part-orbital-source-class.md`

## Setup

Let `S` be a finite set of places containing infinity and write `S_f=S\{infinity}`.  Put

```text
L_p(z)=(1-p^(-z))^(-1),
g_S(t)=product_(p in S_f)L_p(1/2+i t)^(-1)
      =product_(p in S_f)(1-p^(-1/2-i t)).               (1)
```

Let `U_infinity` and `U_S` be the raw Mellin realizations of the archimedean and semilocal
`L2` spaces.  The explicit calculation in Proposition 4.6 of Connes--Consani--Moscovici is

```text
U_S theta_S U_infinity^(-1)=M_(g_S).                     (2)
```

For finite `S`, `g_S`, `g_S^(-1)`, and their first derivatives are bounded on the real line.
Indeed every factor is separated from zero by `1-p^(-1/2)`.  Thus multiplication by `g_S`
and by its inverse preserves the Sobolev core `H1(R)`.

Let

```text
D=-i d/dt                                                     (3)
```

on that core, and transport `D` to the two physical realizations as `D_infinity` and `D_S`.

## Exact Euler connection theorem

Define the finite prime logarithmic source on the critical line by

```text
Phi_S(t)=-sum_(p in S_f) L_p'/L_p(1/2+i t).                (4)
```

Then on the common `H1` core,

```text
theta_S^(-1) D_S theta_S-D_infinity
  =U_infinity^(-1) M_(Phi_S) U_infinity.                   (5)
```

Equivalently,

```text
D_S theta_S-theta_S D_infinity
  =theta_S U_infinity^(-1) M_(Phi_S) U_infinity.           (6)
```

### Proof

By `(2)`, the Mellin-coordinate form of the left side of `(6)` is `[D,M_(g_S)]`.  For a
core vector `f`,

```text
[D,M_(g_S)]f=-i g_S' f.
```

Since `z=1/2+i t`, logarithmic differentiation of `(1)` gives

```text
g_S'(t)/g_S(t)
  =i d/dz log(product_(p in S_f)L_p(z)^(-1))|_(z=1/2+i t)
  =i Phi_S(t).                                             (7)
```

Hence `-i g_S'=g_S Phi_S`, so `[D,M_(g_S)]=M_(g_S)M_(Phi_S)`.  Conjugating by
the two Mellin transforms proves `(5)` and `(6)`. `QED`

## Exact von Mangoldt coefficients

For `Re z>0`,

```text
-L_p'/L_p(z)
  =log(p) p^(-z)/(1-p^(-z))
  =sum_(m>=1) log(p) p^(-m z).                             (8)
```

Consequently

```text
Phi_S(t)
  =sum_(p in S_f)sum_(m>=1)
       log(p) p^(-m/2) exp(-i m t log(p)).                 (9)
```

These are exactly the finite von Mangoldt coefficients.  Reflection `t |-> -t` supplies the
opposite orbit, so the reflected pairing of `(9)` with a multiplicative test function gives the
two local terms at `p^m` and `p^(-m)` in the semilocal Weil distribution.  Thus the orbital
coefficient extracted in
`connes-semilocal-finite-part-orbital-source-class.md` and the connection coefficient in `(5)`
are the same source datum, not merely two expressions with the same prime support.

## Dual-pair matrix-coefficient form

Proposition 4.7(iii) of the same paper proves the flat dual pairing

```text
<theta_S f,eta_S h>=<f,h>.                                (10)
```

Combining `(6)` with `(10)` yields the exact source value relation

```text
<(D_S theta_S-theta_S D_infinity)f,eta_S h>
  =<M_(Phi_S)U_infinity f,U_infinity h>.                  (11)
```

No trace, basis, finite section, Xi zero, or limiting measure occurs in `(11)`.  The prime source
is the static failure of the logarithmic-position generator to intertwine the two constraint
embeddings.  In particular, this is a constraint defect, not a proposed scaling flow for zeta.

## Place additivity and reflection

For disjoint finite prime sets `F` and `G`,

```text
g_(F union G)=g_F g_G,
Phi_(F union G)=Phi_F+Phi_G.                              (12)
```

Thus the connection defects form the same filtered additive system as the local Weil
distributions.  On the real spectral line,

```text
g_S(-t)=conj(g_S(t)),
Phi_S(-t)=conj(Phi_S(t)).                                 (13)
```

Writing `g_S=|g_S| exp(i arg(g_S))`, equation `(7)` separates the two reflected components:

```text
d/dt arg(g_S)=Re(Phi_S),
d/dt log|g_S|=-Im(Phi_S).                                (14)
```

Equivalently, the orientation component is the phase derivative of the semilocal place map,
while the metric component is its logarithmic norm derivative.  The positive Euler metric tangent
already formalized in the corpus is therefore the metric shadow of this full complex connection;
it cannot recover the orientation component by itself.

## Contraction of the finite Euler parameter connection

The existing analytic kernel chart uses independent finite Euler parameters

```text
g_a(z)=product_(p in S_f)(1-a_p p^(-z)).                  (15)
```

Its parameter connection in the `p` direction is

```text
A_p(a;z)=g_a(z)^(-1) partial_(a_p)g_a(z)
        =-p^(-z)/(1-a_p p^(-z)).                          (16)
```

At the actual Euler point `a_p=1`, equation `(8)` gives the exact contraction law

```text
Phi_S(z)=-sum_(p in S_f)log(p) A_p(1;z).                 (17)
```

Thus the spectral logarithmic-position connection `(5)` is not the whole finite-parameter
connection appearing in a mixed projection curvature.  It is its canonical arithmetic
contraction by the vector field

```text
V_S=-sum_(p in S_f)log(p) partial_(a_p).                  (18)
```

This distinction prevents a false discharge: `(17)` identifies the source-bearing tangent
combination, but it does not say that every parameter connection vanishes on an Xi zero fibre.
It supplies the exact value relation that any proposed zero-fibre connection reader must preserve.

## Reflection value versus Euler-parameter tangent

The formal corpus uses the FE-paired scalar family

```text
F_(p,z)(a)=log(p)[a p^(-z)/(1-a p^(-z))
                   -a p^(-(1-z))/(1-a p^(-(1-z)))].       (18a)
```

The connection theorem identifies its **value**, rather than its derivative, at the actual Euler
point:

```text
F_(p,z)(1)=Phi_p(z)-Phi_p(1-z).                           (18b)
```

Its empty-parameter derivative is the already formalized horizontal seam

```text
F_(p,z)'(0)=log(p)[p^(-z)-p^(-(1-z))].                    (18c)
```

Therefore the connection reflection has the exact grade decomposition

```text
F_(p,z)(1)=F_(p,z)'(0)
  +sum_(m>=2)log(p)[p^(-m z)-p^(-m(1-z))].               (18d)
```

This is distinct from the corpus's actual-parameter **tangent** tail, whose grade `m` has the
larger coefficient `m log(p)`.  The connection route therefore asks for cutoff descent of the
coefficient-one Lambert tail `(18d)`, not the parameter-Hessian tail.  On the real horizontal
coordinate used by the Xi seam, the grade-two reflected term vanishes exactly at `Re z=1/2`.
Thus this simplification does not make the tail compact; it removes an unnecessary parameter
derivative from the source comparison.

### Actual-point Hessian and spectral curvature as direct orientation readers

There is a second, complementary actual-point coordinate.  Differentiating the local connection
once more in its own Euler parameter and then setting `a_p=1` gives

```text
T_p(z)=log(p) p^(-z)/(1-p^(-z))^2.                       (18e)
```

For `q=p^(-conj(rho))` and `r=p^(-(1-rho))`, elementary polarization yields

```text
T_p(conj(rho))-T_p(1-rho)
 =C_p(rho)(1-q r)/[(1-q)^2(1-r)^2].                     (18f)
```

All three extra factors are invertible in the open strip.  Hence, for every single prime `p`,

```text
T_p(conj(rho))=T_p(1-rho) iff C_p(rho)=0
                                  iff Re(rho)=1/2.       (18g)
```

This gives a sharper target for any semilocal construction whose normal-curvature reader already
returns the actual Euler-parameter Hessian: one graded-reality value at one finite place is enough.
Such a reader need not isolate the first Lambert grade or prove descent of the whole tail `(18d)`.
The conclusion is conditional on producing the value equality `(18g)` from the completed
prime--Gamma source; the local factorization itself does not supply that orientation theorem.

This does not replace the coefficient-one connection route when the available operator is the
spectral logarithmic-position connection `(18b)`, nor the exterior-Calkin route when quotient-norm
comparison of actual and empty tangent sections is required.  It identifies a distinct, shorter
operator interface rather than conflating those three derivatives.

The parameter Hessian is also the normalized spectral derivative of the same connection:

```text
Phi_p'(z)=-log(p) T_p(z).                                (18h)
```

Consequently a normal-curvature construction formulated in the spectral variable has the equally
short target

```text
Phi_p'(conj(rho))=Phi_p'(1-rho)                          (18i)
```

at any one prime.  The implication `(18i) -> (18g)` uses only the nonvanishing of `log(p)`.
Through the imaginary-slope Gamma substitution `(18d3)`, this curvature is also a scaled
trigamma-reflection pair.  Thus parameter Hessian, spectral curvature, and imaginary-slope Gamma
curvature are exact representatives of one finite orientation coordinate; no carrier change or
limit is involved.

## One-Cauchy Poisson chamber of the connection

`finite-euler-connection-cauchy-phase-chambers.md` evaluates the FE-paired value `(18b)` on a
centered upper-half-strip Cauchy diagonal.  For `z=x+i y`, `0<y<1/2`, it is exactly

```text
log(p)/(2y) [P_(p^(-1/2+y))(x log(p))
             -P_(p^(-1/2-y))(x log(p))].                 (18d1)
```

Its sign is positive precisely when

```text
cos(x log(p))
  >(p^(-1/2+y)+p^(-1/2-y))/(1+p^(-1)),                  (18d2)
```

and negative for the reverse strict inequality.  Kronecker density makes the negative chambers
simultaneous for every finite nonempty prime packet.  Thus the connection is the correct finite
source coordinate but is not itself a positive Cauchy source.  The remaining cutoff/resolvent
descent must retain this phase and prove that the completed prime--Gamma remainder compensates its
explicit negative chamber; replacing that theorem by positivity of the finite Euler connection is
now ruled out exactly.

## Imaginary-slope Gamma-reflection realization

`finite-euler-imaginary-gamma-reflection-weld.md` gives a second exact representative of the same
connection.  Euler reflection yields

```text
1-p^(-s)
  =-2 i pi exp(-s log(p)/2)
    /[Gamma(i s log(p)/(2pi)) Gamma(1-i s log(p)/(2pi))], (18d3)
```

and logarithmic differentiation identifies `Phi_p` with the corresponding scaled digamma
reflection anomaly.  Hence the semilocal place multiplier itself is a finite product of reciprocal
Gamma pairs with prime-dependent imaginary slopes.  The FE-paired value `(18b)` is the logarithmic
derivative of the symmetric Gamma quartet

```text
(1-p^(-s))(1-p^(-(1-s))).                                (18d4)
```

This closes the Euler-to-Gamma value bridge but does not import the positive-real-slope Gamma
boundary theorems: their slope hypothesis is genuinely different.  The full prime character
carrier in `(18d3)` lives in the cofinal family of imaginary slopes `log(p)/(2pi)`.

The FE--Schwarz two-value comparison needed by the Xi seam has now been factored exactly in
`heat-aperture-prime-seam-reflection-collapse.md`.  If

```text
Phi_p(s)=log(p)p^(-s)/(1-p^(-s)),
```

then on the open strip

```text
Phi_p(conj(rho))-Phi_p(1-rho)
 =C_p(rho)/[(1-p^(-conj(rho)))(1-p^(-(1-rho)))].
```

The denominator is invertible, so equality of these two actual connection values is equivalent to
vanishing of the canonical seam.  This converts the former common-charge normalization into a
concrete connection-value constraint, but no semilocal theorem presently forces the constraint on
all Xi fibres.

## Positive connection-tail Calkin rigidity

Fix a prime `p`, `0<sigma<1`, and grade `j+2`.  The reflected connection-tail coefficient is

```text
c_j^conn(p,sigma)=log(p)
  [p^(-(j+2)sigma)-p^(-(j+2)(1-sigma))].                 (18e)
```

The sequence is absolutely summable in `j`, the scales `p^(j+2)` are strictly increasing, and

```text
c_0^conn(p,sigma)=0 iff sigma=1/2.                       (18f)
```

The last equivalence follows from strict monotonicity of real powers with base `p>1`.  Applying
the already formalized general theorem `summableEvenPositiveEulerCorner_not_isCompactOperator`
gives the paper consequence

```text
the additive Sonin principal lift of the connection tail is compact
  iff sigma=1/2.                                         (18g)
```

At `sigma=1/2` every reflected coefficient vanishes, so the lift is zero.  Off the critical line,
`c_0^conn` is a nonzero Calkin coordinate.  This is a positive orientation theorem: even the
smaller coefficient-one tail faithfully records horizontal displacement.  Therefore the desired
proof must cancel it inside the completed prime--Gamma connection, across grades or places; it
cannot classify it as an individually compact remainder.

## Consequences for the current Sonin route

Three formerly separate construction requests are now closed:

```text
finite semilocal Sonin carrier
  = theta_S(classical Sonin carrier),
finite prime logarithmic source
  = theta_S^(-1) D_S theta_S-D_infinity,
finite-part orbital coefficients
  = Fourier coefficients of the same connection.         (19)
```

This also identifies the correct replacement for the false proposition
`SoninSemilocalFluxNormalization`.  The bounded Hilbert--Schmidt projection-correction pairing is
not supposed to grow like `log(p^m)`.  The logarithmic growth lives in the connection with the
unbounded logarithmic-position operator before compression.  The Lean obstruction to the bounded
pairing is therefore consistent with, and positively selects, `(5)`.

The remaining theorem is narrower.  One must compress or resolvent-dress the connection `(5)` on
the exact Sonin/prolate graph and prove that its cyclic finite part agrees with the completed
prime--Gamma source while retaining a one-sided floor.  Neither the Hilbertian isomorphism nor the
connection identity supplies that sign.

## Sharpened top-down chain

```text
Connes--Consani--Moscovici theta_S isomorphism
  -> exact Euler connection identity (5) and parameter contraction (17)
  -> exact finite von Mangoldt source matrix coefficient (11)
  -> [OPEN] Sonin cutoff/resolvent cyclic descent including the Burnol conductor
  -> [OPEN] uniform completed lower floor or source-core positivity
  -> existing completed prime--Gamma source criterion
  -> RH.                                                    (20)
```

The first open arrow is no longer allowed to introduce an arbitrary relative trace.  It must be
the cutoff or relative-trace image of the explicit connection `(5)`, and it must preserve `(11)`.

## Literature

- A. Connes, C. Consani, H. Moscovici,
  [*Zeta zeros and prolate wave operators: semilocal adelic operators*](https://arxiv.org/abs/2310.18423),
  especially Propositions 4.6--4.8 and Theorem 4.6.
- A. Connes and C. Consani,
  [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368), for the semilocal cutoff trace and
  quantized-differential source.
- A. Connes and C. Consani,
  [*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771),
  for the archimedean Sonin compression and conductor-side positivity comparison.

## Lean decision

The bounded one-prime multiplier, its weighted Hardy--Titchmarsh square, and the exact physical
local-factor transport are already formalized in `HardyTitchmarshSemilocalSquare.lean`.  The new
step requires a closed derivative operator and common-domain commutator.  Adding only the scalar
calculus identity would not formalize `(5)`.  No Lean file is added until the unbounded common-core
interface is present.  This card is nevertheless wired into the exact existing formal multiplier
and source-criterion modules.

## Gates

- [x] exact finite semilocal multiplier from the literature
- [x] bounded inverse and common `H1` core
- [x] Euler connection commutator identity
- [x] exact von Mangoldt coefficient expansion
- [x] dual-pair matrix-coefficient value relation
- [x] place additivity and reflection law
- [x] identify the orientation and metric components
- [x] identify the von Mangoldt source as the logarithmic-prime contraction of the Euler chart
- [x] separate the actual connection value from the actual-parameter tangent
- [x] exact coefficient-one reflected Lambert-tail decomposition
- [x] factor the actual-point parameter Hessian FE--Schwarz defect through one prime seam
- [x] reduce an actual-Hessian source reader to any one finite place
- [x] identify the actual Hessian with normalized spectral connection curvature
- [x] identify the same curvature with the imaginary-slope trigamma-reflection pair on paper
- [x] prove paper-level Calkin rigidity of the coefficient-one connection tail
- [x] replace the refuted bounded projection-correction normalization
- [ ] formalize the closed logarithmic-position common-core interface
- [ ] prove cutoff/resolvent cyclic descent preserving `(11)`
- [ ] include the Burnol conductor and prove a completed lower floor
- [ ] conclude RH
