# A pointed doubling-Fock carrier couples the prime tail to the exact completed trace

- **ID:** `theta-prime-pointed-doubling-fock-carrier`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HILBERT--POLYA SOURCE CARRIER / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every `m>=4`, one source-defined analytic Hilbert space simultaneously carries
  bounded normalized critical-prime evaluations, the completed two-sided theta functional, and its
  entire trace-moment germ.  The distinguished constant vector has trace exactly equal, after the
  proved Fourier normalization, to the completed Riemann zeta function on the critical line.

## Source Hilbert space and distinguished point

Let

```text
phi_m(z)=(1+|z|^2)^(m/2),
H_m=F_m^2={f entire:int_C |f(z)|^2 exp(-2phi_m(z)) dA(z)<infinity},  (1)
```

with `m>=4`.  Write `K_m` for its reproducing kernel.  The constant entire function

```text
one(z)=1                                                       (2)
```

belongs to `H_m`, because `exp(-2phi_m)` is integrable on the plane.  It is the distinguished point
of the carrier.

Let

```text
h(u)=xiThetaLogSource(u)
    =exp(u/4)(theta(exp u)-1)  for u>0,
h(-u)=h(u).                                                    (3)
```

The exact source identity and reflection in `(3)` are already formalized in
`XiThetaSourceSeam.lean`.

## Prime channel `[PROVED]`

For primes `p`, put

```text
lambda_p=log p,
w_p=(log p)^2/p,
(S_m f)_p=sqrt(w_p) f(lambda_p)/sqrt(K_m(lambda_p,lambda_p)).  (4)
```

The theorem `critical-prime-doubling-fock-phase-transition.md` proves

```text
S_m:H_m->ell^2(P) is bounded for m>=4,
S_m is compact exactly for m>4.                                (5)
```

Thus the whole all-prime tail is a well-defined Hilbert incidence, not a list of formal point
values.  At `m=4` its noncompactness records a persistent critical arithmetic channel; for `m>4`
the stronger confinement makes it compact.

## Completed trace channel `[PROVED]`

For `z in C`, define, with the Fourier sign used by the project,

```text
T_m(f)(z)=int_R f(u) h(u) exp(-2 pi I u z) du.                (6)
```

Changing the Fourier sign only replaces `z` by `-z`; the exact real-frequency normalization below
uses `XiThetaCriticalTrace.lean`.

For `u>0`, the theta expansion gives

```text
|h(u)|
 <= 2 exp(u/4) sum_(n>=1) exp(-pi n exp u)
 <= C exp(u/4-pi exp u).                                     (7)
```

Evenness gives the corresponding estimate with `|u|` on the whole line.  The doubling-Fock kernel
diagonal estimate gives

```text
|f(u)| <= ||f||_(H_m) sqrt(K_m(u,u))
        <= C_m ||f||_(H_m) exp(phi_m(u))/rho_m(u),            (8)
```

where `rho_m(u) asymp (1+|u|)^(1-m/2)`.  Since `exp(|u|)` dominates every polynomial,

```text
int_R exp(phi_m(u)+R|u|) |h(u)|/rho_m(u) du<infinity          (9)
```

for every finite `R`.

Equations `(8)`--`(9)` prove all of the following.

1. For every `z`, the integral `(6)` is absolutely convergent.
2. For every compact `Q subset C`, there is `C_Q<infinity` such that

   ```text
   sup_(z in Q)|T_m(f)(z)| <= C_Q ||f||_(H_m).               (10)
   ```

3. `T_m(f)` is entire, by differentiation under the integral.
4. Every trace moment is a bounded linear functional:

   ```text
   T_m(f)^(n)(0)=int_R (-2 pi I u)^n f(u)h(u)du.              (11)
   ```

Thus

```text
T_m:H_m->O(C)                                                 (12)
```

is continuous when `O(C)` has its locally uniform topology, while the source carries the stronger
Hilbert norm.

## Exact completed-zeta trace `[PROVED; FORMALIZED PARENT]`

At the distinguished point `one`,

```text
T_m(one)(w)=Fourier(h)(w).                                   (13)
```

The formal theorem

```text
completedRiemannZeta0(1/2+it)
  =Fourier(h)(t/(4pi))/2                                    (14)
```

therefore gives

```text
completedRiemannZeta0(1/2+it)
  =T_m(one)(t/(4pi))/2.                                     (15)
```

Both sides are entire functions of the complexified variable `t`: this follows from `(9)` for the
right side and from the entire pole-subtracted completion for the left side.  Equality on the real
axis therefore extends by the identity theorem.  Hence their divisors agree after the fixed linear
rescaling `t -> t/(4pi)`.

Consequently the single pointed Hilbert carrier contains:

```text
weighted all-prime coefficient tail : S_m(one),
completed two-sided theta source     : h,
distinguished entire trace           : T_m(one),
distinguished trace moments          : (T_m(one)^(n)(0))_(n>=0),
completed critical divisor           : Div(T_m(one)).        (16)
```

No zero is inserted into the construction.  The divisor in `(16)` is carried because the exact
completed source transform is carried.

## Positive Hilbert--Polya consequence

The ambient-`L2` incompatibility is not categorical.  It is repaired by a source-selected analytic
Hilbert norm:

```text
J_m:H_m -> ell^2(P) x O(C),
J_m(f)=(S_m f,T_m(f))                                       (17)
```

is continuous for every `m>=4`, and `one` is a distinguished global incidence point.  This gives
an explicit realization of the carrier shape required by the critical-disc Euler-orbit results:

```text
all-prime tail + completion + distinguished trace/divisor moments.  (18)
```

The construction is pointed, global, and stronger than compact-open germ convergence.  Its prime
channel has the required `1/log N` microlocal scale at `m=4`, or a strictly finer scale at `m>4`.

This is not yet a Hilbert--Polya proof.  The missing theorem is now narrower:

> Construct, from the incidence `(17)` and without reading `Div(T_m(one))`, a self-adjoint operator
> or canonical system whose characteristic entire function is `T_m(one)` up to a zero-free factor.

Equivalently, one must promote an exact source trace into a divisor-faithful spectral determinant.
The present theorem supplies the carrier and the topology; it does not manufacture the spectral
positivity.

## Attacks and exact boundary

1. **Target-fed divisor attack.** The definition of `H_m`, `S_m`, `h`, and `T_m` uses no zero.  The
   divisor appears only after applying the already proved source Fourier identity.
2. **Tautological trace attack.** Equation `(15)` is a known exact transform identity, not a new
   proof of RH.  Zeros of a Fourier transform are not automatically eigenvalues of a self-adjoint
   operator.
3. **Phase-rank attack.** The nodes `log p` remain explicitly marked in the `ell^2(P)` coordinate.
   They are not compressed into the finite archimedean Gamma field.
4. **Gauge attack.** The prime channel uses normalized kernels, so zero-free RKHS gauges do not
   change its boundedness or compactness class.
5. **Topology attack.** Point evaluation and every trace moment are continuous in `H_m`; neither is
   defined by choosing representatives of an ambient `L2` class.
6. **Spectral attack.** Multiplication by `u` in a measure space would give continuous spectrum and
   would not make the zeros in `(15)` eigenvalues.  A successful next operator must use the global
   incidence, not merely the spectral theorem for the theta measure.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The construction combines the standard
doubling-Fock pointwise estimate and Carleson embedding with the classical theta transform for the
completed zeta function.  Once the quartic carrier is selected, boundedness of `(6)` is an immediate
consequence of the double-exponential theta tail.  The exact coupling is useful project
infrastructure, but it does not introduce a new parent mechanism or a new RH theorem.

Parent sources:

- R. Oliver and D. Pascuas, *Toeplitz operators on doubling Fock spaces*,
  `https://arxiv.org/abs/1508.02887`;
- J. Marzo and J. Ortega-Cerda, *Pointwise estimates for the Bergman kernel of the weighted Fock
  space*, Journal of Geometric Analysis 19 (2009), 890--910;
- the Jacobi theta transformation and Riemann's Mellin representation of the completed zeta
  function.

## Lean status

The exact source reflection, integrability, and critical Fourier identity `(14)` are already
formalized.  Complete carrier theorem still depends on doubling-Fock/Carleson and trace-continuity
infrastructure not yet present in the Lean tree; a wrapper around `(14)` alone would not formalize
the substantive construction.

`formal/GaloisForLFunctions/RHTower/MomentFockKernel.lean` and
`formal/GaloisForLFunctions/RHTower/PolynomialMomentFock.lean` now construct the exact polynomial
radial moment coefficient carrier, bounded point evaluations, unit normalized prime-log kernels,
and a distinguished vector whose evaluation is identically `1`.  `MomentFockEntire.lean` proves
every vector's coefficient series is entire and agrees exactly with bounded evaluation.
`PolynomialMomentFockNorm.lean` proves weighted-square integrability on `C` and exact equality
between coefficient norm and literal weighted plane norm.  Remaining work is concrete prime
Carleson boundedness and bounded/entire theta trace on this carrier; card therefore remains at
Stage 2.
`PolynomialMomentFockKernelBound.lean` supplies the explicit diagonal-kernel and point-evaluation
growth envelope. `PolynomialMomentFockThetaTrace.lean` now closes the complete trace channel:
two-sided double-exponential theta domination, integrability against every absolute exponential
weight, absolute convergence and entire dependence, exact all-order derivative moments, bounded
continuous-linear moment and point-trace functionals, uniform vertical-strip bounds (hence compact
local-uniform continuity), and the exact completed-zeta trace at the distinguished constant vector.
All new declarations passed the targeted leaf build and axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. The card remains at Stage 2 only because the concrete
normalized prime-kernel Carleson estimate from `critical-prime-doubling-fock-phase-transition.md`
is not yet formalized.

`PolynomialFockPotentialGeometry.lean` additionally supplies exact radial curvature and Laplacian
density together with two-sided adapted-radius comparisons.  This removes an abstract metric input
from the shared Carleson producer, but does not itself prove boundedness of the normalized prime
sampling map.  Its targeted leaf build and axiom audit passed with only the same standard axioms.

## Gates

- [x] pointed polynomial doubling-Fock carrier constructed
- [x] all-prime normalized sampling bounded for `m>=4`
- [x] completed theta functional bounded on the same Hilbert space
- [x] entire trace and all moments proved continuous
- [x] exact completed critical trace identified at the distinguished point
- [x] no divisor input and no ambient-`L2` representative choice
- [x] missing spectral-determinant theorem isolated
- [x] parent-theory novelty claim rejected
- [ ] complete unconditional Lean formalization
