# Euler--Hellinger/Gamma relative Mellin anomaly law

- **ID:** ULF-EHGM-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor relative-completion and exact anomaly theorem
- **Parents:** ULF-ESAC-001; `cubic-ward-hellinger-completed-source-trace-incidence`
- **Status:** `[PAPER-PROVED] [BRIDGE] [LEAN-READ-ONLY PASS]`
- **Surviving RH edge:** identify the actual anomaly-subtracted Euler--theta completion with the
  source-side Mellin transport below and prove its residual Xi boundary is a positive contraction
  of the order-six aperture carrier.

## 1. Higher-law interpretation

Two source gauges can agree on every individual cell and still disagree on every mixed packet.
The missing datum is neither another producer nor a scalar correction.  It is the unique
equivariant operator changing one coherent orbit into the other.  Its metric defect is invisible
on each orbit vector, lives only in cross-label incidence, has zero trace, and is necessarily
indefinite.

This is the first literal realization in the corpus of the proposed relative-completion law:

```text
same Euler weights + same dilation orbit
  local gauge 1: order-six aperture/Gamma feature
  local gauge 2: cubic Hellinger/collision feature
  unique Mellin transport M between gauges
  metric anomaly Q=M* M-I
  relative completion: collision Gram = aperture Gram + compressed anomaly.
```

The polar phase of `M` disappears from positive Grams; only its positive modulus survives.  Its
modulus tends to zero at high Mellin frequency, so `M` is injective with dense nonclosed range and
unbounded inverse.  Thus phase quotient, open lifted history, noncompact completion, and an exact
zero-trace anomaly arise from one mechanism rather than four analogies.

## 2. Corpus audit and correction

The in-progress card `cubic-ward-hellinger-completed-source-trace-incidence` already proves more
than a diagonal budget.  Its P-G177-A constructs the full Euler/Hellinger synthesis and proves

```text
Tr K=(115/1728) integral_0^infinity t^2[-zeta'/zeta](1+t)dt
    =routePPrimitiveCollisionCubicTraceBudget.        (EHGM.1)
```

Therefore the scalar aperture identity in ULF-ESAC-001 is a new Stokes interpretation of an
existing equality, not a new scalar theorem.  What ULF-ESAC-001 adds is a different canonical
off-diagonal operator `C`, its order-six Gamma Gram, and its singular sixth boundary.

Required corpus searches for `Mellin multiplier Gamma ratio dilation`, `Hellinger Gamma coherent
vector`, `same diagonal Gram anomaly`, and the exact constant `18/sqrt(23)` found no theorem or
paper card relating those two source syntheses.  General Mellin-multiplier, Gamma-six, Hellinger,
and Gram-anomaly machinery exists, but not the transport or conservation law below.

## 3. The two forced dilation gauges

Let `H=L2((0,infinity),dt)` and use the unitary dilation

```text
(D_lambda u)(t)=sqrt(lambda)u(lambda t), lambda>0.    (EHGM.2)
```

Define two unit vectors

```text
h_lambda(t)=sqrt(8/15) lambda^3 t^(5/2)exp(-lambda t),
f_lambda(t)=sqrt(864/115) lambda^(3/2)t
              [exp(-lambda t)-exp(-2lambda t)].      (EHGM.3)
```

Both are dilation orbits: `h_lambda=D_lambda h_1` and
`f_lambda=D_lambda f_1`.  Elementary Gamma integrals give

```text
||h_lambda||=||f_lambda||=1,                         (EHGM.4)
<h_mu,h_lambda>=[2sqrt(lambda mu)/(lambda+mu)]^6.    (EHGM.5)
```

Let `I=Primes x Nat`, `lambda_i=log(p^(e+1))`, and

```text
s_i=115/[864 p^(e+1)(e+1)^3 log(p)^2].               (EHGM.6)
```

Define Hilbert--Schmidt syntheses

```text
W_6 e_i=sqrt(s_i)h_(lambda_i),
W_H e_i=sqrt(s_i)f_(lambda_i).                       (EHGM.7)
```

Then

```text
C=W_6*W_6                                             (EHGM.8)
```

is exactly ULF-ESAC-001's aperture capacity.  Moreover

```text
sqrt(s_i)f_(lambda_i)
 =sqrt(Lambda(p^(e+1))/p^(e+1)) t
    [exp(-lambda_i t)-exp(-2lambda_i t)],             (EHGM.9)
```

so

```text
K=W_H*W_H                                             (EHGM.10)
```

is exactly P-G177-A's full primitive Euler/Hellinger collision Gram at `R=1`, `kappa=0`.

## 4. Unique equivariant Mellin transport

Use the unitary Mellin transform, up to the harmless common `1/sqrt(2pi)` normalization,

```text
(Mellin u)(xi)=integral_0^infinity u(t)t^(-1/2-i xi)dt. (EHGM.11)
```

The base vectors have transforms

```text
Mellin(h_1)(xi)=sqrt(8/15) Gamma(3-i xi),
Mellin(f_1)(xi)=sqrt(864/115) Gamma(3/2-i xi)
                  [1-2^(-3/2+i xi)].                 (EHGM.12)
```

Hence define

```text
m(xi)=(18/sqrt(23))
       Gamma(3/2-i xi)/Gamma(3-i xi)
       [1-2^(-3/2+i xi)].                            (EHGM.13)
```

The Gamma function has no zeros, its denominator has no real-line poles, and
`|1-2^(-3/2+i xi)|>=1-2^(-3/2)>0`.  Stirling's formula gives

```text
m is bounded and continuous,
m(xi)!=0 for every real xi,
|m(xi)|=O(|xi|^(-3/2)).                              (EHGM.14)
```

Let `M` be multiplication by `m` in Mellin coordinates.  Equations
`(EHGM.12)--(EHGM.13)` and dilation covariance give

```text
boxed: M h_lambda=f_lambda for every lambda>0.        (EHGM.15)
```

This transport is canonical.  After the logarithmic unitary
`u(t)->exp(x/2)u(exp x)`, dilations become translations and Mellin transform becomes Fourier
transform.  Every bounded operator commuting with all translations is a Fourier multiplier.  A
dilation-equivariant operator sending `h_1` to `f_1` must therefore have symbol `(EHGM.13)`, since
`Mellin(h_1)` never vanishes.  Thus `M` is the unique bounded dilation-equivariant gauge change.

Since `m` is nowhere zero, `M` is injective and has dense range.  Since `|m(xi)|->0`, its range is
not closed and `M^(-1)` is unbounded.  This properness is not imposed after construction; it is
forced by the relative Gamma orders in the two source features.

## 5. Phase quotient and local information neutrality

Write the polar decomposition pointwise:

```text
m=(m/|m|)|m|,  M=U|M|.                               (EHGM.16)
```

Because `m` never vanishes, `U` is a unitary Mellin multiplier.  Positive Gram formation quotients
out this entire phase:

```text
<M h_mu,M h_lambda>=<|M|h_mu,|M|h_lambda>.           (EHGM.17)
```

Put

```text
Q=M* M-I.                                            (EHGM.18)
```

Although `Q` is nonzero, `(EHGM.4)` and `(EHGM.15)` prove exact cellwise neutrality:

```text
boxed: <h_lambda,Q h_lambda>=0 for every lambda>0.    (EHGM.19)
```

The operator is not globally neutral.  Its multiplier `|m|^2-1` is negative at high frequency.
At zero,

```text
|m(0)|^2=(81 pi/92)(9/8-1/sqrt(2))>1.                (EHGM.20)
```

For an entirely symbolic lower bound, use `pi>3` and `1/sqrt(2)<29/40`; the right side is then
strictly larger than `243/230`.  Thus `Q` has both positive and negative spectral regions.  Local
norm equality has hidden a genuinely indefinite global mixing defect.

## 6. Exact relative-completion conservation law

From `(EHGM.15)` and `(EHGM.7)`,

```text
W_H=M W_6.
```

Therefore

```text
boxed: K=C+D,
D=W_6*QW_6.                                          (EHGM.21)
```

Here `D` is self-adjoint trace class.  Equations `(EHGM.19)` and `(EHGM.7)` give

```text
D(i,i)=0 for every Euler label i,
Tr D=0.                                              (EHGM.22)
```

The anomaly is not zero.  For the two labels `(p,0)` and `(p,1)`, whose clocks are `lambda` and
`2lambda`, the normalized correlations are

```text
<h_(2lambda),h_lambda>=512/729,
<f_(2lambda),f_lambda>=7794 sqrt(2)/14375.            (EHGM.23)
```

They are unequal because `sqrt(2)` is irrational.  Hence `D!=0`.  A nonzero self-adjoint
trace-class operator of trace zero cannot be positive or negative semidefinite, so `D` is
indefinite.

This is an exact conservation identity, not a bound:

```text
same diagonal capacity + same total capacity
  = order-six aperture Gram
  + zero-diagonal, zero-trace, sign-indefinite mixing anomaly
  = cubic Hellinger collision Gram.                  (EHGM.24)
```

No prime-independent scalar can express `D`; its entire content is off-diagonal incidence.  Yet
the generating multiplier `M` is universal and prime-independent.  This escapes the corpus no-go
against one shared scalar ghost without introducing label-fitted data.

## 7. Theta history lift

Let `Phi` be the theta Mellin-six history flux, `Tr Phi=1`.  Define

```text
T_6=Phi tensor C,
T_H=Phi tensor K,
Delta_rel=Phi tensor D.                              (EHGM.25)
```

Then

```text
boxed: T_H=T_6+Delta_rel,
Tr(T_H)=Tr(T_6)=routePPrimitiveCollisionCubicTraceBudget,
Tr(Delta_rel)=0.                                     (EHGM.26)
```

The two positive endpoints are integral--nuclear and retain every unsquared Euler coefficient.
Their relative anomaly is nuclear, purely mixed, and indefinite.  The order-six endpoint also
retains ULF-ESAC-001's singular sixth source boundary.  Thus theta history, Stokes aperture,
Euler prime powers, Gamma coherence, and collision formation are now connected by one exact
transport and one exact conservation identity.

## 8. RH-facing consequence and exact remaining theorem

This theorem supplies the previously missing source-side anomaly subtraction:

```text
boxed: T_6=T_H-Delta_rel.                             (EHGM.27)
```

It is derived from literal source features, preserves unsquared Euler coefficients, and requires
no divisor.  It also explains why scalar and positive-compression attempts failed: the correction
has zero diagonal and zero trace but is irreducibly indefinite.

What remains is not to invent that subtraction.  It is to prove that actual Euler--theta
completion uses this unique dilation-equivariant gauge change and that, after `(EHGM.27)`, the
completed Xi cubic Loewner synthesis factors contractively through `W_6` with no residual boundary.
If so, its total strict-right energy is at most
`Tr C<115/108`, while one strict-right copy costs at least `115/108`; functional equation then
gives RH.

This is still open.  The theorem does, however, remove three degrees of freedom from that edge:

1. source operator is fixed (`C`);
2. metric subtraction is fixed (`D`);
3. completion gauge change is fixed uniquely (`M`).

Only the Xi landing/residual-boundary theorem remains.  Supplying a zero before constructing that
landing would still be circular.

### Exact limitation: `M` is not the Xi landing

The corpus's primitive spectral-floor theorem must be applied here.  Every Euler source clock has
`lambda_i>=log 2`, whereas every strict-right Xi conormal has real rate `0<a<1/2`.  The multiplier
`M` sends `h_lambda` to `f_lambda`, whose slowest exponential is still `exp(-lambda t)`.  It changes
coherent gauge and regularity, not spectral rate.  Therefore `M` cannot map a primitive source
column to a strict-right Xi column and does not discharge W-H184.

The surviving architecture is a forced factorization, not a completed proof:

```text
order-six Euler aperture gauge
  -- unique equivariant M --> cubic Euler/Hellinger gauge
  -- missing noncommuting polar--Gamma rate changer R --> completed Xi conormal gauge. (EHGM.28)
```

Attack 38 in the audited frontier proves that `R` cannot intertwine the aperture semigroup: its
commutator must carry the source/target rate gap.  ULF-EHGM-001 fixes the first arrow and its metric
anomaly.  The only unsolved mechanism is now the second arrow together with its augmented
conservation law.

## 9. Hostile novelty and failure audit

1. Mellin diagonalization of dilation-equivariant operators and scale filtering are classical;
   see Gerald Kaiser, [*Wavelet Filtering with the Mellin Transform*](https://arxiv.org/abs/math-ph/0108013).
2. Gamma-integral coherent vectors and Gram factorizations are classical.  No novelty is claimed
   for `(EHGM.12)` in isolation.
3. Scalar equality `(EHGM.1)` is explicitly pre-existing corpus work.  ULF-ESAC-001's scalar
   novelty claim is corrected accordingly.
4. The surviving corpus-specific theorem is the unique explicit multiplier `(EHGM.13)` between
   the two already-forced Euler gauges and the compressed anomaly law
   `(EHGM.21)--(EHGM.27)`.
5. Failure condition: if the actual completed Xi synthesis does not factor through the
   anomaly-subtracted `W_6`, this is a source-geometry theorem but not an RH selector.
6. Stronger failure already proved: `M` alone preserves the Euler spectral floor and cannot be the
   Xi landing.  It is the source-gauge component of completion, not the rate-changing component.

## 10. Lean status

Both endpoint diagonals, their common trace, Euler summability, Gamma integrals, and parent source
syntheses have substantial Lean infrastructure.  This pass was explicitly Lean-read-only.  The
Mellin multiplier, uniqueness, dense nonclosed range, compressed zero-trace anomaly, and explicit
nonzero mixed entry require later formalization.
