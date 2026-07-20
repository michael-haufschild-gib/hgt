# Gamma--Xi response gap: one-cut Krein spectrum

- **ID:** gamma-xi-response-gap-one-cut-krein-spectrum
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `GammaJordanXiTangentResponseGap.lean` · Gamma-sewn signed Jordan / Xi tangent response
- **Statement:** The exact Gamma--Xi response gap has a unique spectral sign cut; consequently it is not a Hilbert variogram, no nonzero causal scalar transfer can Hilbertize it, and its canonical positive survivor is a two-channel Krein decomposition.

## Goal

Determine whether the positive prime response-gap kernel already constructed in the source admits
the Hilbert squared-distance representation needed by the aperture program.  The result must use
the literal Gamma and Xi response laws, not a generic realization theorem or a finite graph
completion.

## Gates

- [x] 0 → 1  in-progress: literal source response, explicit spectral attack, Door-2 passport
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open mathematical dependency
- [ ] 2 → 3  formalized: Lean theorem, direct leaf check, exact module build, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact theorem [PROVED HERE]

For `alpha>0`, put

```text
phi_alpha(t)=sech(t)^alpha,
f_alpha(s)=2^(alpha-2)/(pi Gamma(alpha))
             |Gamma(alpha/2+i s/2)|^2.
```

Then `phi_alpha(t)=int exp(i t s) f_alpha(s) ds`.  Let

```text
G(t)=(3/2)phi_(5/2)(t)-(1/2)phi_(1/2)(t),
X(t)=2phi_3(t)-phi_1(t),
W(t)=G(t)-X(t).
```

These are respectively the compiled joined Gamma--Jordan response, the all-depth Xi tangent
response in the common hyperbolic coordinate, and their response gap.  There is a unique
`s_* > 0` such that, with

```text
D(s)=s^2(2f_(1/2)(s)-f_1(s)),
```

```text
D(s)>0  iff  0<|s|<s_*,
D(s)=0  iff  s=0 or |s|=s_*,
D(s)<0  iff  |s|>s_*.
```

Moreover

```text
W(t)=int exp(i t s)D(s)ds
    =H_hi(t)-H_lo(t),

H_hi(t)=int_(|s|>s_*) (1-cos(ts))(-D(s))ds,
H_lo(t)=int_(0<|s|<s_*) (1-cos(ts))D(s)ds.
```

Both `H_hi` and `H_lo` are Hilbert squared-distance kernels.  The difference `W` is not
conditionally negative definite and hence is not itself a Hilbert squared-distance kernel.  If a
scalar stationary transfer has multiplier `h`, its filtered spectrum is `|h|^2 D`; it can be a
Hilbert variogram only if `h=0` almost everywhere on `(-s_*,s_*)`.  In particular a nonzero causal
Hardy transfer cannot do this, by boundary uniqueness.  A noncausal sharp high-pass projection
does do it and produces exactly `H_hi`.

## Proof

The Gamma recurrence gives the exact density recurrence

```text
f_(alpha+2)(s)=(alpha^2+s^2)/(alpha(alpha+1)) f_alpha(s).
```

At `alpha=1/2` and `alpha=1`, respectively, this yields

```text
(3/2)f_(5/2)-(1/2)f_(1/2)=2s^2 f_(1/2),
2f_3-f_1=s^2 f_1.
```

Fourier transformation proves the displayed formula for `D`.  Its total mass is zero because
`W(0)=G(0)-X(0)=1-1=0`.

Since both densities are strictly positive, their comparison is governed by

```text
q(s)=f_1(s)/f_(1/2)(s)
    =sqrt(2 pi) |Gamma(1/2+i s/2)|^2
                  /|Gamma(1/4+i s/2)|^2.
```

For `s>0`, logarithmic differentiation gives

```text
(log q)'(s)
 =Im psi(1/4+i s/2)-Im psi(1/2+i s/2)>0.
```

The strict inequality follows term by term from

```text
Im psi(a+i u)=sum_(n>=0) u/((n+a)^2+u^2),
```

because `u>0` and `1/4<1/2`.  Thus `q` is strictly increasing on the positive half-line.

At zero, Gamma duplication and strict decrease of Gamma on `(0,3/2]` give

```text
Gamma(1/4)^2 > Gamma(1/4)Gamma(3/4)=sqrt(2) pi.
```

Consequently

```text
q(0)<sqrt(pi)<2.
```

The vertical Gamma-ratio asymptotic gives

```text
|Gamma(1/4+i s/2)|/|Gamma(1/2+i s/2)|
  ~(s/2)^(-1/4),
```

so `q(s)~sqrt(pi s)` and tends to infinity.  Continuity and strict monotonicity now give a unique
positive solution `q(s_*)=2`.  Since

```text
D(s)=s^2 f_(1/2)(s)(2-q(s))
```

and `q` is even, the three sign statements follow.

For a continuous translation-invariant kernel vanishing at zero, the Levy--Khintchine--Schoenberg
representation says that conditional negative definiteness is equivalent to a representation
`int (1-cos(ts)) dnu(s)` with `nu` positive, up to a nonnegative quadratic term at frequency zero.
Uniqueness of the Fourier transform of finite signed measures forces the off-zero representing
measure of `W` to have density `-D`.  This is impossible because `D` is strictly positive on the
nonempty low-frequency interval.  Splitting the positive and negative parts of `D` gives the two
displayed positive Hilbert channels and the exact Krein difference.

Finally scalar stationary filtering multiplies the density by `|h|^2`.  Positivity of the
variogram measure therefore forces `h=0` almost everywhere wherever `D>0`.  Boundary uniqueness
for Hardy functions makes this impossible for a nonzero causal transfer.  The characteristic
function of the high-frequency region is a legal noncausal projection and leaves the positive
measure `(-D)1_(|s|>s_*) ds`, proving the survivor.

## Novelty / parent audit

The family `phi_alpha=sech^alpha` and its Gamma-modulus densities is the classical generalized
hyperbolic-secant family (Harkness--Harkness, 1968).  The Gamma recurrence, digamma monotonicity,
vertical Gamma asymptotic, Schoenberg representation, and Hardy boundary uniqueness are parent
tools.  Exact-formula and concept searches found no source treating the particular compiled
Gamma--Xi combination `G-X`, its unique sign cut, or the causal Hilbertization obstruction.  The
new claim is the source-specific synthesis and the resulting one-cut Krein law, not any parent
identity in isolation.

Primary parent references:

- W. L. Harkness and M. L. Harkness, *Generalized Hyperbolic Secant Distributions*, JASA 63 (1968), 329--337.
- NIST DLMF, Chapter 5, for Gamma recurrence, duplication, psi series, and vertical asymptotics.
- Schoenberg's translation-invariant negative-type representation and the standard Hardy boundary uniqueness theorem.

## No-go closure

- **Exact killing theorem/mechanism:** the low-frequency interval has `D>0`, whereas a Hilbert variogram requires off-zero Fourier density `D<=0`; a causal scalar multiplier cannot vanish on that interval without vanishing identically.
- **Strongest positive survivor:** the unique source-derived cut gives the exact two-channel decomposition `W=H_hi-H_lo`; `H_hi` is a genuine infinite Hilbert channel obtained by the sharp high-pass projection.
- **New insight:** pointwise positivity and bilipschitz comparison of the prime gap do not imply negative type.  The missing RH converter cannot be a scalar causal dressing of this gap; it must either be noncausal at the canonical cut or genuinely couple the low and high Krein channels before taking norms.
- **Status:** complete paper proof; permanent unconditional Lean formalization in progress.

## Log

- 2026-07-20 — extracted from the exact Gamma--Jordan and Xi tangent responses; paper proof and parent novelty audit completed.
