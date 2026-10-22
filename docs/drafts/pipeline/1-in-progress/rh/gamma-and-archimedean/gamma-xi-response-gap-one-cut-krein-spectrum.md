# Gamma--Xi response gap: one-cut Krein spectrum

- **ID:** gamma-xi-response-gap-one-cut-krein-spectrum
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `GammaJordanXiTangentResponseGap.lean` · Gamma-sewn signed Jordan / Xi tangent response
- **Statement:** The compiled Gamma and Xi responses are normalized second-moment-biased symmetric Meixner laws in strict monotone-likelihood-ratio order, hence have one spectral crossing; analytic tangent rigidity rules out scalar Hilbertization even after restriction to the accumulating inverse-prime chamber.

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

Both `H_hi` and `H_lo` are Hilbert squared-distance kernels.  The global translation-invariant
difference `W` is not conditionally negative definite and hence is not itself a global Hilbert
squared-distance kernel.  It is also not conditionally negative definite after restriction to the
inverse-prime coordinates

```text
x_p=atanh(1/p).
```

Equivalently, some finite prime packet and zero-sum real coefficients violate the negative-type
quadratic form.  If a
scalar stationary transfer has multiplier `h`, its filtered spectrum is `|h|^2 D`; it can be a
Hilbert variogram only if `h=0` almost everywhere on `(-s_*,s_*)`.  In particular a nonzero causal
Hardy transfer cannot do this, by boundary uniqueness.  A noncausal sharp high-pass projection
does do it and produces exactly `H_hi`.

The prime-restricted no-go has a sharp finite-jet survivor.  Write `mu=B-A=-D` and

```text
m_n=int s^(2n) mu(ds).
```

Every `m_n` for `n>=1` is strictly positive.  More strongly, for every nonzero real polynomial
`P` with `P(0)=0` and `deg P<=6`,

```text
int |P(i*s)|^2 mu(ds) > 0.                              (GX-JET6)
```

Thus a negative-type witness exists but its first possible polynomial tangent order is at least
seven.

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

There is a stronger positive formulation.  Put

```text
A(s)=2s^2 f_(1/2)(s),       B(s)=s^2 f_1(s).
```

The response identities at `t=0`, equivalently
`-(sech(t)^alpha)''|_(t=0)=alpha`, give `int A=int B=1`.  Furthermore

```text
B(s)/A(s)=q(s)/2
```

is strictly increasing in `|s|`.  Thus `B` strictly dominates `A` in monotone-likelihood-ratio
order: the Xi tangent response is more tail-heavy than the joined Gamma response.  In particular,
every integrable increasing observable of `|s|` has at least as large an expectation under `B` as
under `A`, strictly so for nonconstant observables.  The one-cut law is the threshold form of this
stronger ordering.

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

### Tangent rigidity on the inverse-prime chamber [PROVED HERE]

The following general theorem is the killing mechanism.  Let `mu` be an even finite signed measure
with an exponential moment and put

```text
w(t)=int (1-cos(t*s)) mu(ds).
```

If `w(x-y)` is conditionally negative definite on any infinite subset of the real line
accumulating at zero, then

```text
s^2 mu(ds) >= 0.                                        (GX-TAN)
```

To prove it, choose distinct nodes in the set converging to zero.  Their divided differences of
`exp(i*s*x)` converge in `L^2(|mu|)` to the corresponding derivatives at zero; the exponential
moment supplies the common integrable majorant.  The negative-type quadratic form, with the
zero-sum divided-difference coefficients, therefore implies

```text
int |P(i*s)|^2 mu(ds) >= 0
```

for every real polynomial `P` with `P(0)=0`.  Even/odd splitting yields

```text
int s^2 Q(s)^2 mu(ds) >= 0
```

for every real polynomial `Q`.  Polynomials are dense in `L^2(s^2|mu|)` because the exponential
moment makes the Fourier transform of any orthogonal finite signed measure analytic; vanishing of
all moments then forces that measure to vanish.  Approximation of indicators of the negative part
now proves `(GX-TAN)`.

For the response gap, `mu=B-A` is negative on the nonempty interval `0<|s|<s_*`, so `(GX-TAN)` is
impossible.  Infinitely many primes and `atanh(1/p)->0` therefore kill conditional negative type on
the inverse-prime chamber without any prime-number-theorem input.

For the positive finite-jet survivor, strict MLR and equal total mass give every pure moment
`m_n>0`.  Direct differentiation of the two exact sech response laws gives

```text
m_1=3/2,
m_2=105/4,
m_3=5607/8,
m_4=450615/16,
m_5=51499833/32,
m_6=7975041165/64.
```

After the harmless scaling `a_n=2^n m_n`, the odd and even `3 by 3` Gram blocks have positive
leading principal minors and determinants

```text
det H_odd = 43,641,657,900,
det H_even = 16,867,972,687,606,200.
```

Even/odd splitting of `P` proves `(GX-JET6)`.  Therefore the analytic obstruction is genuinely
multi-order: no pure jet, and no mixed jet through degree six, can witness it.

## Novelty / parent audit

The family `phi_alpha=sech^alpha`, its Gamma-modulus densities, and the density recurrence are
classical; Pitman--Yor (2003), equations (32), (33), and (39), gives them in essentially the exact
normalization used here.  Jordaan--Wang--Zhou (2014), formula (15), proves the parent monotonicity
of the relevant Gamma-weight ratios.  The Gamma recurrence, digamma monotonicity, vertical Gamma
asymptotic, Schoenberg representation, and Hardy boundary uniqueness are therefore all literature
or parent tools, not discoveries here.

Exact-formula and concept searches found no source treating the particular *compiled response
laws* `A=2s^2f_(1/2)` and `B=s^2f_1` as normalized laws, their strict MLR ordering, the accumulating-
tangent rigidity `(GX-TAN)`, or the six-jet-positive/finite-prime-negative separation.  Those
source-law statements are presently classified `[NOVELTY UNVERIFIED]`; the recurrence is
`[LITERATURE]`, raw ratio monotonicity is `[REDISCOVERED]`, and the causal-filter obstruction is
`[BRIDGE]`.  No priority claim is made.

Primary parent references:

- J. Pitman and M. Yor, *Infinitely Divisible Laws Associated with Hyperbolic Functions*, Canadian Journal of Mathematics 55 (2003), 292--330.
- K. Jordaan, K. Wang, and J. Zhou, *Monotonicity of zeros of polynomials orthogonal with respect to an even weight*, Integral Transforms and Special Functions (2014).
- NIST DLMF, Chapter 5, for Gamma recurrence, duplication, psi series, and vertical asymptotics.
- Schoenberg's translation-invariant negative-type representation and the standard Hardy boundary uniqueness theorem.

## No-go closure

- **Exact killing theorem/mechanism:** globally the low-frequency interval has `D>0`, whereas a translation-invariant Hilbert variogram requires off-zero Fourier density `D<=0`; a causal scalar multiplier cannot vanish on that interval without vanishing identically.  On any accumulating restriction, `(GX-TAN)` would force `s^2(B-A)>=0`, contradicting the same open negative band.  Hence the unchanged scalar gap is not Hilbertizable even on inverse-prime coordinates.
- **Strongest positive survivor:** `A` and `B` are normalized response laws in strict MLR order.  Their unique source-derived cut gives the exact two-channel decomposition `W=H_hi-H_lo`; `H_hi` is a genuine infinite Hilbert channel.  Simultaneously `(GX-JET6)` shows that all polynomial tangent packets through degree six are strictly positive even though some finite prime packet is negative.
- **New insight:** the Xi tangent response shifts spectral mass monotonically outward relative to the Gamma response, but the obstruction is invisible to low jets.  Restriction and scalar nonstationarity cannot repair the unchanged kernel.  The RH-bearing metric must change the object by retaining residue-pointed multichannel source data.
- **Status:** the strict MLR law, unique cutoff, and exact three sign chambers are permanently
  formalized without project axioms in `GammaXiResponseGapOneCutSpectrum.lean`.  The Fourier
  representation, Schoenberg no-go, Hardy obstruction, two-channel integral realization,
  inverse-prime tangent rigidity, and six-jet survivor remain paper-only, so this card deliberately
  stays in progress.

## Log

- 2026-07-20 — extracted from the exact Gamma--Jordan and Xi tangent responses; paper proof and parent novelty audit completed.
- 2026-07-20 — formalized the source-specific strict MLR cross-product theorem and the exact
  one-cut spectral sign law; kept the global Hilbert/Krein consequences outside the formalized
  claim until their analytic measure layer is compiled.
- 2026-07-20 — proved on paper that accumulating inverse-prime restriction cannot restore negative
  type; extracted the strictly positive degree-six tangent survivor and the degree-at-least-seven
  obstruction threshold.
