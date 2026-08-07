# Suzuki critical rooted Bianchi cofinal no-go

- **ID:** `suzuki-critical-rooted-bianchi-cofinal-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-critical-rooted-bianchi-cofinal-no-go-formalized.md`
- **Type:** hostile audit of `SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`
- **Status:** `[PAPER-PROVED] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`
- **Parent:** `suzuki-rooted-midpoint-compound-gram.md`

## Exact question

Can the raw pointed Gamma--Bianchi vector proposed to pay midpoint debt `d^2` be passed cofinally as an ordinary positive Hilbert Gram at Suzuki's critical prime weight?

## Corpus normalization

Existing raw Bianchi atom at prime `p` and displacement `x` has diagonal mass

```text
b_x(p) = Lambda(p)/p * exp(-x log p).
```

All proved cofinal convergence theorems assume `x>0`.  Suzuki screw source instead has critical prime coefficient `Lambda(p)/sqrt(p)`.  Matching these weights forces

```text
x = -1/2,
b_(-1/2)(p) = Lambda(p)/sqrt(p).                     (1)
```

This is not a fitted proxy.  Corpus theorem
`vonMangoldtGammaRenormalizedBoundaryCoordinate_eq` identifies uniquely renormalized complete
Gamma-conormal boundary coordinate with square root of `b_x`.  Hence at `x=-1/2` actual existing
source coordinate is

```text
GammaBoundary_crit(p)=sqrt(Lambda(p)/sqrt(p)).        (2)
```

## Killing theorem

`SUZUKI-CRITICAL-ROOTED-BIANCHI-DIVERGENCE` `[PAPER-PROVED]`:

1. identity `(1)` holds prime by prime;
2. `p |-> Lambda(p)/sqrt(p)` is not summable over primes;
3. therefore actual critical Gamma-conormal boundary coordinate `(2)` is not an `ell^2` vector and
   its diagonal Gram has no finite cofinal limit;
4. for every scalar `c`, `p |-> c GammaBoundary_crit(p)` is square-summable iff `c=0`.

## Falsifiers

- A summability theorem at `x=-1/2` for the exact raw mass.
- A normalization in existing Bianchi feature that changes `Lambda(p)/p` before inverse translation.
- A proved source cancellation performed before the raw diagonal limit.

## Proof

For prime `p`, `Lambda(p)=log p`, `sqrt(p)<=p`, and `log 2<=log p`.  Hence

```text
log 2 / p <= Lambda(p)/sqrt(p).
```

Euler's divergence of the prime harmonic series forces divergence.  No prime-number theorem or estimate is required.

More explicitly, for every prime `p`, positivity gives

```text
exp(log(p)/2)=sqrt(p),
p=sqrt(p)^2.
```

Therefore

```text
b_(-1/2)(p)
 = Lambda(p)/p * exp(log(p)/2)
 = Lambda(p)/sqrt(p).
```

Since `p>=2`, monotonicity of logarithm and `sqrt(p)<=p` give

```text
log(2)/p <= log(p)/p <= log(p)/sqrt(p)
                         = Lambda(p)/sqrt(p).
```

All terms are nonnegative.  If critical mass were summable, comparison and division by positive
constant `log(2)` would make `sum_p 1/p` summable, contradicting Euler.  Taking square-root feature
`Bcrit(p)=sqrt(Lambda(p)/sqrt(p))`, its squared norm is exactly divergent critical mass.  Hence no
unrenormalized cofinal `ell^2` Bianchi vector exists.

For scalar-renormalization rigidity, `(c Bcrit(p))^2=c^2 b_(-1/2)(p)`.  When `c != 0`, summability
would imply summability of `b_(-1/2)` after division by `c^2`, contradiction.  At `c=0` it is
trivial.  Thus fixed scalar border cannot leave any nonzero proportion of critical rooted
coordinate.  Leading cancellation must be exact and coordinatewise before limit.  Square.

## Hostile audit

- **Finite aperture:** not attacked.  Every finite cutoff remains a literal positive Gram.
- **Absolute Euler displacement:** not attacked.  Existing cofinal theorems assume `x>0`, where decay restores summability.
- **Critical displacement:** killed exactly at `x=-1/2`; no limit exchange or estimate is involved.
- **Cancellation escape:** possible only if prime/polar/Gamma cancellation is performed before taking separate raw diagonal limit.  Such cancellation is absent from original equation `(4)`.
- **Scalar border escape:** killed.  Every nonzero constant residual multiple remains divergent.
  Viable repair needs exact coordinatewise cancellation, not global rescaling or finite border.
- **Generalized Nevanlinna escape:** one-negative-square theory classifies indefinite kernels but does not turn divergent raw critical vector into Hilbert vector.

Verdict on original unrenormalized cofinal claim: `FALSE`.

## Relentless-interrogation target

Original architecture is false only in its **unrenormalized cofinal order of operations**.  Strongest positive survivor is:

> keep finite physical aperture; combine rooted Bianchi debt with global Xi/Gamma/polar counterterm at kernel level; prove cancellation and positivity there; only then take cofinal limit.

This is stronger than adding an unspecified remainder because it forbids a separate critical raw
Gram and forces source cancellation before completion.  More precisely, if `B_M(p)` is rooted
boundary coordinate and `J_M(p;z)` actual Julia/Volterra coordinate, completed feature must be
formed prime-by-prime,

```text
R_M(p;z)=J_M(p;z)-m B_M(p)+L_M(p;z),                 (3)
```

where `L_M` is source-derived boundary leakage.  Gram may be taken only after forming `R_M`.
Scalar-rigidity theorem forces leading `B_M` coefficient in `(3)` to cancel exactly; no nonzero
prime-independent residual is admissible.

## Corrected open core

`SUZUKI-FINITE-APERTURE-RENORMALIZED-MIDPOINT-GRAM` `[CONJECTURE] [OPEN CORE]`:

> At every finite physical aperture, combine rooted `d^2` Bianchi debt with prime-dependent Volterra boundary leakage and exact Gamma/polar counterterm at compound-kernel level.  Prove resulting finite kernel is a Gram.  Establish cofinal convergence only for already-cancelled kernel.

This passes killing theorem because no divergent critical raw diagonal is assigned an independent limit.

## Novelty audit

- Euler divergence and comparison: `[BRIDGE]`.
- Critical inverse-translation identity for existing raw Bianchi normalization: exact source
  specialization, `[NOVELTY UNVERIFIED]`.
- Exact connector to uniquely renormalized Gamma-conormal boundary: `[NEW CONNECTION] [NOVELTY
  UNVERIFIED]`.
- Scalar-renormalization rigidity: `[NEW THEOREM] [NOVELTY UNVERIFIED]`.
- Scientific delta: rules out standalone cofinal rooted Hilbert completion and forces exact
  coordinatewise cancellation before Gram/limit.
