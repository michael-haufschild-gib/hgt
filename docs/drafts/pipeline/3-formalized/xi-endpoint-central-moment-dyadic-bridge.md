# Xi Endpoint--Central Moment Dyadic Bridge

- **ID:** xi-endpoint-central-moment-dyadic-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Xi endpoint reciprocal traces and the prime--archimedean central moment germ
- **Statement:** Every centered reciprocal-square Xi moment, equivalently every fixed prime--Gamma source Taylor moment, is an explicit absolutely convergent dyadic transform of the raw endpoint reciprocal traces.

## Goal

Weld two previously separate top-down carriers by an exact value relation.  The endpoint Neumann
route produces raw reciprocal traces \(T_k=\sum_\rho\rho^{-k}\); the central trace--Hankel route uses
the moments of \(-\left(\rho-\tfrac12\right)^{-2}\).  The theorem proves that the latter contains no
additional divisor-side data once the complete raw trace carrier is known.

## Theorem

Let

\[
T_k=\sum_q\rho_q^{-k},\qquad
M_m=\sum_q\left(-\frac1{(\rho_q-\tfrac12)^2}\right)^{m+1},
\]

where \(q\) ranges over the nontrivial Xi divisor with exact multiplicity.  Then for every
\(m\ge0\), unconditionally,

\[
\boxed{
M_m=(-1)^{m+1}\sum_{n\ge0}
\binom{n+2m+1}{2m+1}2^{-n}T_{n+2m+2}.}
\]

The same right-hand side equals the \(m\)-th analytic trace moment of the normalized continued
prime--Gamma relative source.

The series is absolutely convergent after expanding it over both \(n\) and the divisor copies.

## Proof

For the raw reciprocal coordinate \(z=1/\rho\),

\[
-\frac1{(\rho-\tfrac12)^2}
=-\frac{z^2}{(1-z/2)^2}.
\]

Raising this identity to the \((m+1)\)-st power and applying the negative-binomial series gives

\[
\left(-\frac{z^2}{(1-z/2)^2}\right)^{m+1}
=(-1)^{m+1}\sum_{n\ge0}
\binom{n+2m+1}{2m+1}2^{-n}z^{n+2m+2}.
\]

The endpoint theorem supplies \(|z|<9/10\) and \(\sum_q|z_q|^2<\infty\).  The undamped
negative-binomial double family of base order \(2m+2\) is already absolutely summable; multiplication
by \(2^{-n}\) only decreases its norm.  Fubini therefore gives the displayed moment identity.
The existing prime--archimedean central moment theorem then replaces \(M_m\) by the exact Taylor
moment of the completed source.

## Formal certificate

- `xiZeroCopyReciprocalSquare_eq_rawDyadicMobius`
- `hasSum_xiZeroCopyReciprocalSquare_pow_rawDyadicTraces`
- `summable_xiCentralRawDyadicTrace_double`
- `xiCentralReciprocalMoment_eq_rawDyadicTraces`
- `primeArchSourceMoment_eq_rawDyadicTraces`

Primary module:

- `formal/GaloisForLFunctions/RHTower/XiEndpointCentralMomentDyadicBridge.lean`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Contribution to the RH chains

The bridge gives the unconditional chain

\[
\text{raw endpoint trace carrier}
\Longrightarrow
\text{all centered reciprocal-square Xi moments}
=
\text{all fixed prime--Gamma source moments}
\Longrightarrow
\text{the complete central trace--Hankel test data}.
\]

It does not prove the required positivity of that Hankel data.  Its effect is to eliminate a
possible source-to-divisor value-identification gap: any source-side theorem that controls the
dyadic raw-trace transforms now acts directly on the already formalized RH-equivalent central
Hankel cone.

## Gates

- [x] 0 → 1 in-progress: exact rational substitution and dyadic transform identified
- [x] 1 → 2 fully-proven: complete absolute-convergence proof above
- [x] 2 → 3 formalized: Lean module builds without placeholders and is wired into the umbrella
- [ ] 3 → 4 publication-ready: standalone novelty and literature status not claimed
