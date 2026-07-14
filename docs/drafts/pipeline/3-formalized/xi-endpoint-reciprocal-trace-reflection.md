# Xi Endpoint Reciprocal-Trace Reflection

- **ID:** xi-endpoint-reciprocal-trace-reflection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Xi endpoint Neumann carrier and functional-equation reflection
- **Statement:** Functional-equation reflection imposes an absolutely convergent negative-binomial Ward law on every multiplicity-exact Xi reciprocal-power trace of order at least two.

## Goal

Constrain the all-order reciprocal traces already carried by the endpoint completed value without
assuming RH or introducing another divisor-location criterion.  The result removes redundant
degrees of freedom from any finite-coefficient or source-side argument that uses these traces.

## Theorem

Index the nontrivial Xi divisor with exact multiplicity and put

\[
z_q=\rho_q^{-1},\qquad T_k=\sum_q z_q^k \quad(k\ge2).
\]

Functional-equation reflection preserves the divisor copies and acts on the raw coordinate by

\[
z_q\longmapsto -\frac{z_q}{1-z_q}.
\]

The endpoint value bound gives \(|z_q|<9/10\) uniformly and
\(\sum_q|z_q|^2<3/4\).  Therefore, for every integer \(k\ge2\), the double family

\[
\binom{n+k-1}{k-1}z_q^{k+n}
\]

is absolutely summable over \((n,q)\), and

\[
\boxed{
T_k=(-1)^k\sum_{n\ge0}\binom{n+k-1}{k-1}T_{k+n}.}
\]

Removing the leading term gives the constraint-only form

\[
\boxed{
\sum_{n\ge0}\binom{n+k}{k-1}T_{k+n+1}
=\bigl((-1)^k-1\bigr)T_k.}
\]

Thus every even-order higher-trace tail vanishes, while every odd-order tail is exactly
\(-2T_k\).  In particular,

\[
\boxed{\sum_{n\ge0}(n+2)T_{n+3}=0.}
\]

## Proof

The exact divisor reflection \(\rho\mapsto1-\rho\) yields

\[
\frac1{1-\rho}=-\frac{z}{1-z}.
\]

For \(|z|<1\), the negative-binomial series gives

\[
(-1)^k\left(-\frac z{1-z}\right)^k
=\sum_{n\ge0}\binom{n+k-1}{k-1}z^{k+n}.
\]

To sum over the full divisor, use \(|z_q|<9/10\), \(k\ge2\), and
\(\sum_q|z_q|^2<\infty\):

\[
\left|\binom{n+k-1}{k-1}z_q^{k+n}\right|
\le
\binom{n+k-1}{k-1}\left(\frac9{10}\right)^n|z_q|^2.
\]

The scalar negative-binomial majorant is summable.  Tonelli/Fubini therefore permits both
summation interchange and reindexing by the multiplicity-preserving reflection equivalence.  This
proves the all-order identity.  Splitting off its \(n=0\) term proves the leading-term-free law.

## Formal certificate

- `xiRawReciprocalCoordinate_reflect_eq_mobius`
- `hasSum_xiRawReciprocalCoordinate_reflect_binomial`
- `summable_xiRawReciprocalTraceReflection_double`
- `summable_xiRawReciprocalPowerTrace_reflectionSeries`
- `xiRawReciprocalPowerTrace_reflection`
- `xiRawReciprocalPowerTrace_reflection_tail`
- `xiRawReciprocalPowerTrace_reflection_tail_two`

Primary module:

- `formal/GaloisForLFunctions/RHTower/XiEndpointReciprocalTraceReflection.lean`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Contribution to the RH chain

The theorem is unconditional and is not itself an RH equivalence.  It sharpens the endpoint chain
to

\[
\text{completed endpoint source value}
\Longrightarrow
\text{strict reciprocal disk and }\ell^2\text{ mass}
\Longrightarrow
\text{all-order trace reflection constraints}
\Longrightarrow
\text{fewer independent source coefficients at the sharp endpoint gate}.
\]

It does not force the reflection defect to vanish: a functional-equation orbit may still be a
nontrivial two-cycle.  The remaining RH-bearing task is a source-side orientation statement strong
enough to collapse those two-cycles, now subject to the exact trace relations above.

## Gates

- [x] 0 → 1 in-progress: exact constraint and absolute-convergence mechanism identified
- [x] 1 → 2 fully-proven: complete proof above
- [x] 2 → 3 formalized: Lean module builds without placeholders and is wired into the umbrella
- [ ] 3 → 4 publication-ready: standalone novelty and literature status not claimed
