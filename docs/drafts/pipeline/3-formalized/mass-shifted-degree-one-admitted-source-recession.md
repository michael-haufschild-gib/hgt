# Mass-shifted canonical degree-one admitted-source recession

- **ID:** mass-shifted-degree-one-admitted-source-recession
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, survivor of Conjecture 61
- **Statement:** Canonical moving degree-one null admission converges to scaled root `1/2` and its literal arithmetic source has positive limit `11/64`.

## Goal

Replace failed degree-only uniformity by actual null-admission law. Sign the literal completed source
along canonical moving first face, before reflection aggregation.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven: `[PROVED HERE]`
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Paper proof `[PROVED HERE]`

Write `m_k(w)=Re xiShiftedReciprocalMoment(w²,k)` and

\[
 R(w)=w^2\frac{m_1(w)}{m_0(w)}.
\]

The normalized moment limits are

\[
 N_k(w):=\frac{2w^{2k+1}}{\log w}m_k(w)\to c_k.
\]

Since `c₀=1` and `m₀>0`, exact cancellation gives `R(w)=N₁(w)/N₀(w)` eventually. Hence
`R(w)→c₁/c₀=1/2`.

Canonical null amplitude is

\[
 A_w=X-\frac{m_1(w)}{m_0(w)}=X-\frac{R(w)}{w^2}.
\]

Using exact degree-one source law and normalized limits,

\[
 \frac{w^9}{\log w}\mathcal S(w,A_w)
 =R(w)^2N_2(w)-3R(w)N_3(w)+2N_4(w)
 \longrightarrow
 \frac14\frac38-\frac32\frac5{16}+2\frac{35}{128}
 =\frac{11}{64}>0.
\]

Positive scaling implies canonical admitted arithmetic source is eventually strictly positive.
No computation, RH assumption, fixed reporter, or pointwise kernel sign is used.

## Significance

Generic moving monic degree one is cofinally negative at scaled root `5/4`, while actual null
admission converges to safe root `1/2`. Admission is a constitutive source constraint, not a
dimension bound. Higher-degree successor should use scaled arcsine orthogonal polynomial selected
by Hankel nullity.

## Exact successor

Identify every fixed-degree canonical scaled null polynomial with its arcsine orthogonal limit and
evaluate adaptive source quadratic form on that admitted limit. Then determine whether resulting
positive margins are uniform in degree or decay to zero.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedAdaptiveArithmeticSourceDegreeOneAdmissionRecession.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Capstones:
  - `tendsto_scaled_xiShiftedDegreeOneNullRoot_squareParam`
  - `tendsto_scaled_xiShiftedDegreeOneAdmittedArithmeticSource`
  - `xiShiftedDegreeOneAdmittedArithmeticSource_eventually_pos`
- Direct check: PASS, warning-free.
- Target build: PASS.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
