# Actual adaptive mixed Gamma kernel pointwise-positivity no-go

- **ID:** mass-shifted-adaptive-mixed-kernel-pointwise-positivity-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, Conjecture 55
- **Statement:** The actual amplitude-selected mixed Gamma kernel can be strictly negative inside the physical Euler ray, already for a linear amplitude; hence source domination cannot follow from pointwise positivity of the common kernel.

## Goal

Close the residual logical gap between “the mixed factorial carrier can change sign” and the
stronger claim actually needed to rule out a positive-kernel proof: the Gamma average defining the
literal adaptive source kernel can itself remain negative at a physical source point.

## Gates

- [x] 0 → 1 in-progress: exact physical witness and source-native formula identified
- [x] 1 → 2 fully-proven: complete symbolic paper proof below; no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: report integration and claim audit

## Falsified conjecture

For every `w > 0`, real polynomial amplitude `A`, and `x > 1`,

\[
  \mathcal K_{w,A}(x)\ge 0.
\]

This is false for the actual kernel of Conjecture 55, not only for an abstract positive carrier.
In fact, failure is maximal: for every fixed physical source point `x≥1`, some linear amplitude
makes the kernel strictly negative there.

## Exact witness and proof `[PROVED HERE]`

Fix `w>0`, put

\[
 x_w=e^{1/w},\qquad a_w={111\over133}w^2,
 \qquad A_w(X)=1-a_wX.
\]

Then `x_w>1` and `w log x_w=1`.  If `B_n` is the corpus reverse-Bessel polynomial, the coefficient
packet of `A_w^2` is `(1,-2a_w,a_w^2)`, while the forced midpoint adaptation `M_1` gives
`(2,-6a_w,4a_w^2)`.  The exact normalized radial-kernel law therefore gives

\[
 \mathcal K_{w,A_w}(x)
 ={x^{-(1/2+w)}\over96w^9}
 \left(24w^4 B_2(z)-12a_ww^2B_3(z)+a_w^2B_4(z)\right),
 \qquad z=w\log x.
\]

The closed reverse-Bessel coefficients give

\[
 B_2(1)=7,\qquad B_3(1)=37,\qquad B_4(1)=266.
\]

At `x=x_w`, the bracket is

\[
 168w^4-444a_ww^2+266a_w^2
 =-{2298\over133}w^4.
\]

Consequently

\[
 \boxed{
 \mathcal K_{w,A_w}(e^{1/w})
 =-{383\over2128w^5}
   \left(e^{1/w}\right)^{-(1/2+w)}<0.}
\]

All equalities are finite polynomial identities plus the already formalized common-kernel law;
no asymptotic or numerical input enters.

## Exact complete linear-amplitude classification `[PROVED HERE]`

For `A_a(X)=1-aX` and `z=w log x`, direct formation of the midpoint-adapted square packet gives

\[
 \mathcal K_{w,A_a}(x)
 ={x^{-(1/2+w)}\over96w^9}
 \left(24w^4B_2(z)-12aw^2B_3(z)+a^2B_4(z)\right).       \tag{1}
\]

Its discriminant is governed by the exact positive-coefficient identity

\[
 \begin{aligned}
 D(z)&=3B_3(z)^2-2B_2(z)B_4(z)\\
 &=z^6+10z^5+42z^4+90z^3+105z^2+90z+45.
 \end{aligned}                                           \tag{2}
\]

Hence `D(z)>0` for every `z≥0`.  Since `B_4(z)>0`, the vertex

\[
 a_*(w,x)={6w^2B_3(z)\over B_4(z)}
\]

is nonzero and (1) becomes

\[
 \boxed{
 \mathcal K_{w,A_{a_*}}(x)
 =-{x^{-(1/2+w)}D(z)\over8w^5B_4(z)}<0.}                 \tag{3}
\]

Thus for every `w>1/2` and every `x≥1`, there exists a linear amplitude with negative actual
mixed Gamma kernel at `x`.

## No-go closure

- **Exact killing theorem/mechanism:** factorial-diagonal adaptation of the square packet does not
  preserve positivity after the literal reverse-Bessel Gamma average.  The order-2,3,4 radial
  kernels have enough strict log-concavity at `w log x=1` for the linear-amplitude quadratic to
  have a negative interval; `a_w` is its vertex.
- **Strongest positive survivor:** pointwise sign is governed exactly by the quadratic
  `24w^4B_2(z)-12aw^2B_3(z)+a^2B_4(z)` on the complete one-parameter linear-amplitude family,
  with exact positive discriminant (2), minimizing amplitude, and negative minimum (3).
  Thus a valid theorem must restrict amplitudes by actual null-flag admission or compare the
  rational–Gamma and von Mangoldt formations after signed integration.  It cannot use only
  `Λ(m)≥0`, positivity of each unmixed reverse-Bessel kernel, or positivity of the Gamma density.
- **New insight:** failure occurs before reflection aggregation and before continuum/prime
  subtraction.  Admission sensitivity is therefore load-bearing at kernel formation itself, not a
  correction that can be imposed on the final scalar source.
- **Status:** formalized in
  `RHTower.XiShiftedAdaptiveMixedGammaKernelPointwiseNoGo`; direct elaboration and targeted module
  build pass. Axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-11 — exact physical-ray counterexample derived; paper proof closed.
- 2026-08-11 — complete linear-amplitude quadratic, positive discriminant, pointwise minimizer,
  universal physical-ray no-go, and rational fixed witness formalized in Lean.
