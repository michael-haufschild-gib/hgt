# Theta-cusp fourth-moment concentration reduction

- **ID:** theta-cusp-fourth-moment-concentration-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-moment reduction
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`

## Statement

Let

\[
m_j=2\int_0^\infty x^{2j}\Phi(x)\,dx,
\qquad \Phi=\thetaCuspFullSource>0.
\]

Then

\[
m_2^2\le m_1m_3.
\]

Consequently the fourth-moment concentration inequality

\[
7m_0m_2\le15m_1^2                                      \tag{C4}
\]

implies

\[
3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2\ge0,
\]

and therefore every linear-polynomial continued prime--Gamma source Hankel test is nonnegative.

## Proof

Cauchy--Schwarz in
`L²((0,∞),dx)` applied to

\[
f(x)=x\sqrt{\Phi(x)},\qquad g(x)=x^3\sqrt{\Phi(x)}
\]

gives `m₂² ≤ m₁m₃`. All required square-integrability follows from the already formalized Schwartz
decay of `Phi`.

The target cubic decomposes exactly as

\[
\begin{aligned}
&3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2\\
&\qquad=3m_0(m_1m_3-m_2^2)+m_2(15m_1^2-7m_0m_2).
\end{aligned}
\]

The first summand is nonnegative by Cauchy--Schwarz and positivity of `m₀`; the second is
nonnegative by `(C4)` and positivity of `m₂`. Normalizing by the positive moment `m₀` gives the
sixth-moment criterion already identified with the first nonconstant source Hankel block. `QED`

## Lean certificate

- `integrableOn_thetaCuspRawMoment`
- `thetaCuspRawEvenMoment_two_sq_le_one_mul_three`
- `thetaCuspRawEvenMoment_nonneg`
- `ThetaCuspFourthMomentConcentration`
- `thetaCusp_raw_cubic_nonneg_of_fourthMomentConcentration`
- `thetaCuspSixthMomentHankelInequality_of_fourthMomentConcentration`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_fourthMomentConcentration`

## Positive top-down chain

```text
explicit theta-cusp fourth-moment concentration (C4)
  -> automatic sixth-moment cumulant inequality
  -> every degree-one prime--Gamma trace-Hankel test is nonnegative.
```

This does not prove `(C4)`, does not settle higher polynomial degrees, and does not prove RH. Its
substantive reduction is that the first open nonconstant source test no longer requires a direct
sixth-order estimate: a fourth/second moment ratio bound suffices.

High-precision evaluation of the actual theta-cusp moments gives

\[
\frac{7m_0m_2}{15m_1^2}\approx1.30251466714643>1.
\]

Accordingly, the conditional implication remains a correct formal theorem, but `(C4)` is
numerically excluded as a producer for the actual source.  The positive replacement is the
two-ratio gate in `theta-cusp-first-hankel-two-ratio-gate.md`, which retains the essential sixth
moment and is numerically oriented correctly.

## Classification

Moment log-convexity by Cauchy--Schwarz and the displayed algebraic decomposition are standard. The
result is useful route compression and a checked Lean theorem, not new scientific knowledge.

## Gates

- [x] all theta-cusp raw moments proved integrable
- [x] moment log-convexity proved in Lean
- [x] fourth-moment concentration reduced to the sixth-moment criterion in Lean
- [x] linear-polynomial source Hankel consequence proved in Lean
- [x] numerically reject `(C4)` as an actual-source producer
- [ ] extend the mechanism to higher source Hankel blocks
