# Theta-cusp sixth-moment Hankel minor

- **ID:** theta-cusp-sixth-moment-hankel-minor
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`
- **Statement:** The first nonconstant two-by-two Hankel minor of the normalized completed prime--Gamma trace is nonnegative because the exact theta-cusp density satisfies a sixth-order raw-moment inequality.

## Object

Let
\[
\Phi(x)=\thetaCuspFullSource(x)>0\qquad(x>0)
\]
and normalize its even moments by
\[
r_{2j}=\frac{2\int_0^\infty x^{2j}\Phi(x)\,dx}
              {2\int_0^\infty\Phi(x)\,dx}.
\]
The denominator is `Xi 0` and is strictly positive by
`PrimeArchThetaFirstMoment.lean`.

## Exact reduction

For
\[
G(t)=-\frac1t\frac{d}{dt}\log\Xi(t)
     =M_0+M_1t^2+M_2t^4+O(t^6),
\]
formal power-series division gives
\[
M_0=r_2,
\qquad
M_1=\frac{r_2^2}{2}-\frac{r_4}{6},
\qquad
M_2=\frac{r_6}{120}-\frac{r_2r_4}{8}+\frac{r_2^3}{4}.
\]
Therefore
\[
\det\begin{pmatrix}M_0&M_1\\M_1&M_2\end{pmatrix}
=\frac{r_2r_6}{120}+\frac{r_2^2r_4}{24}-\frac{r_4^2}{36}.
\]
The positive target is
\[
3r_2r_6+15r_2^2r_4-10r_4^2\ge0.
\]

This statement contains no Xi zeros and no RH hypothesis.

## Attack

Positivity of `Phi` alone is insufficient. For a general positive symmetric density, a sufficiently
small heavy-tail component can make `r₄/r₂²` arbitrarily large and defeat the displayed expression.
Consequently a proof must use a shape constraint special to the theta-cusp source.

The available exact structure is
\[
\Phi=D^2T-\frac14T,
\]
where `T = thetaCuspTailDerivative 0` and `D=d/dx`, together with reflection, Schwartz decay, the
explicit polynomial-Gaussian atom expansion, and strict positivity on `x>0`.

## Candidate moves

1. `[CONJECTURE]` Integration by parts against `x^{2j}` converts `r₂,r₄,r₆` into a finite collection of positive tail moments with coefficients forming a positive quadratic form.
2. `[CONJECTURE]` The probability measure proportional to `Phi(x) dx` on the positive half-line satisfies a sharp kurtosis--sixth-moment inequality stronger than Cauchy--Schwarz because `Phi` is the positive eigenimage of `D²-1/4` on the reflected theta tail.
3. `[CONJECTURE]` The polynomial-Gaussian atom sum is sign-regular of order two after the cusp threshold; its first three even moments then give the required determinant by total positivity.
4. `[CONJECTURE]` The full reflected source satisfies a quantitative curvature--tail inequality stronger than log-concavity. Every individual positive atom is strictly log-concave: with `q=2πn²e^{2x}`, its logarithmic curvature is
   \[
   -2q-\frac{12q}{(q-3)^2}<0.
   \]
   The unresolved step is controlling the variance of the atom logarithmic slopes under summation. Plain log-concavity is not a sufficient theorem schema for the target cumulant inequality. For the normalized symmetric generalized-Gaussian family `f_p(x) ∝ exp(-|x|^p)`, `p ≥ 1`,
   \[
   m_k(p)=\frac{\Gamma((k+1)/p)}{\Gamma(1/p)}.
   \]
   The target expression `E(p)=3m₂m₆+15m₂²m₄-10m₄²` satisfies `E(1)=0` and, using `ψ(n)=H_{n-1}-γ`,
   \[
   E'(1)=-1488<0.
   \]
   Hence `E(p)<0` for all `p>1` sufficiently close to `1`, although every `f_p` is log-concave. A viable shape theorem must therefore exploit a stronger theta-specific condition, such as a uniform curvature floor or an atom-dominance estimate that places the source on the Gaussian-or-lighter side of the cumulant boundary.

## Fourth-moment reduction

Write

\[
m_j=2\int_0^\infty x^{2j}\Phi(x)\,dx.
\]

`[PROVED IN LEAN]` Cauchy--Schwarz gives the automatic Stieltjes log-convexity inequality

\[
m_2^2\le m_1m_3.
\]

The unnormalized target has the exact decomposition

\[
\begin{aligned}
&3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2\\
&\qquad=3m_0(m_1m_3-m_2^2)+m_2(15m_1^2-7m_0m_2).
\end{aligned}
\]

Therefore the source-only fourth-moment concentration bound

\[
7m_0m_2\le15m_1^2                                      \tag{C4}
\]

already implies the sixth-moment Hankel inequality. Equivalently, for the normalized theta-cusp
probability measure,

\[
\frac{r_4}{r_2^2}\le\frac{15}{7}.
\]

This is a genuine reduction of the open analytic input: the sixth raw moment is eliminated, while
the only use of it is the unconditional Cauchy--Schwarz term. The resulting formal chain is

```text
ThetaCuspFourthMomentConcentration
  -> ThetaCuspSixthMomentHankelInequality
  -> every linear-polynomial prime--Gamma source Hankel test is nonnegative.
```

The reduction does not prove `(C4)`, and the linear-polynomial level alone does not imply RH. The
next analytic target is now the explicit fourth/second moment ratio of `thetaCuspFullSource`, not a
sixth-order cumulant inequality.

## Immediate Lean interfaces

- `PrimeArchThetaCumulantMinor.lean` proves differentiation under the theta-cusp integral at every order and
  `iteratedDeriv_Xi_zero_eq_rawEvenMoment`.
- The same module proves the exact formulas for `M₀,M₁,M₂` from the first six derivatives of `Xi` and the
  scaled determinant identity.
- `forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality` proves that the
  displayed source-only inequality is equivalent to nonnegativity of every linear-polynomial prime--Gamma
  trace-Hankel test.

Thus all algebraic and Fourier-transfer interfaces are unconditional in Lean. The original
sixth-moment inequality remains open; the fourth-moment concentration bound is now a sufficient,
strictly lower-order source target.

## Completion condition

- [x] General even derivative/moment identity in Lean
- [x] `M₀,M₁,M₂` cumulant formulas in Lean
- [x] Cauchy--Schwarz log-convexity `m₂² ≤ m₁m₃` in Lean
- [x] Fourth-moment concentration implies the sixth-moment criterion in Lean
- [ ] Prove `7m₀m₂ ≤ 15m₁²` for the explicit theta-cusp source
- [ ] Paper proof of `3r₂r₆ + 15r₂²r₄ - 10r₄² ≥ 0`
- [ ] Lean proof of the first two-by-two source Hankel minor
- [ ] Identify a mechanism that plausibly extends beyond the first minor
