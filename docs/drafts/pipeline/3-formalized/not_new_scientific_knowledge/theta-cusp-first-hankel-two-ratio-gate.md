# Theta-cusp first Hankel two-ratio gate

- **ID:** `theta-cusp-first-hankel-two-ratio-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Two source-pure quadratic theta-cusp moment-ratio inequalities imply the first
  nonconstant prime--Gamma Hankel block.

## Goal

Replace the numerically false fourth-moment concentration producer by a viable positive source
gate for the first nonconstant Hankel level.  The replacement separates the cubic obstruction into
two quadratic moment-ratio defects and contains no Xi zero data.

## Theorem

Write

\[
m_j=2\int_0^\infty x^{2j}\Phi(x)\,dx,
\qquad \Phi=\text{thetaCuspFullSource}>0.
\]

Assume

\[
14m_2^2\le 9m_1m_3,                                    \tag{U}
\]

and

\[
16m_0m_2\le45m_1^2.                                    \tag{L}
\]

Then the exact identity

\[
\begin{aligned}
&m_0(9m_1m_3-14m_2^2)+m_2(45m_1^2-16m_0m_2)\\
&\qquad=3\bigl(3m_0m_1m_3+15m_1^2m_2-10m_0m_2^2\bigr)
\end{aligned}
\]

and `m_0,m_2>=0` imply the sixth-moment cumulant inequality.  Consequently,

\[
Q_{\mathrm{prime\text{-}Gamma}}(a+bX)\ge0
\qquad(a,b\in\mathbb R).
\]

## Positive chain

```text
enhanced adjacent ratio (U)
  + relaxed concentration ratio (L)
  -> first nonconstant theta-cumulant Hankel determinant
  -> every real linear-polynomial prime--Gamma Hankel test is nonnegative.
```

High-precision pre-certification gives

```text
m1*m3/m2^2  ~= 1.56826779548 > 14/9,
m0*m2/m1^2  ~= 2.79110285817 < 45/16.
```

This numerical check is not a proof of `(U)` or `(L)`.  It shows that both proposed source
inequalities have the correct orientation for the actual theta-cusp source.  By contrast, the
older condition `7*m0*m2 <= 15*m1^2` has the wrong orientation numerically and cannot produce this
Hankel level.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantRatioSplit.lean`

Principal declarations:

- `ThetaCuspUpperAdjacentRatioSeparation`
- `ThetaCuspRelaxedFourthMomentConcentration`
- `thetaCusp_ratioSplit_exact_identity`
- `thetaCusp_raw_cubic_nonneg_of_ratioSplit`
- `thetaCuspSixthMomentHankelInequality_of_ratioSplit`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit`

## Gates

- [x] source-pure ratio conditions isolated
- [x] exact algebraic decomposition proved
- [x] first nonconstant Hankel consequence formalized
- [x] numerical orientation pre-certified for the actual source
- [ ] prove `(U)` from the explicit theta-cusp density
- [ ] prove `(L)` from the explicit theta-cusp density
- [ ] extend the ratio mechanism to arbitrary Hankel degree
- [ ] full countable prime--Gamma source Hankel cone
