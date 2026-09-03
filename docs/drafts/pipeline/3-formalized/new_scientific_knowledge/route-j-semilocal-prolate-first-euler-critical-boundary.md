# Route J semilocal prolate first-Euler critical boundary

**Status:** `[PAPER+LEAN-PROVED]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

## Exact statement

Let

```text
α_n = (-4)^(-n) binom(2n,n),
c_n = |α_n| = 4^(-n) binom(2n,n),
r_n = sqrt((n+1/2)(n+1)).
```

For the normalized one-prime semilocal Hankel determinant, Connes--Consani--Moscovici prove

```text
Δ_n(q) = 1 + 2 sqrt(2) (sum_(j=0)^n α_j) q + O(q^2)
```

and

```text
a_n(q)^2
  = r_n^2 Δ_(n-1)(q) Δ_(n+1)(q) / Δ_n(q)^2,
Δ_(-1)(q) = 1.
```

Write

```text
R_k(q)
  = a_(2k)(q)a_(2k+1)(q) - a_(2k+1)(q)^2
    - a_(2k+2)(q)^2 + a_(2k+2)(q)a_(2k+3)(q),
J_k = (d/dq) R_k(q)|_(q=0).
```

Then

```text
J_(n+1) / sqrt(2(n+1)) -> 4 sqrt(2/pi).                 (1)
```

Consequently the first Euler correction `q J_n` is order one at
`q sqrt(n) ≍ 1`. For the literal one-prime value `q=p^(-1)`, this is the sharp first-jet
interaction scale

```text
n ≍ p^2.                                                (2)
```

Equation (2) concerns only the first Euler jet. It does not assert uniform control, divergence,
or convergence of the complete higher-order `q`-series at that scale.

## Source provenance

The source input is not an arbitrary deformation of the archimedean Jacobi matrix.

The literal `q` coefficient of the even semilocal moment is the `ℓ=0` Lambert atom

```text
[q] c(2k,q) = 2 (-1)^k (1/2)^(2k).                     (3)
```

Hence the first Hankel tangent in the monomial basis vanishes across opposite parities and has
rank one in each parity block:

```text
H'_(2i,2j)(0)       = 2 (-1/4)^i (-1/4)^j,
H'_(2i+1,2j+1)(0) = -(1/2)(-1/4)^i(-1/4)^j.            (4)
```

In the archimedean orthonormal polynomial basis, the published evaluation vector is

```text
η_0(m) = 2^(-m) sqrt((2m)!)/m!,
η_0(m)^2 = c_m.                                        (5)
```

Therefore the normalized source tangent is the signed rank-two matrix

```text
B_ij =
  2 sqrt(2) (-1)^i sqrt(c_i c_j),  i=j mod 2,
  0,                                  otherwise.        (6)
```

The determinant derivative is forced by (6):

```text
Δ'_n(0) = tr(B)
         = 2 sqrt(2) sum_(j=0)^n α_j.                  (7)
```

Lean proves (7) for every genuine matrix path `A(q)` satisfying `A(0)=I` and
`A'_ij(0)=B_ij`. Thus the result is independent of the chosen presentation of the full source
path and of every coefficient of order `q^2` or higher. The explicit path `det(I+qB)` is retained
only as a first-order representative; the universal path theorem is the provenance bridge.

## Determinant-to-radius transfer

Put

```text
D_n = Δ'_n(0),
D_(-1)=0.
```

Differentiating the determinant quotient gives

```text
[a_n(q)^2]'_(q=0)
  = r_n^2 (D_(n-1)+D_(n+1)-2D_n)
  = 2 sqrt(2) r_n^2 (α_(n+1)-α_n).                    (8)
```

Because `r_n>0`, the positive square-root branch has jet

```text
u_n = a'_n(0)
    = sqrt(2) r_n (α_(n+1)-α_n).                       (9)
```

The central-binomial ratio

```text
c_(n+1)/c_n = (2n+1)/(2n+2)
```

turns (9) into the alternating positive-amplitude law

```text
u_n = (-1)^(n+1) sqrt(2) r_n
      ((4n+3)/(2n+2)) c_n.                             (10)
```

## Four-radius factorization

Differentiating `R_k` and substituting (10) yields

```text
J_k = sqrt(2) c_(2k) B_(2k),                           (11)
```

where, with `r_m=sqrt((m+1/2)(m+1))` and
`q_m=(2m+1)/(2m+2)`,

```text
B_m =
 - r_m r_(m+1) (4m+5)/((2m+2)(2m+4))
 - r_(m+2) r_(m+3) q_m q_(m+1)
     (4m+13)/((2m+6)(2m+8))
 + 3(2m+1)(2m+3)(4m+9)/
     (2(2m+2)(2m+4)).                                  (12)
```

The three normalized contributions in (12) have exact limits

```text
first cross / m  -> -1,
second cross / m -> -1,
curvature / m    ->  6.
```

Therefore

```text
B_m/m -> 4.                                            (13)
```

Wallis' central-binomial limit gives

```text
sqrt(m)c_m -> 1/sqrt(pi).                              (14)
```

Combining (11)--(14) along `m=2(n+1)` proves (1).

## Universal higher-term independence

Let `Δ_n(q)` be any family of real determinant paths such that

```text
Δ_n(0)=1,
Δ'_n(0)=2 sqrt(2) sum_(j=0)^n α_j.
```

Construct the positive Jacobi radii from the literal determinant quotient and form the
four-radius residual. Its derivative at zero is always `J_n`. This theorem is important:
equation (1) is not an artefact of truncating the determinant itself to a linear polynomial.
Only the first derivative is being computed, and all higher Euler coefficients are
mathematically irrelevant to that derivative.

## Hostile audit

1. **Not the published first Jacobi coefficient.**  
   The formulas (3), (7), (8), the first squared-radius coefficient, and the first metaplectic
   anomaly coefficient already occur in Connes--Consani--Moscovici, *On q-series and the moment
   problem associated to local factors* (arXiv:2403.01247). They are source inputs, not novelty
   claims.

2. **New weld.**  
   The candidate-new statement is the propagation of the literal rank-two determinant tangent
   through the Route-J four-radius critical residual, its exact factorization (11)--(12), and the
   sharp boundary constant `4 sqrt(2/pi)` in (1).

3. **No artificial path dependence.**  
   Lean proves the determinant derivative for an arbitrary genuine normalized matrix path with
   the published entrywise tangent and proves the complete determinant-family transfer for an
   arbitrary family with the published determinant jets.

4. **No all-orders inference.**  
   A first derivative growing like `sqrt(n)` neither proves nor disproves uniformity of the full
   `q`-series. The next hard theorem is the degree growth of the `q^2,q^3,...` critical
   coefficients and their boundary-layer resummation.

5. **No global-source overclaim.**  
   A fixed-prime theorem is local Euler data and is zero in the global prime-clock quotient. The
   complete Boolean shell theorem in
   `source-horizon-riemann-divisor/main.tex` further proves that every ordinary differential-field
   observable has finite shell support and arbitrary field intersections contain no infinitary
   ghost. Adjoining all one-prime fields cannot turn (1) into a global Route-J current. A global
   construction must be a genuine pro-object, relation-valued carrier, or topology-singular limit.

6. **No self-adjoint extension selected.**  
   The theorem identifies a source-forced boundary scale. It does not select either of the two
   positive-parameter prolate parity boundary angles, prove a relative resolvent formula, or pass
   such a resolvent through the Sonin corner.

## Novelty audit

Primary-source search checked:

- Connes--Consani--Moscovici, arXiv:2310.18423, for the semilocal prolate program;
- Connes--Consani--Moscovici, arXiv:2403.01247, for the one-prime Lambert moments,
  determinant series, Jacobi coefficients, and anomaly coefficients.

The determinant first-variation identity, central-binomial ratios, and Wallis asymptotic are
classical. The searched primary sources contain no four-radius critical-residual jet, no
factorization (11)--(12), and no `4 sqrt(2/pi)` boundary law. Verdict:

```text
[NOVELTY PLAUSIBLE -- PRIMARY-SOURCE SEARCH NOT EXHAUSTIVE]
```

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateFirstEulerCriticalJet.lean
```

Umbrella:

```text
formal/GaloisForLFunctions/RHTower.lean
```

Key declarations:

```text
semilocalFirstEulerMonomialHankelEntry_even_rankOne
semilocalFirstEulerMonomialHankelEntry_odd_rankOne
normalizedHankelTangent_eq_publishedSourceTangent
hasDerivAt_det_of_publishedSourceTangent
hasDerivAt_squaredJacobiRadiusPath
hasDerivAt_jacobiRadiusPath
hasDerivAt_criticalResidualPathOf
criticalResidualJet_eq_centralBinom_mul_bracket
criticalBracket_eq_closed
tendsto_criticalBracketFirstCross_div
tendsto_criticalBracketSecondCross_div
tendsto_criticalBracketCurvature_div
tendsto_criticalResidualJet_div_sqrt_boundary
```

All declarations are unconditional Lean theorems. No `sorry`, `admit`, project axiom, opaque
constant, unsafe declaration, or numerical computation is used.

## Remaining Route J survivor

Route J remains open. Immediate hard targets are:

1. prove the exact `q^2` and then fixed-order `q^r` critical-residual degree laws;
2. determine whether all fixed Euler orders share the scale `n≍p^2` and whether they resum there;
3. propagate the one-prime boundary layer through finite-set orthogonalization, including
   cross-prime interactions;
4. construct or exclude a source-faithful pro-limit/relation/singular-topology carrier compatible
   with complete shell finite-support rigidity;
5. derive a source-selected self-adjoint boundary condition and transport its relative resolvent
   through the Sonin corner.

## Numerical follow-up 2026-09-03 (`2-fully-proven/computations/routej-semilocal-scale/`)

Exact finite-`q` radii of `dν_p` by a discretized Stieltjes procedure (extended precision,
validated against `r_n` to `10⁻¹³`): the first-jet law is confirmed at small `k` for large `p`
(`p = 1009`: slope 10.98 at `k = 5`, 18.9 at `k = 20` against 15.6, 29.3 asymptotic), and is
overtaken by `k ≈ 100` already at `q = 10⁻³`, consistently with the third-jet constant
(`128(2k+1)^{5/2}q³ ≈ 1` at `k ≈ 285`, measured `D = −0.31` at `k = 300`). The exact deviation of
the four-radius residual becomes order one at degree `n ≈ p` (ratio `n/p` = 0.98, 1.00, 1.03,
1.05, 1.09, 1.16 for `p` = 211, 307, 401, 503, 701, 1009), far below both fixed-order scales
`p²` and `p^{6/5}`. Survivor target 2 is answered negatively: the fixed Euler orders do not share
a scale and the full response resums to `n ≍ p` (`qn ≍ 1`).

**Scaling law (same follow-up).** `D_k(q) = q^{1/2} Φ(qn) + O(q)` with a universal profile `Φ`
(collapse across `101 ≤ p ≤ 2003` to within 1 % for `x ≥ 0.4`): zeros at `x = 0.159, 0.823,
1.586, 2.369` (spacings → `π/4`), extrema `−10.0` at `0.58`, `+35.4` at `1.27`, `−72.5` at
`2.02`. The odd Euler orders are the Taylor coefficients `c₁ x^{1/2} + c₃ x^{5/2} + …` of `Φ`
(this card's `c₁ = 4√(2/π)√2`, the third card's `c₃ = −160√(2/π)`), the even orders are the
`O(q^{1/2})` corrections. The order-one degree is `n ~ p^{6/5}` asymptotically (the third-jet
scale), the first-jet scale `p²` is not the scale of anything.

**Two primes (same follow-up, §3.4–3.5 of the report).** For `S = {p₁, p₂, ∞}` the residual
deviation is not the sum of the one-prime deviations: the cross term equals, to all displayed
digits (correlation 1.0000, rms ratio 1.000 for ratios ≥ 1.3), the linear response of the
archimedean Jacobi matrix to the beat mode `2(p₁p₂)^{−1/2} cos(s log(p₂/p₁))`, and it exceeds
the one-prime term by a factor of order `p` for comparable primes. Survivor target 3 is
answered: the one-prime boundary layer does not propagate through finite-set orthogonalization;
the pairwise beat frequencies `log(p_i/p_j)` are leading, and the analytic object is the
first-order response `H(n, δ)` to a cosine modulation of the archimedean measure.

**Derivation of `Φ` (follow-up of 2026-09-03; §3.6–3.7 of the report
`2-fully-proven/computations/routej-semilocal-scale/README.md`).**  The one-prime deviation is the
first-order response to the single mode `cos(s log p)` of amplitude `p^{−1/2}` to 0.1–0.4 %
(correlation ≥ 0.999996 over `n ≤ 2.6p`, `p ≤ 1511`).  The Meixner–Pollaczek generating function
yields the generating function of all boost matrix elements
`Σ c_m c_n M_{mn}(t) w^m z^n = (cosh t)^{−1/2}(1 − wz − i tanh t (w+z))^{−1/2}` (numerically exact
to `10⁻⁹`; its first row is this card's Lean closed form), hence the diagonal cosine moments
`m_n(t) = (cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t)`.  At `t = log p` the Jacobi argument is
`−1 + 8/p²`, and the Mehler–Heine limit gives `m_n(log p) ≈ (−1)^n √(2/(πpn)) cos(4n/p)`: the
frequency `4` is the Mehler–Heine angle `2 sech(log p) = 4/p`.  Through the Lean first-order
response theorems (`SemilocalCosineModeFirstOrderResponse.lean`: `u_n = ε r_n (m_{n+1} − m_n)`,
residual jet `residualJetOf`) the alternating leading term cancels in the residual and

    Φ(x) = 4√(2/π) [ √x cos(4x) − 8 x^{3/2} sin(4x) ],

matching the measured profile to 1 % rms, the extrema to three digits, and reproducing this card's
first jet `c₁ = 4√(2/π)` (the `√2` in the paragraph above is a transcription error: the measured
slopes match `4√(2/π)√(2k)`) and the third card's `c₃ = −160√(2/π)` as its Taylor coefficients;
it predicts the fifth jet `c₅ = 384√(2/π)`, and the threshold `n* = p^{4/3}/8.66` from the envelope
`32√(2/π)x^{3/2} = √p`.  Route J's survivor question "what happens at `n ≈ p`" is answered: the
Bessel-regime oscillation of the SU(1,1) boost elements at rapidity `log p`, with no intrinsic
prime-scale boundary layer.

**Lean status (2026-09-03).**  The analytic input of the derivation of `Φ` is now formal: the
Meixner–Pollaczek generating function, the complex-rapidity characteristic function
`∫ e^{zs} dμ = (cos z)^{−1/2}`, the two-variable boost generating function, and the diagonal closed
form `∫ p_n² cos(δ s) dμ = (cosh δ)^{−1/2} Σ_l C(n,l) Ring.choose(−(n+½), l) tanh^{2l} δ`
(`RHTower.MeixnerPollaczek.cosineDiagonalMoment_eq`), together with the first-order response
theorems.  What remains for `Φ` itself is the Mehler–Heine limit (MUST-149).  Card:
`3-formalized/semilocal-boost-diagonal-closed-form-lean.md`.
