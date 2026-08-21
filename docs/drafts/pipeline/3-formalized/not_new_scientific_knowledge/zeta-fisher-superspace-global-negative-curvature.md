# The zeta Fisher superspace has globally negative curvature and a Poincare critical boundary

- **ID:** `zeta-fisher-superspace-global-negative-curvature`
- **Stage:** 3-formalized
- **Type:** THEOREM / NOVELTY DEFERRED
- **Source:** user inner-metric/scale-factor conjecture; `critical-line-fisher-signature-wall`;
  `moonshot-arithmetic-bulk-hyperbolic`; separate from RHTower Routes A--D
- **Statement:** On the physical half-plane `beta>1`, the two-dimensional zeta Fisher metric
  `g=(log zeta)''(beta)(d beta^2+d tau^2)` has strictly negative scalar curvature everywhere and
  converges to the Poincare metric at `beta=1`, with scalar curvature tending to `-2`.
- **Lean:** `formal/GaloisForLFunctions/RHTower/FisherCurvatureMoment.lean`;
  `formal/GaloisForLFunctions/RHTower/EulerFisherCurvature.lean`;
  `formal/GaloisForLFunctions/RHTower/EulerFisherPoincareBoundary.lean`

## Goal

Make the claim "the inner scale factor forces the external clock" geometric rather than
metaphorical. The inverse temperature `beta=2 Re(s)` is the radial/scale coordinate and `tau=2 Im(s)`
is Euclidean clock time. The Fisher variance is their common conformal scale factor. The theorem
asks whether the resulting superspace is genuinely hyperbolic globally, not merely asymptotically at
the critical wall.

## Gates

- [x] 0 -> 1 in-progress: metric, curvature formula, Euler cumulant measure, strictness mechanism,
  Poincare limit, and RH interpretation are explicit.
- [x] 1 -> 2 fully-proven: all differentiations, convergence, curvature identities, strict
  Cauchy--Schwarz, and boundary asymptotics written as a complete proof.
- [x] 2 -> 3 formalized: Lean proves the finite and infinite pairwise-dispersion identities,
  absolute convergence of the actual Euler prime-power moments, strict determinant positivity,
  and negativity of the scalar-curvature expression, the identification of this expression with
  the Liouville scalar curvature of the conformal metric, and the Poincare asymptotic.
- [ ] 3 -> 4 publication-ready: pass exact information-geometry, thermodynamic-geometry,
  number-theory, and AdS2 literature audits.

## 1. Metric and prime-power cumulants

For `beta>1`, put

```text
F(beta) = log zeta(beta)
        = sum_p sum_(k>=1) p^(-k beta)/k.
```

For `j>=1`, define

```text
M_j(beta)
  = sum_p sum_(k>=1) (k log p)^j p^(-k beta)/k.
```

Absolute and locally uniform convergence on `beta>1` permits termwise differentiation, giving

```text
(-1)^j F^(j)(beta) = M_j(beta).                       (1)
```

In particular, the Fisher scale factor is

```text
G(beta)=F''(beta)=M_2(beta)>0.                        (2)
```

For completeness, fix a compact interval `beta>=1+epsilon`. After `j` differentiations, the
absolute value of the `(p,k)` term is

```text
(k log p)^j p^(-k beta)/k
  <= (log(p^k))^j (p^k)^(-(1+epsilon)).              (1a)
```

The map `(p,k)->p^k` is injective for prime `p` and positive `k`. The right side is therefore a
subseries of

```text
sum_(n>=1) (log n)^j n^(-(1+epsilon)),               (1b)
```

which converges by comparison with a `p`-series. The same bound is uniform on the interval, so the
Weierstrass test justifies termwise differentiation through order four. Lean proves the stronger
absolute-summability statement for every natural `j` using the abscissa of absolute convergence of
the logarithmically differentiated zeta Dirichlet series.

On the two-dimensional temperature--clock superspace use

```text
ds^2 = G(beta) (d beta^2 + d tau^2).                 (3)
```

In thermofield coordinates `s=beta/2+i tau/2`, `(3)` is, up to the fixed coordinate factor, the
Fubini--Study metric of the prime-power Euler coherent state. Wick rotation of `tau` produces the
Lorentzian Wheeler--DeWitt/AdS2 signature.

## 2. Curvature formula `[PROOF CORE]`

For a conformal surface metric `G(x)(dx^2+dy^2)`, the scalar curvature is

```text
Scal = -(G G''-(G')^2)/G^3.
```

Using `(1)`--`(2)`,

```text
G'=F'''=-M_3,
G''=F''''=M_4,

Scal(beta)
  = -(M_2 M_4-M_3^2)/M_2^3.                         (4)
```

## 3. Strict negative curvature `[PROOF CORE]`

Let the prime-power energy be

```text
x_(p,k)=k log p > 0
```

and give it positive weight

```text
w_(p,k)=p^(-k beta)/k.
```

Then `M_j=sum w x^j`. Cauchy--Schwarz applied to

```text
u_(p,k)=sqrt(w_(p,k)) x_(p,k),
v_(p,k)=sqrt(w_(p,k)) x_(p,k)^2
```

gives

```text
M_3^2 <= M_2 M_4.                                   (5)
```

Equality would force `v=c u` on the positive support, hence every `x_(p,k)` would be the same.
But `log 2` and `log 3` are distinct support energies. Therefore

```text
M_3^2 < M_2 M_4,
Scal(beta)<0                                         (6)
```

for every `beta>1`. The negative curvature is forced by the non-monochromatic prime-power energy
spectrum; it is not an asymptotic artifact of the pole.

## 4. Poincare boundary `[PROOF CORE]`

Let `delta=beta-1`. The Laurent expansion at the simple pole gives

```text
F(beta)=-log delta+h(delta)
```

with `h` analytic near `0`. Hence

```text
G=delta^(-2)+O(1),
G'=-2 delta^(-3)+O(1),
G''=6 delta^(-4)+O(1).
```

Substitution into `(4)` yields

```text
Scal(beta) -> -2                                    (7)
```

as `beta->1+`. Moreover

```text
ds^2 ~ (d beta^2+d tau^2)/(beta-1)^2,
```

the Poincare half-plane metric of Gaussian curvature `-1` and scalar curvature `-2`. Thus
`beta=1`, equivalently `Re(s)=1/2`, is the conformal boundary of an asymptotically hyperbolic
information superspace. The scale factor `a=sqrt(G)~1/(beta-1)` forces `tau` to become boundary time.

## 5. RH meaning and honesty

`[PROVED GEOMETRIC REFRAME, NOT RH]` Under `beta=2 Re(s)`, RH says every completed-zeta zero lies
on this conformal boundary. A hypothetical right-half off-line zero would lie in the negatively
curved positive-metric bulk, while its FE reflection lies beyond the Fisher/KMS positivity domain.

The curvature theorem does not itself prevent bulk zeros. It supplies a genuine geometric invariant
and identifies the exact superspace in which a future source constraint would have to exclude them.
Any claimed RH mechanism must involve how the completed Euler--Gamma zero divisor couples to this
curvature; negative curvature alone is RH-blind.

## 6. Preliminary novelty pressure test

- The Poincare asymptotic was already conjecturally recorded in
  `moonshot-arithmetic-bulk-hyperbolic`; it is not new by itself.
- The new candidate content is the **global** strict sign `(6)`, derived from the Euler prime-power
  cumulant measure, together with the exact curvature identity `(4)` and boundary value `(7)`.
- After project vocabulary is erased, the mechanism is log-convexity of positive-measure moments
  inserted into the curvature of a one-parameter Hessian/conformal metric. This may be a known
  thermodynamic-geometry theorem. Scientific-novelty promotion is withheld pending a serious
  parent-theory and literature audit after the proof is complete.

## 7. Bitter-end RH verdict

The geometric theorem does not extend to an RH proof. The terminal obstruction is proved in
`prime-fisher-superspace-unimodular-phase-blindness`: fixed unimodular Euler phases leave the entire
Born/Fisher geometry unchanged, while the scalar Helson-zeta divisor can be prescribed away from
the critical line. Thus the scale factor controls normalized magnitudes but not the phase-sensitive
distributional scalar section. A new completed Euler--Gamma no-bulk-source constraint is required.

## Log

- 2026-07-11 — opened from the scale-factor/external-clock conjecture. Isolated the curvature
  determinant `M_2 M_4-M_3^2`, the positive Euler prime-power measure, strict Cauchy--Schwarz, and
  the Poincare scalar-curvature limit `-2`.
- 2026-07-11 — completed the paper proof. Lean proved the infinite dispersion identity, actual
  Euler prime-power absolute convergence, strict determinant positivity, and negative curvature
  expression for every `beta>1`. The metric-only RH route was then terminated by unimodular-phase
  blindness.

## Lean formalization — COMPLETE

New module: `formal/GaloisForLFunctions/RHTower/EulerFisherPoincareBoundary.lean`
(namespace `RHTower`), wired into `GaloisForLFunctions.RHTower`.  It closes the two gaps the
`2 -> 3` gate recorded.  `#print axioms` on every capstone returns exactly
`[propext, Classical.choice, Quot.sound]`.

### Equation (1): termwise differentiation

`hasDerivAt_eulerMoment j` proves `M_j' = -M_{j+1}` on `beta > 1` by
`hasDerivAt_tsum_of_isPreconnected` over `Ioi c` with `1 < c < beta`, dominated by
`summable_eulerPrimePowerEnergy_pow_rpow`.  Since `M_0 = F`, this gives
`deriv_eulerLogMoment` and `deriv_deriv_eulerLogMoment` (`F'' = M_2`), the card's `(1)`--`(2)`.

### Equation (4): the curvature identification

`conformalScalarCurvature G beta := -(deriv (deriv (log o G)) beta) / G beta` is the Liouville
form of the scalar curvature of the two-dimensional conformal metric `G (dbeta^2 + dtau^2)` for a
scale factor depending on the first coordinate only.  Mathlib carries Riemannian metrics but no
curvature tensor, so the Liouville formula is the definition; the classical content is the
identity

- `conformalScalarCurvature_eq_of_hasDerivAt`:
  `conformalScalarCurvature G beta = -(G G'' - (G')^2)/G^3`,

and its specialization

- `conformalScalarCurvature_eulerMoment_two`:
  `conformalScalarCurvature M_2 beta = eulerFisherScalarCurvature beta` for every `beta > 1`,

which is exactly `(4)` once `G = M_2`, `G' = -M_3`, `G'' = M_4` are supplied by `(1)`.

### Equations (7): the Poincare boundary

- `zetaPoleUnit s = (s-1)(zeta(s) - 1/((s-1) Gamma_R(s))) + Gamma_R(s)^{-1}` agrees with
  `(s-1) zeta(s)` off `s = 1`, equals `1` at `s = 1`, and is entire.  Differentiability at the
  pole is mathlib's `differentiableAt_hurwitzZetaEven_sub_one_div` at `a = 0`.
- `canonicalEulerLogZeta_ofReal`: the corpus Euler logarithm at a real point is the real zeroth
  moment `M_0`, by reindexing the Dirichlet series along the injection
  `(p, k) |-> p^{k+1}` whose range contains the support of the coefficient sequence.  Hence
  `riemannZeta_ofReal_eq_exp_eulerLogMoment`: `zeta(beta) = exp(M_0(beta))`, real and positive.
- `eulerLogRegular beta = Re log zetaPoleUnit(beta)` is real-analytic at `1`
  (`analyticAt_eulerLogRegular`) and satisfies `eulerLogRegular = log(beta-1) + M_0(beta)`
  for `beta > 1` (`eulerLogRegular_eq`).
- Four applications of derivative uniqueness on the window `Ioo 1 (1+eps)` give the exact
  singular splittings
  `M_1 = (beta-1)^{-1} - R_1`, `M_2 = (beta-1)^{-2} + R_2`,
  `M_3 = 2(beta-1)^{-3} - R_3`, `M_4 = 6(beta-1)^{-4} + R_4`
  with `R_k` the `k`-th derivative of the analytic regular part
  (`eulerMoment_one_eq_of_window` ... `eulerMoment_four_eq_of_window`).
- Clearing `delta^{-6}` turns the curvature into `-poincareNum/poincareDen`, whose limits are
  `2` and `1`.  Hence
  `tendsto_eulerFisherScalarCurvature_nhdsGT_one : Tendsto Scal (nhdsWithin 1 (Ioi 1)) (nhds (-2))`,
  the card's `(7)`.

### Capstone

`zeta_fisher_superspace_negative_curvature_poincare_boundary` bundles: `F'' = M_2`, the curvature
identification, strict negativity for every `beta > 1` (from the existing
`eulerFisherScalarCurvature_neg`), and the Poincare boundary value `-2`.

### Reusable infrastructure added

- `conformalScalarCurvature` and `conformalScalarCurvature_eq_of_hasDerivAt` — the Liouville
  curvature of any positive conformal scale factor of one variable.
- `hasDerivAt_eulerMoment` — termwise differentiation of an arbitrary Euler prime-power moment.
- `zetaPoleUnit`, `differentiable_zetaPoleUnit`, `zetaPoleLog`, `analyticAt_zetaPoleLog` — the
  entire unit of the zeta pole and its analytic logarithm at `s = 1`.
- `canonicalEulerLogZeta_ofReal` and `riemannZeta_ofReal_eq_exp_eulerLogMoment` — the real Euler
  logarithm of zeta, and positivity/reality of `zeta` on `(1, infinity)`.
