# The zeta Fisher superspace has globally negative curvature and a Poincare critical boundary

- **ID:** `zeta-fisher-superspace-global-negative-curvature`
- **Stage:** 1-in-progress
- **Type:** NOVELTY UNVERIFIED / THEOREM (paper target)
- **Source:** user inner-metric/scale-factor conjecture; `critical-line-fisher-signature-wall`;
  `moonshot-arithmetic-bulk-hyperbolic`; separate from RHTower Routes A--D
- **Statement:** On the physical half-plane `beta>1`, the two-dimensional zeta Fisher metric
  `g=(log zeta)''(beta)(d beta^2+d tau^2)` has strictly negative scalar curvature everywhere and
  converges to the Poincare metric at `beta=1`, with scalar curvature tending to `-2`.

## Goal

Make the claim "the inner scale factor forces the external clock" geometric rather than
metaphorical. The inverse temperature `beta=2 Re(s)` is the radial/scale coordinate and `tau=2 Im(s)`
is Euclidean clock time. The Fisher variance is their common conformal scale factor. The theorem
asks whether the resulting superspace is genuinely hyperbolic globally, not merely asymptotically at
the critical wall.

## Gates

- [x] 0 -> 1 in-progress: metric, curvature formula, Euler cumulant measure, strictness mechanism,
  Poincare limit, and RH interpretation are explicit.
- [ ] 1 -> 2 fully-proven: all differentiations, convergence, curvature identities, strict
  Cauchy--Schwarz, and boundary asymptotics written as a complete proof.
- [ ] 2 -> 3 formalized: Lean proves the positive-measure moment determinant and its strict form;
  formalize the zeta Euler-cumulant specialization as far as the current analytic library permits.
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

## Log

- 2026-07-11 — opened from the scale-factor/external-clock conjecture. Isolated the curvature
  determinant `M_2 M_4-M_3^2`, the positive Euler prime-power measure, strict Cauchy--Schwarz, and
  the Poincare scalar-curvature limit `-2`.
