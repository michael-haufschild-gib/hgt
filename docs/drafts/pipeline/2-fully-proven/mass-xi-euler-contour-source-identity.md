# Mass–Xi Euler-contour source identity

- **ID:** `mass-xi-euler-contour-source-identity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · Section 9.3
- **Statement:** For `a > 1/2`, `Re τ > 0`, and any `c` with `1/2 < c < a`, the mass-shifted Xi trace is exactly the normalized symmetric bottom Euler-line contour of the principal mass test `z ↦ exp (-τ sqrt (z² + a²))` against `XiC'/XiC`.

## Goal

Close the report's stale source-to-trace seam without assuming RH or a vertical bound.  The theorem
must identify the existing folded mass carrier with one analytic even test on the full
multiplicity-exact centered Xi divisor, exhaust that divisor by symmetric rectangles, prove the
vertical edge vanishes, and leave a literal bottom line lying in the absolutely convergent
von-Mangoldt half-plane.  It does not by itself prove the Section 9.3 bound.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `xiMassTraceC_eq_normalizedBottomEulerContour`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Define

```text
M_(a,τ)(z) = exp(-τ * Complex.sqrt(z²+a²)).
```

1. Prove `z²+a²` lies in the principal slit plane throughout `|Im z|<a`; hence `M_(a,τ)` is
   analytic there and even.
2. Prove `Complex.sqrt(xiSpectralPoint(q)²+a²)` equals the custom principal root used by
   `xiMassFamily`; therefore `M_(a,τ)(xiSpectralPoint(q))` is exactly its existing trace term.
3. Extend the rectangle Cauchy/weighted argument-principle stack from entire weights to weights
   analytic on a neighbourhood of the closed rectangle.  Apply it on symmetric rectangles of
   depth `c`, which contain every Xi zero because `|Im xiSpectralPoint|<1/2<c<a`.
4. Establish uniform value and derivative bounds on `R+iy`, `|y|≤c`:

   ```text
   Re sqrt((R+iy)²+a²) > |R|,
   |Im sqrt((R+iy)²+a²)| < |y|,
   |M_(a,τ)(R+iy)| ≤ exp(-Re(τ)|R| + |Im(τ)|c).
   ```

   Insert these bounds into the existing integrated vertical-resolvent near/far decomposition.
   Exponential decay beats its reciprocal-`3/2` and reciprocal-square divisor moments, so a
   cofinal divisor-avoiding sequence of vertical edges vanishes.
5. Evenness of `M_(a,τ)` and oddness of `XiC'/XiC` fold the top edge to the bottom.  Since
   `c>1/2`, the bottom line is the honest von-Mangoldt `LSeries` minus the archimedean logarithmic
   derivative.

## Door passport

- **Source purity:** bottom line uses only von Mangoldt `LSeries` and `archFactor`; no zero bound or
  RH hypothesis.
- **Non-circularity:** contour identity is a value relation.  No boundedness, sign, or zero-free
  conclusion is assumed.
- **Novelty audit:** internal corpus has arbitrary-entire finite contour synthesis and a complete
  sharp-rectangular specialization, but no principal mass-root specialization and no mass trace
  Euler-line identity.  External audit found classical Guinand–Weil ancestry, not this formal
  mass/folded-divisor bridge.
- **Load-bearing remainder:** uniform complex-time boundedness of resulting bottom prime–Gamma
  source remains Section 9.3 open core.

## Proof `[PROVED HERE]`

Write `τ=σ+iu`, with `σ>0`, and put

```text
s_a(z) = Complex.sqrt(z²+a²),
M_(a,τ)(z) = exp(-τ s_a(z)).
```

### 1. Principal branch on the mass strip

Let `z=x+iy` and `|y|<a`.  If `z²+a²` is real, then `2xy=0`.  When `x=0`, its real part is
`a²-y²>0`; when `y=0`, its real part is `x²+a²>0`.  Thus `z²+a²` never meets the nonpositive real
axis.  The principal square root is holomorphic throughout the open strip `|Im z|<a`, so
`M_(a,τ)` is holomorphic there.  Since its argument depends on `z²`, it is even.

Write `s_a(x+iy)=A+iB`.  Principal-root identities give

```text
A²-B² = x²-y²+a²,       AB=xy,       A>0.
```

Also

```text
A² = (|z²+a²| + Re(z²+a²))/2 ≥ Re(z²+a²) > x².
```

Hence `A>|x|`.  From `AB=xy`, either `x=0` and `B=0`, or
`|B|=|xy|/A<|y|`.  Consequently, uniformly for `|y|≤c<a`,

```text
|M_(a,τ)(x+iy)| ≤ exp(-σ|x|+|u|c).                    (1)
```

Differentiating inside the strip gives

```text
s_a'(z)=z/s_a(z),
M_(a,τ)'(z)=-τ z M_(a,τ)(z)/s_a(z).
```

For `R≥2` and `|y|≤c`, `|s_a(R+iy)|>R` and `|R+iy|≤R+c`; therefore

```text
|M_(a,τ)'(R+iy)|
  ≤ |τ|(1+c/2) exp(-σR+|u|c).                         (2)
```

### 2. Exact identification with the folded mass carrier

For every multiplicity copy `q`, `xiPoissonPoint(q)²=xiSpectralPoint(q)²`.  The argument
`xiSpectralPoint(q)²+a²` has positive real part when `a>1/2`.  Both `Complex.sqrt` and the custom
root in `xiMassFamily` square to this argument and have positive real part.  Their difference times
their sum is zero, while the sum cannot vanish because its real part is positive.  They are equal.
Thus

```text
M_(a,τ)(xiSpectralPoint(q)) = (xiMassFamily ha).term τ q.     (3)
```

The already proved mass-family summability for `σ>0` now yields absolute summability of the full
Xi-divisor value family and

```text
sum'_q M_(a,τ)(xiSpectralPoint(q)) = (xiMassFamily ha).traceC τ.  (4)
```

### 3. Finite symmetric contour identity with a local analytic weight

Fix `c` with `1/2<c<a`.  Every centered Xi zero has imaginary part in `(-1/2,1/2)`, hence lies
strictly between the horizontal sides `Im z=±c`.  For any `R>0` avoiding every real coordinate of
the Xi divisor, factor `XiC` on the closed symmetric rectangle

```text
Q_(R,c)=[-R,R] × i[-c,c]
```

into its finite zero product times a nonvanishing analytic cofactor.  The weighted argument
principle only needs the weight analytic on a neighbourhood of `Q_(R,c)`; Step 1 supplies that
neighbourhood.  Analytic multiplicity equals copied-divisor multiplicity, so

```text
∮_(∂Q_(R,c)) M_(a,τ)(z) XiC'(z)/XiC(z) dz
 = 2πi sum_(q in Q_(R,c)) M_(a,τ)(xiSpectralPoint(q)).          (5)
```

This is the local-weight version of the existing entire-weight rectangle theorem; its proof is
identical after replacing `univ` by the intersection of the mass strip and the nonzero-cofactor
neighbourhood.

### 4. Gap-free vertical-edge vanishing

On an avoiding right edge, replace `XiC'/XiC` by the absolutely convergent relative-resolvent
trace.  For `p=xiSpectralPoint(q)` its summand is

```text
K_z(p)=p⁻¹-(p-z)⁻¹=-z/[p(p-z)].
```

Set `E_R=exp(-σR+|u|c)` and

```text
H_(R,p)(y)=-M_(a,τ)(R+iy)(R+iy)/p.
```

Equations (1)--(2) give, on `[-c,c]`,

```text
|H_(R,p)(y)|       ≤ E_R (R+c)/|p|,
|H_(R,p)'(y)|      ≤ C_(a,c,τ) E_R (R+c+1)/|p|.       (6)
```

The scaled vertical Cauchy lemma subtracts `H_(R,p)(Im p)` before integration.  Its remainder
vanishes linearly at the pole height, cancelling the Cauchy singularity uniformly even when the
edge approaches `Re p`.  Therefore, for the near spectrum `|p|≤3(R+c)`,

```text
| integral_(-c)^c M_(a,τ)(R+iy)K_(R+iy)(p) dy |
 ≤ C E_R(R+c+1)/|p|.                                  (7)
```

Since the corpus already proves

```text
sum'_q 1/(|p_q| sqrt|p_q|) < infinity,
```

and `1/|p|≤sqrt(3(R+c))/(|p|sqrt|p|)` on the near spectrum, its total contribution is

```text
O(E_R (R+c+1) sqrt(R+c)) = o(1).                       (8)
```

For `|p|>3(R+c)`, `|p-(R+iy)|≥(2/3)|p|`; hence direct integration gives

```text
| integral_(-c)^c M_(a,τ)(R+iy)K_(R+iy)(p) dy |
 ≤ C_c E_R(R+c)/|p|².                                  (9)
```

The reciprocal-square divisor sum is finite, so the far contribution is also `o(1)`.  Bounds
(7)--(9) provide absolute summability and justify exchanging divisor sum with the edge integral.
Every interval of positive length contains a radius avoiding the countable set of divisor real
coordinates; choose a cofinal avoiding sequence.  Along it the full right vertical edge tends to
zero.  Evenness gives the same for the left edge.

### 5. Exhaustion and Euler-line identity

`M_(a,τ)` is even and `XiC'/XiC` is odd.  The symmetric-contour folding identity turns (5) into
twice the bottom edge plus twice the right edge.  The finite sums in (5) converge to (4), while
Step 4 kills the right edge.

On the bottom line, `c>1/2` places

```text
s=1/2+c+ix
```

in `Re s>1`.  The existing exact bottom law is

```text
XiC'(x-ci)/XiC(x-ci)
 = -i (LSeries(Λ,1/2+c+ix)-archFactor'/archFactor(1/2+c+ix)).   (10)
```

The `LSeries` is uniformly bounded there.  The archimedean logarithmic derivative has logarithmic
growth, and (1) has exponential `x`-decay, so the bottom integrand is absolutely integrable.
Truncated bottom integrals therefore converge to the full integral.  Taking the limit in (5)
proves

```text
(xiMassFamily ha).traceC τ
 = (2πi)⁻¹ 2 integral_(x in R)
     M_(a,τ)(x-ci) XiC'(x-ci)/XiC(x-ci) dx.             (11)
```

All inputs are unconditional.  Equation (10) makes (11) a literal Euler-line prime–archimedean
source identity.  No boundedness or RH-equivalent hypothesis occurs.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active attack

## Log

- 2026-08-04 — created in 0-backlog; promoted immediately to in-progress after internal and external audits.
- 2026-08-04 — branch/folding and gap-free integrated-resolvent attacks succeeded; complete paper proof closed and moved to Stage 2.
