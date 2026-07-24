# Squared-Xi Log-Derivative Three-Point Orbit Positivity

- **ID:** `squared-xi-logderivative-three-point-orbit-positivity`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / exact protected chamber for a finite RH-disproof test
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOVELTY UNAUDITED] [SIGNIFICANT ROUTE KILL]`
- **Sources:** Riemann's theta-integral representation of `xi`; the genus-zero canonical product
  in the squared centered variable; the critical-strip theorem
- **Statement:** Let

  `g(y)=xi'(1/2+sqrt(y))/(2*sqrt(y)*xi(1/2+sqrt(y)))`

  with the removable center value. Then the matrix

  `G=[[g(0),g(1),g(4)],[g(1),g(0),g(1)],[g(4),g(1),g(0)]]`

  is positive definite unconditionally. In particular `det(G)>0`, so this point triple cannot
  disprove RH.

## 1. A Nonnumerical Low-Height Zero-Free Rectangle

Write

`psi(x)=sum_(n>=1) exp(-pi*n^2*x)`.

Riemann's theta integral is

`xi(s)=1/2+(s*(s-1)/2)*I(s)`,                            (1)

where

`I(s)=integral_[1,infinity]
        psi(x)*(x^(s/2)+x^((1-s)/2))*dx/x`.              (2)

Suppose `0<=Re(s)<=1`. For `x>=1`, both real exponents in (2) are at most `1/2`, so

`|I(s)|<=2*integral_[1,infinity] psi(x)*x^(-1/2) dx`.    (3)

Use only `pi>3`, `n^2>=n`, and `x>=1`:

`psi(x)
 <=sum_(n>=1) exp(-3*n*x)
 <=exp(-3*x)/(1-exp(-3))`.

Since `x^(-1/2)<=1`, equation (3) gives

`|I(s)|<=2/(3*(exp(3)-1))<1/4`.                          (4)

The last strict inequality follows, for example, from the first three positive terms of the
exponential series: `exp(3)>1+3+3^2/2`.

If also `|Im(s)|<=3/2`, then `|s|<2` and `|s-1|<2`. Hence

`|s*(s-1)*I(s)|<1`.

Equation (1) and the reverse triangle inequality imply `xi(s)!=0`. Therefore every Xi zero in the
critical strip satisfies

`|Im(s)|>3/2`.                                           (5)

No zero table or numerical evaluation enters (5).

## 2. Squared-Zero Coordinates

Let `rho=sigma+i*gamma` be a Xi zero with `gamma>0` and put

`delta=sigma-1/2`,
`t=gamma^2-delta^2`,
`q=4*delta^2*gamma^2`.

The critical strip gives `delta^2<=1/4`, while (5) gives `gamma^2>9/4`. Consequently

`t>2`,                                                     (6)

and

`0<=q<=gamma^2=t+delta^2<=t+1/4`.                         (7)

In the squared centered coordinate, the conjugate roots are

`(rho-1/2)^2=-t+2*i*delta*gamma`

and its complex conjugate. Their contribution to the logarithmic derivative is a positive
multiple of

`H_(t,q)(y)=(t+y)/((t+y)^2+q)`.                           (8)

Critical-line roots are included by setting `q=0`.

## 3. Exact Three-Point Algebra

Fix `t>2` and `0<=q<=t+1/4`. Put

`a=H_(t,q)(0)`, `b=H_(t,q)(1)`, `c=H_(t,q)(4)`.

Because `q<t^2`, the function in (8) is positive and strictly decreasing on `[0,infinity)`, so

`a>b>c>0`.                                                 (9)

The determinant factorization is

`det [[a,b,c],[b,a,b],[c,b,a]]
 =(a-c)*(a*(a+c)-2*b^2)`.                                 (10)

All denominators in the second factor are positive. On clearing them,

`a*(a+c)-2*b^2
 =2*P(t,q)/
   ((t^2+q)^2*((t+1)^2+q)^2*((t+4)^2+q))`,               (11)

where

`P(t,q)
 =(t+1)^2*t^2*(t+4)*(5*t+2)
  +(t+1)^2*t*(2-11*t)*q
  -(17*t^2+36*t+16)*q^2-q^3`.                            (12)

For `t>2`, every nonconstant coefficient of (12) as a polynomial in `q` is negative. Therefore
`P(t,q)>=P(t,t+1/4)`. Exact expansion gives

`64*P(t,t+1/4)
 =320*u^6+5184*u^5+33744*u^4+112544*u^3
   +201564*u^2+181620*u+62775`,                           (13)

where `u=t-2>0`. Every coefficient in (13) is positive. Thus `P(t,q)>0`; equations (9)--(11) and
the principal-minor criterion prove that the orbit matrix is positive definite.

## 4. Canonical-Product Assembly

The even centered function `w |-> xi(1/2+w)` becomes a genus-zero entire function of order
`1/2` in `y=w^2`. Its logarithmic derivative has the absolutely convergent expansion

`g(y)=sum_z m_z/(y-z)`,                                   (14)

over its squared zeros. Pair nonreal conjugate squared zeros in (14). Equations (6)--(8) identify
each pair with a positive multiple of one matrix proved positive definite in Section 3; a real
negative squared zero is the `q=0` case.

The matrix `G` is therefore an entrywise convergent sum of positive semidefinite orbit matrices.
At least one orbit is present, and each orbit matrix is positive definite, so `G` itself is
positive definite. This proves `det(G)>0`.

## Consequence

The squared-seam kernel need not be positive definite globally unless RH holds, but the specific
diameter-two point set is protected unconditionally by the critical strip and the elementary
low-height zero-free rectangle. A successful finite-kernel disproof must leave this protected
geometry or use a higher-order source packet.

## Lean formalization

The exact three-point algebra of Section 3 — the self-contained, unconditional heart of the route
kill — is formalized in
`formal/GaloisForLFunctions/RHTower/SquaredXiThreePointOrbitPositivity.lean` (namespace `RHTower`).

- `orbitH t q y = (t + y)/((t + y)² + q)` is the paired-zero response `H_{t,q}(y)`; `orbitP` is the
  numerator polynomial `P(t,q)` of equation (12); `orbitMatrix t q = !![a,b,c; b,a,b; c,b,a]` with
  `a = orbitH t q 0, b = orbitH t q 1, c = orbitH t q 4`.
- `orbitP_pos (ht : 2 < t) (hq0 : 0 ≤ q) (hq : q ≤ t + 1/4) : 0 < orbitP t q` — proved by the exact
  monotone-in-`q` factorization down to `q = t + 1/4` (all coefficients verified by `ring`), where
  `64 · P(t, t+1/4)` equals the strictly positive `u = t − 2` expansion of equation (13).
- `orbitMatrix_posDef (ht : 2 < t) (hq0 : 0 ≤ q) (hq : q ≤ t + 1/4) : Matrix.PosDef (orbitMatrix t q)`
  — the full positive-definiteness. The orbit matrix is `rfl`-equal to
  `HilbertMetric.threePointCorrelationMatrix a b b c`, so positive definiteness is discharged by the
  reusable corpus criterion `HilbertMetric.threePointCorrelationMatrix_posDef_iff` (PosDef ↔ det > 0
  on the nondegenerate chamber). The determinant is `(a − c)(a(a+c) − 2b²)`; the exact identity
  `(a(a+c) − 2b²)·Den = 2 P(t,q)` with `Den > 0` reduces its sign to `orbitP_pos`.
- `orbitMatrix_det_pos … : 0 < (orbitMatrix t q).det` — the headline `det G > 0`.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]` only. `formal lint passed`.
(Sections 1, 2, 4 — the low-height zero-free rectangle, the `(t,q)` chamber conversion from the
theta integral, and the genus-zero canonical-product assembly that supplies `t > 2, 0 ≤ q ≤ t+1/4`
— remain paper analysis feeding the formalized algebraic core.)

## Gates

- [x] Low-height Xi zero-free rectangle proved without zero computation.
- [x] Critical-strip zeros converted to the exact `(t,q)` chamber.
- [x] Per-orbit determinant reduced to a rational polynomial.
- [x] Polynomial positivity proved with exact positive coefficients.
- [x] Principal minors checked.
- [x] Genus-zero canonical-product assembly completed.
- [x] Candidate negative determinant refuted strictly.
- [ ] Independent analytic audit of the theta-integral normalization and canonical-product
  multiplicity bookkeeping.
- [x] Lean formalization of the exact protected-chamber orbit positivity (`RHTower.orbitMatrix_posDef`).

## Log

- 2026-07-17 -- Proved while replacing an unsourced three-point sign conjecture by an exact orbit
  audit. No numerical zero information or floating-point evaluation was used.
- 2026-07-24 -- Formalized Section 3 unconditionally in Lean (`RHTower.orbitMatrix_posDef`,
  `orbitMatrix_det_pos`, `orbitP_pos`), reusing `HilbertMetric.threePointCorrelationMatrix_posDef_iff`
  for the positive-definiteness step; axioms clean, lint passed; promoted to `3-formalized/needs-audit`.
