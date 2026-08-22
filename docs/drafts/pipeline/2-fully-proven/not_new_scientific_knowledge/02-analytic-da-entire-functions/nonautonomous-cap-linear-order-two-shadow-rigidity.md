# Nonautonomous cap rigidity for linear order-two inner functions

- **ID:** `nonautonomous-cap-linear-order-two-shadow-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; composition observability
- **Statement:** A genuinely nonautonomous first-order entire outer function composed with a minimal linear order-two entire inner function has exact differential order three.

## Theorem

Let `g` be a transcendental entire function such that

`g''=q(z)g'+p(z)g`,

where `p,q in C(z)`, `p!=0`, and `g,g'` are algebraically independent over `C(z)`. Let `f` be a transcendental entire first-order DA function such that `f` and `f'` are algebraically independent over `C`. Then

`ord_DA(f o g)=3`.

Equivalently, the shadow-recovery defect of this composition is zero.

## State constraint

Put

`x=g`, `v=g'`, `y=f(g)`.

Choose the algebraic derivative branch

`A(x,y)=f'(x).`

The state derivation is

`D x=v`,

`D v=p x+q v`,

`D y=A v`.

Clunie growth makes `y` transcendental over `C(z)<g>`, while `x,v` are algebraically independent by hypothesis. Hence the algebraic state field has transcendence degree three over `C(z)`.

## Three-jet determinant

Set

`C=A_x+A_y A`.

Then

`D y=A v`,

`D^2 y=C v^2+A(px+qv).`

The output-jet Jacobian with respect to `(x,v,y)` reduces, after expanding along the first row, to

`J=det partial(Dy,D^2y)/partial(x,v)`.

A direct calculation gives

`J=v^2(2A_x C-A C_x)-p A(xA_x+A).`

The `q`-terms cancel exactly.

If `J=0`, algebraic independence of `v` over the algebraic closure of `C(z)(x,y)` forces both coefficients to vanish. Since `p!=0` and `A` is not the zero branch,

`xA_x+A=0.`

Thus `xA` is independent of `x`, so there is an algebraic function `c(y)` with

`A(x,y)=c(y)/x.`

Along the analytic solution,

`x f'(x)=c(f(x)).`

## Entire rigidity of the matching equation

Put

`F(t)=f(exp t).`

Then `F` is entire, `2 pi i`-periodic, and satisfies the autonomous first-order ADE

`F'(t)=c(F(t)).`

The Briot--Bouquet classification of transcendental entire autonomous first-order solutions makes `F` a Laurent polynomial in one exponential `exp(a t)`. Periodicity and the fact that `F(t)=f(exp t)` descends to a single-valued entire function at `x=0` force every occurring exponent to be a nonnegative integer power of `x=exp t`. Hence `f` is a polynomial.

This contradicts the assumed transcendence of `f`. Therefore `J!=0`.

The functions

`y,y',y''`

are algebraically independent, while every higher derivative lies in the algebraic three-state field. Consequently

`ord_DA(f o g)=3`.

## Boundary

- The condition `p!=0` is structural. If `p=0`, the linear equation is independent of `g`; the inner function has a primitive defect and belongs to the already classified primitive-compression regime.
- Autonomous outer functions are excluded because their primitive compression is real.
- No positivity, real-axis condition, or Wiman asymptotic is used.

## Parent-theory verdict

The determinant is a three-state nonlinear observability calculation, and the final exclusion uses the classical Briot--Bouquet classification. The combination closes an important boundary case but introduces no mechanism beyond those parents. It is therefore a bridge.

## Gates

- [x] Complete determinant proof.
- [x] Degenerate `p=0` boundary classified.
- [x] Entire matching equation excluded by autonomous first-order classification.
- [x] Parent-theory audit; bridge verdict.
- [ ] Lean deferred: the pure determinant identity is formalizable, but the decisive entire-classification input is absent from the formal tree and the repository's numerical-precertification rule conflicts with the no-computation research mode.

## Primary references

1. Classical Briot--Bouquet classification, as recorded in A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
2. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
3. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.

