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
- [ ] Lean: the entire-classification input is now **partly formalized**; see below.

## Lean status

The card's decisive input is the Briot--Bouquet classification of transcendental entire solutions of
an autonomous first-order equation `F' = c(F)`.  The **polynomial-coefficient case is now proved
unconditionally** in the formal tree:

| Result | Declaration |
|---|---|
| `deg c ≤ 1`: every entire solution is `d + c·exp(a z)` | `HTGeometry.eq_briotBouquetMap_of_deriv_eq_affine` |
| `deg c ≥ 2`: every entire solution is constant | `HTGeometry.eq_const_of_deriv_eq_comp` |
| a nonconstant solution omits every root of `c` | `HTGeometry.eq_const_of_root_of_deriv_eq_comp` |
| the pure-power case `F' = γ(F − a)^d` | `HTGeometry.eq_const_of_deriv_eq_const_mul_pow` |
| the two-distinct-root case, via the second main theorem | `HTGeometry.not_nonconstant_of_two_roots` |

The route is: a nonconstant solution omits every root of `c`, so `F'` is zero-free; the second main
theorem then applies with both counting terms zero and the ramification term supplied by Jensen,
forcing `T(r,F) = O(log r)`, hence polynomial growth, hence a degree contradiction.  No
complex-analytic ODE flow, no Picard, and no Wiman--Valiron input is used.

Also built, and available to the algebraic case below:

| Result | Declaration |
|---|---|
| Picard's little theorem, unconditional | `HTGeometry.eq_const_of_omits_two` |
| the sharp form: at most one omitted value | `HTGeometry.subsingleton_compl_range_of_nonconstant` |
| Jensen's inequality for `m(r,1/g)`, zeros allowed | `HTGeometry.proximity_inv_le_sub` |
| the Newton exponent dichotomy of the relation | `HTGeometry.exists_deriv_dichotomy_of_relation` |
| exponential type from a linear derivative bound | `HTGeometry.norm_le_mul_exp_of_norm_deriv_le` |

**The algebraic case is now closed in Lean.**  The card's own equation is `x f'(x) = c(f(x))` with
`f` entire, and the card needs only the conclusion *`f` is a polynomial*, which contradicts
transcendence.  Writing the minimal polynomial of `c` as `sum_{k <= m} C_k(Y) W^k`, that reads

```text
sum_{k <= m} C_k(f(z))*(z f'(z))^k = 0 ,
```

and the following is proved unconditionally and axiom-cleanly.

| Result | Declaration |
|---|---|
| **the Euler relation forces a polynomial** | `HTGeometry.eventually_taylorCoeff_eq_zero_of_euler_relation_general` |
| the generic Newton case, via Gol'dberg's central-index bound | `HTGeometry.eventually_taylorCoeff_eq_zero_of_euler_relation` |
| the analytic core, with the central-index bound as input | `HTGeometry.false_of_euler_relation_of_centralIndex_le_pow` |
| the Newton exponent dichotomy of the relation | `HTGeometry.exists_dichotomy_of_relation` |
| a dominant constant term excludes the tame branch | `HTGeometry.exists_not_tame_of_dominant_constant_term` |
| the wild branch bounds `T` by a logarithmic derivative | `HTGeometry.characteristic_le_logDeriv_shift_of_wild` |
| the wild branch forces `T(r,f) = O(log r)` | `HTGeometry.exists_characteristic_le_log_of_wild` |
| the divisor mass against the characteristic at three nearby radii | `HTGeometry.divisorMass_le_characteristic` |
| a zero-free circle in every interval of radii | `HTGeometry.exists_radius_divisor_sphere_eq_zero` |
| Picard's little theorem, unconditional | `HTGeometry.eq_const_of_omits_two` |
| exponential type from a linear derivative bound | `HTGeometry.norm_le_mul_exp_of_norm_deriv_le` |

The proof splits on the largest index `ms` carrying the maximal total degree `deg C_k + k`.  When
`ms >= 1`, Gol'dberg's theorem makes the central index polynomial in the radius, and the Newton
exponent dichotomy — the exponent is a fraction with denominator at most `m`, so it cannot lie
strictly between `1` and `1 + 1/m` — becomes a dichotomy for the central index at the Wiman--Valiron
radii; divergence of the central index kills the tame side, and the wild side bounds the maximum term
by a power of the radius, which a transcendental function cannot obey.  When `ms = 0` the constant
term dominates, the tame side is impossible at every point where `|f|` is large, and integrating the
wild bound over the circle gives `T <= S`, the collapse behind Picard's theorem.

The paper route through the Briot--Bouquet classification is bypassed entirely: no classification of
the solutions is needed, only the growth conclusion.

## Remaining formalization

What is not yet formalized is the card's *differential-algebra* half: the three-jet determinant
`J = v^2(2A_x C - A C_x) - p A(x A_x + A)`, the state field of `(x, v, y) = (g, g', f(g))`, and the
conclusion `ord_DA(f o g) = 3`.  The corpus's composition apparatus — `daRank`, `shadowSet`,
`compSet`, `visibilityField`, `relTrdeg` in `CompositionRelativeVisibility`,
`RelativeVisibilityDegree` and `TwoDefectDecomposition` — carries the first-order inner case; the
order-two inner case of this card is the remaining build.

## Primary references

1. Classical Briot--Bouquet classification, as recorded in A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
2. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
3. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.

