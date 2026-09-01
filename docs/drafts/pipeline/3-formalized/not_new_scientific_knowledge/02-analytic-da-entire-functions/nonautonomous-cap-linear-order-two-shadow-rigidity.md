# Nonautonomous cap rigidity for linear order-two inner functions

- **ID:** `nonautonomous-cap-linear-order-two-shadow-rigidity`
- **Stage:** 3-formalized
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
- [x] Lean: the whole theorem is formalized, unconditionally and axiom-cleanly; see below.

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

## The differential-algebra half, in Lean

The state field, the three-jet observability determinant and the conclusion `ord_DA(f ∘ g) = 3` are
formalized.  In the `ℂ`-normalisation used throughout the corpus, `trdeg_ℂ = ord_DA + 1`, so the
card's conclusion is `daRank (f ∘ g) = 4`.

| Statement | Lean theorem | Module |
|---|---|---|
| **`ord_DA(f ∘ g) = 3`** (`daRank (f∘g) = 4`) | `daRank_comp_linear_order_two` | `NonautonomousCapLinearOrderTwo` |
| `z, y, y′, y″` algebraically independent | `algebraicIndependent_comp_jets_of_linear_order_two` | `NonautonomousCapLinearOrderTwo` |
| the four states `y, z, x, v` are algebraically independent | `algebraicIndependent_state_four` | `NonautonomousCapLinearOrderTwo` |
| `(f∘g, g)` algebraically independent | `algebraicIndependent_comp_inner_pair` | `NonautonomousCapLinearOrderTwo` |
| `A = f′∘g` algebraic over `ℂ(g, f∘g)` | `isAlgebraic_compJetElem_one_pairField` | `NonautonomousCapLinearOrderTwo` |
| the Euler matching equation forces a polynomial | `exists_polynomial_of_euler_matching` | `EulerMatchingCompositionState` |
| the substituted Euler relation forces a polynomial | `exists_polynomial_of_euler_mero_relation` | `EulerCompositionPolynomialRigidity` |
| finitely many Taylor coefficients means a polynomial | `exists_polynomial_of_eventually_taylorCoeff_eq_zero` | `EulerCompositionPolynomialRigidity` |
| algebraicity over `K[t]` gives a polynomial-coefficient relation | `exists_polynomialCoeff_relation_of_isAlgebraic_adjoin_singleton` | `AdjoinSingletonAlgebraicWitness` |
| coordinate derivations: kernels, stability, algebraic closure | `derivationBase_eq_zero_of_isAlgebraic_adjoin`, `derivationBase_mem_algebraicClosure_adjoin`, `derivationInt_eq_zero_of_isAlgebraic_adjoin` | `DerivationAlgebraicStability` |

### How the Lean proof runs

The four coordinate derivations `∂_y, ∂_z, ∂_x, ∂_v` are produced by prescribing their values on the
algebraically independent family `(f∘g, z, g, g′)` (`exists_derivation_prescribed`).  Because a
derivation vanishing on a subfield kills everything algebraic over it, `∂_z A = ∂_v A = 0` and, since
`p, q` are rational, `∂_x p = ∂_x q = ∂_v p = ∂_v q = 0`.

The ambient derivation is then identified with the coordinate combination
`D = ∂_z + v ∂_x + (qv + px) ∂_v + (Av) ∂_y` on the state field: their difference is a derivation
killing all four generators, hence killing everything algebraic over them.  Applying it to `A` gives
`A₂ = ∂_x A + A ∂_y A` for `A₂ = f″ ∘ g`, so `A₂` is algebraic over `ℂ(g, f∘g)` too.

The output jets are `y`, `A v`, `A₂ v² + A(qv + px)`, and the Jacobian against
`(∂_z, ∂_y, ∂_x, ∂_v)` is block triangular with an identity block on `(z, y)` and lower block
determinant exactly the card's

```text
J = v²(2A₂ ∂_x A − A ∂_x A₂) − p A (x ∂_x A + A),
```

the `q`-terms cancelling as in the paper proof.  Since `v` is transcendental over the algebraic
closure of `ℂ(z, g, f∘g)`, `J = 0` forces `x ∂_x A + A = 0`, i.e. `∂_x(x A) = 0`.  A transcendence
count then makes `x A = g·(f′∘g)` algebraic over `ℂ[f∘g]` — otherwise `g`, which `∂_x` moves, would
add a third degree to a field of transcendence degree two — and a denominator-free witness for that
algebraicity is exactly the Euler relation `∑_k C_k(f)·(z f′)^k = 0`, which makes `f` a polynomial.

The upper bound `daRank (f∘g) ≤ 4` is the observation that every jet of `f∘g` is algebraic over the
four-generator state field, whose relative algebraic closure still has transcendence degree four.

All declarations are axiom-clean (`propext, Classical.choice, Quot.sound`).

## Primary references

1. Classical Briot--Bouquet classification, as recorded in A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
2. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
3. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.

