# Newton-corner unit cost for nonautonomous first-order composition

- **ID:** `newton-corner-nonautonomous-composition-unit-cost`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED]`
- **Lane:** general hypertranscendence; nonautonomous first-order DA boundary
- **Statement:** A first-order input/output derivative constraint whose output-dominant Newton branch is linear forces every composition layer to contribute exactly one unit of minimal ADE order.

## Input/output constraint

Let `f` be a transcendental entire solution of a first-order ADE. Write the independent input as `U`, the output as `V=f(U)`, and the derivative as `W=f'(U)`. After choosing an irreducible component, `W` is algebraic over `C(U,V)`.

Call a branch **output-linear at the Newton corner** if, in the Puiseux field at `V=infinity` over the algebraic closure of `C(U)`,

`W=lambda V(1+lower powers of V)`, with `lambda!=0`.

Equivalently, its initial form for the nested order `V >> U` is `lambda V`. This definition concerns the static algebraic input/output constraint; it does not choose an orbit or an evolution parameter.

## Theorem

`[BRIDGE] [PROVED HERE]` Let `f_1,...,f_n` be transcendental entire functions. Suppose:

1. each `f_k` satisfies a first-order ADE and has an output-linear derivative branch `B_k(U,V)`;
2. `f_k` has finite order;
3. for the composition states

   `F_k=f_k o ... o f_1`,

   the analytic derivative selects the stated algebraic branch.

Then

`ord_DA(F_n)=n`.

If every `f_k` also has positive lower order, then

`cd_+(F_n)=n`.

## Proof

### 1. State independence

`[PROVED HERE]` `F_1,...,F_n` are algebraically independent over `C(z)`.

Clunie's composition-growth theorem gives successive separation

`T(r,F_k)/T(r,F_(k-1)) -> infinity`.

If `F_k` were algebraic over `C(z,F_1,...,F_(k-1))`, the Nevanlinna root estimate applied to its polynomial relation would give

`T(r,F_k)=O(log r + sum_(j<k)T(r,F_j))`,

contradicting the separation.

### 2. Algebraic state constraint

Set `X_0=z` and let `X_1,...,X_n` be independent state coordinates. Adjoin algebraic elements

`b_k=B_k(X_(k-1),X_k)`.

On this finite algebraic extension define

`delta X_0=1`,

`delta X_k=b_k delta X_(k-1)=product_(j=1)^k b_j`.

The field is stable under `delta`: differentiating the minimal polynomial of each `b_k` expresses `delta b_k` algebraically in the same field.

### 3. Filtered observability lemma

`[PROVED HERE]` Under the nested Puiseux order

`X_n >> X_(n-1) >> ... >> X_1 >> X_0`,

the observability Jacobian

`J_n=det partial(X_n,delta X_n,...,delta^(n-1)X_n)/partial(X_1,...,X_n)`

is nonzero.

Indeed, `b_k` has initial form `lambda_k X_k`. Every entry of `J_n` is a finite algebraic expression in the `b_k` and their coordinate derivatives. Choose successive rational weights for the `X_k` so rapidly increasing that they refine the nested Puiseux order and separate all finitely many monomials occurring in `J_n`. Replacing one `b_k` by a lower Puiseux term, or differentiating such a lower term, strictly lowers the resulting weight.

The initial part of `J_n` is therefore the initial part of the Jacobian for

`delta_0 X_k=product_(j=1)^k lambda_j X_j`.

That affine-exponential product cascade is observable: after passing to its logarithmic velocities, the triangular Jacobian induction has base determinant `1`, and the leading coefficient in the newest velocity is the preceding determinant times a nonzero scalar. Hence its Jacobian has a nonzero initial monomial. The same monomial survives in `J_n`, proving `J_n!=0`.

### 4. Exact differential order

Substitute `X_k=F_k` and `b_k=f_k'(F_(k-1))`. State independence makes this substitution injective over `C(z)`. The nonzero Jacobian shows that

`F_n,F_n',...,F_n^(n-1)`

are algebraically independent over `C(z)`.

All derivatives lie in the finite algebraic state field of transcendence degree `n`, so

`F_n,F_n',...,F_n^(n)`

are algebraically dependent. Therefore `ord_DA(F_n)=n`.

### 5. Exact positive composition depth

The displayed factorization gives `cd_+(F_n)>=n` when the factors have positive lower order. Finite order of every factor gives an iterated maximum-modulus upper bound of exponential height at most `n-1`. The Polya growth-depth lower bound rules out `n+1` positive-lower-order factors. Hence `cd_+(F_n)=n`.

## Nonautonomous examples

`[PROVED HERE]` Let

`f(z)=L(exp(az))+P(z)`,

where `a!=0`, `P` is a polynomial, and `L` is a nonconstant Laurent polynomial. Put `t=exp(aU)`. Then

`V-P(U)=L(t)`,

`W=a t L'(t)+P'(U)`.

The first relation makes `t` algebraic over `C(U,V)`. On a branch over `V=infinity`, the second gives `W~lambda V` with `lambda!=0`. Thus every compositional iterate satisfies

`ord_DA(f^[n])=cd_+(f^[n])=n`.

The smallest genuinely nonautonomous example is

`f(z)=exp z+z`,

whose exact derivative constraint is

`W=V-U+1`.

Its output-dominant initial form is `W=V`, so `ord_DA(f^[n])=n`.

## Exact remaining obstruction

For a general first-order DA cascade, define the **algebraic observability defect**

`def_obs(F_n)=n-trdeg_(C(z)) C(z)(F_n,F_n',F_n'',...)`.

`[BRIDGE]` Standard differential-algebraic observability identifies this number with the dimension of the generic algebraic unobservable foliation of the state constraint.

`[PROVED HERE]` The Newton-corner condition forces `def_obs(F_n)=0`.

`[OPEN CORE]` Any counterexample to exact unit cost for a first-order DA composition must therefore produce a positive-dimensional algebraic foliation invariant under the cascade derivation and invisible to the output. This is the precise order-compression mechanism to classify.

## HT and RH pressure test

The theorem extends exact constraint-order recession beyond autonomous maps. Canonical limits of these nonautonomous cascades can cross from DA approximants to an HT limit only through unbounded observability rank.

No zero-localization statement follows. A possible RH use would require an independently defined zeta/xi approximation whose limiting functional constraint also carries positivity or spectral rigidity. The other agent's Euler/translation lane is not used here.

## Parent-theory verdict

- **Proof gate:** complete on paper.
- **Parent-theory gate:** Wang--Sontag (1995) proves that the order of an input/output differential equation cannot be smaller than the minimal dimension of an observable analytic realization. Isidori--Krener--Gori-Giorgi--Monaco (1981) studies observability of cascade-connected nonlinear systems. The differential-algebraic and foliation interpretations are also standard.
- **Verdict:** the Newton-corner calculation is a useful sufficient rank check for the composition realization, but it is a direct bridge through established observability theory, not new scientific knowledge.
- **Scientific label:** `[BRIDGE] [PROVED]`.

## Gates

- [x] Complete paper proof.
- [x] Explicit genuinely nonautonomous family.
- [x] Exact failure object isolated.
- [x] Nonlinear observability parent audit; result downgraded to bridge.
- [x] Iteration/differential-order audit sufficient for non-novelty verdict.
- [ ] Lean only after novelty and numerical pre-certification gates can both be met.

## Primary references checked so far

1. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.
2. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
3. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
4. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
5. A. Isidori, A. J. Krener, C. Gori-Giorgi, and S. Monaco, *The Observability of Cascade Connected Nonlinear Systems*, IFAC Proceedings Volumes 14 (1981), 19--24.

## Lean status

The Newton-corner degeneration for this card shares its obstruction with
`asymptotically-exponential-algebraic-cascade-unit-cost`; both reduce to controlling the *valuation*
of the model cascade's output-jet determinant, whose nonvanishing the corpus already owns
(`ExpAffineCascade.scaled_jet_det_ne_zero`).

Two things are now settled about that valuation.

* The naive route fails.  Taking the bounds in the separable product form `a_i + b_j` forced by
  `det_ne_zero_of_hasLead`, the boundary matrix has entries `(v_i)_j · c_n^i` with `v_i = (i,…,i,1)`,
  so its first `n − 1` columns are proportional and `det L = 0` for `n ≥ 3`.  The leading terms of the
  determinant cancel.
* The repair that suggested itself — that `det m` is a single monomial, so its valuation is known —
  is **false**: `det (sumJacobian 2) = X₁²(1 − X₂)`, so the height-four model determinant is not a
  monomial.

Machinery built toward this card and available: `MultiGradedNewtonModel`,
`ObservabilityJacobianTransfer`, `LaurentLeadingDeterminant`, `LaurentHasLead`,
`HahnLeadingCoefficient`, `CascadeModelAlgebra`, `ScalarMonomial`, `TowerMonomialShape`.
See `_STAGE3-LEDGER.md` for the full route analysis.
