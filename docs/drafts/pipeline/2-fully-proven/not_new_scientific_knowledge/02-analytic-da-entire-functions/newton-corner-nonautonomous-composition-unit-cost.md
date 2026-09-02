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
- [ ] Lean differential-order observability capstone.
- [x] Lean exact positive composition depth.

## Primary references checked so far

1. J. Clunie, *The composition of entire and meromorphic functions* (1970), 75--92.
2. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
3. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
4. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
5. A. Isidori, A. J. Krener, C. Gori-Giorgi, and S. Monaco, *The Observability of Cascade Connected Nonlinear Systems*, IFAC Proceedings Volumes 14 (1981), 19--24.

## Lean status

The Newton degeneration this card's step 2 proposes is now **proved unusable**, and an exact
replacement is built.

* For the model cascade, `deg_w (δ^i X_n) = W_n + i·W_(n−1)` and the top-weight part of `δ^i X_n` is
  exactly `P_(n−1)^i P_n`, so the Jacobian's top-weight entry degrees are `a(i,k) = D_i − w_k`: the
  leading coefficient matrix is **rank one for every choice of positive weights**, every surviving
  permutation of the assignment problem ties, and the model determinant is always a strictly
  lower-order term.  No reweighting repairs this.
* The general degeneration criterion is Lean
  (`HTGeometry/LogScaleDeterminantNonCancellation.lean`: `hasLogScaleExponent_det_of_perturbation`,
  `…_on`, `det_ne_zero_of_perturbation_unique_max_on`); its hypothesis is uniqueness of the optimal
  assignment, which the previous point shows fails identically here.

The replacement is an exact, hypothesis-free reduction:

| Statement | Theorem | Module |
|---|---|---|
| `δH = U·H ⟹ det (∂_j δ^i H) = H^(n+1)·det(∂_j H ; ∂_j δ^s U)` | `derivationIterateOutputJacobian_det_uniformBordered` | `DerivationBorderedJetReduction` |
| the Bell rows are a unitriangular change of the jet rows | `uniformBordered_derivationBell_det_eq`, `derivationBellCoeff_det` | `DerivationBorderedJetReduction` |
| **the peel step**, with any number of border rows | `peelMatrix_det_succ` | `DerivationJetPeel` |
| the whole chain peeled at once | `peelMatrix_det_chain` | `DerivationJetPeel` |
| **closed form** `det (∂_j δ^i Y_0) = (∏_m Y_m^(N−m−1))·det (∂_j Y_m)` | `outputJacobian_det_eq_gradientMatrix` | `DerivationJetPeel` |
| observability from the chain gradients | `outputJacobian_det_ne_zero_of_gradientMatrix` | `DerivationJetPeel` |

Here `Y_0` is the output and `Y_(m+1) = δY_m/Y_m`.  This removes the hypothesis `hterminalU` of the
corpus's terminal-scaled reduction, which the general cascade cannot satisfy: `∂_n U = 0` for
`U = P_n/X_n` forces `A_n' X_n = A_n`, i.e. exact linearity.

The composition-depth half is now closed in
`HTGeometry/FiniteOrderCascadeCompositionDepth.lean`.  The unconditional theorem
`compositionDepth_finiteOrder_positiveCascade` proves exact depth `n` from precisely the finite
prefix assumptions used by this card: differentiability, nonconstancy, finite-order envelopes, and
positive lower order for the `n` displayed factors.  Its proof first gives the generic finite-order
upper growth-height bound and then combines it with the existing Pólya lower bound; no assumptions
on factors beyond the finite cascade are introduced.

The exact multigraded Puiseux/Hahn determinant endpoint is now closed in
`HTGeometry/HahnTowerGradientStaircase.lean`.  The theorem
`algebraicIndependent_hahnCascade_of_leads` proves algebraic independence of the terminal output
and all descending-prefix logarithmic states from their actual leading Hahn coefficients.  It
retains arbitrary strictly higher branch terms, differentiates them with the coordinate
derivations, proves the complete reversed-column boundary determinant, and invokes the
domain-valued Jacobian criterion.  Generic Hahn determinant coefficient calculus is supplied by
`HTGeometry/HahnLeadingCoefficient.lean`.

**The remaining open core is one statement:** the gradients `∂_j Y_m`, `m < n`, of the iterated
logarithmic derivatives of `X_n` are linearly independent.  For the cascade `Y_1 = P_(n−1) h_n(X_n)`
and `Y_2 = T_(n−1) + P_(n−1) κ_n(X_n)` with `κ_n = X_n h_n'(X_n) → 0`, so the asymptotic input is now
needed only to prove that these actual logarithmic states have the descending-prefix Hahn leads
consumed by the new capstone.  See `_STAGE3-LEDGER.md`.

Also owned: `ExpAffineCascade.scaled_jet_det_ne_zero` (the model determinant),
`TerminalPowerCascadeInduction.algebraicIndependent_cascadeOutput` (the exactly-triangular case),
`MultiGradedNewtonModel`, `ObservabilityJacobianTransfer`, `LaurentLeadingDeterminant`,
`LaurentHasLead`, `HahnLeadingCoefficient`, `CascadeModelAlgebra`, `ScalarMonomial`,
`TowerMonomialShape`.
