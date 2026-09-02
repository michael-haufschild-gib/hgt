# Unit differential-order cost for autonomous first-order entire cascades

- **ID:** `asymptotically-exponential-algebraic-cascade-unit-cost`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED]`; downgraded after Schanuel-function parent audit
- **Lane:** general hypertranscendence; finite DA boundary and infinite-depth obstruction
- **Statement:** Every layer in a finite composition of transcendental entire autonomous first-order DA maps contributes exactly one unit of minimal ADE order; in particular `ord_DA(f^[n])=n` for every such `f`.

## Definition: algebraic exponential-cover map

An entire transcendental function `f` is an **algebraic exponential-cover map** if:

1. there is a nonzero algebraic function `A` over `C(X)` such that, in the corresponding algebraic function field,

   `f'(z)=A(f(z))`;

2. some Puiseux branch at `X=infinity` satisfies, for `lambda in C*`,

   `A(X)=lambda X(1+o(1))`.

The algebraic relation between `A` and `X` makes `f` a solution of an autonomous first-order ADE.

Examples include:

- `a+b exp(cz)` with nonzero complex `b,c`;
- affine conjugates of `sin`, `cos`, `sinh`, and `cosh`;
- `L(exp(cz))` for any nonconstant complex Laurent polynomial `L` and `c!=0`. Here `exp(cz)` is algebraic over the value and `f'` has a branch asymptotic to a nonzero scalar multiple of `f`.

## Theorem

`[BRIDGE] [PROVED HERE]` Let `f_1,...,f_n` be algebraic exponential-cover maps of finite positive lower order and set

`F_k=f_k o ... o f_1`, for `1<=k<=n`.

Then

`ord_DA(F_n)=cd_+(F_n)=n`.

## Proof

### 1. Independence of the intermediate constraint states

`[PROVED HERE]` The functions `F_1,...,F_n` are algebraically independent over `C(z)`.

Clunie's composition-growth theorem gives

`T(r,F_k)/T(r,F_(k-1)) -> infinity`

for every `k>=2`, outside the standard harmless exceptional set if needed. If a first algebraic relation occurred at `F_k`, the standard Nevanlinna root estimate for that polynomial relation would give

`T(r,F_k)=O(log r + sum_(j<k) T(r,F_j))`.

The right side is `o(T(r,F_k))` by the successive growth separation, a contradiction.

### 2. Algebraic product-cascade observability

Let `X_1,...,X_n` be algebraically independent. For each `j`, let `A_j(X_j)` be algebraic over `C(X_j)` and possess a Puiseux branch at infinity of the form

`A_j(X_j)=lambda_j X_j(1+o(1))`, with `lambda_j!=0`.

In a common finite algebraic extension of `C(X_1,...,X_n)`, define a derivation by

`delta X_k = product_(j=1)^k A_j(X_j)`.

`[PROVED HERE]` The output observables

`X_n, delta X_n, ..., delta^(n-1) X_n`

are algebraically independent.

Let `J` be their Jacobian with respect to `X_1,...,X_n`, computed after extending the coordinate derivations to the finite separable algebraic field. Each entry of `J` is a finite algebraic differential expression in the `A_j` and their ordinary derivatives.

Expand at the product branch `X_j=infinity` in the iterated Puiseux field. The leading term is obtained by replacing every

`A_j(X_j)` by `lambda_j X_j`,

because every correction has strictly lower exponent in at least one independent variable; the same holds after ordinary differentiation. The resulting leading Jacobian is the observability Jacobian of the affine-exponential product cascade

`delta_0 X_k = product_(j=1)^k lambda_j X_j`.

That Jacobian is nonzero by the triangular observability induction: after passing to the logarithmic velocities, the coefficient of the highest power of the newest velocity is, up to a nonzero scalar, the preceding Jacobian, with base determinant `1`. Hence the leading Puiseux term of `J` is nonzero. Therefore `J!=0`, and the Jacobian criterion proves algebraic independence of the `n` observables.

### 3. Application to composition

Put `X_k=F_k`. The chain rule and `f_k'=A_k o f_k` give

`F_k'=A_k(F_k)F_(k-1)'`, with `F_0'=1`,

and hence

`F_k'=product_(j=1)^k A_j(F_j)`.

Thus the intermediate states realize the algebraic product cascade from Step 2. The field obtained from

`C(z)(F_1,...,F_n)`

by adjoining the algebraic values `A_j(F_j)` is a finite algebraic differential extension and has transcendence degree `n` by Step 1. Step 2 shows that

`F_n,F_n',...,F_n^(n-1)`

are algebraically independent. Therefore no ADE of order below `n` exists.

All derivatives of `F_n` lie in that same differential field of transcendence degree `n`. Its `n+1` elements

`F_n,F_n',...,F_n^(n)`

are algebraically dependent. Hence `ord_DA(F_n)=n`.

### 4. Exact positive-order composition depth

The displayed factorization gives `cd_+(F_n)>=n`, since each factor has positive lower order. Each factor also has finite order by Gold'berg. Iterating finite-order maximum-modulus upper bounds shows that `T(r,F_n)` has exponential height at most `n-1`. The Polya growth-depth lemma would force height at least `n` if `F_n` admitted `n+1` positive-lower-order transcendental entire factors. Therefore `cd_+(F_n)<=n`.

## Complete autonomous order-one corollary

`[BRIDGE] [PROVED HERE]` Let `f` be any transcendental entire solution of an autonomous first-order algebraic differential equation

`P(f,f')=0`, with `P in C[X,Y]` nonzero.

Then, for every `n>=1`,

`ord_DA(f^[n])=cd_+(f^[n])=n`.

The classical Briot--Bouquet classification, in Eremenko's formulation, says that every meromorphic solution of an autonomous first-order ADE is elliptic, rational, or `R(exp(az))` with `R` rational. An entire transcendental solution can be neither elliptic nor rational. If `R` had a pole in `C*`, the surjectivity of `exp(az)` onto `C*` would produce poles of `f`. Thus `R` has poles only at `0` and `infinity`, so it is a Laurent polynomial.

For a Laurent polynomial `L`, the element `t=exp(az)` is algebraic over `f=L(t)`, while

`f'=a t L'(t)`

is algebraic over `f`. On a branch over infinity determined by either `t -> infinity` or `t -> 0`, one has `f'~lambda f` for some `lambda!=0`. Hence `f` is an algebraic exponential-cover map. It has order and lower order one, so the cascade theorem applies to every iterate.

## HT law exposed by the theorem

`[BRIDGE]` Within this broad first-order DA class, algebraic finite quotients do not compress differential complexity: a quotient such as `exp -> sinh` changes the finite cover but not the one-order cost of a composition layer.

`[CONJECTURE]` The asymptotically linear algebraic branch is a local model for a larger law: any composition tower of first-order DA entire factors with no continuous deck symmetry has minimal differential order equal to the number of algebraically independent intermediate states.

`[CONJECTURE]` For every transcendental entire DA function `f`, the sequence `ord_DA(f^[n])` is unbounded, where `f^[n]` is the `n`-th compositional iterate. Bergweiler's 1995 incoherence theorem proves only that the iterates do not all satisfy one common ADE; bounded minimal order with varying equations is not excluded by that theorem. The present result proves the stronger exact law `ord_DA(f^[n])=n` for every autonomous first-order entire `f`.

`[RESOLVED ELSEWHERE]` The complete nonautonomous order-one extension is proved in `../needs-audit/universal-first-order-entire-cascade-unit-cost.md` using Wiman observability charge and a terminal-linear Bell determinant induction. The remaining open core is autonomous and nonautonomous higher order.

An infinite cascade in this class has no finite ADE budget. This gives a constructive boundary mechanism for HT functions: HT appears as the failure of every finite constraint order to observe an unbounded tower of independent finite-cover states.

## RH pressure test, not selector

The completed xi function has finite order, so it cannot itself be a nontrivial finite cascade in this positive-growth class beyond the Polya exceptional regime. The theorem does not constrain xi's zeros and does not imply RH.

Its possible future RH value is architectural: if an Euler--archimedean object can be represented as a limit of finite algebraic-cover constraints with provably diverging observability rank, HT is automatic and the remaining RH question would have to be encoded in the limiting constraint geometry, not in a finite ADE. No such representation is claimed here.

## Novelty and significance gates

- **Proof gate:** complete on paper; the only external inputs are Gold'berg's first-order finite-order theorem and Polya's composition growth estimate.
- **Significance gate:** exact all-order equality for the complete class of transcendental entire autonomous first-order DA functions, quantitatively strengthening Bergweiler's uniform-incoherence theorem on this boundary.
- **Parent-theory gate:** Reinhart's 1993 dissertation proves that the minimum ADE order of a Schanuel function is controlled by the number of algebraically independent functions needed in its construction, extending Babakhanian's exponential-tower result. Every function in the autonomous corollary is a Laurent polynomial in an exponential, and every finite iterate is a Schanuel function. Together with Clunie independence, this is a closer parent than Otsubo or Bergweiler and removes the scientific-novelty claim.
- **Literature gate:** the earlier search missed Reinhart because the dissertation is access-restricted and surfaced only through its repository abstract. Wang--Sontag's general order-versus-observable-dimension theorem is a second parent for the state-space proof.
- **Rediscovery gate:** no prior project card or formal result states the algebraic product-cascade observability lemma or the exact order law.
- **Scientific label:** `[BRIDGE] [PROVED]`; exact autonomous specialization retained as a useful project theorem, not claimed as new science.

## Gates

- [x] 0 -> 1: well-posed class and nontrivial examples.
- [x] 1 -> 2: complete paper proof with a nonzero observability Jacobian.
- [x] Significance: exact law across finite algebraic quotients and all depths.
- [x] Parent theory: Otsubo 1980 checked and not subsuming.
- [x] Dedicated iteration/differential-order literature audit.
- [x] Oscillatory and multi-tract autonomous order-one audit resolved by Briot--Bouquet classification plus Clunie growth separation.
- [ ] Nonautonomous order-one and autonomous higher-order audit.
- [ ] Lean differential-order observability capstone and Briot--Bouquet classification.
- [x] Lean exact positive composition depth.

## Primary references checked

1. A. A. Gold'berg, finite-order theorem for entire solutions of first-order algebraic differential equations.
2. G. Polya, *On an integral function of an integral function*, J. London Math. Soc. 1 (1926), 12--15.
3. S. Otsubo, *Minimal length of Liouville chain for solutions of an algebraic differential equation*, J. Math. Soc. Japan 32 (1980), 623--629.
4. L.-W. Liao and C.-C. Yang, *On the growth and factorization of entire solutions of algebraic differential equations*, Ann. Acad. Sci. Fenn. Math. 25 (2000), 73--84.
5. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
6. G. Fernandes, *A survey on the hypertranscendence of the solutions of the Schroder's, Bottcher's and Abel's equations*, in *Transcendence in Algebra, Combinatorics, Geometry and Number Theory* (2021); arXiv:2102.12168.
7. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95, especially the Briot--Bouquet classification in Section 7.
8. J. Clunie, *The composition of entire and meromorphic functions*, in *Mathematical Essays Dedicated to A. J. Macintyre* (1970), 75--92.
9. G. M. Reinhart, *Schanuel Functions and Algebraic Differential Equations*, PhD dissertation, University of Illinois (1993).
10. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.

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
`HTGeometry/HahnFractionLeadingCoefficient.lean`.  The theorem
`algebraicIndependent_hahnFractionNestedCascade_of_leads` proves algebraic independence of the
terminal output and all descending logarithmic states from their actual leading Hahn fractions in
the nested order `X_n ≫ ⋯ ≫ X_1`.  It retains arbitrary higher branch terms, supports every field
operation and quotient-rule differentiation, proves the complete triangular boundary determinant,
and invokes the domain-valued Jacobian criterion.  The required fraction-field valuation and
complex-linear coordinate derivations are supplied by `HTGeometry/HahnFractionValuation.lean`;
generic Hahn determinant coefficient calculus remains in `HTGeometry/HahnLeadingCoefficient.lean`.

The exact ramified logarithmic-state propagation and gradient independence are now closed in
`HTGeometry/RamifiedMultiGradedNewtonModel.lean`.  Its capstone
`algebraicIndependent_hahnFractionRamLogState` starts from arbitrary positive common Puiseux
ramification indices and the card's nonzero output-linear branch leads, permits all higher branch
terms, proves every iterated logarithmic state has the required nested suffix lead, and concludes
algebraic independence.  The same module's
`algebraicIndependent_hahnFractionRamCascadeOutputJets` converts this through a finite bounded peel
to algebraic independence of the terminal coordinate's first full time-jet block.  The key
off-coordinate theorem uses a discrete lexicographic target bound,
not the false claim that every correction gains one fixed multidegree.

`HTGeometry/RamifiedPuiseuxCascadeTransfer.lean` now closes the transport after branch realization:
`algebraicIndependent_cascadeOutputJets_of_ramifiedPuiseuxSpecialization` pulls the nonzero Hahn
observability determinant back along a differential specialization and applies the source-field
Jacobian criterion.

`HTGeometry/RamifiedPuiseuxBranchField.lean` now constructs that specialization intrinsically.
It takes the relative algebraic closure of the rational coordinate field inside the Hahn fraction
field, proves that every selected algebraic velocity branch belongs to it, restricts all coordinate
derivations and the cascade derivation to it, and closes
`algebraicIndependent_ramifiedPuiseuxBranchCascadeOutputJets`.  The same module proves
`algebraicIndependent_ramifiedPuiseuxBranchCascadeOutputJets_of_realization`: for any selected
target realization, agreement on coordinate images and the exact coordinate cascade law forces
commutation on the whole algebraic branch field and transports the full output-jet independence.
The commutation step is a theorem, not a hypothesis on every algebraic branch element; it follows
from the target-valued algebraic-extension uniqueness theorem
`derivation_map_eq_of_isAlgebraic` in
`HTGeometry/AlgebraicDerivationMapUniqueness.lean`.

`HTGeometry/AutonomousRamifiedPuiseuxCascadeActual.lean` now closes the card's selected-branch
differential-order theorem in the actual meromorphic cascade.  Its structure
`AutonomousRamifiedPuiseuxBranchSelection` records exactly the card's analytic branch selection:
the algebraic velocities lie in the relative branch field, their product is the actual state
derivative, and the branch embedding carries the selected nonzero output-linear Puiseux leads.
The module constructs the ordinary time derivation and the coordinate frame on that branch field;
`derivation_map_eq_of_isAlgebraic_tower_adjoin` derives full intertwining from agreement on state
generators.  It then proves actual output-jet independence over `C`, proves the clock transcendental
over the branch field, descends the jets to `C(z)`, and concludes
`exactDifferentialOrder_entireCascade_of_autonomousRamifiedPuiseuxBranchSelection` with no added
observability or differential-specialization premise.  The combined capstone
`exactOrder_and_compositionDepth_autonomousRamifiedPuiseuxCascade` adds the already-closed
finite-order/positive-lower-order growth half and proves both equalities in one theorem.

**Remaining open core:** formalise the full Briot--Bouquet classification and its entire-function
specialization to Laurent polynomials in an exponential.  This is the only remaining gate for the
card's complete autonomous first-order corollary and stage-3 promotion.  See `_STAGE3-LEDGER.md`.

Also owned: `ExpAffineCascade.scaled_jet_det_ne_zero` (the model determinant),
`TerminalPowerCascadeInduction.algebraicIndependent_cascadeOutput` (the exactly-triangular case),
`MultiGradedNewtonModel`, `ObservabilityJacobianTransfer`, `LaurentLeadingDeterminant`,
`LaurentHasLead`, `HahnLeadingCoefficient`, `CascadeModelAlgebra`, `ScalarMonomial`,
`TowerMonomialShape`.
