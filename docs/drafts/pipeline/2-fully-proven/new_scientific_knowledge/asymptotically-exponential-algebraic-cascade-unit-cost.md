# Unit differential-order cost for autonomous first-order entire cascades

- **ID:** `asymptotically-exponential-algebraic-cascade-unit-cost`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
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

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]` Let `f_1,...,f_n` be algebraic exponential-cover maps of finite positive lower order and set

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

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]` Let `f` be any transcendental entire solution of an autonomous first-order algebraic differential equation

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

`[OPEN CORE]` Pass from autonomous order one to nonautonomous order one and autonomous higher order. The Eremenko classification and the one-dimensional algebraic product cascade no longer apply directly.

An infinite cascade in this class has no finite ADE budget. This gives a constructive boundary mechanism for HT functions: HT appears as the failure of every finite constraint order to observe an unbounded tower of independent finite-cover states.

## RH pressure test, not selector

The completed xi function has finite order, so it cannot itself be a nontrivial finite cascade in this positive-growth class beyond the Polya exceptional regime. The theorem does not constrain xi's zeros and does not imply RH.

Its possible future RH value is architectural: if an Euler--archimedean object can be represented as a limit of finite algebraic-cover constraints with provably diverging observability rank, HT is automatic and the remaining RH question would have to be encoded in the limiting constraint geometry, not in a finite ADE. No such representation is claimed here.

## Novelty and significance gates

- **Proof gate:** complete on paper; the only external inputs are Gold'berg's first-order finite-order theorem and Polya's composition growth estimate.
- **Significance gate:** exact all-order equality for the complete class of transcendental entire autonomous first-order DA functions, quantitatively strengthening Bergweiler's uniform-incoherence theorem on this boundary.
- **Parent-theory gate:** Otsubo's Liouville-chain theorem gives only a coarse converse bound between Liouville length and ADE order. Bergweiler (1995) proves that the iterates of a transcendental entire function cannot all satisfy one fixed ADE. Neither result proves unbounded minimal order, exact linear growth, or output-jet observability.
- **Literature gate:** checked against Otsubo (1980), Bergweiler (1995), the 2021 Fernandes survey of differential algebra and iteration, the sources cited there, Crossref, OpenAlex, arXiv, and the project corpus. The located results concern Liouville-chain length, coherent families, or HT of functional-equation solutions; no minimal-order divergence or exact unit-cost theorem was found.
- **Rediscovery gate:** no prior project card or formal result states the algebraic product-cascade observability lemma or the exact order law.
- **Scientific label:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; publication priority remains to be independently verified.

## Gates

- [x] 0 -> 1: well-posed class and nontrivial examples.
- [x] 1 -> 2: complete paper proof with a nonzero observability Jacobian.
- [x] Significance: exact law across finite algebraic quotients and all depths.
- [x] Parent theory: Otsubo 1980 checked and not subsuming.
- [x] Dedicated iteration/differential-order literature audit.
- [x] Oscillatory and multi-tract autonomous order-one audit resolved by Briot--Bouquet classification plus Clunie growth separation.
- [ ] Nonautonomous order-one and autonomous higher-order audit.
- [ ] Lean only after novelty and numerical pre-certification gates can both be met.

## Primary references checked

1. A. A. Gold'berg, finite-order theorem for entire solutions of first-order algebraic differential equations.
2. G. Polya, *On an integral function of an integral function*, J. London Math. Soc. 1 (1926), 12--15.
3. S. Otsubo, *Minimal length of Liouville chain for solutions of an algebraic differential equation*, J. Math. Soc. Japan 32 (1980), 623--629.
4. L.-W. Liao and C.-C. Yang, *On the growth and factorization of entire solutions of algebraic differential equations*, Ann. Acad. Sci. Fenn. Math. 25 (2000), 73--84.
5. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
6. G. Fernandes, *A survey on the hypertranscendence of the solutions of the Schroder's, Bottcher's and Abel's equations*, in *Transcendence in Algebra, Combinatorics, Geometry and Number Theory* (2021); arXiv:2102.12168.
7. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95, especially the Briot--Bouquet classification in Section 7.
8. J. Clunie, *The composition of entire and meromorphic functions*, in *Mathematical Essays Dedicated to A. J. Macintyre* (1970), 75--92.
