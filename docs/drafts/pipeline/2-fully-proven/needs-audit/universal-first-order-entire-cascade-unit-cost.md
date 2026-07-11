# Universal unit differential-order cost for first-order entire cascades

- **ID:** `universal-first-order-entire-cascade-unit-cost`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE] [NEEDS AUDIT]`
- **Lane:** general hypertranscendence; finite DA boundary under composition
- **Statement:** If `f_1,...,f_n` are transcendental entire functions satisfying first-order algebraic differential equations over `C(z)`, then the composition `F_n=f_n o ... o f_1` has minimal ADE order exactly `n`.

## Goal

Determine whether first-order differential algebraicity has a universal, representation-independent composition cost. The autonomous and output-linear Newton-corner cases are already proved. The present claim removes both restrictions.

If true, the result gives a broad finite-boundary law for hypertranscendence: no entire first-order algebraic constraint can hide a composition state, and an infinite cascade necessarily leaves every finite differential order. RH is not used to select or prove the statement.

## Theorem

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]` Let `f_1,...,f_n` be transcendental entire functions, and suppose that for each `k` there is a nonzero polynomial

`P_k(U,V,W) in C[U,V,W]`

such that

`P_k(z,f_k(z),f_k'(z))=0`.

Put `F_k=f_k o ... o f_1`. Then

`ord_DA(F_n)=n`.

Goldberg's theorem makes every `f_k` finite order. No autonomous hypothesis, common equation, common factor, or positive lower-order hypothesis is imposed.

## Reduction I: every transcendental entire first-order solution has a nondegenerate Wiman place

`[PROVED HERE, PAPER LEVEL]` Fix one `f` and an irreducible equation

`P(z,f,f')=0`.

Write

`P(U,V,W)=sum_(b,c) a_(b,c)(U)V^b W^c`

and let `d=max(b+c)`. At Wiman--Valiron maximum points `z_r`, outside the standard exceptional set,

`f'(z_r)/f(z_r)=(nu(r)/z_r)(1+o(1))`,

where `nu(r)` is the central index. Since a transcendental entire function dominates every power of `r` along such points, dividing the differential equation by `f(z_r)^d` kills every term of total `(V,W)`-degree below `d`. The surviving top symbol is

`Q(U,T)=sum_(b+c=d) a_(b,c)(U)T^c`,

with `T=W/V`, and

`Q(z_r,nu(r)/z_r)=o` of its Newton scale.

Goldberg gives finite order, while Strelitz gives positive order `rho=rho(f)>0` for a transcendental entire first-order solution. Choose Wiman--Valiron radii on which

`log nu(r)/log r -> rho`.

Then `T=nu(r)/z_r` has Newton scale `U^(rho-1)`. For `Q(z_r,T)` to vanish at its top scale, at least two monomials of `Q` must attain the maximal weight at `p=rho-1`; otherwise the unique maximal monomial could not be cancelled by either another top-symbol term or a lower total-degree term. Thus `p` is a slope of the Newton polygon of `Q` at `U=infinity`. The Newton--Puiseux theorem gives a branch `tau(U)` of `Q(U,T)=0` with

`tau(U)=c U^p(1+o(1))`, `c!=0`,

and a corresponding place of the derivative constraint

`W=tau(U)V(1+ lower powers of V)`.

Here `p=rho-1`. Hence

`p+1=rho>0`.

There is no component ambiguity: `P` was chosen irreducible over `C(U)`, and its roots in `W` form one algebraic function-field component. After substituting `W=TV`, the Newton--Puiseux place above the selected root of the top symbol is therefore a place of the same irreducible component containing the analytic element `f'`.

Call this a **nondegenerate Wiman place**. Its initial monomial is

`W=c U^p V`, with `q:=p+1>0`.

### Audit closure: the Newton place is genuinely on the irreducible derivative curve

The weight argument above can be made without assuming convergence of the phase of the Wiman points.  Put

`p=rho-1`

and give a top-symbol monomial `a_(b,c)(U)T^c` the weight

`deg a_(b,c)+cp`.

Along radii for which `log nu(r)/log r -> rho`, one has

`|nu(r)/z_r|=r^(p+o(1))`.

After division by `f(z_r)^d`, every lower-total-degree term is smaller than every fixed power of `r`, because a transcendental entire maximum modulus dominates all powers while `f'/f` has polynomial Wiman scale.  If the top symbol had a unique maximal-weight monomial, its gap from the remaining finitely many weights would be a fixed positive number.  The factor `r^o(1)` cannot erase that gap, so the unique monomial could not be cancelled.  Hence the maximal face contains at least two distinct powers of `T`.

The corresponding Newton edge polynomial has a nonzero root: after removing its smallest power of `T`, at least two terms remain, so its remaining polynomial has a nonzero complex root.  Newton--Puiseux at `U=infinity` therefore gives

`tau(U)=c U^p(1+o(1))`, `c!=0`,

on a finite Puiseux cover.  Finally, write `W=VT`.  Then

`V^(-d)P(U,V,VT)=Q(U,T)+lower powers of V`.

Newton--Puiseux in `V^(-1)` lifts the root `T=tau(U)` to a place

`W=tau(U)V+lower powers of V`.

Because `P` is irreducible in `C(U)[V,W]` and depends on `W`, it remains irreducible over `C(U,V)` after taking its primitive part.  All derivative branches are places of this one algebraic function field.  The selected place need not be the asymptotic branch followed by the analytic solution: a nonzero nested initial coefficient at any place proves that the corresponding algebraic field element is nonzero.  This is exactly what the later observability determinant requires.

## Reduction II: the initial monomial cascade is observable

`[PROVED HERE]` Choose a nondegenerate Wiman place for every layer. On a common Puiseux cover, the initial derivative constraints have the form

`b_k=c_k X_(k-1)^p_k X_k`, and set `q_i=p_(i+1)+1>0` for `1<=i<n`.

For the state derivation

`delta X_k=product_(j<=k)b_j`,

put `v_k=delta X_k/X_k`. Up to nonzero constants and a known monomial in `X_0=z`,

`v_k=product_(i<k) X_i^q_i`.

Choose compatible rays on the finite Puiseux cover and rescale the coordinates recursively so that the nonzero monomial coefficients and the relevant state coordinates are positive real. This is possible because the exponent matrix is triangular and every `q_i` is a positive rational number. Set `w_i=q_i v_i` for `1<=i<n`. Here `w_1` is a known function of the base variable, because `v_1=c_1 z^p_1`; the actual hidden velocity coordinates are `w_2,...,w_(n-1)`. After a known positive scalar rescaling and a monotone change of the real time variable, they satisfy the universal triangular system

`dot w_1=0` with `w_1>0` fixed by the base branch,

`dot w_j=w_j(w_1+...+w_(j-1))` for `j>=2`,

Put `m=n-1`. The second logarithmic jet of the terminal output determines

`S_m=w_1+...+w_m`.

For `n<=2` observability is immediate from `X_n` and `v_n`; assume `n>=3`. This system is observable in the hidden coordinates `w_2,...,w_m` on the positive orthant. Let `a` and `b` be two distinct hidden initial states, and let `k>=2` be the first coordinate where they differ. All earlier trajectories agree, while `w_k^a/w_k^b` is the nonunit constant `a_k/b_k`. Assume it is greater than one. If `k=m`, the observed sum `S_m` already differs. If `k<m`, then

`d/dt log(w_(k+1)^a/w_(k+1)^b)=S_k^a-S_k^b`

is eventually positive with divergent integral. Hence `w_(k+1)^a/w_(k+1)^b->infinity`. Induction propagates this strict separation to the terminal state, and therefore to `S_m`; the reverse inequality is symmetric. Distinct positive initial states cannot have the same output germ.

The output already gives the initial values of `X_n` and `v_n=delta X_n/X_n`. The triangular monomial identities

`v_(i+1)/v_i=constant times X_i^q_i`

then show that `(v_n,w_2,...,w_(n-1))` is a finite, locally injective coordinate system for `X_1,...,X_(n-1)`, because every `q_i` is nonzero. Together with `X_n`, the full `n`-state monomial cascade is observable.

For completeness, the required rank statement follows directly. Let `r` be the maximal rank of all finite maps formed from the output Lie derivatives. If `r` were smaller than the hidden state dimension, choose finitely many Lie derivatives whose differentials have rank `r` on an open set. Maximality makes the differential of every further Lie derivative lie in their span. The common level sets of the chosen finite map are then positive-dimensional analytic leaves, and every output Lie derivative is locally constant on each leaf. Two distinct points on a leaf have identical full output jets and hence, by analyticity, identical output germs. This contradicts the positive-orthant distinguishability proved above. Therefore `r` is the full hidden dimension, so finitely many output derivatives have a nonzero Jacobian minor.

This is the no-input analytic observation-space argument abstracted by Wang--Sontag. Since the present vector field and output are algebraic, the minor is an algebraic function. Nonvanishing on the real positive branch proves that it is nonzero over the complex Puiseux function field as well.

## Reduction III: terminal-linear observability induction

The actual algebraic cascade field is the finite extension generated by the states `X_1,...,X_n` and the derivative branches `b_k`. Clunie's composition-growth separation proves that the analytic states

`F_1,...,F_n`

are algebraically independent over `C(z)`: at the first algebraic dependence, the Nevanlinna root estimate would bound `T(r,F_k)` by `O(log r+sum_(j<k)T(r,F_j))`, contradicting the successive Clunie separation. Thus the state field has transcendence degree `n`.

For clarity, this use of composition growth is an induction, not a genericity assumption.  If `k` were the first dependent state, clear denominators in a polynomial relation and regard it as a polynomial in `F_k` with coefficients in `C[z,F_1,...,F_(k-1)]`.  The standard algebraic-function/root estimate gives

`T(r,F_k)=O(log r+sum_(j<k)T(r,F_j))`

outside the usual exceptional set.  For transcendental entire outer `f_k`, Clunie--Steinmetz composition separation makes

`T(r,f_k o F_(k-1)) / T(r,F_(k-1))`

unbounded on admissible radii.  Applying the same separation one level earlier shows that `T(r,F_(k-1))` dominates `log r+sum_(j<k-1)T(r,F_j)` on a common sequence.  Hence the displayed algebraic root bound is impossible.  The argument starts with the ordinary transcendence of `F_1` over `C(z)` and proves independence at every depth.

`[PROVED HERE]` Work in the iterated Puiseux field with nested order

`X_n >> X_(n-1) >> ... >> X_1 >> z`.

Put

`G_k=delta X_k`, `A_k=G_k/X_k`.

Write `A_k^0` for the highest `X_k`-coefficient of `A_k`; it is independent of `X_k`. The Wiman places give the successive nested initial laws

`A_1^0=c_1 z^p_1`,

`in_(X_(k-1)) A_k^0=c_k A_(k-1)^0 X_(k-1)^q_(k-1)`, `q_(k-1)>0`.

For a function `H` of `r` state variables define its output-jet determinant

`J_r(H)=det partial(H,delta H,...,delta^(r-1)H)/partial(X_1,...,X_r)`.

Two exact row-reduction identities control the nested initial term.

### Bell reduction for a terminal-linear state

Suppose `delta X_r=A X_r` and `A` is independent of `X_r`. Write

`delta^j X_r=X_r B_j(A,delta A,...,delta^(j-1)A)`,

where `B_0=1` and `B_(j+1)=delta B_j+A B_j`. In the Jacobian for `J_r(X_r)`, subtract `B_j` times the first row from row `j`. The last column vanishes below its first entry, while the remaining block is `X_r` times the Jacobian of `B_1,...,B_(r-1)`. The Bell transformation from

`(A,delta A,...,delta^(r-2)A)` to `(B_1,...,B_(r-1))`

is triangular with diagonal one. Therefore

`J_r(X_r)=+- X_r^(r-1) J_(r-1)(A)`.

For the full algebraic branch, `delta X_r=A_r X_r+lower powers of X_r`. Because every lower-state component of `delta` is independent of `X_r`, taking the highest `X_r`-coefficient commutes with the finitely many Lie derivatives in `J_r`. Hence the same identity gives the highest `X_r`-coefficient with `A=A_r^0`, the leading coefficient of `A_r`.

### Bell reduction for a positive-power terminal observation

Now let `H=C X_r^q`, with `q!=0`, `C` independent of `X_r`, and `delta X_r=A X_r`. Put

`U=delta H/H=delta C/C+qA`,

which is independent of `X_r`. The same row operation, now using `partial H/partial X_r=qH/X_r`, gives

`J_r(H)=+- q H^r/X_r J_(r-1)(U)`.

Apply these identities successively. The first removes `X_n` and replaces the output by `A_n^0`. Its highest `X_(n-1)` term is

`H=c_n A_(n-1)^0 X_(n-1)^q_(n-1)`.

The second Bell identity applied to `H` removes `X_(n-1)`. Its new lower output is

`U=delta A_(n-1)^0/A_(n-1)^0+q_(n-1)A_(n-1)^0`.

At the next nested place the first summand is independent of `X_(n-2)` at top degree, whereas the second has the strictly positive power `X_(n-2)^q_(n-2)`. Thus

`in_(X_(n-2)) U=q_(n-1) in_(X_(n-2))A_(n-1)^0`.

The same argument repeats down the triangular flag. Every step contributes a nonzero factor `q_i`, a nonzero power of a state coordinate, and a nonzero algebraic leading coefficient. The terminal base is the one-variable derivative

`partial(c A_1 X_1^q_1)/partial X_1=c q_1 A_1 X_1^(q_1-1)!=0`.

Therefore the nested initial coefficient of

`J_n(X_n)`

is nonzero. The actual output jets `X_n,delta X_n,...,delta^(n-1)X_n` are algebraically independent.

This induction repairs the failed generic perturbation argument: it does not assume observability is open under arbitrary lower Puiseux terms. It identifies a specific nested leading coefficient of the raw output-jet determinant and proves recursively that lower terms cannot reach it.

Consequently the terminal output differential field has transcendence degree `n`. Conversely all output derivatives lie in the `n`-dimensional algebraic state field. For one DA element, the differential transcendence degree of its generated differential field equals the least order of an irreducible ADE: minimality makes the lower jets algebraically independent, and the nonzero separant makes all higher jets algebraic. Hence

`ord_DA(F_n)=n`.

## New characteristic: quantized Wiman observability charge

For a transcendental entire first-order DA function `f`, define its **Wiman observability charge** at the proved Newton place by

`omega(f)=p+1`,

where `f'/f` has top-symbol branch `c z^p`. Reduction I proves the exact identity

`omega(f)=rho(f)>0`.

Reduction III shows that the nested leading output-jet determinant contains a nonzero factor contributed by every `omega(f_k)`. Its magnitude does not alter the state cost: every nonzero charge contributes exactly one observable algebraic state. Therefore

`ord_DA(f_n o ... o f_1)=sum_(k=1)^n 1_(omega(f_k)!=0)=n`.

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` First-order entire composition complexity is thus **quantized by the support of the Wiman charges, not by their magnitudes**. A factor of order `1/2` and a factor of order `100` each cost one differential order. The boundary `omega=0` is the exact point where the Bell induction loses its nonzero factor; transcendental entire first-order ADE solutions cannot lie on that wall.

This charge is not a renamed Nevanlinna order: its new role is as the coefficient that survives the terminal-linear observability determinant and converts analytic growth into an exact algebraic state count.

## Why the known parent theory does not yet settle the candidate

- Wang--Sontag proves that an input/output equation cannot have order below the minimal dimension of an observable analytic realization. It does not prove that a composition realization arising from an arbitrary first-order entire ADE is observable.
- Isidori--Krener--Gori-Giorgi--Monaco characterizes loss of observability in nonlinear cascades by a partial matching of subsystem dynamics. It does not supply the Wiman-place exclusion of such matching for transcendental entire ADE solutions.
- Goldberg supplies finite order; Wiman--Valiron supplies the top homogeneous symbol; neither treats minimal ADE order of iterated compositions.
- Liao--Yang proves pseudo-primality of every transcendental entire first-order ADE solution. That rules out a first-order ADE for a two-layer transcendental composition by growth, but it does not give the all-depth exact order law.
- Ait El Manssour--Sattelberger--Teguia Tabuguia constructs ADEs for compositions and proves the general upper bound `ord(f o g)<=ord(f)+ord(g)` for equations linear in their highest derivative. It does not prove exactness for special entire solutions or automatic observability of their composition states.

The candidate's possible new content is therefore narrow: **entire first-order ADE growth forces a nondegenerate Newton place, and that place forbids every positive-dimensional unobservable matching in every finite composition cascade.**

## Counterexample gate

A counterexample would have to defeat one of three proved steps:

1. the analytic component has no Wiman place with output exponent one, contrary to the top-symbol reduction;
2. the associated monomial cascade is distinguishable but nevertheless has deficient generic algebraic observability rank;
3. the terminal-linear Bell induction has a zero nested leading coefficient despite every `q_i` being nonzero.

All three alternatives are closed in the proof above. The exact compression boundary of the mechanism is `q_i=0`.

## HT consequence: universal first-order Poincare recession

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]` Let `f` be any transcendental entire first-order DA function with a repelling fixed point `zeta` and multiplier `lambda`. Its normalized Poincare function `phi` is the locally uniform limit

`g_n(z)=f^[n](zeta+z/lambda^n) -> phi(z)`.

The theorem gives `ord_DA(f^[n])=n`. Minimal ADE order is invariant under precomposition by a nonconstant affine map, because the triangular substitutions

`g_n^(j)(z)=lambda^(-nj)(f^[n])^(j)(zeta+z/lambda^n)`

and their inverse transport an ADE without changing its highest derivative index. Hence

`ord_DA(g_n)=n`.

Bergweiler proves that `phi` is HT for every transcendental entire `f`. Thus the complete nonautonomous first-order entire class has a canonical HT boundary with exact constraint-order recession

`1,2,3,... -> infinity`.

The qualification **canonical** is essential. Arbitrary locally uniform approximation cannot detect HT, since polynomials of ADE order zero approximate every entire function.

## RH pressure test, not research selector

The theorem is wholly about general HT structure. Only after it is proved could one ask whether a zeta-related object admits a canonical first-order constraint cascade. No Euler, translation-spectrum, divisor-Hermite, or zero-localization claim is made here, and none is needed for the theorem.

## Novelty gate

- **Current label:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE] [NEEDS AUDIT]`.
- **Parent-theory audit:** Wang--Sontag, nonlinear cascade observability, Goldberg, Wiman--Valiron, Liao--Yang, Bergweiler, and Reinhart's Schanuel-function order work identified.
- **Targeted literature audit:** exact-title and concept searches across arXiv, Crossref, OpenAlex, the Wang--Sontag cited-by corpus, the full Liao--Yang paper, and the full 2023 *D-Algebraic Functions* paper found upper composition-order bounds, generic elimination algorithms, pseudo-primality, and Schanuel-class exactness, but no theorem asserting exact order `n` for every composition of arbitrary transcendental entire first-order ADE solutions.
- **Residual novelty under test:** automatic generic observability for the complete nonautonomous first-order entire ADE class.
- **Failure rule:** if Isidori's matching criterion plus standard Newton-polygon theory yields the automatic-observability statement directly, downgrade the result to `[BRIDGE]`.

## Gates

- [x] 0 -> 1: well-posed complete class, independent attack, counterexample gate, parent theories named.
- [x] Close component bookkeeping and positivity in the Wiman-place lemma.
- [x] Close distinguishability-to-generic-rank for the monomial cascade.
- [x] Replace the invalid generic filtered lift by the terminal-linear Bell induction.
- [x] 1 -> 2: complete paper proof with no open dependency.
- [x] Targeted literature and citation-descendant search after proof.
- [ ] Independent expert priority and proof check.
- [ ] Lean only after novelty and numerical-precertification instructions can be reconciled.

## Primary references checked

1. A. A. Goldberg, finite-order theorem for meromorphic solutions of first-order algebraic differential equations.
2. W. K. Hayman, Wiman--Valiron growth methods and the general ADE growth conjecture.
3. L.-W. Liao and C.-C. Yang, *On the growth and factorization of entire solutions of algebraic differential equations*, Ann. Acad. Sci. Fenn. Math. 25 (2000), 73--84.
4. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
5. A. Isidori, A. J. Krener, C. Gori-Giorgi, and S. Monaco, *The Observability of Cascade Connected Nonlinear Systems*, IFAC Proceedings Volumes 14 (1981), 337--342.
6. G. M. Reinhart, *Schanuel Functions and Algebraic Differential Equations*, PhD dissertation, University of Illinois (1993).
7. R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia, *D-Algebraic Functions*, J. Symbolic Comput. 2023; arXiv:2301.02512.
8. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.

## Log

- 2026-07-11 -- Created after the autonomous and output-linear Newton-corner theorems. Isolated the nondegenerate Wiman place and the positive monomial observability degeneration as the two mechanisms that may close the complete nonautonomous first-order class.
- 2026-07-11 -- Medalist re-audit withdrew the premature proved label: the state derivation is not homogeneous for the naive Puiseux weight, so monomial observability does not yet imply observability of the full lower-term cascade. The exact open core is a flat finite-jet degeneration or a no-matching theorem.
- 2026-07-11 -- Closed that open core without a generic degeneration: exact Bell-polynomial row reductions remove terminal variables one at a time, and the nested leading determinant acquires a nonzero factor from every `q_i=p_(i+1)+1`. This proves that `q_i=0` is the sharp compression wall and that positive Wiman exponents force full observability.
