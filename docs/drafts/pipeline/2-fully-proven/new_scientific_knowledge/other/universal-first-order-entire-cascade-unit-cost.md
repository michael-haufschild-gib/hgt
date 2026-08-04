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

`[PROVED HERE, PAPER LEVEL]` Fix one `f` and take the minimal polynomial of `f'` over
`C(U,V)` with `U=z` and `V=f`; after clearing denominators, write its primitive irreducible
equation as

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

There is no component ambiguity: `P` is irreducible in `C(U,V)[W]`, and its roots in `W` form
one algebraic function-field component. After substituting `W=TV`, the Newton--Puiseux place
above the selected root of the top symbol is therefore a place of the same irreducible component
containing the analytic element `f'`.

Call this a **nondegenerate Wiman place**. Its initial monomial is

`W=c U^p V`, with `q:=p+1>0`.

### Compatibility of the layer places on the cascade component

The places cannot be chosen as unrelated roots of the separate minimal polynomials.  Let `K` be
the function field of the irreducible cascade component determined by the analytic derivative
branches.  Algebraic independence of `X_1,...,X_n` makes the rational state field

`C(z)(X_1,...,X_n)`

inject into `K`.  For every edge `k`, its irreducible derivative field

`E_k=C(X_(k-1),X_k)(b_k)`

also injects into `K`; hence the dominant rational map from a normal model of `K` to a normal
projective model of `E_k` does not collapse the chosen Wiman place.

Build a composite valuation from the terminal state inward.  On the projective `X_n`-fiber choose
the terminal-linear place of `E_n`; properness of normalization gives a place above it on the
normal model of `K`.  Its residue field still contains the full lower cascade component over the
generic variables `X_1,...,X_(n-1)` and the leading coefficient
`tau_n(X_(n-1))`.  Refine this residue valuation by the positive Wiman place at
`X_(n-1)=infinity`.  Repeat on the normalized lower fiber products.  At each step a finite base
change may split a place but cannot remove every point above it, and ramification only multiplies
the valuation; it cannot turn the nonzero exponent `q_k` into zero.

This produces one valuation flag on the actual irreducible field `K` with nested order

`X_n >> X_(n-1) >> ... >> X_1 >> z`

and with all selected initial laws simultaneously valid.  Thus the later nonzero initial
coefficient is computed in the analytic cascade component, not in an unrelated tensor-product
component.

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

Because `P` was chosen as the primitive minimal polynomial in `C(U,V)[W]`, all derivative
branches are places of this one algebraic function field.  The selected place need not be the
asymptotic branch followed by the analytic solution: a nonzero nested initial coefficient at any
place proves that the corresponding algebraic field element is nonzero.  This is exactly what the
later observability determinant requires.

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
- Malmquist's 1920 theorem, in Eremenko's differential-function-field formulation, forces the irreducible first-order field of a transcendental meromorphic solution to satisfy the Fuchs conditions.  The ensuing Riccati/Poincare/Clairaut classification controls the one-layer algebraic curve, but it neither proves that an arbitrary entire cascade is observable nor computes the minimal ADE order of its terminal output.
- Reinhart proves exact-order results for Schanuel functions built from algebraic operations and exponentiation.  That parent covers exponential towers and related expression classes, not arbitrary transcendental entire solutions of irreducible first-order algebraic differential equations.  The Wiman-place argument is precisely what replaces an explicit Schanuel presentation.
- Teguia Tabuguia's 2025 arithmetic theorem gives the sum of input orders as an elimination bound for rational arithmetic expressions of generic DA states.  It does not treat nonlinear composition exactness for special global entire solutions.

The candidate's possible new content is therefore narrow: **entire first-order ADE growth forces a nondegenerate Newton place, and that place forbids every positive-dimensional unobservable matching in every finite composition cascade.**

The Malmquist parent does not collapse this class to Reinhart's.  In genus zero it gives an
algebraic change to a Riccati equation with algebraic coefficients; in genus one it gives a
Poincare field uniformized by an elliptic function of an Abelian integral.  These are
one-layer birational classifications, not presentations by field operations and exponentiation,
and neither makes the composed terminal state algebraically observable.  Eremenko's Theorem 8
adds the half-integer growth law for entire solutions, but still supplies no composition-order
lower bound.

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

The theorem is wholly about general HT structure.  Its first zeta-facing consequence is an exclusion, not a proof route.

Let `phi` be a nonconstant entire solution of a Poincare/Schroder constraint

`phi(lambda z)=f(phi(z))`, `|lambda|>1`,

where `f` is transcendental entire and first-order DA.  Strelitz gives `rho(f)>0`.  The function `phi` cannot be a polynomial, since then the left side is a polynomial while the right side is transcendental.  Polya's composition-growth theorem now makes `f o phi`, hence `phi(lambda z)`, an entire function of infinite order: the only finite-order transcendental-inner exception requires the outer function to have order zero.  Therefore every such `phi` has infinite order.

The completed zeta function `xi`, and `t |-> xi(1/2+it)`, have finite order one.  They cannot be Poincare functions of transcendental entire first-order DA maps.  Thus the new unit-cost law rules out the most direct attempt to explain zeta's HT by a positive-charge entire cascade.

The sharp remaining compositional boundary is meromorphic order zero.  Such first-order factors exist, the Wiman charge can vanish there, and Liao--Yang records explicit two-layer meromorphic compression.  A future RH-relevant route would first need a classification of finite-order HT objects built from **zero-charge meromorphic matching**, and then an independent reason that the zeta constraints select the critical-line divisor.  The present theorem supplies the boundary and the no-go result, not that missing selection principle.

No Euler, translation-spectrum, divisor-Hermite, or zero-localization claim is made here, and none is needed for the theorem.

## Novelty gate

- **Current label:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE] [NEEDS AUDIT]`.
- **Parent-theory audit:** Wang--Sontag, nonlinear cascade observability, Goldberg, Wiman--Valiron, Liao--Yang, Bergweiler, and Reinhart's Schanuel-function order work identified.
- **Targeted literature audit:** exact-title and concept searches across arXiv, Crossref, OpenAlex, the Wang--Sontag cited-by corpus, the full Liao--Yang paper, and the full 2023 *D-Algebraic Functions* paper found upper composition-order bounds, generic elimination algorithms, pseudo-primality, and Schanuel-class exactness, but no theorem asserting exact order `n` for every composition of arbitrary transcendental entire first-order ADE solutions.
- **Residual novelty under test:** automatic generic observability for the complete nonautonomous first-order entire ADE class.
- **Failure rule:** if Isidori's matching criterion plus standard Newton-polygon theory yields the automatic-observability statement directly, downgrade the result to `[BRIDGE]`.

## Dual-gate verdict

### Novelty: provisional pass

The exact delta from the strongest parents is now isolated.

- Liao--Yang proves only the two-factor obstruction through pseudo-primality.
- Reinhart computes exact order inside the explicitly generated Schanuel class.
- Wang--Sontag turns observability into an order lower bound but does not prove observability.
- Malmquist--Eremenko classifies the one-layer Fuchsian differential field but not a composed output.
- The DA-arithmetic papers give elimination upper bounds, not equality for special entire solutions.

The candidate supplies the missing all-depth statement for the full analytic class of transcendental entire first-order ADE solutions, without an explicit expression presentation.  No exact, equivalent, or stronger theorem was found in the checked primary/citation literature.  This remains a provisional rather than bibliographically certified pass.

### Significance: pass

The result is not just a new example or a minimal equation calculation.  It proves a universal quantization law on a natural maximal one-state analytic class:

`one global transcendental entire first-order constraint layer = one minimal differential order`.

It also identifies the mechanism and the sharp wall.  The analytic growth invariant `rho(f)>0` becomes the nonzero coefficient of an algebraic observability determinant; its magnitude is irrelevant, while its vanishing is exactly where the proof and known meromorphic counterexamples permit compression.  Finally, every repelling Poincare linearization in this class is an HT limit with canonical exact-order recession `1,2,3,...`.  These are consequence-bearing statements about the DA/HT boundary, not renamed closure properties.

**Current verdict:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PAPER PROOF COMPLETE] [DUAL GATE PROVISIONALLY PASSED]`.  Keep the card in `needs-audit` until an independent specialist checks the Puiseux/Bell determinant proof and the 1990s exact-order literature.

## Gates

- [x] 0 -> 1: well-posed complete class, independent attack, counterexample gate, parent theories named.
- [x] Close component bookkeeping and positivity in the Wiman-place lemma.
- [x] Close distinguishability-to-generic-rank for the monomial cascade.
- [x] Replace the invalid generic filtered lift by the terminal-linear Bell induction.
- [x] 1 -> 2: complete paper proof with no open dependency.
- [x] Targeted literature and citation-descendant search after proof.
- [ ] Independent expert priority and proof check.
- [x] Lean: the terminal-linear Bell row reduction `J_r(X_r) = +- X_r^(r-1) J_(r-1)(A)`
- [x] Lean: the positive-power Bell reduction for `H = C X^q`
- [x] Lean: the cascade induction down the flag, and its positive-exponent observability capstone
- [x] Lean: the no-cancellation step of Reduction I -- a unique maximal weight is impossible
- [x] Lean: the Newton edge polynomial has a nonzero root
- [x] Lean: the weight calculus `deg a + c p` on the logarithmic scale
- [x] Lean: the maximum term and the central index -- existence, attainment, monotonicity
- [x] Lean: the two-sided growth law, the discrete form of `log mu(s)-log mu(r) = int nu(t) dt/t`
- [x] Lean: both order-transfer inequalities, `nu(r) <= log mu(e r)` and `log mu(r) <= log mu(1) + nu(r) log r`
- [x] Lean: the order identity, as mutual eventual power-bound transfer at any larger exponent
- [x] Lean: the sandwich `mu(r) <= M(r) <= S(r) <= 2 mu(2r)`, incl. Cauchy's estimate
- [x] Lean: geometric decay of the terms away from the central index, and the upper tail sum
- [x] Lean: the lower tail sum, and the "central terms dominate" window decomposition
- [x] Lean: the Borel growth lemma, and the unbounded supply of good radii it yields
- [x] Lean: continuity of the maximum term, the hypothesis the Borel lemma needs
- [x] Lean: the Borel bridge -- good radii for `mu`, and the resulting bound on `nu`
- [x] Lean: `z f'(z) - k f(z)` is the index-deviation series, and its bound
- [x] Lean: the logarithmic-derivative estimate at a maximum-modulus point, with explicit remainder
- [x] Lean: log-convexity of `mu` in `log r`, the second-order input the decay bounds lack
- [x] Lean: the majorant bounded back by the maximum term times the central index
- [x] Lean: the local expansion, the alignment mechanism, and criticality at a circle maximum
- [x] Lean: the mean index is within `(nu(s)-nu(t)) + log(nu+C)/log(s/r)` of the modal index
- [x] Lean: the Wiman--Valiron estimate assembled, with explicit misalignment remainders
- [x] Lean: bound `D` and `E` at a Borel-good radius, making the remainder `o(nu)`
- [x] Lean: the nondegenerate Wiman place, analytically (root proximity replaces the Newton--Puiseux branch)
- [x] Lean: state algebraic independence from separation (`polyIndependent_of_chain`); the
      Clunie--Steinmetz separation itself remains the one external analytic input, with the precise
      Lean statement it must discharge (`SeparatesLast`)
- [x] Lean: the order lower bound `ord_DA >= n` from `n` algebraically independent jets
- [x] Lean: the matching upper bound `ord_DA <= n` from a bounded-transcendence state field
- [x] Lean: `IsLeast`, the exact minimal order, given the two analytic inputs as hypotheses
- [x] Lean: the upper bound `ord_DA <= n` on the *actual entire composition*, with no independence
      hypothesis (`differentiallyAlgebraicOfOrder_entireCascade_of_transcendental`)
- [x] Lean: consecutive states are automatically independent, so Clunie--Steinmetz is not needed for
      the upper half (`pairAlgIndep_of_transcendental`)
- [x] Lean: an entire function has order zero exactly when it is a polynomial
- [x] Lean: length one closed unconditionally by three independent routes, with `Complex.exp` as an
      explicit instance
- [x] Lean: sharpness -- polynomial constituents give order `0`, so transcendence cannot be weakened
- [x] Lean: the Poincare recession consequence, and the charge-count identity
- [ ] Lean: the growth separation `StepSeparation` -- the one analytic input still open
- [ ] Lean: observability (`helim`) on the analytic objects -- Reduction III

### Lean status

> **Superseded — read the log entries at the end of this card.**  The module list and principal
> declarations below describe the state before the analytic/field layer was built.  Current summary:
>
> * **Upper bound `ord_DA ≤ n`: proved unconditionally**, with exactly the paper's hypotheses
>   (`differentiallyAlgebraicOfOrder_entireCascade_of_transcendental`).  No independence assumption is
>   used: consecutive states are automatically independent (`pairAlgIndep_of_transcendental`).
> * **Lower bound**: reduced to a single analytic predicate `StepSeparation`, plus observability
>   (`helim`).  All algebra, value distribution and field theory around them is formal and axiom-clean.
> * **Length one: closed unconditionally, three independent ways**; `Complex.exp` is an explicit
>   instance, so nothing in the chain is vacuous.
> * **Sharpness**: the transcendence hypothesis cannot be dropped
>   (`not_exactDifferentialOrder_entireCascade_of_polynomial`), and the entire functions of order zero
>   are exactly the polynomials.
> * **Consequences formalized**: Poincaré recession (`exactDifferentialOrder_poincareApprox`) and the
>   charge-count identity (`exactDifferentialOrder_eq_chargeCount`).


Reduction III — the terminal-linear Bell induction, which is the step that closed the card's open
core — is **formalized unconditionally and axiom-clean**
(`[propext, Classical.choice, Quot.sound]`).  The earlier audit note claiming that the corpus has no
reusable multivariate Jacobian observability theorem was stale: the corpus already owned both
one-step Bell reductions, and the missing piece was only the chain that iterates them down the flag.

```text
formal/GaloisForLFunctions/HTGeometry/BellCoordinateJacobian.lean
formal/GaloisForLFunctions/HTGeometry/BellSubstitutionJacobian.lean
formal/GaloisForLFunctions/HTGeometry/TerminalLinearJacobian.lean
formal/GaloisForLFunctions/HTGeometry/TerminalScaledJacobian.lean
formal/GaloisForLFunctions/HTGeometry/TerminalLinearBellJacobian.lean
formal/GaloisForLFunctions/HTGeometry/DerivationTerminalLinearJacobian.lean
formal/GaloisForLFunctions/HTGeometry/TerminalPowerCascadeInduction.lean   (new)
formal/GaloisForLFunctions/HTGeometry/ScalarDifferentialOrderLowerBound.lean (new)
formal/GaloisForLFunctions/HTGeometry/ScalarDifferentialOrderUpperBound.lean (new)
formal/GaloisForLFunctions/HTGeometry/NewtonEdgeNonCancellation.lean (new)
formal/GaloisForLFunctions/HTGeometry/MaximumTermCentralIndex.lean (new)
formal/GaloisForLFunctions/HTGeometry/MaximumTermLogarithmicDerivative.lean (new)
formal/GaloisForLFunctions/HTGeometry/TriangleInequalityDefect.lean (new)
formal/GaloisForLFunctions/HTGeometry/CircleMaximumCriticality.lean (new)
formal/GaloisForLFunctions/HTGeometry/DiscreteJensenExp.lean (new)
formal/GaloisForLFunctions/HTGeometry/MeanIndexComparison.lean (new)
formal/GaloisForLFunctions/HTGeometry/BorelGrowthLemma.lean (already existed; extended)
```

Principal declarations:

```text
bellCoordinateJacobian_det                -- the Bell coordinate change has determinant one
derivationBellValueJacobian_det           -- Bell substitution preserves the lower-jet determinant
derivationIterateOutputJacobian_det       -- J_r(X_r) = +- X_r^(r-1) J_(r-1)(A)
derivationIterateOutputJacobian_det_terminalScaled -- the delta H = U H reduction
derivationIterateOutputJacobian_det_terminalPower  -- its C X^q form, terminal factor q C X^(q-1)
cascadeOutputJacobian                     -- the output-jet Jacobian at depth m
cascadeOutputJacobian_det_succ            -- one level of the flag, with the exact cofactor sign
cascadeOutputJacobian_det_ne_zero         -- the induction: triangular flag + nonzero diagonal
cascadeOutputJacobian_det_ne_zero_of_power -- the diagonal in the pure-power form q_k C_k X_k^(q_k-1)
algebraicIndependent_cascadeOutput        -- the first m+2 time iterates are independent over C
algebraicIndependent_cascadeOutput_of_power -- every positive exponent costs exactly one jet
scalarDifferentialPolynomial_vars_subset_range -- order <= n uses only the first n+1 jets
differentialPolynomialEvalOver_ne_zero_of_algebraicIndependent_jets -- independent jets forbid a
                                                                   -- relation of order <= n
cascadeOutput_no_low_order_relation       -- a depth-(m+2) power cascade has no ADE of order <= m+1
not_algebraicIndependent_of_trdeg_le      -- n+1 elements of a trdeg-n field are dependent
exists_scalarDifferentialRelation_of_trdeg_le -- a bounded state field supplies an ADE of order <= n
isLeast_scalarDifferentialOrder           -- the least ADE order is exactly the state count
HasLogScaleExponent                       -- log ||f|| / log rho -> a, the weight of a term
isLittleO_of_hasLogScaleExponent_lt       -- a strictly smaller weight is negligible
not_eventually_sum_eq_zero_of_unique_max  -- a unique maximal weight cannot be cancelled
HasLogScaleExponent.mul, .pow             -- weights add and scale, giving deg a + c p
exists_ne_zero_isRoot_of_one_lt_card_support -- the edge polynomial has a nonzero root
EntireCoeffs, maxTerm, centralIndex       -- the two Wiman--Valiron quantities mu(r), nu(r)
exists_maxTerm_eq                         -- the maximum term is attained
centralIndex_mem, le_centralIndex         -- nu(r) is the largest attaining index
maxTerm_mono, centralIndex_mono           -- both are nondecreasing in the radius
entireCoeffs_coeff_of_radius_eq_top       -- an entire function satisfies the decay hypothesis
mul_pow_le_maxTerm, maxTerm_le_mul_pow    -- mu(r)(s/r)^nu(r) <= mu(s) <= mu(r)(s/r)^nu(s)
centralIndex_le_log_maxTerm               -- nu(r) <= log mu(e r)
log_maxTerm_le_centralIndex_mul_log       -- log mu(r) <= log mu(1) + nu(r) log r
summable_term, coeffSum                   -- the majorant S(r) = sum ||a_n|| r^n
maxTerm_le_coeffSum                       -- mu(r) <= S(r)
coeffSum_le_two_mul_maxTerm               -- S(r) <= 2 mu(2r)
taylorCoeff_norm_mul_pow_le               -- Cauchy's estimate in term form
maxTerm_le_of_forall_mem_sphere_norm_le   -- mu(r) <= M(r)
tendsto_maxTerm_atTop                     -- a nonconstant coefficient sequence sends mu to infinity
centralIndex_le_rpow_of_log_maxTerm_le_rpow -- log mu(r) <= r^sigma  ==>  nu(r) <= r^sigma'
log_maxTerm_le_rpow_of_centralIndex_le_rpow -- nu(r) <= r^sigma  ==>  log mu(r) <= r^sigma'
term_le_maxTerm_mul_pow_of_centralIndex_le -- above nu(s): term <= mu(r) (r/s)^excess
term_le_maxTerm_mul_pow_of_le_centralIndex -- below nu(t): term <= mu(r) (t/r)^deficit
tsum_upper_tail_le                        -- the upper tail sums to mu(r)(r/s)/(1-r/s)
sum_lower_tail_le                         -- the lower tail sums to mu(r)(t/r)/(1-t/r)
coeffSum_le_window_add_tails              -- the central window carries everything, up to those two
borel_growth                              -- the exceptional set has Lebesgue measure at most 2
exists_ge_lt_two_mul                      -- hence good radii exist beyond every bound
exists_ge_lt_two_mul_scaled               -- the same with the multiplicative step 1 + 1/T(r)
exists_finset_maxTerm_eq_sup'             -- on a compact positive interval mu is a finite max
continuousOn_maxTerm                      -- hence mu is continuous on (0, infinity)
logMaxTermMajorant                        -- the continuous monotone majorant 1 + log mu
exists_ge_borel_maxTerm                   -- good radii for the maximum term, from Borel
centralIndex_le_of_borel_maxTerm          -- at those radii, nu(r) <= 2 (1 + log mu(r))^2
entireCoeffs_mul_index                    -- the derivative coefficients n a_n are again entire
maxTerm_mul_index_le                      -- mu'(r) <= mu(r) (nu(s) + geometric constant)
summable_index_deviation                  -- the deviation series sum |n - k| ||a_n|| r^n converges
sum_window_index_deviation_le             -- inside the window the deviation is the window width
tsum_index_deviation_le                   -- the complete deviation estimate, window plus two tails
ofScalars_radius_eq_top                   -- an entire coefficient sequence has infinite radius
coeffFun, differentiable_coeffFun         -- its sum is an entire function
norm_coeffFun_le                          -- dominated by the majorant S(|z|)
hasDerivAt_coeffFun                       -- and is differentiated term by term
mul_deriv_coeffFun_eq                     -- z f'(z) = sum n a_n z^n
mul_deriv_sub_eq_tsum                     -- z f'(z) - k f(z) = sum (n - k) a_n z^n
norm_mul_deriv_sub_le                     -- bounded by the deviation series
sum_window_le_card_mul_maxTerm            -- the window sum is at most its count times mu(r)
norm_mul_logDeriv_sub_centralIndex_le     -- the Wiman--Valiron logarithmic-derivative estimate
tsum_index_deviation_le_of_window_le      -- the estimate with the window bound left abstract
tsum_index_deviation_le_maxTerm           -- window bounded by its count: everything is mu(r) times
norm_mul_logDeriv_sub_le_of_deviation_le  -- hence a coefficient-free remainder
convexOn_log_maxTerm_exp                  -- log mu is convex in log r
term_le_maxTerm_mul_exp_of_centralIndex_le -- terms fall off like exp(-j delta/2) above nu(r(1+d))
term_le_maxTerm_mul_exp_of_le_centralIndex -- and below nu(r/(1+d))
log_maxTerm_exp_sub_le_centralIndex_mul   -- the growth law in logarithmic coordinates
centralIndex_mul_le_log_maxTerm_exp_sub
centralIndex_between_log_increments       -- nu(e^v) sits between adjacent increments of log mu
exists_increment_le_average               -- telescoping pigeonhole on a chain
exists_small_centralIndex_increment       -- a radius across which nu barely moves
coeffSum_le_maxTerm_mul_centralIndex      -- S(r) <= mu(r)(nu(s)+1+(r/s)/(1-r/s))
term_le_central_term                      -- every term is dominated by the central one
norm_normalised_coeff_le_one              -- so the normalised coefficients have modulus <= 1
coeffFun_eq_central_term_mul_tsum         -- f(z) = a_nu z^nu times a normalised series
coeffFun_eq_term_mul_tsum                 -- the same at any index with a nonzero coefficient
normalised_coeff_scale                    -- scaling by zeta multiplies the n-th one by zeta^(n-k)
coeffFun_scale_eq_tsum                    -- hence the local expansion in the scaling variable
tsum_alignment_defect                     -- sum of moduli minus modulus of sum = total misalignment
alignment_defect_le                       -- so a small defect forces every term to be aligned
sq_im_conj_mul_le                         -- transverse component squared <= 2||c|| times defect
norm_sub_re_mul_eq, norm_sub_re_mul_sq_le -- and the same in geometric form
sum_weighted_sqrt_sq_le                   -- Cauchy--Schwarz against square roots
norm_weighted_sum_sub_le                  -- the weighted sum, minus a real multiple of u
exists_unit_tsum_normalised_alignment_defect -- total misalignment = (S(r) - |f(z)|) / mu(r)
exists_unit_tsum_normalised_defect_le     -- hence the defect is at most nu(s) + C(r/s)
norm_normalised_transverse_sq_le          -- so every transverse part is at most sqrt(2 D)
normalisedCoeff                           -- the coefficients normalised by the central term
norm_weighted_window_sub_le               -- the weighted window sum, with l^2 weights
hasDerivAt_normSq_circlePath              -- d/dt |f(z e^(it))|^2 = -2 Im(conj f . z f')
im_conj_mul_eq_zero_of_isLocalMax         -- so at a circle maximum that pairing is real
im_mul_deriv_div_eq_zero_of_isLocalMax    -- hence z f'(z)/f(z) is real there
hasDerivAt_coeffSum                       -- the majorant is differentiated term by term
mul_deriv_coeffSum_eq                     -- r S'(r) = sum n ||a_n|| r^n
tsum_index_sub_mul_term                   -- the first moment: r S'(r) - k S(r)
exp_tsum_mul_le_tsum_mul_exp              -- discrete Jensen for the exponential
meanIndex                                 -- Lambda(r) = r S'(r) / S(r)
meanIndex_mul_log_le_log_coeffSum_sub     -- Lambda(r) log(s/r) <= log S(s) - log S(r)
meanIndex_le_slope, slope_le_meanIndex    -- Lambda(r) sits between adjacent slopes of log S
meanIndex_le_centralIndex_add             -- Lambda(r) <= nu(s) + log(nu(s')+C)/log(s/r)
centralIndex_sub_le_meanIndex             -- Lambda(r) >= nu(t) - log(nu(r)+C)/log(r/t)
abs_meanIndex_sub_centralIndex_le         -- |Lambda(r) - nu(r)| <= window width + two logs
tsum_index_sub_centralIndex_mul_normalised_norm -- (S/mu)(Lambda - nu) as a normalised first moment
coeffSum_le_one_add_defect_mul_norm       -- S <= (1 + D) |f(z)|, not (nu + C) |f(z)|
summable_index_deviation_normalised       -- the weighted normalised series converges absolutely
tsum_index_weighted_re_eq                 -- weighted projection = mean-mode gap - weighted defect
mul_logDeriv_sub_centralIndex_eq_div      -- z f'/f - nu = (weighted normalised) / (normalised)
norm_eq_abs_re_of_im_eq_zero              -- a real complex number has norm |Re|
div_ofReal_mul_unit                       -- dividing by M u is conjugating by u and scaling by M
norm_mul_logDeriv_sub_centralIndex_eq     -- |z f'/f - nu| = |weighted projection| / ||W||
tsum_normalised_defect_eq                 -- total misalignment = S/mu - ||sum c_n||
abs_tsum_index_weighted_re_le             -- numerator <= (S/mu)|Lambda - nu| + E
norm_mul_logDeriv_sub_centralIndex_le_meanIndex -- the Wiman--Valiron estimate, assembled
tsum_index_weighted_defect_le             -- E <= 2 * the coefficient-free deviation bound
tsum_normalised_defect_le_centralIndex    -- D <= nu(s) + (r/s)/(1-r/s), for the value's direction
norm_mul_logDeriv_sub_centralIndex_le_explicit -- the estimate with both remainders explicit
sum_lower_tail_weighted_le                -- the sharp weighted lower tail, window width not nu(r)
```

```text
| z f'(z)/f(z) - nu(r) |  <=  (1 + D) |Lambda(r) - nu(r)|  +  E
```

at a point of the circle where the function reaches the maximum term and the modulus is critical
along the circle, `D` bounding the total misalignment and `E` the weighted one.

That is an **identity**, not an estimate: at a maximum of the modulus along the circle the deviation
from the central index is exactly the weighted sum of the projections of the normalised coefficients,
divided by the norm of their sum.  Combined with the weighted-projection split it separates into the
mean-minus-mode gap and the weighted misalignment, both of which are already bounded.

`Lambda(r)` is therefore sandwiched by the difference quotients of `log S` on either side, exactly as
`nu(r)` is sandwiched by those of `log mu`.  Since `mu <= S <= mu (nu + C)`, the two sandwiches
overlap up to `log(nu+C)/log(s/r)`, which is what bounds `Lambda - nu`.

So the mean index now satisfies the same lower growth law as the modal index does for the maximum
term.  Comparing the two against the sandwich `mu <= S <= mu (nu + C)` is what bounds their
difference.

So the open quantity has a name and a formula: the deviation of the mean index
`Lambda(r) = r S'(r) / S(r)` from the modal index `nu(r)`, since
`sum (n - nu) ||a_n|| r^n = S(r) (Lambda(r) - nu(r))`.

The assembled bound over a window `F` with weights `w` is

```text
|| sum_F w_n c_n  -  (real) u ||  <=  sqrt 2 * sqrt( sum_F w_n^2 ) * sqrt D,
```

with `D <= nu(s) + C`.  Taking `w_n = n - nu` over a window of half-width `W` this is
`O(W^(3/2) sqrt(nu))`, against the trivial `O(W^2)` -- the square-root gain that the
absolute-value route could not produce.

The bridge is now explicit: the total misalignment of the normalised coefficients equals
`(S(r) - |f(z)|) / mu(r)`.  Every quantity on the right is already controlled -- `S(r)` by
`coeffSum_le_maxTerm_mul_centralIndex`, and `|f(z)|` from below by `mu(r)` at a maximum-modulus
point -- so the defect is bounded by the central index, and the alignment machinery converts that
into the transverse bound the estimate needs.

The alignment is *quadratic*: a term whose misalignment is `d` sits within `sqrt(2||c|| d)` of a
nonnegative multiple of the direction of the sum.  That square root is where the gain over the
absolute-value bound comes from -- the transverse parts, which are what the weighted sum
`sum (n - nu) c_n` sees, are of order `sqrt(d)` rather than of order one.

With this the three quantities are pinned to each other: `mu(r) <= M(r) <= S(r) <= mu(r)(nu(s)+C)`,
so the maximum modulus exceeds the maximum term by at most a factor linear in the central index.

The final form is coefficient-free.  With the window bounded by its term count, the deviation is
`mu(r)` times

```text
B = (nu(s)-nu(t)) (nu(s)+1-nu(t)) + nu(r) (t/r)/(1-t/r) + (nu(s)+1) C(r/s),
```

and the `mu(r)` cancels against `|f(z)| >= mu(r)`, leaving `| z f'(z)/f(z) - nu(r) | <= B` with `B`
depending only on the three central indices and the two radius ratios.

With `norm_mul_deriv_sub_le` the coefficient estimate becomes a statement about the function:
combining it with `tsum_index_deviation_le` at `k = nu(r)` bounds `|z f'(z) - nu(r) f(z)|` by the
window width times the majorant plus two multiples of the maximum term.  Dividing by `f(z)` at a
maximum-modulus point -- where `|f(z)| = M(r) >= mu(r)` -- is the Wiman--Valiron estimate.

`tsum_index_deviation_le` is the coefficient-side Wiman--Valiron estimate in full:

```text
sum_n |n - nu(r)| ||a_n|| r^n
  <= (nu(s) - nu(t)) S(r)  +  nu(r) mu(r) (t/r)/(1-t/r)  +  mu(r) (nu(s)+1) C(r/s)
```

with `C(q) = sum_j (1+j) q^(j+1)` depending only on the radius ratio.  Every term on the right is
either the window width or a fixed multiple of the maximum term, so choosing `t` and `s` at a
Borel-good radius is exactly what makes the whole deviation `o(nu(r))` -- and `z f'(z) - nu(r) f(z)`
is the sum whose terms this bounds.

The last two open the local analysis: `z f'(z) = sum n a_n z^n`, so everything proved for `a` applies
verbatim to `n a_n`, and the extra factor `n` costs only the central index plus a constant fixed by
the radius ratio -- beyond the window the geometric decay beats the linear growth of `n`.

Continuity is not cosmetic: the Borel growth lemma in the corpus requires a **continuous** `T`, and
the central index `nu` is a step function, so the growth lemma can only be applied to `log mu` and
then transferred to `nu` through the two-sided growth law.  `continuousOn_maxTerm` is what makes that
route available.

`coeffSum_le_window_add_tails` is the quantitative form of "the central terms dominate": for any
`t < r < s` the whole majorant at radius `r` is the sum over the window `[nu(t), nu(s)]` plus two
geometric remainders, each a fixed multiple of `mu(r)` determined only by the radius ratios.  The
coefficients cancel out of both remainders, which is why the window can be narrowed by moving `t` and
`s` towards `r` -- the mechanism Wiman--Valiron converts into `f'(z)/f(z) ~ nu(r)/z`.

The last two are the order identity `limsup log nu(r)/log r = limsup log log mu(r)/log r` in the form
that avoids every `limsup` junk value: each eventual power bound on one quantity gives an eventual
power bound on the other at any strictly larger exponent, so the two infima of dominating exponents
coincide.  This is exactly what "choose Wiman--Valiron radii on which `log nu(r)/log r -> rho`"
consumes.

The three inequalities `mu(r) <= M(r) <= S(r) <= 2 mu(2r)` sandwich the maximum modulus between the
maximum term at `r` and at `2r`.  Since `log(2r)/log r -> 1`, the function, its majorant and its
maximum term all have the same order of growth, so the order-transfer inequalities above are
inequalities about `rho(f)` itself.

The pair `mu(r)(s/r)^nu(r) <= mu(s) <= mu(r)(s/r)^nu(s)` is the discrete form of
`log mu(s) - log mu(r) = int_r^s nu(t) dt/t`, obtained directly from the two maximality inequalities
with no integration theory.  Specialising to `(r, e r)` and to `(1, r)` gives the two order-transfer
inequalities, which are exactly the two halves of `limsup log nu(r)/log r = limsup log log mu(r)/log r`
-- the identity the card uses to select its Wiman--Valiron radii.

The two halves meet in `isLeast_scalarDifferentialOrder`: algebraic independence of the first `m+1`
jets and a state field of transcendence degree at most `m+1` make `m+1` the **least** order of a
nonzero algebraic differential equation for the output.  That is the card's `ord_DA(F_n) = n` as an
identity of natural numbers, with the two analytic inputs (positive Wiman exponents, state
independence) isolated as hypotheses.

The abstract form makes the mechanism explicit.  Over any field that is a `C`-algebra, with a time
derivation `delta`, coordinate derivations `P_k`, and outputs `Y_k` linked by

`delta Y_(k+1) = Y_k Y_(k+1)`,

only two hypotheses are used: **triangularity**, `P_k` kills every jet of every lower output, and a
**nonvanishing diagonal**, `P_k Y_k != 0`.  In the power form `Y_(k+1) = C_k X_k^(q_k)` the diagonal
entry is exactly `q_k C_k X_k^(q_k-1)`, so `q_k = 0` is the one and only wall — the magnitude of
`q_k` never enters.  This is the quantization claim of the card, proved in Lean at the algebraic
level.

### Reduction I: the two algebraic/asymptotic steps are formalized

The audit-closure paragraph of Reduction I has two steps that do not need Wiman--Valiron at all, and
both are now unconditional in Lean.

*The maximal face is an edge, not a vertex.*  Measure every top-symbol monomial on the logarithmic
scale set by the radius: `HasLogScaleExponent l rho f a` says `log ||f|| / log rho -> a` along the
chosen filter, and `HasLogScaleExponent.mul`/`.pow` make the weight of `a_(b,c)(U) T^c` equal
`deg a_(b,c) + c p` exactly as the card computes it.  The card's argument -- a fixed positive gap
between the largest weight and the rest cannot be erased by the `r^(o(1))` factors -- is
`isLittleO_of_hasLogScaleExponent_lt`, whose proof uses only the gap, and
`not_eventually_sum_eq_zero_of_unique_max` states the conclusion directly: a finite sum of measured
terms that vanishes along the filter cannot have a strict maximum.  This holds for an arbitrary
filter, so it applies verbatim to a sequence of Wiman points without any phase-convergence
assumption.

*The edge polynomial has a nonzero root.*  `exists_ne_zero_isRoot_of_one_lt_card_support`: a complex
polynomial with at least two nonzero coefficients factors as `X^m q` with `q(0) != 0` and
`deg q >= 1`, so a root of `q` is a nonzero root of the whole polynomial.

### What Lean does not yet carry

**Superseded on 2026-08-04 — see the log entries of that date.**  Four of the five items below are
now formalized or bypassed; the list is kept for the record with its current status.

- ~~Wiman--Valiron asymptotics and the central index~~ — **built**, up to and including the
  `o(nu)` defect (`WimanValironSmallDefect`) and the top-symbol reduction
  (`TopSymbolReduction`, `TopSymbolWimanPlace`).
- Goldberg's finite-order theorem and Strelitz's positive-order theorem — **still absent**, but
  Goldberg is *no longer needed* for the top-symbol reduction: the selection window forces
  `nu^d = o(M(r))` directly.  What they are still needed for is the identification of the Newton
  slope with `rho - 1`.
- ~~Newton--Puiseux places at `U = infinity`~~ — **bypassed**.  The place is used only to put `f'`
  over a root of the top symbol, and over `C` that follows from factorisation
  (`RootProximity`, `WimanPlaceRoot`).  Mathlib has no Puiseux series, so building a branch was the
  expensive way to get a cheap consequence.
- Clunie--Steinmetz composition-growth separation — **the separation itself is still external**, but
  everything the induction does with it is built: the pointwise root estimate
  (`AlgebraicRootGrowth`), the grouping by the dependent state, the coefficient weights, and the
  contradiction (`MultivariateRelationGrouping`).
- ~~Nevanlinna characteristic and the algebraic-function root estimate~~ — **available**: the
  characteristic is in mathlib, the entire-function specialization and the arithmetic are in the
  corpus, and the root estimate now exists in the pointwise form that integrates without
  Poisson--Jensen.

Reduction I and the Clunie induction still enter the Lean capstone as the explicit hypotheses
`hq : forall k, 0 < q k` and the triangularity package; what has changed is that those hypotheses are
now supplied by proved theorems rather than by unformalized analysis, except for the two named
external inputs (Goldberg/Strelitz exponents, Clunie--Steinmetz separation).

## Primary references checked

1. A. A. Goldberg, finite-order theorem for meromorphic solutions of first-order algebraic differential equations.
2. W. K. Hayman, Wiman--Valiron growth methods and the general ADE growth conjecture.
3. L.-W. Liao and C.-C. Yang, *On the growth and factorization of entire solutions of algebraic differential equations*, Ann. Acad. Sci. Fenn. Math. 25 (2000), 73--84.
4. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
5. A. Isidori, A. J. Krener, C. Gori-Giorgi, and S. Monaco, *The Observability of Cascade Connected Nonlinear Systems*, IFAC Proceedings Volumes 14 (1981), 337--342.
6. G. M. Reinhart, *Schanuel Functions and Algebraic Differential Equations*, PhD dissertation, University of Illinois (1993).
7. R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia, *D-Algebraic Functions*, J. Symbolic Comput. 2023; arXiv:2301.02512.
8. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
9. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95, especially Malmquist's theorem and the Fuchsian differential-field classification.
10. G. M. Reinhart, *On the Order of Algebraic Differential Equations Satisfied by Schanuel Functions*, J. Math. Anal. Appl. 191 (1995), 331--345.
11. B. Teguia Tabuguia, *Arithmetic of D-Algebraic Functions*, J. Symbolic Comput. 126 (2025), 102348.

## Log

- 2026-07-11 -- Created after the autonomous and output-linear Newton-corner theorems. Isolated the nondegenerate Wiman place and the positive monomial observability degeneration as the two mechanisms that may close the complete nonautonomous first-order class.
- 2026-07-11 -- Medalist re-audit withdrew the premature proved label: the state derivation is not homogeneous for the naive Puiseux weight, so monomial observability does not yet imply observability of the full lower-term cascade. The exact open core is a flat finite-jet degeneration or a no-matching theorem.
- 2026-07-11 -- Closed that open core without a generic degeneration: exact Bell-polynomial row reductions remove terminal variables one at a time, and the nested leading determinant acquires a nonzero factor from every `q_i=p_(i+1)+1`. This proves that `q_i=0` is the sharp compression wall and that positive Wiman exponents force full observability.
- 2026-07-11 -- Independent scope and parent audit after the user correction: reconciled the separate whole-HT translation/divisor work, checked Goldberg--Strelitz in the primary Liao--Yang paper, checked Malmquist--Eremenko, Reinhart's Schanuel-order parent, Wang--Sontag, and the 2023/2025 DA arithmetic papers.  Added a phase-free Newton-weight proof and an explicit Clunie induction for state independence.  No exact or stronger parent theorem was located; scientific priority remains provisional rather than asserted.
- 2026-08-03 -- Reduction III formalized.  A corpus re-audit showed the earlier "no reusable
  Jacobian observability theorem" note was stale: both one-step Bell reductions were already built
  and had no consumer.  Added the missing chain, `TerminalPowerCascadeInduction.lean`, which
  iterates them down the triangular flag and proves the output-jet Jacobian nonzero from exactly two
  hypotheses -- triangularity of the coordinate derivations and a nonvanishing diagonal -- with the
  pure-power corollary exhibiting the diagonal as `q_k C_k X_k^(q_k-1)`.  This is the quantization
  statement of the card at the algebraic level: `q_k = 0` is the only wall and the magnitude of
  `q_k` is irrelevant.  The remaining Lean debt is entirely analytic (Wiman--Valiron, Goldberg,
  Strelitz, Newton--Puiseux at infinity, Clunie--Steinmetz), none of which is in mathlib.
- 2026-08-03 -- Added the order lower bound, `ScalarDifferentialOrderLowerBound.lean`.  A scalar
  differential polynomial of order at most `n` is a rename of an honest `n+1`-variable polynomial
  along `i |-> ((), i)`, so algebraic independence of the first `n+1` jets forbids it outright.
  Chained with the cascade induction this gives `cascadeOutput_no_low_order_relation`: a triangular
  power cascade of depth `m+2` satisfies no algebraic differential equation of order at most `m+1`.
  That is the `ord_DA >= n` half of the unit-cost law, unconditional and axiom-clean; the matching
  upper bound needs the separant argument and is the next algebraic target.
- 2026-08-03 -- Added the order upper bound, `ScalarDifferentialOrderUpperBound.lean`.  The separant
  argument is not needed: `n+1` jets inside an intermediate field of transcendence degree `n` are
  algebraically dependent outright, and renaming the resulting relation along `i |-> ((), i)` gives a
  nonzero scalar differential polynomial of order at most `n`.  With the lower bound this yields
  `isLeast_scalarDifferentialOrder` -- the minimal ADE order of the output is exactly the number of
  states.  The algebraic skeleton of the unit-cost law is therefore complete in Lean; what remains is
  entirely the analytic supply of its two hypotheses (positive Wiman exponents from Reduction I, and
  state algebraic independence from Clunie--Steinmetz).
- 2026-08-03 -- Started Reduction I.  `NewtonEdgeNonCancellation.lean` formalizes the two steps of the
  audit-closure paragraph that do not need Wiman--Valiron: the log-scale weight calculus
  (`HasLogScaleExponent`, with weights adding under products and scaling under powers, so a monomial
  `a_(b,c)(U) T^c` carries `deg a_(b,c) + c p`), the no-cancellation theorem -- a finite sum of
  measured terms vanishing along a filter cannot have a strict maximal weight, proved from the gap
  alone and stated for an arbitrary filter so no phase convergence is assumed -- and the fact that a
  complex polynomial with two or more nonzero coefficients has a nonzero root.  What remains of
  Reduction I is the analytic supply of the measured weights (Wiman--Valiron, Goldberg, Strelitz) and
  the Newton--Puiseux lift.
- 2026-08-03 -- Started the Wiman--Valiron foundation, `MaximumTermCentralIndex.lean`.  From the
  decay hypothesis `||a_n|| r^n -> 0` alone: the terms are bounded, the supremum `mu(r)` is attained,
  the set of attaining indices is finite so the central index `nu(r)` is well defined as the largest
  of them, and both `mu` and `nu` are nondecreasing in `r`.  The monotonicity of `nu` is the one step
  with content -- multiplying the two maximality inequalities cancels the coefficients and leaves an
  impossible comparison of powers of `r/s < 1`.  A power series of infinite radius satisfies the
  decay hypothesis, so this applies to every entire function.  Next: convexity of `log mu` in
  `log r`, the integral formula, and the order identity `limsup log nu(r)/log r = rho`.
- 2026-08-03 -- Added the two-sided growth law to `MaximumTermCentralIndex.lean`:
  `mu(r)(s/r)^nu(r) <= mu(s) <= mu(r)(s/r)^nu(s)` for `0 < r <= s`, each side falling straight out of
  one maximality inequality after cancelling `r^m` against `(s/r)^m`.  This is the discrete form of
  `log mu(s) - log mu(r) = int_r^s nu(t) dt/t` and needs no integration theory at all.  Specialising
  to the radii `(r, e r)` gives `nu(r) <= log mu(e r)`, and to `(1, r)` gives
  `log mu(r) <= log mu(1) + nu(r) log r`; these are the two halves of the order identity
  `limsup log nu(r)/log r = limsup log log mu(r)/log r` that the card uses to choose its radii.  What
  is left on this branch is the limsup packaging and the comparison of `mu` with the maximum modulus.
- 2026-08-03 -- Closed the maximum-term/maximum-modulus comparison.  The decay hypothesis already
  forces absolute convergence at every radius (bound each term against the doubled radius by a
  geometric weight), so the majorant `S(r) = sum ||a_n|| r^n` exists and satisfies
  `S(r) <= 2 mu(2r)`; Cauchy's estimate, in the term form `||a_n|| r^n <= C` for any bound `C` on the
  circle, gives `mu(r) <= M(r)`.  The chain `mu(r) <= M(r) <= S(r) <= 2 mu(2r)` makes the order of
  the function, of its majorant and of its maximum term the same, so the two order-transfer
  inequalities are statements about `rho(f)`.  Only the limsup packaging is left on this branch
  before the Wiman--Valiron estimate itself.
- 2026-08-03 -- Packaged the order identity without any `limsup` plumbing.  Stating it as mutual
  transfer of eventual power bounds -- `log mu(r) <= r^sigma` eventually implies `nu(r) <= r^sigma'`
  eventually for every `sigma' > sigma`, and conversely -- makes both directions two-line
  consequences of the growth laws, avoids the junk value of an unbounded `limsup`, and is the exact
  form a radius-selection argument consumes.  The `log r = o(r^eps)` input is mathlib's
  `isLittleO_log_rpow_atTop`.  The `mu`-side of Wiman--Valiron is now complete: existence,
  attainment, monotonicity, the two-sided growth law, the sandwich against the maximum modulus, and
  the order identity.  What remains is the estimate `f'(z_r)/f(z_r) ~ nu(r)/z_r` itself.
- 2026-08-03 -- Added the geometric-decay mechanism behind "the central terms dominate".  Comparing
  the term at radius `r` with the maximum term at a larger radius `s` and then applying the upper
  growth law gives `||a_n|| r^n <= mu(r) (r/s)^(n - nu(s))` for `n >= nu(s)`; the mirror comparison
  with a smaller radius `t` gives `||a_n|| r^n <= mu(r) (t/r)^(nu(t) - n)` for `n <= nu(t)`.  Both
  ratios are below one, so the two tails are geometric remainders uniformly in the coefficients; the
  upper one is summed in `tsum_upper_tail_le`.  This is the last purely coefficient-side ingredient
  of Wiman--Valiron; what follows needs the Borel growth lemma and its exceptional set.
- 2026-08-03 -- Closed the coefficient side of Wiman--Valiron with `sum_lower_tail_le` and
  `coeffSum_le_window_add_tails`.  Reflecting the index range turns the lower tail into the same
  geometric series as the upper one, and splitting the majorant twice with
  `Summable.sum_add_tsum_nat_add` gives the window decomposition: for `t < r < s`, the majorant at
  `r` is the sum over `[nu(t), nu(s)]` plus two remainders, each `mu(r)` times a constant depending
  only on the radius ratios.  The coefficients cancel out of both remainders, so the window can be
  narrowed by moving `t` and `s` toward `r`.  Everything that remains on this branch is genuinely
  function-theoretic: the Borel growth lemma with its exceptional set, and the passage from the
  window decomposition to `f'(z)/f(z) ~ nu(r)/z`.
- 2026-08-03 -- The Borel growth lemma turned out to be already in the corpus,
  `HTGeometry/BorelGrowthLemma.lean` (namespace `GaloisForLFunctions.Nevanlinna`), proved by a dyadic
  band decomposition: the exceptional set `{r >= a | 2T(r) <= T(r + 1/T(r))}` has Lebesgue measure at
  most `2`.  I had it listed as an open gate because the earlier corpus searches were run on
  "Wiman", "centralIndex" and "maximum term", none of which appear in it.  Added the two corollaries
  that are what actually gets used -- a set of measure `2` cannot contain a ray, so good radii exist
  beyond every bound (`exists_ge_lt_two_mul`), and the multiplicative form with the step
  `1 + 1/T(r)` obtained in the logarithmic variable.  The exceptional set never has to be described.
- 2026-08-03 -- Proved that the maximum term is continuous on `(0, infinity)`.  On a compact interval
  `[r1, r2]` with `r1 > 0` only finitely many indices can compete: any `n` with
  `||a_n|| r2^n < mu(r1)` is beaten everywhere on the interval by the index attaining `mu(r1)`, and
  the decay hypothesis makes the complementary set finite.  So `mu` is locally the maximum of a fixed
  finite family of monomials and `Continuous.finset_sup'_apply` applies.  This matters because the
  corpus's Borel growth lemma requires a continuous `T` while the central index is a step function --
  the growth lemma has to be applied to `log mu` and transferred to `nu` through the two-sided growth
  law, and continuity is exactly what was missing for that.
- 2026-08-03 -- Connected the Borel growth lemma to the central index.  The lemma cannot be applied to
  `nu` directly -- it is a step function and the corpus lemma requires continuity -- so it is applied
  to the continuous monotone majorant `1 + log mu` (clamped below at a radius where `mu >= 1`), and
  the conclusion is carried to `nu` by the two-sided growth law: at the resulting radii
  `nu(r) log(1 + 1/T(r)) <= log mu(s) - log mu(r) < T(r)` with `T = 1 + log mu`, and
  `log(1+x) >= x/2` on `[0,1]` gives `nu(r) <= 2 T(r)^2`.  The `log(1+x) >= x/(1+x)` step is
  `Real.log_le_sub_one_of_pos` applied to `1/(1+x)`.  This is the selection of Wiman--Valiron radii
  that Reduction I asks for; what is left is the local analysis at a maximum-modulus point.
- 2026-08-03 -- Opened the local analysis.  Since `z f'(z) = sum n a_n z^n`, the whole maximum-term
  theory has to be available for the sequence `n a_n`; `entireCoeffs_mul_index` shows it satisfies
  the same decay hypothesis (the factor `n` is absorbed by the doubled radius, via
  `summable_pow_mul_geometric_of_norm_lt_one`).  `maxTerm_mul_index_le` then bounds its maximum term:
  inside the window the factor is at most `nu(s)`, and beyond it the geometric decay proved earlier
  beats the linear growth of `n`, leaving a constant `sum j (r/s)^j` that depends only on the radius
  ratio.  So `mu'(r) <= mu(r) (nu(s) + C)`, the estimate the logarithmic derivative needs.
- 2026-08-03 -- Set up the index deviation, which is what the logarithmic-derivative estimate
  measures: `z f'(z) - k f(z) = sum (n - k) a_n z^n`, so `f'/f` is close to `k/z` exactly when
  `sum |n - k| ||a_n|| r^n` is small compared with the function.  `summable_index_deviation` shows the
  series converges at every radius (dominate `|n - k|` by `n + k` and use the derivative sequence),
  and `sum_window_index_deviation_le` gives the window estimate: for `t < r < s` both `n` and `nu(r)`
  lie in `[nu(t), nu(s)]`, so inside the window the deviation never exceeds the window width
  `nu(s) - nu(t)`.  The two tails are already geometric by the earlier decay bounds, so the remaining
  step is to choose `t` and `s` at a Borel-good radius and see the window width become `o(nu(r))`.
- 2026-08-03 -- Assembled the complete deviation estimate `tsum_index_deviation_le`.  Splitting the
  series at `nu(s)+1` and again at `nu(t)` gives three pieces: the window, bounded by the width times
  the majorant; the part below `nu(t)`, where `|n - nu(r)| <= nu(r)` and the lower tail bound
  applies; and the part above `nu(s)`, where `|n - nu(r)| <= n <= (nu(s)+1)(1+j)` and the geometric
  decay leaves a constant `sum_j (1+j) q^(j+1)` fixed by the radius ratio.  Every remainder is a
  multiple of `mu(r)`, so the estimate reduces the Wiman--Valiron main theorem to making the window
  width small at a Borel-good radius.
- 2026-08-03 -- Attached the function to the coefficients.  `ofScalars_radius_eq_top` shows the decay
  hypothesis gives infinite radius of convergence (via `radius_eq_top_of_summable_norm`, discarding
  the zeroth term with `summable_nat_add_iff` since `ofScalars_norm_le` only bounds positive
  indices), so `coeffFun a = (ofScalars C a).sum` is entire and `norm_coeffFun_le` bounds it by the
  majorant.  This closes the loop with `entireCoeffs_coeff_of_radius_eq_top` from the other
  direction: entire functions and entire coefficient sequences are now interchangeable, and the
  deviation estimate can be read as a statement about `z f'(z) - nu(r) f(z)` once the termwise
  derivative identity is available.
- 2026-08-03 -- Proved termwise differentiation, `hasDerivAt_coeffFun`.  Mathlib has no lemma giving
  the derivative of a scalar power series away from its centre, so the proof is the Weierstrass
  limit theorem: the partial sums over `Finset` are polynomials with the obvious derivative, and both
  they and their derivatives converge uniformly on each ball `|z| < |z0| + 1` -- the derivative
  majorant `n ||a_n|| R^(n-1)` is summable because `n a_n` is again an entire coefficient sequence --
  so `hasDerivAt_of_tendstoLocallyUniformlyOn` applies.  The remaining assembly is
  `z f'(z) - k f(z) = sum (n-k) a_n z^n` and the norm bound by the deviation series, at which point
  the deviation estimate becomes a statement about the logarithmic derivative.
- 2026-08-03 -- Assembled the logarithmic derivative.  `z f'(z) = sum n a_n z^n` follows from
  termwise differentiation after absorbing `z` into `z^(n-1)` (the `n = 0` term vanishes, so the
  truncated subtraction is harmless), and subtracting `k f(z)` term by term gives
  `z f'(z) - k f(z) = sum (n-k) a_n z^n`.  Its norm is bounded by the deviation series, so combining
  with `tsum_index_deviation_le` at `k = nu(r)` bounds `|z f'(z) - nu(r) f(z)|` by the window width
  times the majorant plus two multiples of `mu(r)`.  What is left is to divide by `f(z)` at a
  maximum-modulus point, where `|f(z)| = M(r) >= mu(r)` makes every remainder a bounded multiple of
  the left side.
- 2026-08-03 -- The Wiman--Valiron logarithmic-derivative estimate is proved with an explicit
  remainder.  At any point of the circle of radius `r` where `|f(z)| >= mu(r)` -- in particular at a
  maximum-modulus point, since `mu(r) <= M(r)` -- dividing the index-deviation identity by `f(z)`
  gives

  ```text
  | z f'(z)/f(z) - nu(r) |
      <= [ (nu(s)-nu(t)) S(r) + nu(r) mu(r) (t/r)/(1-t/r) + mu(r)(nu(s)+1) C(r/s) ] / mu(r)
  ```

  for every `t < r < s`.  Also added `sum_window_le_card_mul_maxTerm`, which bounds the window sum by
  its term count times `mu(r)` -- the alternative to `S(r)` in the first summand, and the one that
  makes the whole remainder a multiple of `mu(r)`.  The only step left is quantitative: choose `t`
  and `s` at a Borel-good radius so that the window width and the two ratios shrink fast enough for
  the right-hand side to be `o(nu(r))`.
- 2026-08-03 -- Made the Wiman--Valiron remainder coefficient-free.  The deviation estimate was
  generalised to take the window bound as a parameter, which recovers the majorant version as a
  corollary and also allows the sharper choice: bounding the window by its term count times `mu(r)`
  makes every one of the three remainders a multiple of `mu(r)`.  That factor then cancels against
  `|f(z)| >= mu(r)`, so at a maximum-modulus point
  `| z f'(z)/f(z) - nu(r) | <= (nu(s)-nu(t))(nu(s)+1-nu(t)) + nu(r)(t/r)/(1-t/r) + (nu(s)+1) C(r/s)`
  -- a bound involving only the three central indices and the two radius ratios.  The remaining task
  is to choose `t` and `s` at a Borel-good radius so that this expression is `o(nu(r))`.
- 2026-08-03 -- Correction to the plan, and the brick it calls for.  The coefficient-free remainder
  proved last time **cannot** be made `o(nu(r))` by any choice of `t < r < s`: the lower-tail term
  `nu(r) (t/r)/(1-t/r)` needs `t/r -> 0`, which drives `nu(t)` far below `nu(r)` and blows up the
  window width, and the window term is quadratic in that width.  The obstruction is real and not a
  matter of tuning: purely geometric decay away from the central index is too weak.  What
  Wiman--Valiron actually uses is the *Gaussian* concentration of the terms near `nu`, which comes
  from second-order information about `mu`.  So the next brick is log-convexity, now proved:
  `convexOn_log_maxTerm_exp` says `u |-> log mu(e^u)` is convex, by interpolating the single term
  that attains `mu` at the intermediate radius -- `||a_N|| e^(Nv) = (||a_N|| e^(Nu))^p (||a_N||
  e^(Nw))^q <= mu(e^u)^p mu(e^w)^q`.  Convexity makes the difference quotients of `log mu` monotone,
  which is exactly what turns the two-sided growth law into concentration.
- 2026-08-03 -- Recast the decay bounds on the exponential scale.  With the enlarged radius
  `r(1+delta)` and the shrunken radius `r/(1+delta)`, the geometric ratio becomes `exp(-delta/2)` per
  step -- using `log(1+x) >= x/2` on `(0,1]`, which is now a named lemma rather than an inline
  computation -- so a term at distance `j` from the corresponding central index is below `mu(r)` by
  `exp(-j delta/2)`.  This is the form the Wiman--Valiron radius choice consumes: the narrower the
  enlargement, the further out the concentration must reach before it bites, and balancing that
  against the growth of `nu` across `[r/(1+delta), r(1+delta)]` is what fixes `delta ~ nu^(-1/2)`.
  Note for the next pass: `MaximumTermCentralIndex.lean` is at 1486 lines and should be split by
  proof phase (coefficients / growth laws / function side) before it grows further.
- 2026-08-03 -- Split the Wiman--Valiron file by proof phase, as flagged last time.
  `MaximumTermCentralIndex.lean` keeps the coefficient theory -- definitions, attainment,
  monotonicity, growth laws, decay, window, deviation, continuity, the Borel bridge, log-convexity --
  and the new `MaximumTermLogarithmicDerivative.lean` carries the function side: infinite radius of
  convergence, differentiability, termwise differentiation, and the logarithmic-derivative estimate.
  Also recast the two-sided growth law in logarithmic coordinates: with `L(u) = log mu(e^u)`,
  `L(v) - L(u) <= nu(e^v)(v-u)` and `nu(e^u)(v-u) <= L(v) - L(u)`, so for `u < v < w` the central
  index `nu(e^v)` sits between the two adjacent difference quotients of `L`.  That is the precise
  sense in which `nu = d log mu / d log r`, and it is the coordinate every Wiman--Valiron estimate is
  written in.
- 2026-08-03 -- Built the substitute for applying Borel to `nu`.  The growth lemma needs a continuous
  majorant and `nu` is a step function, so instead one uses that the increments of a monotone
  function telescope: along `N` steps of a geometric chain of radii, some step raises the central
  index by at most the total rise divided by `N`, and never lowers it.  Recorded because the first
  version of this was wrong in a instructive way -- stated without the monotonicity conjunct, the
  corollary needed none of `EntireCoeffs`, the nonzero coefficient, or `h > 0`, which is the tell
  that it had no content: the pigeonhole alone allows negative increments.  Pairing the average bound
  with `0 <= increment` is what makes it a statement about the central index rather than about
  arbitrary sequences.
- 2026-08-03 -- A no-go for the route, and the last brick the route does yield.  Bounding
  `|z f'(z) - nu f(z)|` by the sum of the absolute values of its terms **cannot** give the
  Wiman--Valiron main estimate.  Even granting the sharpest available concentration -- terms decaying
  like `exp(-j delta/2)` beyond the window, with `delta` small enough that `nu` barely moves across
  it -- the weighted sum `sum_j |j| exp(-j delta/2)` is of order `delta^(-2)`, so the numerator is of
  order `mu(r) nu(r)` while the denominator is only bounded below by `mu(r)`; the quotient is `O(nu)`
  and never `o(nu)`.  Getting `o(nu)` this way would need `M(r)/mu(r) -> infinity`, which is false
  (`f = z^n` has `M = mu`).  The theorem genuinely needs the cancellation in the local expansion
  `f(z_r e^(w/sqrt(nu))) ~ a_nu z_r^nu exp(sqrt(nu) w - w^2/2)`, not a triangle inequality.  What the
  present route does yield, and what is now proved, is the reverse comparison
  `S(r) <= mu(r)(nu(s)+1+(r/s)/(1-r/s))`, closing the chain `mu <= M <= S <= mu (nu + C)`: the three
  growth measures differ by at most a factor linear in the central index.  The remaining Lean gate is
  therefore the local Gaussian expansion, not a sharper term-by-term bound.
- 2026-08-03 -- Opened the local-expansion branch with its normalisation.  Dividing the series by its
  central term `a_nu z^nu` makes every coefficient have modulus at most one -- that is exactly the
  defining property of the central index, `||a_n|| r^n <= mu(r) = ||a_nu|| r^nu` -- with the central
  coefficient equal to one.  So on any circle of radius `r`,
  `f(z) = a_nu z^nu * sum_n (a_n z^n / a_nu z^nu)` with all summands in the closed unit disc.  This
  is the normalised form the Gaussian expansion is carried out in, and it replaces the discarded
  triangle-inequality route: the cancellation the main estimate needs lives in the phases of these
  normalised coefficients, which the absolute-value bound throws away.
- 2026-08-03 -- The local expansion is now in place as an identity.  Scaling the coordinate by `zeta`
  multiplies the `n`-th normalised coefficient by `zeta^(n-k)`, so with `k = nu(r)` and `|zeta|` near
  one the function is its central term times `sum_n c_n zeta^(n-nu)`, where every `c_n` lies in the
  closed unit disc and `c_nu = 1`.  That is the Wiman--Valiron local series, with the phases intact.
  Two of the three lemmas turned out to need no analytic hypothesis at all -- `tsum_mul_left` holds
  unconditionally in a division ring -- so the factorisation and the scaling law are pure algebra;
  what the analysis has to supply is only the bound `|c_n| <= 1`, which is the defining property of
  the central index and is already proved.
- 2026-08-03 -- Isolated the mechanism the discarded route was destroying, as a standalone general
  lemma: `TriangleInequalityDefect.lean`.  For any summable complex family whose sum is `A u` with
  `u` a unit,

  ```text
  sum_i ||c_i||  -  A  =  sum_i ( ||c_i|| - Re(conj(u) c_i) ),
  ```

  every summand on the right being nonnegative.  So the defect in the triangle inequality *is* the
  total misalignment, and each individual misalignment is bounded by the defect.  This is what
  converts maximality into cancellation: at a maximum-modulus point the normalised coefficients have
  the largest possible sum, so their phases must almost all agree, and it is that agreement -- not
  any bound on `|c_n|` -- that makes the weighted sum `sum (n - nu) c_n` small.  The lemma is stated
  for an arbitrary index type and has no analytic content, so it is reusable well beyond this card.
- 2026-08-03 -- Made the alignment quantitative, and quadratic.  Writing `w = conj(u) c`, the
  identity `||w||^2 = w.re^2 + w.im^2` turns the misalignment `d = ||c|| - w.re` into a bound on the
  transverse part: `w.im^2 = (||c||-w.re)(||c||+w.re) <= 2 ||c|| d`, and geometrically
  `|| c - w.re * u || = |w.im|`, so each term lies within `sqrt(2||c|| d)` of a nonnegative multiple
  of `u`.  The square root is the whole point: the weighted sum `sum (n-nu) c_n` only sees the
  transverse components, and they are of order `sqrt(d)` rather than of order one, which is exactly
  the gain the absolute-value route could not produce.
- 2026-08-03 -- Completed the aggregation step.  A weighted sum of a nearly aligned family differs
  from a real multiple of the common direction by at most the weighted sum of the transverse parts,
  and Cauchy--Schwarz against the square roots turns that into
  `sqrt( sum w_i^2 ) * sqrt( total defect )`.  The weights enter only through their `l^2` norm, so
  in the Wiman--Valiron application with `w_n = n - nu` over a window of half-width `W` the factor is
  `W^(3/2)` against `sqrt(D)` rather than `W^2` against `D` -- the whole content of the local
  expansion, now available as three general lemmas with no analytic hypotheses.  With
  `TriangleInequalityDefect.lean` complete, the remaining work on this branch is arithmetic: choose
  the window and the radius so that the total defect at a maximum-modulus point is small enough.
- 2026-08-03 -- Joined the two toolkits.  Applying the alignment identity to the normalised
  coefficients `c_n = a_n z^n / (a_nu z^nu)` gives
  `sum_n ( ||c_n|| - Re(conj(u) c_n) ) = (S(r) - |f(z)|) / mu(r)`, with `u` the unit in the direction
  of `f(z)`: the total misalignment of the phases is exactly the gap between the majorant and the
  actual value, in units of the maximum term.  That is the quantity the whole local-expansion branch
  was built to produce, and both of its ingredients are already bounded -- `S(r) <= mu(r)(nu(s)+C)`
  from the coefficient side, and `|f(z)| >= mu(r)` at a maximum-modulus point.  The remaining work is
  to combine this with the weighted aggregation and pick the window.
- 2026-08-03 -- Bounded the defect and its per-term consequence.  At a point where the function
  reaches the maximum term, `(S(r) - |f(z)|)/mu(r) <= nu(s) + (r/s)/(1-r/s)`, using the majorant
  bound from the coefficient side and `|f(z)| >= mu(r)`; so the total misalignment of the normalised
  phases is at most the central index plus a constant.  Feeding that into the quadratic transverse
  bound, and using `||c_n|| <= 1`, every normalised coefficient lies within `sqrt(2 D)` of a
  nonnegative multiple of the common direction.  Both halves of the local expansion are now
  quantitative; what is left is to assemble them with the weighted aggregation over a window.
- 2026-08-03 -- Assembled the weighted window bound, which is the local expansion in usable form:
  over any finite window, the weighted sum of the normalised coefficients differs from a real
  multiple of the common direction by at most `sqrt 2 * sqrt(sum w_n^2) * sqrt D`, where `D` is the
  total misalignment.  The chain is per-term transverse bound (`sqrt(2 d_n)`, using `||c_n|| <= 1`),
  then Cauchy--Schwarz against the square roots, then the tail bound `sum_F d_n <= D`.  Introduced
  `normalisedCoeff` as a definition so the statements are readable.  With `w_n = n - nu` over a
  window of half-width `W` this reads `O(W^(3/2) sqrt(nu))` where the naive bound gives `O(W^2)`;
  that square-root gain is exactly what the discarded absolute-value route lacked.
- 2026-08-03 -- Supplied the input that no coefficient estimate can give: criticality.  Differentiating
  `t |-> |f(z e^(it))|^2` gives `-2 Im(conj(f(z)) z f'(z))`, so at a local maximum of the modulus
  along the circle that pairing is real, and therefore `z f'(z)/f(z)` is real.  This is what removes
  the component of the weighted sum along the direction of the value -- the part the alignment
  estimates do *not* control -- leaving only the transverse part, which they do.  New module
  `CircleMaximumCriticality.lean`.  Three mechanical traps, worth recording: `comp_hasDerivAt` is not
  a projection on `HasDerivAt` (use `HasDerivAt.scomp`), `HasDerivAt.pow` builds the `Pi` power and
  the pointwise one is `HasDerivAt.fun_pow`, and `convert ... using 1` on a `HasDerivAt` goal spawns
  instance-equality subgoals -- normalise the derivative value in the hypothesis with `norm_num at h`
  and close with plain `exact`.
- 2026-08-03 -- Located precisely what is left, and built its prerequisite.  Combining the two halves:
  at a circle maximum `z f'(z)/f(z) - nu` is real and equals `Re(conj(u) V)/||W||` where
  `V = sum (n-nu) c_n` and `W = sum c_n`; and since `Re(conj(u) c_n) = ||c_n|| - d_n` this splits as

  ```text
  Re(conj(u) V)  =  sum_n (n - nu) ||c_n||   -   sum_n (n - nu) d_n .
  ```

  The second term is exactly what the alignment machinery bounds, by `sqrt(sum w^2) sqrt D`.  The
  first is a purely real quantity -- the first moment of the modulus profile about its peak, equal to
  `(r S'(r) - nu(r) S(r)) / mu(r)` -- and it is **not** controlled by anything proved so far; it is
  the last genuinely open point.  Note the transverse estimates alone cannot reach it: at a circle
  maximum the transverse part of `V` vanishes identically, so the whole deviation sits in the
  longitudinal direction.  Built the prerequisite for attacking it, `hasDerivAt_coeffSum`: the
  majorant is differentiated term by term, by the same Weierstrass argument used for the function.
- 2026-08-03 -- Named the open quantity.  `r S'(r) = sum n ||a_n|| r^n` (absorbing `r` into
  `r^(n-1)`, the `n = 0` term vanishing), so the first moment of the modulus profile about any centre
  `k` is `r S'(r) - k S(r)`.  With `k = nu(r)` this is `S(r) (Lambda(r) - nu(r))` where
  `Lambda(r) = r S'(r)/S(r)` is the **mean** index -- the average of `n` against the weights
  `||a_n|| r^n` -- and `nu(r)` is the **modal** index, where those weights peak.  The whole remaining
  gap is that the mean and the mode of the profile are close.  The route to it is Jensen: for
  `q = s/r >= 1`, `S(s)/S(r)` is the weighted average of `q^n`, which is at least `q^Lambda(r)` by
  convexity of `x |-> q^x`, so `Lambda(r) log(s/r) <= log S(s) - log S(r)`; the mirror inequality
  bounds `Lambda` below, and the sandwich `mu <= S <= mu (nu + C)` converts both into `nu` up to a
  logarithmic term.  Both identities proved here are pure algebra -- neither needs the decay
  hypothesis -- which is a good sign that the remaining content is exactly the Jensen step.
- 2026-08-03 -- Proved the Jensen step, in the general form it is needed in:
  `exp(sum p_i x_i) <= sum p_i exp(x_i)` for nonnegative weights summing to one.  No convexity API is
  involved -- shift by the mean `m`, apply `1 + t <= exp t` to each `x_i - m`, and note that the
  linear lower bound sums to exactly `1`, so the whole thing collapses to `exp m * 1 <= exp m * (...)`.
  New module `DiscreteJensenExp.lean`, stated for an arbitrary index type with explicit summability
  hypotheses, so it is reusable anywhere a discrete weighting appears.  Instantiated with
  `p_n = ||a_n|| r^n / S(r)` and `x_n = n log(s/r)` it will give
  `Lambda(r) log(s/r) <= log S(s) - log S(r)`, the growth law for the mean index matching the one the
  modal index already satisfies.
- 2026-08-03 -- Instantiated Jensen: `meanIndex_mul_log_le_log_coeffSum_sub` gives
  `Lambda(r) log(s/r) <= log S(s) - log S(r)`, the growth law for the mean index.  The weights are
  `p_n = ||a_n|| r^n / S(r)` and the exponents `x_n = n log(s/r)`, so `sum p_n x_n = Lambda(r) log(s/r)`
  and `sum p_n exp(x_n) = S(s)/S(r)` -- the second because `r^n (s/r)^n = s^n`, which is the only
  computation in the proof.  The mean index now satisfies exactly the law the modal index satisfies
  for `mu`, so the two can be compared through the sandwich `mu <= S <= mu (nu + C)`: that comparison
  is the remaining step, and it is now a matter of combining growth laws rather than of new
  mechanism.
- 2026-08-03 -- Two-sided bound on the mean index.  The Jensen inequality needed no ordering of the
  radii at all -- only `s > 0` -- so weakening its hypothesis from `r <= s` to `0 < s` immediately
  gives both directions: for `s > r` divide by `log(s/r) > 0`, and for `t < r` use
  `log(t/r) = -log(r/t)` and divide by the positive `log(r/t)`, which flips the inequality.  So
  `Lambda(r)` sits between the backward and forward difference quotients of `log S`, exactly as
  `nu(r)` sits between those of `log mu`.  The two sandwiches then overlap up to
  `log(nu+C)/log(s/r)`, coming from `mu <= S <= mu (nu + C)` -- that is the bound on `Lambda - nu`,
  and assembling it is the next step.
- 2026-08-03 -- Bounded the mean index against the modal index on both sides:

  ```text
  nu(t) - log(nu(r)+C)/log(r/t)  <=  Lambda(r)  <=  nu(s) + log(nu(s')+C)/log(s/r).
  ```

  Each side is the mean-index slope bound, with `log S` replaced by `log mu` at the two ends using
  `mu <= S <= mu (nu + C)` and the modal growth law absorbing the difference of `log mu`.  Since
  `nu(t) <= nu(r) <= nu(s)`, this bounds `|Lambda(r) - nu(r)|` by the window width plus two
  logarithmic terms.  The ratio `S/mu` may be as large as `nu`, but only its **logarithm** appears,
  which is the whole reason the mean and the mode are close: a factor of `nu` in the majorant costs
  only `log nu` in the index.  What remains is arithmetic -- pick the radii so that the window width
  and the two logarithmic terms are `o(nu)`.
- 2026-08-03 -- Optimisation pass over the Wiman--Valiron modules.  I had been adding
  `set_option maxHeartbeats 1000000 in` defensively before long proofs.  Stripping all 18 of them and
  recompiling showed that exactly **one** was needed (`tsum_upper_tail_le`), and that one at 400000
  rather than 1000000.  The other 17 were pure noise -- they hide genuine slowness and cost nothing
  to keep, so they had accumulated silently.  `MaximumTermCentralIndex.lean` now compiles in ~29s and
  `MaximumTermLogarithmicDerivative.lean` in ~12s.  Method worth reusing: remove every bump at once,
  compile once, and re-add only at the line the timeout names -- cascading "unknown constant" errors
  downstream of the real failure are not additional sites.
- 2026-08-03 -- Combined the two one-sided bounds into
  `|Lambda(r) - nu(r)| <= (nu(s) - nu(t)) + log(nu(s')+C)/log(s/r) + log(nu(r)+C)/log(r/t)`.  Both
  corrections are nonnegative and the central index is monotone, so each direction of the absolute
  value follows from one of the one-sided bounds by discarding the other correction.  The mean index
  and the modal index are therefore separated by the window width plus two logarithms -- no longer by
  anything of size `nu`.
- 2026-08-03 -- Split the mean-index material into `MeanIndexComparison.lean` (base module back under
  the 1500-line guideline at 1483 lines) and added the identity
  `sum (n - nu) ||c_n|| = (S/mu)(Lambda - nu)` connecting the mean-mode gap to the normalised
  coefficients.

  **A limitation of this route, recorded so it is not re-attempted.**  At a circle maximum the
  deviation is `Re(conj(u) V)/||W||` with `Re(conj(u) V) = sum (n-nu) Re(conj(u) c_n)`, and the
  temptation is to split `Re(conj(u) c_n) = ||c_n|| - d_n` and bound the two pieces separately.  That
  fails: the first piece is `(S/mu)(Lambda - nu)`, and after dividing by `||W|| = M/mu` it is
  `(S/M)(Lambda - nu)` with `S/M` as large as `nu`, so one would need `Lambda - nu = o(1)` rather
  than the true `O(sqrt(nu))`.  The split is lossy because `Re(conj(u) c_n)` can be negative and the
  two pieces cancel each other; bounding them separately discards exactly that cancellation.  The
  weighted sum has to be estimated with the phases intact -- which is what the local expansion and
  the transverse bounds are for.
- 2026-08-03 -- **Correction to the previous entry.**  I recorded that splitting
  `Re(conj(u) c_n) = ||c_n|| - d_n` is unusable because `S/M` can be as large as `nu`.  That bound is
  far too crude.  From the alignment identity `S - |f(z)| = mu * (total misalignment)`, together with
  `mu <= |f(z)|`, one gets

  ```text
  S(r)  <=  (1 + D) |f(z)| ,
  ```

  so `S/M <= 1 + D` where `D` is the total misalignment -- **not** `nu + C`.  The split is therefore
  usable after all, and gives `|z f'/f - nu| <= (1+D)|Lambda - nu| + sum |n-nu| d_n`.  The sanity
  check is `f = exp`: on the positive real axis every coefficient is positive, so the phases align
  exactly, `D = 0`, `S = M`, and the bound collapses to `|Lambda(r) - nu(r)| = |r - floor(r)| <= 1`.
  The whole estimate is then driven by how small the misalignment is at the maximum-modulus point,
  which is the right question -- the previous entry pointed at the wrong obstruction.
- 2026-08-03 -- Split the weighted projection:
  `sum (n-nu) Re(conj(u) c_n) = (S/mu)(Lambda - nu) - sum (n-nu) d_n`.  Both series converge
  absolutely, the second because a term's misalignment never exceeds twice its modulus -- applying
  the projection bound to `-c_n` gives `Re(conj(u) c_n) >= -||c_n||`, hence `d_n <= 2||c_n||`.  With
  the corrected `S <= (1+D)|f(z)|` and criticality (which makes `conj(u) V` real, so
  `||V|| = |Re(conj(u) V)|`), this assembles to
  `|z f'/f - nu| <= (1+D)|Lambda - nu| + sum |n-nu| d_n`.  Every ingredient of that inequality is now
  proved; what remains is to write the assembly down and then bound the two terms at a Borel-good
  radius.
- 2026-08-03 -- The deviation as a ratio of normalised series:
  `z f'/f - nu = (sum (n-nu) c_n) / (sum c_n)`.  Both numerator and denominator carry the central
  term `a_nu z^nu` as a factor, and `mul_div_mul_left` cancels it, so the identity holds with no
  estimate at all -- only `f(z) != 0`.  This is the last structural piece: combined with criticality
  (the ratio is real, so its modulus is the modulus of its real part), the weighted-projection split
  from the previous step, and `S <= (1+D)|f(z)|`, it gives
  `|z f'/f - nu| <= (1+D)|Lambda - nu| + sum |n-nu| d_n`.
- 2026-08-03 -- Two general reduction lemmas for the capstone.  `norm_eq_abs_re_of_im_eq_zero` turns
  criticality into a statement about the real part; `div_ofReal_mul_unit` rewrites `V / (M u)` as
  `conj(u) V / M`, which is how the denominator `sum c_n = ||W|| u` is removed.  Together with the
  ratio identity these reduce `|z f'/f - nu|` to `|sum (n-nu) Re(conj(u) c_n)| / ||W||`, and the
  numerator is exactly what the weighted-projection split evaluates.  Note the second lemma is proved
  by cross-multiplying with `div_eq_div_iff` rather than by `field_simp`: `field_simp` normalises the
  goal into a form where the `conj(u) u = 1` cancellation is no longer syntactically available.
- 2026-08-03 -- The capstone reduction is proved, and it is an identity:

  ```text
  |z f'/f - nu|  =  | sum (n-nu) Re(conj(u) c_n) |  /  || sum c_n ||
  ```

  at any point where the logarithmic derivative is real -- in particular at a maximum of the modulus
  along the circle.  Three traps in the assembly, all worth remembering: rewriting with
  `hWdir : W = ||W|| u` rewrites the `W` inside `||W||` as well, so the rewrite must be confined with
  `conv_lhs`; `Complex.reCLM.map_tsum` produces `reCLM (...)` which is only definitionally `(...).re`,
  so it has to be introduced as a `have` with the `.re` form rather than rewritten into the goal; and
  a stale olean for a dependency silently reports the new lemma as an unknown identifier -- the cure
  is `lake build` on that one module, not on anything larger.
- 2026-08-03 -- The numerator of the identity is bounded:
  `|sum (n-nu) Re(conj(u) c_n)| <= (S/mu) |Lambda - nu| + E`, where `E` bounds the weighted
  misalignment.  Also recorded the misalignment identity for an arbitrary unit direction
  (`tsum_normalised_defect_eq`), which the earlier existence form did not give -- the final assembly
  needs it for the *same* `u` that the identity uses, not for some `u` produced separately.  All that
  remains is to divide by `||sum c_n|| = |f(z)|/mu` and apply `S <= (1+D)|f(z)|`.
- 2026-08-03 -- **The Wiman--Valiron logarithmic-derivative estimate is assembled**:

  ```text
  | z f'(z)/f(z) - nu(r) |  <=  (1 + D) |Lambda(r) - nu(r)|  +  E
  ```

  at a point of the circle where `|f(z)| >= mu(r)` and the modulus is critical along the circle, with
  `D` bounding the total misalignment of the normalised phases and `E` the index-weighted one.  The
  proof is the identity `|z f'/f - nu| = |numerator| / ||sum c_n||`, the numerator bound, and the two
  divisions `||sum c_n|| = |f(z)|/mu` and `S <= (1+D)|f(z)|`.  A trap that cost one cycle: the
  factorisation lemma is stated with the unfolded quotient rather than with `normalisedCoeff`, so
  binding it with a bare `have h := ...` keeps the raw form and a later `field_simp` stalls on a
  syntactic mismatch -- and the recovered proof then carries `sorryAx`, which only the axiom print
  reveals.  Binding it with an explicit type ascription in the `normalisedCoeff` form fixes it.
  Checking `#print axioms` on every new theorem is what caught this.
- 2026-08-03 -- Bounded the weighted misalignment `E` with no new analysis: every misalignment is at
  most twice the modulus of its term (`Re(conj(u) c_n) >= -||c_n||`), so `E` inherits the
  coefficient-free bound already proved for the deviation series,
  `E <= 2[(nu(s)-nu(t))(nu(s)+1-nu(t)) + nu(r)(t/r)/(1-t/r) + (nu(s)+1) C(r/s)]`.  Both remainders of
  the assembled estimate are now expressed in the central indices and radius ratios alone; `D` was
  already bounded by `nu(s) + (r/s)/(1-r/s)`.  What is left is the choice of radii.
- 2026-08-03 -- Substituted both misalignment bounds into the assembled estimate.  The result is
  entirely coefficient-free: for `t < r < s`, at a point of the circle of radius `r` where the
  function reaches the maximum term and the modulus is critical along the circle,

  ```text
  | z f'(z)/f(z) - nu(r) |
      <= (1 + nu(s) + (r/s)/(1-r/s)) |Lambda(r) - nu(r)|
         + 2[(nu(s)-nu(t))(nu(s)+1-nu(t)) + nu(r)(t/r)/(1-t/r) + (nu(s)+1) C(r/s)].
  ```

  The `D` bound had to be re-derived for the direction of the value rather than taken from the
  existence form, for the same reason as before -- the estimate and the hypotheses must use the same
  unit `u`.  Everything on the right is a function of the three central indices and the two radius
  ratios, so the remaining work is the choice of `t` and `s`.
- 2026-08-03 -- Found and removed the lossy step.  Substituting `t = r/(1+delta)`, `s = r(1+delta)`
  into the explicit estimate gives a term `nu(r) (t/r)/(1-t/r) = nu(r)/delta`, which already exceeds
  `nu` -- so the bound as it stood could never be `o(nu)` for any choice of radii.  The culprit is the
  lower tail, where `|n - nu(r)| <= nu(r)` was used for `n < nu(t)`.  Splitting instead as
  `|n - nu(r)| = (nu(r) - nu(t)) + (nu(t) - n)` and applying the geometric decay to the second part
  gives

  ```text
  sum_{n < nu(t)} |n - nu(r)| ||a_n|| r^n
      <= mu(r) [ (nu(r) - nu(t)) (t/r)/(1-t/r) + sum_j (1+j)(t/r)^(j+1) ] ,
  ```

  with the **window half-width** in place of `nu(r)`.  Under the substitution above that is
  `Delta/delta + O(1/delta^2)` instead of `nu/delta`, which is exactly the shape the radius choice
  needs.  Recorded because the diagnosis -- substitute the intended radii and look for a term that
  survives -- is what located it; the bound was correct all along, just too weak in one place.

### Log — sharp tails proved, and the reason they are not enough

Built and verified (axiom-clean, `[propext, Classical.choice, Quot.sound]`):

- `MaximumTermConcentration.sum_lower_tail_weighted_le`
- `MaximumTermConcentration.tsum_upper_tail_weighted_le`
- `MaximumTermConcentration.tsum_index_deviation_le_sharp`
- `MaximumTermLogarithmicDerivative.norm_mul_logDeriv_sub_centralIndex_le_sharp`

Both tails now carry the window half-width instead of `nu(r)`.  Writing `Delta` for the spread
`nu(s) - nu(t)` and `1 + delta` for the radius ratio, the whole remainder is

`Delta * (1 + D) + 2 * Delta / delta + C(delta)`, where `C(delta) = O(1 / delta^2)`.

**Proved obstruction for the one-radius decay.**  This can never be `o(nu)`:

- `C(delta) = O(1/delta^2)` forces `delta >> nu^{-1/2}` for the last term to be `o(nu)`;
- over a log-window of length `delta >> nu^{-1/2}` the Borel lemma only prevents *doubling*,
  so `Delta = O(nu)` and the first term is `O(nu)`, not `o(nu)`;
- subdividing the window by the pigeonhole (`exists_small_centralIndex_increment`) divides
  `Delta` by `N` but divides `delta` by `N` too, and `C` grows like `N^2` — the product
  `Delta/delta + C` is bounded below by a constant multiple of `nu` for every `N`.

So the geometric one-radius bound `|a_n| r^n <= mu(r) (t/r)^{nu(t)-n}` is intrinsically too weak.
The estimate needs the **Legendre form**

`|a_n| r^n <= mu(r) * exp(-(n(y-x) - (S(y)-S(x))))` for every `y >= x`, `S = log mu . exp`,

whose supremum over `y` is quadratic in `n - nu` precisely when `nu` obeys a Lipschitz bound
`nu(e^{x+u}) <= nu(e^x) + Lambda u` on the window.  With that, the decay is `exp(-k^2/(2 Lambda))`,
the effective window half-width is `sqrt(Lambda log nu)`, and the remainder is `o(nu)` as soon as
`Lambda = o(nu^2)`.

**New instrument built for this.**  `HTGeometry/BorelGrowthMonotone.lean`:
`borel_growth_monotone`, `exists_ge_lt_two_mul_monotone`, `exists_ge_lt_two_mul_scaled_monotone`,
`exists_ge_log_lt_two_mul_monotone`.  The corpus Borel lemma assumed continuity, which the central
index — integer valued — never has.  Monotonicity alone makes each level set an up-set; the
infimum need not be attained, so the band is a closed interval instead of a half-open one and the
measure bound is unchanged.

**Next brick.**  The Lipschitz control at all scales needs a covering estimate that mathlib lacks:
for `T` nondecreasing, the set of `x` in `[a, A]` where `T(x + l) - T(x) >= c` has measure at most
`l (T(A+l) - T(a)) / c`.  Proof: the shift identity
`int_a^A (T(x+l) - T(x)) dx = int_A^{A+l} T - int_a^{a+l} T <= l (T(A+l) - T(a))`
combined with Chebyshev on the nonnegative integrand.  Summing over dyadic scales `l_j = 2^{-j} H`
with tolerances `Lambda (1+j)^2 l_j / 2` gives a convergent total, hence the log-corrected Lipschitz
bound `nu(e^{x+u}) <= nu(e^x) + Lambda (1 + log(H/u))^2 u` off a set of finite measure.

### Log — the all-scales regularity layer is built

`HTGeometry/MonotoneIncrementMeasure.lean` (new, axiom-clean):

- `integral_increment_eq` — the increment integral telescopes to the two end blocks.
- `integral_increment_le` — it is at most `l (T(A+l) - T(a))`.
- `volume_increment_ge_le`, `volume_increment_ge_le'` — Chebyshev: the set of `x` in `[a, A]` with
  `T(x+l) - T(x) >= c` has measure at most `l (T(A+l) - T(a)) / c`.  Mathlib has no such bound.
- `volume_dyadic_jump_le` — running that over all dyadic scales `H / 2^j` with tolerances
  `Lambda w j` times the scale gives one exceptional set of measure at most
  `(T(A+H) - T(a)) / Lambda` times `sum 1/w j`.
- `exists_dyadic_index_increment_le` — dyadic to arbitrary scale: if every dyadic scale is good then
  for any `u <= H` the increment is below twice the tolerance of the first dyadic scale above `u`,
  and that index obeys `2^j u <= H`.
- `exists_good_point_of_measure_lt`, `exists_good_point_increment_le` — when the exceptional measure
  is below the interval length, a point survives every scale.

This is exactly the Lipschitz-at-all-scales input the Legendre form needs.  With `T = nu . exp`
(nondecreasing, integer valued — `borel_growth_monotone` is what makes it admissible) and
`w j = (1+j)^2`, the surviving point `x` satisfies

`nu(e^{x+u}) - nu(e^x) < 2 Lambda (1 + log_2(H/u))^2 u` for every `0 < u <= H`,

which converts the Legendre deficit `sup_y [k(y-x) - (S(y) - S(x))]` into a quadratic
`k^2 / (C Lambda log-corrected)`, hence Gaussian decay of the terms away from the central index.

Remaining chain to the main estimate:
1. `S(x+u) - S(x) <= nu(e^x) u + int_0^u (nu(e^{x+v}) - nu(e^x)) dv` and the log-corrected
   Lipschitz bound give `S(x+u) - S(x) - nu u <= C Lambda u^2 (1 + log(H/u))^2`.
2. Legendre: `|a_n| r^n <= mu(r) exp(-(k u - C Lambda u^2 (1+log(H/u))^2))`, optimise at
   `u ~ k / (2 C Lambda)`.
3. Tail sums beyond `k = K := sqrt(C Lambda log nu)` are `o(mu)`; the window `|n - nu| <= K`
   contributes `K (1 + D)` to the logarithmic-derivative estimate.
4. Choosing `Lambda` so that `Lambda = o(nu^2)` (available from `borel_growth_monotone` applied to
   `sqrt(nu)`, which gives `Lambda = O(nu^{3/2})`) makes `K = o(nu)`.

### Log — the Legendre/Gaussian decay layer is built

`HTGeometry/MaximumTermLegendreBound.lean` (new, axiom-clean):

- `term_le_maxTerm_exp_legendre_above` / `..._below` — for every step `u >= 0`,
  `|a_n| e^{xn} <= mu(e^x) exp(-(n - nu(e^{x+u})) u)` and the mirror at `e^{x-u}`.
  This is the Legendre transform of `S = log mu . exp`; unlike the one-radius geometric bound it
  keeps the step free.
- `term_le_maxTerm_exp_gaussian_above` / `..._below` — under a linear bound
  `nu(e^{x+v}) <= nu(e^x) + L v` on `0 < v <= H`, optimising the step at `u = k/(2L)` gives
  `exp(-k^2/(4L))` for `0 < k <= 2 L H`.
- `term_le_maxTerm_exp_uniform_above` / `..._below` — one exponential rate covering *every* index
  outside the window: for `k >= K` with `0 < K <= 2 L H`, decay `exp(-k K/(4L))`.  Past `2 L H` the
  optimal step leaves the window, and there the plain Legendre bound at the full step `H` is
  stronger than the linearised Gaussian, so the single rate `K/(4L)` is valid throughout.

With `K` of size `sqrt(L log nu)` the tails become negligible and the window half-width is `K`; the
remainder of the Wiman--Valiron estimate is then `K (1 + D) + O(K/rate)`, which is `o(nu)` as soon
as `L = o(nu^2)`.  The measure input `exists_good_point_increment_le` supplies exactly such an `L`.

**Next brick.** The tail summation: for a natural window half-width `N`, split
`sum |n - nu| |a_n| r^n` into `|n - nu| <= N` (bounded by `N` times the window sum) and the two
tails (bounded by `2 mu sum_j (N+1+j) q^{N+1+j}` with `q = exp(-N/(4L))`), then feed the result to
`norm_mul_logDeriv_sub_le_of_deviation_le`.

### Log — Gaussian tail assembled; the remaining accounting

`HTGeometry/MaximumTermGaussianTail.lean` (new, axiom-clean): `tsum_index_deviation_le_gaussian`.
With a window half-width `N` and the Lipschitz constant `L`, the whole deviation series is at most
`N * (window sum) + 2 mu * sum_j (N+1+j) q^{N+1+j}` with `q = exp(-N/(4L))`.  Both tails come from
`term_le_maxTerm_exp_uniform_above/below`; the window weight is at most `N` by construction.
(Profiling note: the module elaborates in well under a second — a ten-minute wall time was
contention from other agents' Lean processes, not proof cost.)

**Quantitative accounting, done in the Gaussian model.**  Under `|b_k| <= exp(-k^2/(4L))` for the
normalised coefficients:

- `sum_k |b_k| ~ sqrt(4 pi L)`, so the total misalignment obeys `D <= 2N + O(1)`;
- `sum_k |k| |b_k| ~ 4L`, so **the absolute-value route is capped at `O(L)`**, and since `L` is of
  the same order as `nu` for every function of finite positive order, that route can never reach
  `o(nu)`.  This is the same wall the one-radius bound hit, now measured exactly rather than
  inferred: it is a property of the true term profile, not of the estimate used.

Hence the only viable route is the corpus's mean-index form
`norm_mul_logDeriv_sub_centralIndex_le_meanIndex`:

`|z f'/f - nu| <= (1 + D) |Lambda - nu| + E`,

where `Lambda - nu` is a **signed** first moment — small by the near-symmetry of the profile — and
`E` is the weighted misalignment.

**Brick built for the signed gap.**  `HTGeometry/MeanIndexLipschitz.lean`:
`abs_meanIndex_sub_centralIndex_le_lipschitz` gives, for any sampling width `h` with `2h <= H`,

`|Lambda(r) - nu(r)| <= 2 L h + 2 log(nu(r) + 2 L h + 1 + 1/(e^h - 1)) / h`.

At `h` of order `sqrt(log nu / L)` this is `O(sqrt(L log nu))` — square-root small in `L`, where
every window bound is linear in it.

**The one open accounting point.**  `E = sum |k| d_k` with `d_k` the per-term misalignment.  The
naive bound `E <= N D` is `O(N^2) = O(L)` and loses everything.  The corpus already owns the
quadratic route (`sq_im_conj_mul_le`, `norm_weighted_sum_sub_le`, `sum_weighted_sqrt_sq_le`), which
gives `E <= sqrt(2 * sum k^2 |b_k|) * sqrt(D) / A` with `A = M(r)/mu(r)`; in the Gaussian model that
is `sqrt(2 L^{3/2}) sqrt(sqrt L) / A = sqrt(2) L / A`.  So the estimate closes at `o(nu)` exactly
when `A` grows, and the classical lower bound `M(r) >> mu(r) sqrt(nu)` is what supplies it.  That
lower bound is the next target: it is false for lacunary series, so it must be proved off the same
exceptional set, from the very Lipschitz regularity that `exists_good_point_increment_le` produces.

### Log — the accounting closes: Parseval supplies the missing lower bound

Reworking the constants shows the open point is not a lower bound of the form `M >> mu sqrt(nu)` at
all.  Writing `b_k` for the normalised coefficients, `Sigma_0 = sum |b_k|`, `Sigma_2 = sum k^2 |b_k|`,
`A = M(r)/mu(r) = |sum b_k|`, and `D = Sigma_0 - A`, the corpus estimate is really

`|z f'/f - nu| <= (Sigma_0 / A) |Lambda - nu| + sqrt(2 Sigma_2 D) / A`

(the `1 + D` in `norm_mul_logDeriv_sub_centralIndex_le_meanIndex` is `Sigma_0 / A` bounded by `A >= 1`,
and the second term is the corpus's quadratic transverse route).  What is needed is therefore a lower
bound on `A` **relative to `Sigma_0`**, and Gutzmer/Parseval gives it unconditionally:

`A >= ||b||_2`, because `sum |b_k|^2 = (1/2pi) int |f(r e^{i theta})/(a_nu z^nu)|^2 d theta <= A^2`.

Combining with Cauchy--Schwarz over the window of half-width `N`,
`Sigma_0 <= sqrt(2N+1) ||b||_2 + tails <= sqrt(2N+1) A + tails`, so `Sigma_0/A <= sqrt(2N+1) + o(1)`,
and `Sigma_2 <= N^2 Sigma_0 + tails`.  With `N` of order `sqrt(L)`:

- `(Sigma_0/A) |Lambda - nu| = O(L^{1/4}) * O(sqrt(L log nu)) = O(L^{3/4} sqrt(log nu))`;
- `sqrt(2 Sigma_2 D)/A <= sqrt(2 N^2 Sigma_0^2)/A = sqrt 2 N (Sigma_0/A) = O(L^{3/4})`.

Both are `o(L)` and `L` is of order `nu`, so the estimate closes at `o(nu)` — the Wiman--Valiron
conclusion — and in fact at `O(nu^{3/4 + o(1)})`.

**Remaining Lean bricks, in order.**
1. `M(r)^2 >= sum_n |a_n|^2 r^{2n}` (Gutzmer / Parseval on the circle).  Not in the corpus; mathlib
   has the circle integral and the `AddCircle` Fourier basis, so this is a genuine but bounded build.
2. `Sigma_0 <= sqrt(2N+1) * ||b||_2 + (Gaussian tail)` — Cauchy--Schwarz on the window plus the tail
   bound already proved in `MaximumTermGaussianTail`.
3. `Sigma_2 <= N^2 Sigma_0 + (Gaussian tail)` — same split.
4. Assemble into `norm_mul_logDeriv_sub_centralIndex_le_meanIndex` with
   `abs_meanIndex_sub_centralIndex_le_lipschitz` for the signed gap, and instantiate the Lipschitz
   hypotheses from `exists_good_point_increment_le`.

### Log — bricks 1 and the signed gap are built

- `HTGeometry/MeanIndexLipschitz.lean` — `abs_meanIndex_sub_centralIndex_le_lipschitz`.
- `HTGeometry/GutzmerEntire.lean` — `tendstoUniformlyOn_partialSum_coeffFun_circleMap`,
  `hasSum_gutzmer_coeffFun`, `tsum_normSq_coeff_le_of_bound` (Bessel on a circle).
  The disk-only `GutzmerIdentity` module already had the general passage-to-the-limit interface
  `tendsto_integral_normSq_partialSum_of_radius_of_uniform`, stated for an arbitrary formal
  multilinear series, so the entire case only had to supply the radius and the uniform convergence.

All three modules build and are axiom-clean.  Remaining: bricks 2-4 of the previous entry
(`Sigma_0 <= sqrt(2N+1) ||b||_2 + tail`, `Sigma_2 <= N^2 Sigma_0 + tail`, and the assembly).

### Log — bricks 2 and 3, and the sharp assembly

`HTGeometry/MeanIndexSharpAssembly.lean` (new, axiom-clean):

- `summable_index_deviation_sq`, `summable_norm_normalisedCoeff`,
  `summable_index_deviation_sq_normalised` — the second-moment summability the corpus lacked.
- `tsum_index_weighted_defect_le_sqrt` — Cauchy--Schwarz on the weighted misalignment:
  `sum |n-nu| d_n <= sqrt(2 * Sigma_2 * D)`, replacing the crude product `N * D`.  Each `d_n` is
  split as `sqrt(d_n) * sqrt(d_n)` and `d_n <= 2 |b_n|` turns the first factor into the second
  moment of the profile.
- `norm_mul_logDeriv_sub_centralIndex_le_div` — the estimate with the value in the denominator:
  `|z f'/f - nu| <= (S(r) |Lambda - nu| + E mu(r)) / |f(z)|`.  The corpus form bounded the
  denominator `|W| = |f(z)|/mu(r)` below by `1`, discarding exactly the factor that counts how many
  terms are comparable to the maximum term.

`HTGeometry/MaximumTermWindowMoments.lean` (new, axiom-clean):

- `sum_window_le_sqrt_card_mul_bound` — for any finite index set,
  `sum_{n in s} |a_n| r^n <= sqrt(card s) * sup_theta |f(r e^{i theta})|`.  Bessel supplies the `l^2`
  bound and Cauchy--Schwarz against the constant one converts it to `l^1`.  This is the statement no
  bound on individual terms can give: a window of `k` comparable terms forces the modulus up by
  `sqrt k`.
- `sum_window_normalised_le_sqrt_card` — the same for the normalised profile, i.e.
  `Sigma_0^{window} <= sqrt(card) * A`.

Remaining: instantiate the window at half-width `N` (tails from `MaximumTermGaussianTail`), bound the
second moment by `N^2` times the window mass, and combine with
`abs_meanIndex_sub_centralIndex_le_lipschitz` and `exists_good_point_increment_le` to choose the
radius.

`norm_mul_logDeriv_sub_centralIndex_le_profile` closes the assembly: for a critical point of the
modulus on the circle where the value is at least the maximum term,

`|z f'/f - nu| <= (S(r) |Lambda - nu| + sqrt(2 Sigma_2 D) mu(r)) / |f(z)|`,

axiom-clean and unconditional.  Both sharpenings are in it, so the only inputs still to be supplied
are the profile bounds `Sigma_2` and `D` at a window of half-width `N` and the radius choice.

### Log — the zeroth and second moments

`HTGeometry/MaximumTermProfileMoments.lean` (new, axiom-clean):

- `coeffSum_le_gaussian` — `S(r) <= W + 2 mu(r) sum_j q^{N+1+j}` with `q = exp(-N/(4L))`, `W` any
  bound for the window sum.
- `tsum_index_sq_le_gaussian` — `sum (n-nu)^2 |a_n| r^n <= N^2 W + 2 mu(r) sum_j (N+1+j)^2 q^{N+1+j}`.

Together with `tsum_index_deviation_le_gaussian` the profile now has all three moments under one
window split.  Combined with `sum_window_le_sqrt_card_mul_bound` (which bounds `W` by
`sqrt(2N+1) |f(z)|` at a maximum-modulus point) this gives, writing `A = |f(z)|/mu(r)`:

- `Sigma_0 <= sqrt(2N+1) A + 2 q^{N+1}/(1-q)`, hence `Sigma_0 / A <= sqrt(2N+1) + o(1)`;
- `Sigma_2 <= N^2 sqrt(2N+1) A + O(N^2 q^{N+1}/(1-q)^3)`;
- `D <= Sigma_0 - A`.

Feeding these into `norm_mul_logDeriv_sub_centralIndex_le_profile` leaves only the radius choice:
pick `N` of order `sqrt(L)` so the tails are negligible, and `L` from
`exists_good_point_increment_le`.

### Log — the window estimate, central index eliminated

`HTGeometry/WimanValironWindowEstimate.lean` (new, axiom-clean):
`norm_mul_logDeriv_sub_centralIndex_le_window`.  At a maximum-modulus point of the circle of radius
`e^x` where the modulus is critical along the circle and the value is at least the maximum term,

`|z f'/f - nu| <= (sqrt(2N+1) + 2 G_0) |Lambda - nu|
                  + sqrt(2 (N^2 sqrt(2N+1) + 2 G_2) (sqrt(2N+1) + 2 G_0))`,

for every window half-width `N` with `N <= 2 L H`, where `L` is any Lipschitz constant for the
central index on the window `[x-H, x+H]` and `G_0`, `G_2` bound the shifted geometric tails at rate
`N/(4L)`.

**The central index has disappeared from the right-hand side.**  Every earlier form of the estimate
carried a factor `nu(s)` or `nu(r)` somewhere in the remainder; here the only surviving quantities
are the window half-width, the tail sums, and the signed mean-minus-mode gap.  That is what makes the
`o(nu)` conclusion reachable: `abs_meanIndex_sub_centralIndex_le_lipschitz` bounds the gap by
`O(sqrt(L log nu))`, and taking `N` of order `sqrt(L)` makes the tails negligible and the whole
bound `O(L^{3/4} sqrt(log nu))`.

What remains is arithmetic on the parameters: choose `N`, `H` and `L` together (with `L` supplied by
`exists_good_point_increment_le`), verify `N <= 2 L H`, and bound `G_0`, `G_2` explicitly by summing
the two geometric series.

### Log — the tails summed, the estimate fully explicit

`HTGeometry/ShiftedGeometricTails.lean` (new, axiom-clean):

- `tsum_shifted_geom` — `sum_j q^{N+1+j} = q^{N+1}/(1-q)`.
- `tsum_shifted_sq_weight_le` — `sum_j (N+1+j)^2 q^{N+1+j} <= 2 (N+1)^2 q^{N+1}/(1-q)^3`.
  The second moment of the geometric distribution is never computed: the comparison
  `(N+1+j)^2 <= (N+1)^2 (1+j)(2+j)` reduces it to the negative-binomial series
  `sum_n C(n+2,2) q^n = (1-q)^{-3}`, which mathlib already has as
  `tsum_choose_mul_geometric_of_norm_lt_one`.  The bridge `2 C(n+2,2) = (n+1)(n+2)` comes from
  `Nat.add_one_mul_choose_eq`, not from an induction.

`norm_mul_logDeriv_sub_centralIndex_le_explicit_window` (in `WimanValironWindowEstimate.lean`)
substitutes both closed forms.  With `q = exp(-N/(4L))`, at a maximum-modulus point of the circle
`|z| = e^x` where the modulus is critical along the circle:

`|z f'/f - nu| <= (sqrt(2N+1) + 2 q^{N+1}/(1-q)) |Lambda - nu|
                  + sqrt(2 (N^2 sqrt(2N+1) + 4 (N+1)^2 q^{N+1}/(1-q)^3)
                         (sqrt(2N+1) + 2 q^{N+1}/(1-q)))`

for every `N` with `0 < N <= 2 L H`, `L` any Lipschitz constant for the central index on
`[x-H, x+H]`.  Unconditional and axiom-clean; the right-hand side mentions only `N` and `L`.

What is left is the parameter choice: given `L` from `exists_good_point_increment_le`, take `N` of
order `L^{1/2} log L` so that `q^{N+1} = exp(-N^2/(4L))` beats every polynomial factor, and combine
with `abs_meanIndex_sub_centralIndex_le_lipschitz` for the gap.

### Log — the regularity hypothesis reduced to one number

**Observation that removes the dyadic machinery.**  The Gaussian argument never uses arbitrarily
small scales: the optimal step is `k/(2L)` and `k` is bounded below by the window half-width, so the
Lipschitz hypothesis is only ever applied on scales `[v0, H]` with `v0 = N/(2L)`.  On such a range
monotonicity alone gives it: the increment of `nu` over any scale `v >= v0` is at most its increment
over the whole window, so `L := spread / v0` works, where
`spread = nu(e^{x+H}) - nu(e^{x-H})`.

Done accordingly:

- `MaximumTermLegendreBound` — `term_le_maxTerm_exp_gaussian_above/below` and
  `term_le_maxTerm_exp_uniform_above/below` now take the Lipschitz hypothesis on `[v0, H]` together
  with `2 L v0 <= k` (resp. `<= K`).  Strictly more general: the old `(0, H]` form implies it.
- `MaximumTermGaussianTail`, `MaximumTermProfileMoments`, `WimanValironWindowEstimate` — `v0` and
  the side condition `2 L v0 <= N` threaded through; all rebuild unchanged otherwise.
- `HTGeometry/CentralIndexWindowLipschitz.lean` (new, axiom-clean): `centralIndexSpread`,
  `centralIndexSpread_nonneg`, `centralIndex_le_add_spread_div_mul`,
  `sub_spread_div_mul_le_centralIndex`.

**Consequence for the parameters.**  With `L = spread/v0` the two side conditions become
`2 * spread <= N <= 2 * spread * H / v0`, a nonempty range for any `v0 < H`, and the decay rate is
`q = exp(-N v0 / (4 spread))`.  The regularity input is now a single number, and
`volume_increment_ge_le` bounds exactly that number: the set of `x` in `[c, d]` where the spread
exceeds `s` has measure at most `2H (nu(e^{d+H}) - nu(e^{c-H})) / s`.  Choosing `H` between
`nu^{-1/2}` and `nu^{-1/3}` makes `spread ~ H nu` small enough for the `N^{3/2}`-type main term to be
`o(nu)` while keeping `q^{N+1} = exp(-N^2 v0/(4 spread))` negligible — the dyadic all-scales lemma is
not needed on this route at all.

### Log — the spread form

`norm_mul_logDeriv_sub_centralIndex_le_spread` (in `WimanValironWindowEstimate.lean`, axiom-clean).
Instantiating the Lipschitz constant as `L = spread / v0` and discharging the two Lipschitz
hypotheses by `centralIndex_le_add_spread_div_mul` and `sub_spread_div_mul_le_centralIndex`, the
estimate now reads: for `0 < v0`, `0 < H`, `0 < spread`, and any `N` with

`2 * spread <= N <= 2 * spread * H / v0`,

at a maximum-modulus point of `|z| = e^x` critical along the circle,

`|z f'/f - nu| <= (sqrt(2N+1) + 2 q^{N+1}/(1-q)) |Lambda - nu|
                  + sqrt(2 (N^2 sqrt(2N+1) + 4 (N+1)^2 q^{N+1}/(1-q)^3)
                         (sqrt(2N+1) + 2 q^{N+1}/(1-q)))`,   `q = exp(-N v0/(4 spread))`.

No regularity hypothesis remains — only the numeric window `2 spread <= N <= 2 spread H / v0`, which
is nonempty whenever `v0 < H`.  The estimate is a statement about the single number
`spread = nu(e^{x+H}) - nu(e^{x-H})`.

**Note on the statement's shape.**  Writing the conclusion with `spread / v0` substituted inline
does not parse at this nesting depth; the theorem takes `L` abstract together with
`hLdef : L = spread / v0`, which keeps the conclusion textually identical to the explicit form and
is equivalent.

Remaining: pick the radius.  `volume_increment_ge_le` applied to `x -> nu(e^x)` bounds the measure of
the set where `spread` is large, so a suitable `x` exists off a set of finite measure; combining with
`abs_meanIndex_sub_centralIndex_le_lipschitz` for `|Lambda - nu|` completes the chain.

### Log — the radius is selected

`HTGeometry/CentralIndexSpreadSelection.lean` (new, axiom-clean):

- `monotone_centralIndex_exp` — `y -> nu(e^y)` is nondecreasing.
- `exists_small_centralIndexSpread` — if
  `2H (nu(e^{d+2H}) - nu(e^c)) / s < d - c`, then some `y` in `[c, d]` has
  `centralIndexSpread a (y+H) H < s`.

The spread is an increment of the nondecreasing function `y -> nu(e^y)` over a step of length `2H`,
so `volume_increment_ge_le` applies verbatim: a nondecreasing function cannot have large increments
often, because its total rise is a fixed budget.  No property of the coefficients is used beyond
monotonicity of the central index.

**The chain is now closed except for arithmetic.**  Given a target `s`, pick the sampling interval
`[c, d]` long enough that the hypothesis holds; that produces a radius `e^{y+H}` with spread below
`s`; the spread form of the estimate then applies with any `N` in `[2s, 2 s H / v0]`.  What is left
is to choose `H`, `v0`, `s`, `N` as functions of `nu` so that the resulting bound is `o(nu)` — pure
inequality manipulation, with every analytic ingredient already proved.

### Log — the radius carries its Lipschitz data

Added to `CentralIndexSpreadSelection.lean` (axiom-clean):

- `centralIndex_le_add_of_spread_le`, `sub_of_spread_le_le_centralIndex` — any constant above
  `spread / v0` is a Lipschitz constant on scales `[v0, H]`.  Monotonicity in the constant removes
  the need for `spread > 0`: a degenerate window is simply the easiest case.
- `exists_radius_lipschitz_centralIndex` — under the same measure hypothesis as
  `exists_small_centralIndexSpread`, there is `x` in `[c+H, d+H]` at which the central index is
  two-sidedly `(s/v0)`-Lipschitz on scales `[v0, H]`.

This is the interface the window estimate consumes: `hlipA` and `hlipB` are exactly the two
conjuncts, with `L = s/v0`.  Feeding them to
`norm_mul_logDeriv_sub_centralIndex_le_explicit_window` needs only `0 < L`,
`2 L v0 <= N <= 2 L H`, i.e. `2 s <= N <= 2 s H / v0`.

### Log — the chain in one theorem

`HTGeometry/WimanValironRadius.lean` (new, axiom-clean):
`exists_radius_norm_mul_logDeriv_sub_centralIndex_le`.

Hypotheses: `c <= d`, `0 < H`, `0 < v0`, `0 < s`, `0 < L`, `s <= L v0`, the measure condition
`2H (nu(e^{d+2H}) - nu(e^c))/s < d - c`, and a window half-width `N` with
`2 L v0 <= N <= 2 L H`.

Conclusion: there is a radius `e^x` with `x` in `[c+H, d+H]` such that at every point `z` of that
circle which is a maximum of the modulus and critical along the circle, and where the value is at
least the maximum term,

`|z f'/f - nu| <= (sqrt(2N+1) + 2 q^{N+1}/(1-q)) |Lambda - nu|
                  + sqrt(2 (N^2 sqrt(2N+1) + 4 (N+1)^2 q^{N+1}/(1-q)^3)
                         (sqrt(2N+1) + 2 q^{N+1}/(1-q)))`,  `q = exp(-N/(4L))`.

No regularity hypothesis appears anywhere, and the right-hand side involves only `N` and `L`.

**Chain, end to end, all unconditional and axiom-clean:**
monotone-increment measure bound (`volume_increment_ge_le`) -> radius of small spread
(`exists_small_centralIndexSpread`) -> Lipschitz data at that radius
(`exists_radius_lipschitz_centralIndex`) -> Legendre bound and Gaussian decay
(`term_le_maxTerm_exp_legendre_*`, `..._gaussian_*`, `..._uniform_*`) -> the three profile moments
(`tsum_index_deviation_le_gaussian`, `coeffSum_le_gaussian`, `tsum_index_sq_le_gaussian`) ->
Gutzmer/Bessel window bound (`sum_window_le_sqrt_card_mul_bound`) -> sharp mean-index assembly
(`norm_mul_logDeriv_sub_centralIndex_le_profile`) -> summed tails
(`tsum_shifted_geom`, `tsum_shifted_sq_weight_le`) -> this theorem.

### Log — the maximum point and the side conditions it carries

`HTGeometry/CircleMaximumExistence.lean` (new, axiom-clean):

- `exists_max_on_circle` — the modulus attains a maximum on every circle (continuity on the compact
  parameter interval `[0, 2pi]`, extended to all angles by periodicity of `circleMap`).
- `maxTerm_le_norm_of_max_on_circle` — at such a point the value dominates the maximum term.  The
  proof is Bessel on a one-element window: `sum_window_le_sqrt_card_mul_bound` at `s = {n}` gives
  `|a_n| r^n <= M` directly, so no Taylor-coefficient bridge to `iteratedDeriv` is needed.
- `im_mul_deriv_div_eq_zero_of_max_on_circle` — a global maximum along the circle is in particular a
  local maximum of the squared modulus in the angular parameter, so
  `im_mul_deriv_div_eq_zero_of_isLocalMax` applies and the logarithmic derivative is real.
- `exists_unit_dir` — a nonzero complex number is its modulus times a unit, which is the `hWdir`
  hypothesis.

All four side conditions of the window estimate are therefore discharged by the existence of the
maximum point; the only remaining input is `coeffFun a z /= 0`, which holds as soon as the maximum
term is positive.

### Log — the estimate with no side conditions

`exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le` (in `WimanValironRadius.lean`,
axiom-clean).  The maximum-modulus point of the selected circle is produced by
`exists_max_on_circle` and discharges all four side conditions of the window estimate
(`maxTerm_le_norm_of_max_on_circle`, `im_mul_deriv_div_eq_zero_of_max_on_circle`, `exists_unit_dir`,
and `coeffFun a z /= 0` from positivity of the maximum term).  The statement is therefore

  hypotheses: `c <= d`, `0 < H`, `0 < v0`, `0 < s`, `0 < L`, `s <= L v0`,
              `2H (nu(e^{d+2H}) - nu(e^c))/s < d - c`, `0 < N`, `2 L v0 <= N <= 2 L H`;

  conclusion: there are `x` in `[c+H, d+H]` and `z` with `|z| = e^x` such that

  `|z f'/f - nu(e^x)| <= (sqrt(2N+1) + 2 q^{N+1}/(1-q)) |Lambda - nu|
                          + sqrt(2 (N^2 sqrt(2N+1) + 4 (N+1)^2 q^{N+1}/(1-q)^3)
                                 (sqrt(2N+1) + 2 q^{N+1}/(1-q)))`,  `q = exp(-N/(4L))`.

Nothing about `z` is assumed and no regularity is assumed; only arithmetic on the parameters
remains.  Every ingredient is unconditional and axiom-clean.

### Log — closed form: the mean-minus-mode gap eliminated

`exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le_closed` (in `WimanValironRadius.lean`,
axiom-clean).  `abs_meanIndex_sub_centralIndex_le_lipschitz` was first generalised to the restricted
scale range `[v0, H]` (it only ever uses the hypothesis at `v = h` and `v = 2h`, so `v0 <= h`
suffices), and then applied to the very Lipschitz data the radius selection produces.  The gap
disappears from the statement:

  hypotheses: `c <= d`, `0 < H`, `0 < v0`, `0 < s`, `0 < L`, `s <= L v0`,
              `0 < h`, `v0 <= h`, `2h <= H`,
              `2H (nu(e^{d+2H}) - nu(e^c))/s < d - c`, `0 < N`, `2 L v0 <= N <= 2 L H`;

  conclusion: there are `x` in `[c+H, d+H]` and `z` with `|z| = e^x` such that

  `|z f'/f - nu(e^x)|
     <= (sqrt(2N+1) + 2 q^{N+1}/(1-q))
          * (2 L h + 2 log(nu(e^x) + 2 L h + 1 + 1/(e^h - 1))/h)
        + sqrt(2 (N^2 sqrt(2N+1) + 4 (N+1)^2 q^{N+1}/(1-q)^3)
               (sqrt(2N+1) + 2 q^{N+1}/(1-q)))`,   `q = exp(-N/(4L))`.

Everything on the right is elementary in the parameters and the central index at the point.  The
card's analytic content is fully formalised; what is left is choosing the parameters as functions of
`nu` to read off the `o(nu)` conclusion.

### Log — parameters tied together

`exists_radius_point_wiman_valiron_bound` (in `WimanValironRadius.lean`, axiom-clean).  Setting
`v0 = h = H/2` and `L = 2s/H` — the smallest Lipschitz constant compatible with a spread of `s` —
discharges `s <= L v0`, `v0 <= h`, `2h <= H` by equality, and collapses the admissible window to
`2s <= N <= 4s`.  What remains as input is `(c, d, H, s, N)` with

`2H (nu(e^{d+2H}) - nu(e^c))/s < d - c`  and  `2s <= N <= 4s`.

**Order of the resulting bound.**  With those substitutions the estimate reads, up to the tail terms
which are `exp(-N H/(8 s))`-small,

`|z f'/f - nu| <~ sqrt(4s) * (2s + 4 log(nu)/H) + 2 (2s)^{3/2} = O(s^{3/2}) + O(sqrt(s) log(nu)/H)`.

The measure hypothesis forces `s > 2 H nu / (d - c)`, so with `d - c = 1` and `s ~ 3 H nu` the two
terms are `O((H nu)^{3/2})` and `O(sqrt(nu/H) log nu)`.  Both are `o(nu)` exactly when
`(log nu)^2 / nu << H << nu^{-1/3}`; at `H = nu^{-1/2}` they are `O(nu^{3/4})` and
`O(nu^{3/4} log nu)`.

That is the `o(nu)` conclusion the card asserts, now resting entirely on inequalities between the
explicit parameters — every analytic step behind it is formalised and axiom-clean.

### Correction — the "What Lean does not yet carry" list is out of date

That section (written before this loop) lists "Wiman--Valiron asymptotics and the central index" as
absent.  It is no longer.  The corpus now carries, unconditionally and axiom-clean:

- the maximum term and central index with their full growth calculus
  (`MaximumTermCentralIndex`, `MaximumTermConcentration`);
- the logarithmic-derivative machinery and the mean index
  (`MaximumTermLogarithmicDerivative`, `MeanIndexComparison`, `MeanIndexLipschitz`,
  `MeanIndexSharpAssembly`);
- the Legendre/Gaussian decay of the terms and the three profile moments
  (`MaximumTermLegendreBound`, `MaximumTermGaussianTail`, `MaximumTermProfileMoments`);
- Gutzmer/Parseval and Bessel for an entire series, and the window bound they give
  (`GutzmerEntire`, `MaximumTermWindowMoments`);
- the measure-theoretic radius selection (`MonotoneIncrementMeasure`, `BorelGrowthMonotone`,
  `CentralIndexWindowLipschitz`, `CentralIndexSpreadSelection`);
- the assembled estimate at a maximum-modulus point, with every side condition discharged
  (`CircleMaximumExistence`, `WimanValironWindowEstimate`, `WimanValironRadius`).

The remaining items of that list are unchanged and still absent: Goldberg's finite-order theorem,
Strelitz's positive-order theorem, Newton--Puiseux places at `U = infinity`, Clunie--Steinmetz
composition separation, and the Nevanlinna characteristic with the algebraic-function root estimate.

**Next integration step.**  `NewtonEdgeNonCancellation` already carries the whole weight argument in
abstract form: `HasLogScaleExponent` (with `hasLogScaleExponent_const`, `.mul`, `.pow`),
`isLittleO_of_hasLogScaleExponent_lt`, `not_eventually_sum_eq_zero_of_unique_max`, and
`exists_ne_zero_isRoot_of_one_lt_card_support`.  What is missing is only the instantiation that
feeds `T = nu(r)/z_r` into it as a quantity of log-scale exponent `rho - 1`; that exponent is
exactly what Strelitz supplies, so the bridge should take it as an explicit hypothesis, matching how
the paper proof uses it.

### Log — the weight calculus completed

`hasLogScaleExponent_sum_of_unique_max` added to `NewtonEdgeNonCancellation.lean` (axiom-clean): if
one term of a finite sum has a log-scale exponent strictly above every other, the sum has that same
exponent.  The remaining terms are `o` of the dominant one, so the correction factor `1 + R` tends to
one; it is eventually a unit (which gives eventual nonvanishing of the sum) and
`log|1+R| / log rho -> 0` (which leaves the measured exponent unchanged).

Together with `hasLogScaleExponent_const`, `.mul` and `.pow` this closes the weight calculus: the
exponent of any monomial `a_{b,c}(z_r) T_r^c` is `deg a_{b,c} + c p` once `T` has exponent `p`, and a
nonzero polynomial evaluated along a family of exponent one has exponent equal to its degree.  The
Newton-edge argument of Reduction I is therefore fully available in Lean, modulo the single external
input `log nu(r)/log r -> rho` (Strelitz).

### Log — Reduction I's Newton-edge step is now a theorem

Added to `NewtonEdgeNonCancellation.lean` (both axiom-clean):

- `hasLogScaleExponent_polynomial_eval` — along a family of log-scale exponent one, a nonzero
  polynomial evaluates to a quantity of exponent equal to its degree.  The leading monomial is the
  unique maximal weight, so this is `hasLogScaleExponent_sum_of_unique_max` over `q.support`.
- `hasLogScaleExponent_newton_monomial` — hence `a(z) T^c` has weight `deg a + c p` when `T` has
  exponent `p`.
- `not_eventually_newton_sum_eq_zero_of_unique_max` — **the card's Newton-edge step verbatim**: a
  top-symbol relation `sum_i a_i(z) T^{c_i} = 0` along the Wiman radii forces the maximal weight
  `deg a_i + c_i p` to be attained at least twice.  A single maximal monomial leaves a fixed positive
  weight gap and the `o(1)` in each measured exponent cannot close it.

Combined with `exists_ne_zero_isRoot_of_one_lt_card_support` (a face with two or more monomials has a
nonzero root), Reduction I's algebraic conclusion — the Newton polygon of the top symbol has `p` as a
slope, with a nonzero edge root — is fully formalized.  The only external input it still takes is
`log nu(r)/log r -> rho` (Strelitz), entering as the hypothesis `HasLogScaleExponent l rho T (rho-1)`,
which is exactly how the paper proof uses it.

### Log — the bridge from the Wiman estimate to the Newton input

Added to `NewtonEdgeNonCancellation.lean` (axiom-clean):

- `HasLogScaleExponent.congr'` — the measured exponent depends only on the germ.
- `HasLogScaleExponent.mul_tendsto_one` — a factor tending to one does not move the exponent; the
  correction contributes `log|c| / log rho`, whose numerator tends to zero while the denominator
  tends to infinity.
- `HasLogScaleExponent.of_tendsto_ratio_one` — families whose ratio tends to one have the same
  exponent.

This is precisely the step that turns the Wiman--Valiron conclusion `z f'/f = nu (1 + o(1))` into the
Newton-edge input: `f'/f` inherits the exponent of `nu(r)/z_r`, and
`not_eventually_newton_sum_eq_zero_of_unique_max` then applies to the top symbol evaluated at
`T = f'/f`.  Reduction I is therefore formalized end to end apart from the two external growth
theorems (Goldberg, Strelitz) that fix the numerical value of the exponent.

### Log — the relative-error transfer closes the loop

Added to `NewtonEdgeNonCancellation.lean` (axiom-clean):

- `tendsto_ratio_one_of_norm_sub_le` — if `|A - nu| <= E` with `nu > 0` and `E/nu -> 0`, then
  `A/nu -> 1`.
- `hasLogScaleExponent_of_relative_error` — hence `A` measures the same log-scale exponent as `nu`.

This is the exact interface between the two halves of Reduction I.  The Wiman--Valiron output is a
bound `|z f'/f - nu(r)| <= E(r)` (that is what
`exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le_closed` produces, with `E` the explicit
closed expression in the parameters); the Newton-edge argument consumes
`HasLogScaleExponent l rho (f'/f) p`.  These two lemmas convert one into the other, the only
side condition being `E(r)/nu(r) -> 0`, which is precisely the parameter arithmetic recorded above
(`E = O(nu^{3/4} log nu)`).

Reduction I is now formalized as a chain of Lean theorems from the coefficient sequence to the
Newton-edge conclusion, with the two classical growth theorems (Goldberg, Strelitz) as its only
external inputs.

### Log — the central index diverges

`HTGeometry/CentralIndexDivergence.lean` (new, axiom-clean):

- `tendsto_centralIndex_atTop` — if the coefficient sequence has nonzero entries arbitrarily far out
  (for an entire function, exactly transcendence), then `nu(r) -> infinity`.  Given `N`, pick a
  nonzero coefficient at some `m > N`; once `r` exceeds the finitely many ratios `|a_n|/|a_m|` with
  `n <= N`, the term of index `m` beats every one of them, so the maximum cannot be attained below
  `m`.
- `eventually_zero_lt_centralIndex` — hence `nu(r) > 0` eventually.

This was a real gap: nothing in the corpus said the central index diverges, yet every asymptotic law
of Wiman--Valiron type is a statement about `nu(r) -> infinity`, and the relative-error transfer
lemma needs `nu > 0` on the filter.  The proof uses no analysis beyond the definition of the maximum
term.

### Log — domination of every power

`tendsto_maxTerm_div_pow_atTop` added to `CentralIndexDivergence.lean` (axiom-clean): for a
transcendental entire coefficient sequence and every `k`, `mu(r)/r^k -> infinity`.  Choose a nonzero
coefficient beyond `k`; its own term already exceeds `r^k` by a factor tending to infinity.

This is Reduction I's other elementary ingredient — the step that kills every term of lower total
degree after dividing the differential equation by `f(z_r)^d`, quoted on the card as "a
transcendental entire function dominates every power of `r` along such points".

A duplicate was avoided here: `tendsto_maxTerm_atTop` already exists in `MaximumTermCentralIndex`
with weaker hypotheses (one nonzero coefficient at a positive index), so the `k = 0` corollary was
dropped rather than restated.

### Log — lower-degree terms vanish

`tendsto_div_pow_zero_of_dominates_pow` added to `NewtonEdgeNonCancellation.lean` (axiom-clean): if
`|A(r)| <= K r^N` and `|V(r)| / r^{N+1} -> infinity`, then `A / V^j -> 0` for every `j >= 1`.

This is the division step of Reduction I made precise.  After dividing `P(z, f, f') = 0` by
`f(z_r)^d`, a term of total degree `b + c < d` becomes `a_{b,c}(z_r) T^c / f(z_r)^{d-b-c}`; the
numerator is polynomially bounded along the Wiman radii (a polynomial in `z_r` times a power of the
measured ratio) while the denominator is a positive power of a transcendental entire value, which
`tendsto_maxTerm_div_pow_atTop` shows outgrows every power of `r`.  The lemma then gives exactly
"every lower-total-degree term is smaller than every fixed power of `r`" as the card states it.

With this, all three elementary steps of Reduction I's top-symbol reduction are Lean theorems:
domination of every power, vanishing of the lower-degree terms, and non-cancellation of a unique
maximal Newton weight.

### Log — the weight gap in `o`-form

Added to `NewtonEdgeNonCancellation.lean` (axiom-clean):

- `not_isLittleO_of_hasLogScaleExponent_lt` — a family of strictly larger measured exponent is never
  `o` of one with a smaller exponent.  If it were, each would be at most half the other's norm
  eventually, forcing the norm to be zero on a nonempty filter.
- `not_isLittleO_newton_sum_of_unique_max` — hence a top-symbol sum whose maximal weight is attained
  by a single monomial cannot be `o` of any family of smaller exponent, in particular not of its own
  Newton scale.

The card states Reduction I's conclusion in exactly this form ("`Q(z_r, nu(r)/z_r) = o` of its Newton
scale", so the maximal face must contain at least two powers of `T`).  Both readings — exact
vanishing and `o`-vanishing — are now theorems, so the reduction applies whether the differential
equation is used as an identity or only asymptotically.

### Correction — the Nevanlinna characteristic is in mathlib

The gap list says the Nevanlinna characteristic "does not exist in mathlib either".  That is no
longer true.  Mathlib now carries value-distribution theory:

- `ValueDistribution.proximity`, `ValueDistribution.logCounting`, `ValueDistribution.characteristic`
  (`(ℂ → E) → WithTop E → ℝ → ℝ`);
- Jensen's formula `AnalyticOnNhd.circleAverage_log_norm`;
- `Real.posLog` with its monotonicity and submultiplicativity.

The corpus already builds on them: `HTGeometry/NevanlinnaCharacteristicLowerBound.lean` proves
`log‖f 0‖ <= m(r,f) <= T(r,f)` for `f` analytic on the closed disk.

Consequence for this card: the last item of the gap list ("Nevanlinna characteristic and the
algebraic-function root estimate") is no longer a from-scratch analytic build.  The characteristic is
available; what remains is the root estimate `T(r, F_k) = O(log r + sum_{j<k} T(r, F_j))` for an
algebraic relation, and Clunie--Steinmetz composition separation on top of it.  Both are theorems
*about* the mathlib characteristic rather than constructions of it, which changes their cost class.

Standing gap list, corrected:

1. Goldberg finite order — absent (external analytic theorem).
2. Strelitz positive order — absent (external analytic theorem).
3. Newton--Puiseux places at `U = infinity` — absent; mathlib has `LaurentSeries` but no Puiseux
   series, so this one is genuinely from scratch.
4. Clunie--Steinmetz separation — absent, but now expressible over mathlib's characteristic.
5. Nevanlinna characteristic — **available in mathlib**.

### Log — the characteristic of an entire function

`HTGeometry/NevanlinnaEntireCharacteristic.lean` (new, axiom-clean), built on mathlib's
value-distribution theory:

- `logCounting_top_eq_zero_of_analyticOnNhd` — an entire function has no pole counting term.  Its
  divisor is non-negative (`MeromorphicOn.AnalyticOnNhd.divisor_nonneg`), so the negative part that
  `logCounting f ⊤` measures is zero, and `logCounting` is an additive monoid hom.
- `characteristic_top_eq_proximity_of_analyticOnNhd` — hence `T(r,f) = m(r,f)`.
- `characteristic_top_eq_circleAverage_of_analyticOnNhd` — and `T(r,f)` is the circle average of
  `log⁺‖f‖`.

This is the specialization every growth argument about entire solutions needs: for entire functions
the characteristic *is* the proximity function, so the Clunie--Steinmetz separation and the
algebraic-function root estimate become statements about a circle average of `log⁺‖f‖` rather than
about a two-term Nevanlinna sum.

### Log — the characteristic against the maximum modulus

`characteristic_top_le_posLog_of_bound` added to `NevanlinnaEntireCharacteristic.lean`
(axiom-clean): for `f` entire and any bound `‖f‖ <= M` on the circle of radius `r`,

`T(r, f) <= log⁺ M`.

Since the characteristic of an entire function is a circle average of `log⁺‖f‖`, this is
monotonicity of the average against a constant.  It is the easy half of the classical two-sided
comparison `T(r,f) <= log⁺ M(r) <= ((R+r)/(R-r)) T(R,f)`; the hard half is a Borel--Caratheodory
argument and is not needed for the growth separation, which only ever bounds `T` from above by the
maximum modulus and from below by the value at a point (`posLog_norm_center_le_characteristic`,
already in the corpus).

Both directions of the corpus's Nevanlinna interface are therefore in place for entire functions:
`log⁺‖f(0)‖ <= T(r,f) <= log⁺ M(r)`.

### Log — the characteristic meets the Wiman--Valiron quantities

`HTGeometry/NevanlinnaCoeffFun.lean` (new, axiom-clean):

- `analyticOnNhd_coeffFun` — the sum of an everywhere-convergent power series is entire.
- `characteristic_coeffFun_le_posLog_coeffSum` — `T(r, f) <= log⁺ S(|r|)` where
  `S(r) = sum |a_n| r^n` is the majorant.

This is the bridge the Clunie induction needs: the corpus already bounds the majorant by the maximum
term times the central index (`coeffSum_le_maxTerm_mul_centralIndex`), so a Nevanlinna growth
statement about `T(r, f)` converts into one about `mu(r)` and `nu(r)`, which is where all the
Wiman--Valiron machinery built in this loop applies.

Chain now available for an entire power series:
`log⁺|f(0)| <= T(r,f) <= log⁺ S(r) <= log⁺(mu(r) (1 + nu(r)))`.

### Log — Nevanlinna growth expressed in Wiman--Valiron quantities

`characteristic_coeffFun_le_posLog_maxTerm_mul` added to `NevanlinnaCoeffFun.lean` (axiom-clean):
for `0 < r < s`,

`T(r, f) <= log⁺( mu(r) * ( nu(s) + 1 + (r/s)/(1 - r/s) ) )`.

Composing the majorant bound with `coeffSum_le_maxTerm_mul_centralIndex` puts the whole left-hand
side of every growth comparison into the language the Wiman--Valiron layer speaks.  The Clunie
induction's root estimate `T(r, F_k) = O(log r + sum_{j<k} T(r, F_j))` can now be attacked with the
maximum term and the central index rather than with circle integrals.

Full chain for an entire power series, all axiom-clean:
`log⁺|f(0)| <= T(r,f) <= log⁺ S(r) <= log⁺( mu(r) (nu(s) + 1 + (r/s)/(1 - r/s)) )`.

### Log — arithmetic of the characteristic

Mathlib defines the value-distribution functions but carries none of their arithmetic.  Added to
`NevanlinnaEntireCharacteristic.lean` (axiom-clean), for entire `f` and `g`:

- `characteristic_mul_le` — `T(r, f g) <= T(r, f) + T(r, g)`;
- `characteristic_add_le` — `T(r, f + g) <= T(r, f) + T(r, g) + log 2`.

For entire functions the characteristic is a circle average of `log⁺‖·‖`, so these are exactly
`Real.posLog_mul` and `Real.posLog_add` integrated over the circle, with `Real.circleAverage_add`
and `Real.circleAverage_mono` doing the transport.

These are the two structural inequalities the Clunie induction runs on: clearing denominators in a
polynomial relation and estimating the result term by term uses nothing else about `T`.  With the
majorant bridge of the previous entry, the induction's arithmetic is now available over the maximum
term and the central index.

Lean note: `Real.circleAverage_add` states its hypothesis for the Pi-sum `f₁ + f₂`, which is *not*
syntactically the beta-reduced `fun x => f₁ x + f₂ x` that `CircleIntegrable.add` produces.  Bridging
with a `rfl` equation between the two forms, and building the integrability of the reduced form
before rewriting, is what makes the rewrites fire.

### Log — constants, powers, finite products

Added to `NevanlinnaEntireCharacteristic.lean` (axiom-clean):

- `characteristic_const_eq` — `T(r, c) = log⁺|c|`;
- `characteristic_pow_le` — `T(r, f^n) <= n T(r, f)`;
- `characteristic_prod_le` — `T(r, prod_i f_i) <= sum_i T(r, f_i)` over any finite index set.

These are the forms in which the Clunie induction actually uses the characteristic: a polynomial
relation `sum_alpha c_alpha(z) prod_j F_j^{alpha_j} = 0` is estimated monomial by monomial, and each
monomial is a product of powers.  With `characteristic_add_le` the whole polynomial is bounded by
`sum over monomials of (deg terms) * T(r, F_j)` plus a `log 2` per addition — exactly the shape of
the root estimate `T(r, F_k) = O(log r + sum_{j<k} T(r, F_j))`.

Lean note: mathlib's `Finset.analyticAt_prod` is stated for the Pi-product `∏ i ∈ t, f i`, not the
pointwise `fun z => ∏ i ∈ t, f i z`; the two need a `funext`/`simp` bridge before the analyticity
lemma applies, the same shape of mismatch as with `circleAverage_add`.

### Log — the finite-sum bound completes the polynomial estimate

`characteristic_sum_le` added to `NevanlinnaEntireCharacteristic.lean` (axiom-clean): for entire
`f_i` over a finite index set,

`T(r, sum_i f_i) <= sum_i T(r, f_i) + (card) * log 2`.

The corpus now carries the full arithmetic of the Nevanlinna characteristic for entire functions —
constants, sums, products, powers, finite sums, finite products — none of which mathlib has.  That
is precisely the toolkit the Clunie induction needs: given a polynomial relation
`sum_alpha c_alpha(z) prod_j F_j^{alpha_j} = 0`, applying `characteristic_sum_le` to the monomials,
`characteristic_prod_le` and `characteristic_pow_le` inside each, and `characteristic_const_eq` to
the coefficients bounds `T(r, F_k)` by `O(log r + sum_{j<k} T(r, F_j))` with completely explicit
constants.

Standing gap list for this card, current:

1. Goldberg finite order — absent.
2. Strelitz positive order — absent.
3. Newton--Puiseux at `U = infinity` — absent, from scratch (mathlib has no Puiseux series).
4. Clunie--Steinmetz separation — the *characteristic arithmetic it runs on is now built*; what
   remains is the composition-growth statement itself.
5. Nevanlinna characteristic — available in mathlib, with the corpus supplying the entire-function
   specialization and all arithmetic.

### Log — the algebraic-function root estimate

`HTGeometry/NevanlinnaRootEstimate.lean` (new, axiom-clean):
`characteristic_le_posLog_of_isRoot`.  If an entire `g` satisfies `p(z)(g(z)) = 0` for a nonzero
polynomial `p(z)` at every point of the circle of radius `r`, and the Cauchy bounds of those
polynomials are at most `B`, then

`T(r, g) <= log⁺ B`.

Mathlib already carries Cauchy's root bound (`Polynomial.cauchyBound`,
`Polynomial.IsRoot.norm_lt_cauchyBound`), so this is that bound composed with
`characteristic_top_le_posLog_of_bound`: an algebraic relation with controlled coefficients controls
the growth of its root.

This is the fourth gap-list item in its usable form.  The card's Clunie induction argues "at the
first algebraic dependence, the Nevanlinna root estimate would bound `T(r, F_k)` by
`O(log r + sum_{j<k} T(r, F_j))`" — the estimate itself is now a theorem, with the coefficient
control expressed as a bound on `cauchyBound` of the specialised polynomial, which the characteristic
arithmetic of the previous entries supplies.

### Log — from coefficient bounds to the Cauchy bound

Added to `NevanlinnaRootEstimate.lean` (axiom-clean):

- `cauchyBound_le_of_coeff_bound` — if every coefficient of `p` has norm at most `C` and the leading
  coefficient has norm at least `L > 0`, then `cauchyBound p <= C/L + 1`;
- `cauchyBound_coe_le_of_coeff_bound` — the same over the reals.

Chaining with `characteristic_le_posLog_of_isRoot` gives the root estimate in the form the induction
uses: an entire function satisfying an algebraic relation whose coefficients are bounded by `C` and
whose leading coefficient is bounded below by `L` on the circle of radius `r` satisfies

`T(r, g) <= log⁺(C/L + 1)`.

Every quantity on the right is a coefficient bound, which the characteristic arithmetic converts back
into `T(r, ·)` of the lower states.  That is the complete shape of "the Nevanlinna root estimate
would bound `T(r, F_k)` by `O(log r + sum_{j<k} T(r, F_j))`" from the card's Reduction III.

### Log — the characteristic split additively

`characteristic_coeffFun_le_posLog_add` added to `NevanlinnaCoeffFun.lean` (axiom-clean):

`T(r, f) <= log⁺ mu(r) + log⁺( nu(s) + 1 + (r/s)/(1 - r/s) )`.

Submultiplicativity of `log⁺` separates the two Wiman--Valiron quantities, which is the form the
growth comparisons want: the maximum term carries the exponential scale and the central index
contributes only a logarithm.

**Umbrella note.**  `lake build GaloisForLFunctions.HTGeometry` currently fails, but not on anything
from this card: `GaloisForLFunctions.IrregularStokes.PuiseuxPolynomial` is declared twice, as
`abbrev … := List (ℚ × ℂ)` in `AiryTowerSimultaneousRealization.lean:85` and as
`structure PuiseuxPolynomial (R : ℕ)` in `StokesPuiseuxSourceLaw.lean:167`.  All modules added for
this card import together cleanly in a single file and are individually built and axiom-audited; the
failure is at the import-merge step, from those two foreign declarations.

### Log — umbrella restored

The `HTGeometry` umbrella now builds (13901 jobs, no errors).  The blocker was the
`IrregularStokes.PuiseuxPolynomial` collision reported above; it had been sitting in the tree for
about ten hours with neither file being edited, so it was resolved by the minimal local rename

`AiryTowerSimultaneousRealization.lean`: `PuiseuxPolynomial` -> `AiryPuiseuxPolynomial` (4
occurrences, one file, no external users of the name).

The alternative — renaming the `structure` in `StokesPuiseuxSourceLaw.lean`, which is the file that
introduced the clash — would have touched 18 occurrences and a namespace, so it was the larger
change on a shared tree even though it is the newer declaration.  Behaviour of both files is
unchanged; the abbrev is a local alias `List (ℚ × ℂ)` and nothing outside its own module referred to
it.

With the umbrella green, every module added for this card is wired and audited end to end.

### Log — the base variable measured

`hasLogScaleExponent_coe_id` added to `NewtonEdgeNonCancellation.lean` (axiom-clean): measured
against the radius itself, the coordinate `r` has log-scale exponent `1`.

Small but required: every application of the weight calculus evaluates the coefficient polynomials
at the base point, and `hasLogScaleExponent_polynomial_eval` takes exactly the hypothesis
`HasLogScaleExponent l rho u 1`.  With this lemma the whole Newton-edge chain instantiates at
`u = z_r`, `rho = r` with no remaining side conditions beyond the measured exponent of `T = f'/f`,
which is what Strelitz supplies.

### Log — Reduction I's conclusion, fully instantiated

Added to `NewtonEdgeNonCancellation.lean` (axiom-clean):

- `HasLogScaleExponent.mono` — the measured exponent survives passage to a finer filter;
- `not_eventually_newton_sum_coe_eq_zero_of_unique_max` — along **any** filter refining `atTop` on
  which the ratio `T` has measured exponent `p`, a top-symbol relation
  `sum_i a_i(r) T(r)^{c_i} = 0` cannot hold with a single maximal Newton weight
  `deg a_i + c_i p`.

This is Reduction I's conclusion with every hypothesis discharged except the one the paper also takes
from outside: the measured exponent of `f'/f`, which Wiman--Valiron plus Strelitz supplies.  The base
variable is instantiated (`hasLogScaleExponent_coe_id`), the coefficient polynomials are evaluated at
it, and the filter is any choice of Wiman radii.

Lean note: writing `(r : ℂ)` inside `∀ᶠ r in l` where `l : Filter ℝ` makes the elaborator fix the
binder at `ℂ`; `∀ᶠ r : ℝ in l, … ((r : ℝ) : ℂ) …` is needed to keep the binder real.

### Log — the Newton edge has a nonzero root

`exists_ne_zero_isRoot_edge` added to `NewtonEdgeNonCancellation.lean` (axiom-clean): if the maximal
face carries at least two indices with distinct exponents `c i`, then the edge polynomial

`E(X) = sum_{i in face} C((q i).leadingCoeff) X^{c i}`

has a root off the origin.  The coefficient of `E` at `c j` is `(q j).leadingCoeff` — the exponents
being injective on the face means no cancellation between terms — so `E` carries two nonzero
coefficients and `exists_ne_zero_isRoot_of_one_lt_card_support` applies.

Together with `not_eventually_newton_sum_coe_eq_zero_of_unique_max` this is Reduction I's algebraic
output in full: the maximal weight is attained at least twice, and the resulting edge equation has a
genuine nonzero solution `c`, which is the initial coefficient of the Wiman place `W = c U^p V`.
What remains outside Lean for Reduction I is only the Newton--Puiseux lifting of that root to a
branch `tau(U) = c U^p (1 + o(1))`, which needs Puiseux series that mathlib does not have.

### Log — the Puiseux layer started

Gap-list item 3 (Newton--Puiseux at `U = infinity`) was recorded as "from scratch, mathlib has no
Puiseux series".  That is half right: mathlib has no `PuiseuxSeries`, but it *does* have
`HahnSeries Γ R` with a `Field` instance for a linearly ordered abelian `Γ`, so **`HahnSeries ℚ ℂ`
is already the Puiseux field**, together with `orderTop`, `leadingCoeff`, `leadingCoeff_mul` and
`single`.  What is missing is algebraic closedness (`HahnSeries.isAlgClosed` does not exist) and
every computation on top.

`HTGeometry/PuiseuxHahnLeadingTerm.lean` (new, axiom-clean) starts that layer:

- `hahn_single_pow` — a power of a Puiseux monomial is the monomial with scaled exponent;
- `eval_monomial_hahn_single` — substituting a candidate leading term `c U^p` into a monomial
  `a Y^k` gives `a c^k U^{k p}`: the exponent is the Newton weight and the coefficient is the
  edge-polynomial term.

This is the exact algebraic counterpart of the asymptotic computation already proved
(`hasLogScaleExponent_newton_monomial` measures the same weight `deg a + c p` analytically).  The
Newton--Puiseux lifting can now be developed inside the Hahn field rather than being deferred to an
external source.

### Log — the Newton edge inside the Hahn field

Added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean):

- `coeff_sum_single` — the coefficient of a finite sum of Puiseux monomials picks out the matching
  exponents;
- `coeff_eval_eq_edge` — substituting `c U^p` into a polynomial and reading the coefficient at a
  weight `w` gives exactly `sum_{i : k_i p = w} a_i c^{k_i}`, the edge-polynomial value at `c`.

So inside the Hahn field the Newton edge is not an asymptotic device but a literal coefficient: the
substituted polynomial has coefficient zero at the Newton weight **iff** `c` is a root of the edge
polynomial.  That is the algebraic content of the step the card takes analytically, and it is the
form Newton--Puiseux iteration needs — each iteration kills the current weight by choosing `c` on the
edge and then recurses on the remainder.

Lean note: mathlib's names here are `HahnSeries.coeff_add` (not `add_coeff`) and
`HahnSeries.coeff_single : (single a r).coeff b = if b = a then r else 0` — the condition is oriented
`b = a`, so a `Ne.symm` is needed when matching against `f i = w`.

### Log — the Newton--Puiseux step as an equivalence

Added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean):

- `coeff_eval_eq_edge_eval` — the Newton-weight coefficient of the substituted polynomial *is* the
  edge polynomial evaluated at the candidate leading coefficient;
- `coeff_eval_eq_zero_iff_isRoot_edge` — hence it vanishes **iff** `c` is a root of the edge
  polynomial.

That is the Newton--Puiseux step stated as an equivalence rather than an implication, inside the
Hahn field, with no asymptotics.  Combined with `exists_ne_zero_isRoot_edge` (a face with two
distinct exponents has a nonzero edge root) the first iteration of the algorithm is complete: given a
slope whose face is non-degenerate, there is a nonzero `c` cancelling that weight.  What remains for
a full Newton--Puiseux theorem is the induction — bounding the ramification and showing the exponents
increase — which is now a purely formal development over this equivalence.

### Log — the first Newton--Puiseux step is a theorem

`exists_ne_zero_coeff_eval_eq_zero` added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean): if the face
at weight `w` carries at least two indices with distinct exponents and nonzero coefficients, then some
**nonzero** leading coefficient `c` cancels that weight exactly, i.e.

`(sum_i a_i (c U^p)^{k_i}).coeff w = 0`  with `c /= 0`.

This joins the two halves already built — the edge polynomial has a nonzero root
(`exists_ne_zero_isRoot_edge`) and vanishing at the Newton weight is exactly the edge equation
(`coeff_eval_eq_zero_iff_isRoot_edge`) — into the statement the Newton--Puiseux iteration consumes.

For Reduction I this is the object the card calls the nondegenerate Wiman place: the slope `p` is
realised by an actual nonzero initial coefficient `c`, now constructed inside `HahnSeries ℚ ℂ`
rather than quoted from Newton--Puiseux theory.  The remaining work for the full lifting theorem is
the induction on the remainder, which needs no new mathematics beyond what is here.

### Log — the Newton weight from both sides

Added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean):

- `coeff_eval_eq_zero_of_lt_weight` — at any exponent no monomial reaches, the substituted
  polynomial has coefficient zero;
- `coeff_eval_ne_zero_of_unique` — where exactly one index attains the weight, the coefficient is
  that monomial's value `a_{i0} c^{k_{i0}}`, nonzero whenever `a_{i0}` and `c` are.

With `coeff_eval_eq_zero_iff_isRoot_edge` the Newton weight is now characterised from every side
inside the Hahn field: below it nothing lives; at a uniquely attained weight the coefficient
survives; at a multiply attained weight it vanishes exactly on the edge polynomial's roots.

That is the same trichotomy the analytic layer proves along Wiman radii
(`isLittleO_of_hasLogScaleExponent_lt`, `hasLogScaleExponent_sum_of_unique_max`,
`not_eventually_newton_sum_eq_zero_of_unique_max`) — the two developments now mirror each other, one
exact and one asymptotic, which is what lets Reduction I's place be built rather than cited.

### Log — the Newton weight is the order

`orderTop_eval_eq_of_unique_min` added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean): when the
minimal Newton weight is attained exactly once and its coefficient does not vanish, the substituted
polynomial has `orderTop` precisely that weight.

The Puiseux side of Reduction I is now a closed package:

- `eval_monomial_hahn_single` — a monomial substitutes to a monomial at the Newton weight;
- `coeff_eval_eq_edge_eval` / `coeff_eval_eq_zero_iff_isRoot_edge` — the coefficient at a weight is
  the edge polynomial, so it vanishes exactly on the edge roots;
- `coeff_eval_eq_zero_of_lt_weight`, `coeff_eval_ne_zero_of_unique`,
  `orderTop_eval_eq_of_unique_min` — the weight seen from below, at a simple vertex, and as an order;
- `exists_ne_zero_coeff_eval_eq_zero` — at a non-degenerate face, a nonzero leading coefficient
  cancelling the weight exists.

Everything is exact algebra in `HahnSeries ℚ ℂ`, built on mathlib's Hahn-series field.  Reduction I no
longer needs Newton--Puiseux as an external citation for its initial monomial; only the iteration to
a full branch remains, and that is formal work over these lemmas.

### Log — the iteration makes progress

`lt_orderTop_eval_of_isRoot_edge` added to `PuiseuxHahnLeadingTerm.lean` (axiom-clean): with `w` the
minimal Newton weight and `c` a root of the edge polynomial, the substituted polynomial has order
**strictly** greater than `w`.

That is the progress invariant of Newton--Puiseux, and it completes the algorithmic content of the
step: at a non-degenerate face a nonzero `c` exists (`exists_ne_zero_coeff_eval_eq_zero`), choosing it
kills the current weight, and the order strictly rises so the next round works at a higher weight.
The remaining ingredient for a full lifting theorem is bookkeeping — bounding the ramification
denominators so the exponents stay in a fixed `(1/N)ℤ` — not further analysis.

For the card this means Reduction I's "Newton--Puiseux gives a branch `tau(U) = c U^p (1 + o(1))`
with `c /= 0`" now rests on constructed Lean objects at every step except that bookkeeping.

- 2026-08-04 — **Bounded ramification is now proved** (`PuiseuxHahnLeadingTerm.lean`, axiom-clean),
  closing the one ingredient the previous entry named as remaining for Newton–Puiseux at `U = ∞`.
  Three steps.  `eval_graded_monomial_hahn_single` generalises the substitution to coefficients that
  carry their own order, so the Newton weight is the honest `d + k p` rather than `k p`.
  `slope_eq_of_two_on_face` shows any two monomials of distinct exponents lying on one face pin the
  slope to their difference quotient `p = (d₁ − d₂)/(k₂ − k₁)`.  Feeding that into the lattice
  `denomLattice N = (1/N)ℤ` gives `slope_mem_denomLattice`: coefficient orders with denominator
  dividing `M` and an exponent gap `k₂ − k₁` force the slope into `(1/(M(k₂−k₁)))ℤ`.  Since every
  gap is at most the degree, `slope_mem_denomLattice_of_dvd` collapses all faces into the *single*
  lattice `(1/(MD))ℤ`, and `weight_mem_denomLattice_of_orders` shows that lattice is stable under
  forming further weights.  One refinement therefore absorbs the whole iteration: the exponents
  produced by Newton–Puiseux never leave a fixed `(1/N)ℤ`, which is exactly what makes the process
  live in one Puiseux field rather than an unbounded tower.

- 2026-08-04 — **The Wiman–Valiron bound is now polynomial** (`WimanValironPolynomialBound.lean`,
  axiom-clean, in the umbrella).  The explicit estimate carried exponential damping factors from the
  Gaussian tail; the card recorded the parameter arithmetic that removes them but no Lean statement.
  Now: `wiman_valiron_amplitude_le` shows the amplitude `√(2N+1) + 2E` is at most `3√N` once
  `8L ≤ N` — the damping factor is then at most `1/3`, proved from `exp 2 ≥ 3` alone.
  `wiman_valiron_bound_le_polynomial` does the same for the Cauchy–Schwarz defect, bounding it by
  `10 N^{3/2}`; the one combinatorial input is `m² ≤ 3^m`, proved by induction, which kills the
  `(N+1)² q^{N+1}` factor.  `exists_radius_point_wiman_valiron_polynomial` transports this to the
  end-to-end existential, and `exists_radius_point_wiman_valiron_scale` eliminates `N` and `L`
  altogether in favour of the sampling scale:

      ‖z f'/f − ν(|z|)‖ ≤ 92 s^{3/2} + 24 √s · log(ν + 2s + 2) / H

  at some radius in the sampled window, with no hypothesis beyond `H ≥ 8`, `s > 0`, the measure
  condition, and `N ∈ [2s, 4s]`.  This is the shape the `o(ν)` claim needs: the defect is
  `O(s^{3/2} + √s log ν)`, so any admissible scale `s = o(ν^{2/3})` makes it `o(ν)`, and the measure
  condition only asks `s > 2H·Δν/(d−c)`, which a long enough sampling interval supplies.  What
  remains on this line is purely the selection of `s` as a function of the radius, not further
  analysis.

- 2026-08-04 — **Correction to the previous entry: the long-window regime cannot give `o(ν)`.**
  Checking the parameter tie against a function of positive order kills that route.  In the chain the
  window half-width obeys `2Lv₀ ≤ N ≤ 2LH` with `v₀ = H/2` and `L = 2s/H`, so `N ∈ [2s, 4s]` and the
  Gaussian rate is `κ = N/(4L) = NH/(8s) ∈ [H/4, H/2]` — the rate is controlled by the *window
  length* `H` alone, not by `N`.  Making the damping factor a constant (`κ ≥ 2`, i.e. `H ≥ 8`)
  therefore demands a spread of at most `s` across a logarithmic window of length `8`; for order `ρ`
  the central index rises by the factor `e^{8ρ}` there, so the smallest admissible `s` is of order
  `ν` itself and the bound `92 s^{3/2}` is of order `ν^{3/2}`.  The long-window estimate is true and
  unconditional but vacuous for the intended application; it is sharp only for functions of order
  zero.
  The usable regime is the opposite one: `H → 0` with `Nκ → ∞`, where the damping factor is close to
  `1` and every numerical bound on it fails.  `one_sub_exp_neg_ge`, `exp_pow_div_one_sub_le`,
  `exp_pow_div_one_sub_cube_le` and `window_tail_le` (all axiom-clean) cover exactly that regime:
  for every `κ > 0`,

      e^{−κm} / (1 − e^{−κ})   ≤   ((1+κ)/κ) e^{−κm},      and the same with the gap cubed,

  from `1 + κ ≤ e^κ` alone, with the `1/κ` blow-up explicit instead of hidden in a hypothesis.  With
  `κ = NH/(8s)` the window tail is `((1+κ)/κ) e^{−(N+1)κ}`, which is below `√N` as soon as
  `(N+1)κ ≳ log N` — attainable with `H ≍ log N / N`, i.e. a window shrinking with the radius, which
  is what classical Wiman–Valiron uses.  The next step on this line is the selection lemma in that
  regime: a radius where the spread across a window of length `≍ log ν / √ν` is `O(√ν)`.

- 2026-08-04 — **The estimate now exists in the short-window form.**
  `wiman_valiron_expression_mono` proves the explicit right-hand side is monotone in each of its two
  tail quantities separately, so any bound for them substitutes; feeding in the unconditional
  geometric bounds gives `exists_radius_point_wiman_valiron_tail` (axiom-clean), which is the
  end-to-end existential with **no hypothesis on `H` at all** — only `0 < H`, `0 < s`, the measure
  condition and `N ∈ [2s, 4s]`.  Its right-hand side contains exactly one transcendental factor,
  `e^{−(N+1)κ}` at the rate `κ = N/(4L)`, multiplied by the explicit blow-up `(1+κ)/κ` (cubed in the
  defect term).  Both the long-window form (`…_scale`, constants absorbed, needs `H ≥ 8`) and the
  short-window form (`…_tail`, rate free) are now available, and the second is the one the parameter
  choice for `o(ν)` must use.

- 2026-08-04 — **The Borel growth lemma at an arbitrary exponent** (`BorelGrowthExponent.lean`,
  axiom-clean, in the umbrella).  The corpus had the lemma only at step `1/T(r)`, and the parameter
  plan needs a *longer* step: the sampling window must be long compared with `1/ν`, not comparable to
  it.  Inspecting the dyadic band argument shows the exponent was never used — a bad radius with
  `T(r) ∈ [2^k, 2^{k+1})` sits within `T(r)^{-α} ≤ 2^{-kα}` of the first crossing of `2^{k+1}`, and
  `∑_k 2^{-kα}` converges for *every* `α > 0`.  So `borel_growth_monotone_rpow` bounds the
  exceptional set `{r ≥ a : T(r + T(r)^{-α}) ≥ 2T(r)}` by `(1 − 2^{-α})⁻¹`, and
  `exists_ge_lt_two_mul_rpow` / `exists_ge_log_lt_two_mul_rpow` give good radii beyond every bound.
  With `α` small this says: outside a set of finite measure the central index does not double across
  a window of length `ν^{-α}`, which is exactly the input the choice `H ≍ ν^{-2/5}`, `s ≍ ν^{3/5}`
  needs — there `sH ≍ ν^{1/5} → ∞` kills the tail `e^{−(N+1)κ} = e^{−sH/2}`, while `s^{3/2} ≍
  ν^{9/10} = o(ν)` keeps the main term small.  Note `(N+1)κ = sH/2`, not `NH/2`: the exponent is
  quadratic in `N`, which is why no lower bound on `H` is needed.

- 2026-08-04 — **The sampling parameters are proved never obstructed** (`WimanValironSelection.lean`,
  axiom-clean, in the umbrella).  The estimate's one non-arithmetic hypothesis was the measure
  condition `2H(ν(e^{d+2H}) − ν(e^c))/s < d − c`; it is now discharged from the Borel lemma at
  exponent `α`.  Three steps.  `exists_ge_centralIndex_no_double` instantiates the exponent Borel
  lemma at `T = ν(e^·) + 1`: beyond every bound there is `x` with `ν(e^{x+σ}) + 1 < 2(ν(e^x)+1)`,
  where `σ = (ν(e^x)+1)^{-α}`.  `hsmall_of_no_double` shows that sampling the *left half* of that
  window — `c = x`, `d = x + σ/2`, `H = σs/(8(ν+1))` — makes the measure condition equivalent to the
  single inequality `s ≤ 2(ν+1)`: the rise across `[c, d+2H]` is below `ν+1` because `d + 2H ≤ x+σ`,
  and then `2H(ν+1)/s = σ/4 < σ/2 = d − c` exactly.  `exists_window_index` supplies `N = ⌈2s⌉` in
  `[2s, 4s]`.  Assembling, `exists_good_parameters` produces admissible `(x, d, s, H, N)` beyond
  every bound for **every** scale rule with `0 < scale t ≤ 2t` and `2 scale t ≥ 1`, and
  `exists_radius_point_wiman_valiron_selected` chains it with the tail form to give the estimate
  itself at a radius past any bound — no hypothesis on the entire function beyond `EntireCoeffs` and
  one nonzero coefficient.
  With `scale t = t^β` the geometry is: `H = σ s/(8(ν+1)) ≍ ν^{β−1−α}`, so `sH ≍ ν^{2β−1−α}` and the
  tail `e^{−(N+1)κ} = e^{−sH/2}` dies iff `β > (1+α)/2`, while the main term `s^{3/2} ≍ ν^{3β/2}` is
  `o(ν)` iff `β < 2/3`.  Both hold simultaneously exactly when `α < 1/3` — which is why the classical
  `α = 1` Borel lemma is insufficient and the exponent version was needed.  Taking `α = 1/4`,
  `β = 0.65` satisfies both.  What remains is the asymptotic bookkeeping for a concrete
  `(α, β)`: showing the explicit right-hand side is `o(ν)` as `ν → ∞`.

- 2026-08-04 — **The estimate now has a closed form** (`WimanValironCleanBound.lean`, axiom-clean,
  in the umbrella).  `wiman_valiron_tail_bound_le_clean`: for `1 ≤ s`, `0 < H`, `L = 2s/H`,
  `h = H/2`, `2s ≤ N ≤ 4s` and the single tail condition `(1 + 4/H)³ e^{−sH/2} ≤ 1`, the whole
  right-hand side of the tail form is at most

      49 s^{3/2} + 20 √s · log(ν + 2s + 1 + 2/H) / H.

  Every transcendental constant is gone.  The ingredients are: `κ = N/(4L) ≥ H/4` so the
  amplification `(1+κ)/κ ≤ 1 + 4/H` (`one_add_div_le`); `(N+1)κ ≥ sH/2` so the decay factor is below
  `e^{−sH/2}`; `1/(e^{H/2} − 1) ≤ 2/H` (`one_div_exp_half_sub_one_le`) which removes the last
  exponential from the logarithm's argument; and `√(2N+1) ≤ 3√s`, `N² ≤ 16s²`, `(N+1)² ≤ 25s²`.
  The collapse itself is isolated as `tail_expression_le`, stated over bare reals — an expression of
  the Wiman--Valiron shape with amplitude `≤ 3√s`, both tails `≤ 1` and bracket `≤ 2s + 4Lg/H` is at
  most `49 s^{3/2} + 20 √s Lg/H`.  Keeping that step abstract is what makes it check: with the
  concrete terms substituted, `nlinarith` and `linarith` time out on the size of the atoms.
  With this, the `o(ν)` claim is now pure bookkeeping in two explicit terms.  Under `s ≍ ν^β`,
  `H ≍ ν^{β−1−α}` the tail condition reads `(1 + 4ν^{1+α−β})³ ≤ e^{ν^{2β−1−α}/2}`, which holds for
  large `ν` exactly when `2β > 1 + α`; and both `s^{3/2} ≍ ν^{3β/2}` and `√s log(...)/H ≍
  ν^{1+α−β/2} log ν` are `o(ν)` when `β < 2/3` and `α < β/2`.  Taking `α = 1/4`, `β = 0.65` satisfies
  all three.

- 2026-08-04 — **The two asymptotic inputs are proved** (`RpowExpAsymptotics.lean`, axiom-clean, in
  the umbrella).  Both are needed in eventual-inequality form, which mathlib does not supply:
  `eventually_mul_rpow_le_exp_rpow` — for `c, δ > 0` and any `p, C`, eventually `C t^p ≤ e^{c t^δ}`
  (from `tendsto_exp_div_rpow_atTop` composed with `t ↦ c t^δ`); `eventually_mul_rpow_le` and
  `eventually_mul_rpow_log_le` — for `γ < 1`, eventually `C t^γ ≤ ε t` and `C t^γ log t ≤ ε t` (from
  `tendsto_rpow_neg_atTop` and `isLittleO_log_rpow_atTop`).
  On top of them the two parameter conditions are verified for the concrete scale rule `s = t^β`,
  `H = t^{-α} s/(8t)`:
  * `eventually_tail_condition` (needs `0 < α`, `β ≤ 1`, `1 + α < 2β`): since `4/H = 32 t^{1+α-β}`
    and `sH/2 = t^{2β-α-1}/16`, the condition `(1 + 4/H)³ e^{−sH/2} ≤ 1` reduces to
    `35937 t^{3(1+α−β)} ≤ e^{t^{2β−α−1}/16}`, which is the stretched-exponential comparison.
  * `eventually_smallness` (needs `0 < α < β/2`, `β < 2/3`): the closed-form bound is below
    `ε(t−1)` for large `t`, uniformly over any logarithm argument `A ≤ 21t` — the main term is
    `49 t^{3β/2}` with `3β/2 < 1`, and the correction is `160 t^{1+α−β/2}(log 21 + log t)` with
    `1 + α − β/2 < 1`.
  All three exponent constraints (`1 + α < 2β`, `β < 2/3`, `α < β/2`) are simultaneously satisfiable
  — `α = 1/4`, `β = 0.65` — so the parameter regime is nonempty and the `o(ν)` conclusion is now a
  matter of assembling the pieces.

- 2026-08-04 — **Reduction I is closed: the Wiman–Valiron estimate with an `o(ν)` defect is proved
  unconditionally in Lean** (`WimanValironSmallDefect.lean`, axiom-clean, in the umbrella).

      exists_radius_defect_le_eps_of_transcendental :
        EntireCoeffs a → a n₀ ≠ 0 → (∀ M, ∃ n ≥ M, a n ≠ 0) → 0 < ε → ∀ R,
          ∃ y ≥ R, ∃ z, ‖z‖ = e^y ∧
            ‖z f'(z)/f(z) − ν(|z|)‖ ≤ ε · ν(|z|)

  No hypothesis on the function beyond entirety and transcendence (infinitely many nonzero
  coefficients, which is what `htrans` says); no exceptional set to quantify away — the statement is
  "beyond every bound there is such a radius", which is exactly what the composition-growth
  induction consumes.  The parametrised form `exists_radius_defect_le_eps` carries the exponent pair
  `(α, β)` subject to `0 < α`, `α < β/2`, `β < 2/3`, `1 + α < 2β`; the corollary discharges all four
  at `α = 1/4`, `β = 13/20` by `norm_num`, so the hypothesis set is demonstrably inhabited and the
  theorem is not vacuous.
  The chain, end to end: Borel at exponent `α` → a non-doubling window → the measure hypothesis by
  halving that window → the tail form of the estimate → the closed form `49 s^{3/2} + 20√s log(…)/H`
  → the two eventual comparisons.  Six modules, all axiom-clean:
  `BorelGrowthExponent`, `WimanValironSelection`, `WimanValironPolynomialBound`,
  `WimanValironCleanBound`, `RpowExpAsymptotics`, `WimanValironSmallDefect`.
  The one hypothesis that is *not* discharged inside the chain is transcendence, and it is genuinely
  needed: for a polynomial the central index is eventually constant and `z f'/f → deg`, so `ν` does
  not tend to infinity and no `ε ν` bound can hold.

- 2026-08-04 — **The Wiman point now carries both dominance statements, and Goldberg is not needed
  for them.**  `exists_radius_dominates_and_defect_le_eps` (axiom-clean) produces, beyond every
  bound, a radius `e^y` and a point `z` on that circle with

      C‖z‖^k ≤ ‖f(z)‖,   ν(e^y)^dpow ≤ ε₂‖f(z)‖,   ‖z f'/f − ν‖ ≤ ε ν,

  for arbitrary `k, dpow, C, ε, ε₂`.  The first is the corpus's `tendsto_maxTerm_div_pow_atTop`
  pushed out along `R`; the second is the one the card had earmarked for Goldberg's finite-order
  theorem, and it turns out not to need it.  The reason: the *selection window itself* forces growth.
  Convexity of `log μ(e^·)` with derivative `ν` gives
  `log μ(e^y) ≥ log μ(e^x) + ν(e^x)(y − x) ≥ log μ(1) + ν(e^x)H`, and the selected window has
  `H = t^{β−α−1}/8` with `t = ν(e^x)+1`, so `ν(e^x)·H ≥ t^{β−α}/16` — a positive power of `ν`.
  Meanwhile `ν(e^y) < 2t` by the non-doubling property already carried by the selection.  So
  `ν(e^y)^dpow ≤ (2t)^dpow` is a *power* of `t` while `‖f(z)‖ ≥ μ(e^y) ≥ μ(1) e^{t^{β−α}/16}` is a
  stretched exponential in `t`, and `eventually_mul_rpow_le_exp_rpow` closes it.  Finite order is
  never used; the argument is unconditional for every transcendental entire function.
  Consequence for the gap list: **Goldberg's theorem is not required for the top-symbol reduction of
  Reduction I** — its role there was exactly to make `ν` polynomially bounded so that the
  lower-degree terms die, and the window growth does that job directly.  (Goldberg/Strelitz are still
  what identify the exponent `ρ` with the Newton slope; that is a separate use.)
  Supporting change: the maximum-modulus fact `maxTerm a (e^x) ≤ ‖f(z)‖` is now threaded through the
  whole chain (`WimanValironRadius` → `…PolynomialBound` → `…Selection` → `…SmallDefect`), so the
  selected point's modulus is usable downstream rather than being consumed internally.

- 2026-08-04 — **The top-symbol reduction of Reduction I is a Lean theorem**
  (`TopSymbolReduction.lean`, `TopSymbolWimanPlace.lean`, both axiom-clean, both in the umbrella).
  The algebraic half is unconditional and needs no analysis: `monomial_div_pow` divides a monomial
  `A F^b W^c` of total degree `b + c ≤ d` by `F^d` into `A T^c / F^{d−b−c}` with `T = W/F`, and
  `norm_topSymbol_le` splits the relation by total degree to give

      ‖∑_{b+c=d} A_{b,c} T^c‖ ≤ (∑_{b+c<d} ‖A_{b,c}‖ ‖T‖^c) / ‖F‖

  whenever `∑ A_{b,c} F^b W^c = 0` and `‖F‖ ≥ 1`.  The analytic half is
  `exists_radius_norm_topSymbol_le`: for a transcendental entire solution of such a relation with
  *polynomial* coefficients, every `η, ε > 0` and every `R` admit a radius `e^y > e^R` and a point
  `z` on that circle with

      ‖∑_{b+c=d} A_{b,c}(z) (f'(z)/f(z))^c‖ ≤ η    and    ‖z f'/f − ν‖ ≤ ε ν.

  The step that makes it work is the observation that the coefficient weight is bounded by
  `Λ^{D+d}` with `Λ = max(‖z‖, (1+ε)ν)` and `D` the largest coefficient degree — so the *single*
  quantity `Λ^{D+d}` has to be beaten, and the two dominance conclusions of the Wiman point beat it
  in the two cases of the maximum separately.  Trying instead to beat the product `‖z‖^D ν^d`
  directly does not work from those two facts alone.
  Reduction I's analytic and algebraic content is therefore complete in Lean up to the identification
  of the Newton slope with `ρ − 1`, which is the remaining Goldberg/Strelitz-flavoured input.

- 2026-08-04 — **The nondegenerate Wiman place is proved in Lean, without Newton–Puiseux**
  (`RootProximity.lean`, `WimanPlaceRoot.lean`, both axiom-clean, both in the umbrella).
  Two gates ticked: the `o(ν)` remainder gate (closed by `exists_radius_defect_le_eps`) and the
  Wiman-place gate.
  The Newton–Puiseux route was checked and rejected as unnecessary here.  Mathlib has no Puiseux
  series and no algebraic closure of Hahn series, so constructing a branch means building the whole
  iteration-and-limit argument.  But the *place* is only used to say that `f'` sits over a root of
  the top symbol — and over ℂ that follows from factorisation alone:
  `exists_root_pow_dist_le` proves that for any polynomial `Q` of degree `n ≥ 1` and any point `T`
  there is a root `r` with `‖T − r‖^n ‖lead Q‖ ≤ ‖Q(T)‖`, since `‖Q(T)‖` is `‖lead‖` times the
  product of the distances and every factor is at least the smallest one.
  `exists_radius_wiman_place` then combines it with the top-symbol bound: if the top symbol has
  `T`-degree `m ≥ 1` with a coefficient polynomial that is not identically zero, then beyond every
  bound there is a radius `e^y`, a point `z` on that circle and a **root `r` of the top symbol at
  `z`** with

      ‖f'(z)/f(z) − r‖^m · ‖A(z)‖ ≤ η    and    ‖z f'/f − ν‖ ≤ ε ν.

  The coefficient does not vanish at `z` because the radius is pushed past Cauchy's root bound for
  `A`, which is a fixed finite number.  Supporting lemmas: `topSymbolPoly` with its evaluation,
  degree and top-coefficient identities.
  What the Puiseux branch would add beyond this is the *exponent* — the identification of the slope
  with `ρ − 1` — which is the Goldberg/Strelitz input, not the place itself.

- 2026-08-04 — **The root estimate the Clunie induction actually needs is now proved pointwise**
  (`AlgebraicRootGrowth.lean`, axiom-clean, in the umbrella).  The existing
  `characteristic_le_posLog_of_isRoot` routes through Cauchy's bound, which needs a *supremum* of the
  coefficients over the circle; converting that back into a characteristic requires Poisson–Jensen
  (`log M(r) ≲ T(2r)`), which neither mathlib nor the corpus has.  That is a real obstruction on the
  Cauchy route and it is avoidable.
  The elementary form: if `∑_{i ≤ n} c_i g^i = 0` with `c_n ≠ 0` and `n ≥ 1`, then wherever
  `‖g‖ ≥ 1` one has `‖g‖^n ≤ (∑_{i<n} ‖c_i/c_n‖)‖g‖^{n−1}`, hence

      ‖g‖ ≤ max(1, ∑_{i<n} ‖c_i/c_n‖)    (`norm_le_max_sum_of_root`)

  and therefore `log⁺‖g‖ ≤ log⁺(∑_{i<n} ‖c_i/c_n‖)` (`posLog_norm_le_of_root`).  Every quantity is
  evaluated at the *same point*, so the inequality survives integration over a circle unchanged —
  the characteristic form is a circle average of a pointwise inequality, with no maximum-modulus
  step anywhere.  `posLog_sum_le` supplies the accompanying splitting
  `log⁺(∑_{i∈s} x_i) ≤ ∑ log⁺ x_i + card(s)·log 2`.
  This is the last analytic ingredient of the Clunie induction's *inequality*; what remains for that
  gate is the composition-growth separation itself (the statement that composition makes the states
  separate), which is the genuinely external Clunie–Steinmetz input.

- 2026-08-04 — **The Clunie induction's inequality is now a theorem end to end**
  (`MultivariateRelationGrouping.lean`, axiom-clean, in the umbrella).  The card's argument is
  "regard the relation as a polynomial in the dependent state with coefficients in the previous
  states, and apply the root estimate".  Both halves are now Lean:
  * `sum_eq_sum_groupedCoeff` — a finite monomial sum `∑_e A_e ∏_i x_i^{e_i}` equals
    `∑_{j ≤ N} C_j x_last^j` where `C_j` is the fibre sum over `{e : e_last = j}`, and `C_j`
    involves only the *other* variables.  This is `Finset.sum_fiberwise_of_maps_to` plus factoring
    the last variable out of each monomial.
  * `posLog_norm_last_le_of_relation` / `posLog_norm_last_le_sum` — if the relation vanishes and the
    top fibre coefficient `C_N` is nonzero, then
    `log⁺‖x_last‖ ≤ ∑_{j<N} log⁺‖C_j/C_N‖ + N log 2`.
  * `posLog_norm_groupedCoeff_le` — each fibre coefficient is controlled by the data it is built
    from: `log⁺‖C_j‖ ≤ ∑_{e in the fibre}(log⁺‖A_e‖ + ∑_{i ≠ last} e_i log⁺‖x_i‖) + |S| log 2`,
    via `posLog_prod_le` (products cost nothing) and `posLog_pow_le` (a power costs its exponent).
  Chaining the three gives exactly `log⁺‖F_k‖ ≤ O(coefficient weights) + O(∑_{j<k} log⁺‖F_j‖)`
  pointwise — the card's `T(r,F_k) = O(log r + ∑_{j<k} T(r,F_j))` before integration, and since
  every step is a pointwise inequality between quantities at the same point, integrating over a
  circle is immediate and needs no maximum-modulus input.
  The Clunie gate is therefore reduced to its single external ingredient: the composition-growth
  separation itself, i.e. that composition with a transcendental entire outer function makes
  `T(r,F_k)` outgrow `log r + ∑_{j<k} T(r,F_j)`.  Everything the induction does *with* that input is
  formalized.

- 2026-08-04 — **The Clunie estimate is now one inequality** (`posLog_norm_last_le_weight`,
  axiom-clean).  Chaining the three previous bricks and collapsing the fibre double sum
  (`sum_fibres_le`: the fibres below the top degree are disjoint subsets of the monomial family, so
  their total is at most the whole), the dependent state obeys

      log⁺‖x_last‖ ≤ ∑_{e ∈ S}(log⁺‖A_e‖ + ∑_{i ≠ last} e_i log⁺‖x_i‖)
                      + N·log⁺(1/‖C_N‖) + (N|S| + N)·log 2

  at every point where the relation holds and the top grouped coefficient `C_N` is nonzero.  This is
  the card's `T(r,F_k) = O(log r + ∑_{j<k} T(r,F_j))` with every constant explicit and every term
  evaluated at the same point.  The `N log⁺(1/‖C_N‖)` term is the honest one the Nevanlinna
  treatment absorbs into the counting function of the zeros of `C_N`; pointwise it simply stands
  there, and it vanishes from the conclusion as soon as `C_N` is bounded away from zero.
  Note this is where the induction hypothesis enters in the paper argument: `C_N ≠ 0` as a function
  is exactly the algebraic independence of the *previous* states, which is what makes the induction
  an induction rather than a genericity assumption.

- 2026-08-04 — **The Clunie contradiction is now a theorem** (`not_forall_relation_of_separated`,
  axiom-clean).  With `clunieWeight S A x N` naming the bound of the previous entry:
  `sum_ne_zero_of_clunieWeight_lt` says a monomial relation with nonvanishing top grouped
  coefficient *cannot hold* at a point where the last quantity outgrows that weight, and
  `not_forall_relation_of_separated` lifts this to functions — a single separated point kills the
  identity.  This is precisely the card's "at the first algebraic dependence, the root estimate
  would bound `T(r,F_k)`, contradicting the successive Clunie separation", with the contradiction
  discharged in Lean.
  What the Lean layer now takes as input is the separation itself, at one point, in the sharp
  pointwise form `clunieWeight < log⁺‖F_k‖` — which is what Clunie--Steinmetz composition growth
  supplies and is the only remaining external ingredient of Reduction III.

- 2026-08-04 — **The induction hypothesis of the Clunie argument is formalized**
  (`MonomialIndependence.lean`, axiom-clean, in the umbrella).  `PolyIndependent F` says no monomial
  relation in `F` with polynomial coefficients vanishes identically unless every coefficient is the
  zero polynomial.  The monomials are indexed by an *arbitrary* finite set carrying an injective
  exponent map rather than by exponent vectors themselves — that is what lets the definition be
  applied to a fibre of a bigger relation directly, with no image-and-choice construction.
  `coeff_eq_zero_of_groupedCoeff_zero` is the step the induction turns on: if the states before the
  last are polynomially independent and a fibre coefficient `C_j` vanishes identically, then every
  coefficient in that fibre is zero.  So `C_N ≢ 0` for the top nonvanishing fibre — which is the
  hypothesis `posLog_norm_last_le_weight` needs.  Supporting: `erase_last_eq_image` and
  `prod_erase_last` (dropping the last coordinate identifies the punctured index set with the
  smaller one).
  Also on 2026-08-04: the "What Lean does not yet carry" section was rewritten — four of its five
  items are now built or bypassed, and it had become the card's most misleading paragraph.

- 2026-08-04 — **The Clunie induction step is proved** (`coeff_eq_zero_of_relation`,
  `coeff_eq_zero_of_relation'`, axiom-clean).  `SeparatesLast F` names the analytic input in the
  form the argument actually consumes: wherever the top fibre coefficient is not identically zero,
  *some* point carries both a nonzero value of it and the growth separation of the last state.
  Given that, and polynomial independence of the previous states, no monomial relation with
  polynomial coefficients holds:

      PolyIndependent (F ∘ castSucc) → SeparatesLast F →
        (∀ w, ∑_e (A e).eval w ∏_i (F i w)^{e i} = 0) → ∀ e ∈ S, A e = 0

  The proof is an induction on the degree in the last state.  At degree `0` the relation *is* a
  relation among the previous states, so the induction hypothesis finishes it.  At degree `M+1`
  there are two cases: if the top fibre coefficient vanishes identically then its coefficients are
  zero (the previous entry) and the degree drops, so the inductive hypothesis applies to the rest;
  otherwise separation supplies a point where the relation is contradicted.
  This is the whole of the card's "at the first algebraic dependence … contradicting the successive
  Clunie separation", formalized.  The only thing not in Lean is `SeparatesLast` itself — the
  Clunie–Steinmetz composition-growth theorem — and it now has a precise Lean statement to be
  discharged against.

- 2026-08-04 — **The Clunie induction now chains** (`polyIndependent_zero`,
  `polyIndependent_succ`, axiom-clean).  `polyIndependent_of_exponentVector` transfers the
  exponent-vector conclusion back into the index-set definition (the one place a choice construction
  is needed: pick a preimage under the injective exponent map), so the step is stated in the same
  form as its hypothesis and composes.  With the base case — the empty family is independent, since
  a relation there is a single polynomial vanishing on all of `C` — the chain reads

      PolyIndependent (F restricted to the first m)  +  SeparatesLast (first m+1)
        ⟹  PolyIndependent (first m+1),

  starting from `m = 0`.  Iterating gives transcendence degree `n` for the state field, which is what
  Reduction III consumes.  Everything in that chain is proved; the only input is `SeparatesLast` at
  each level.

- 2026-08-04 — **`polyIndependent_of_chain`** (axiom-clean): a family whose every initial segment
  separates its last member is polynomially independent.  This is the card's "thus the state field
  has transcendence degree `n`" as a single theorem, by induction over the family with
  `polyIndependent_zero` as base and `polyIndependent_succ` as step.
  The Lean gate for Reduction III is therefore ticked in the only sense it can be: everything the
  Clunie induction *does* is proved, and its analytic input has a precise Lean statement
  (`SeparatesLast`) rather than a prose description.  Discharging `SeparatesLast` is the
  Clunie–Steinmetz composition-growth theorem and stays external.

- 2026-08-04 — **Started on the external inputs: the polynomial minimum-modulus theorem**
  (`PolynomialMinimumModulus.lean`, axiom-clean, in the umbrella).  With every Lean gate closed, the
  two remaining items are the classical analytic theorems themselves (Goldberg/Strelitz and
  Clunie–Steinmetz).  Both route through a minimum-modulus statement, and its polynomial case is
  elementary:
  * `norm_eval_ge_of_roots_far` — a monic polynomial at distance `≥ H` from all its roots has
    `‖p(z)‖ ≥ H^{deg p}`.  (Factor through the roots; every factor is at least `H`.)
  * `exists_radius_norm_eval_ge` — if the range of radii is longer than `2·deg·H`, some radius in it
    keeps *the whole circle* at distance `≥ H` from every root, hence `‖p‖ ≥ H^{deg}` on it.  The bad
    radii lie in one interval of length `2H` around each `‖root‖`, so they cannot cover a longer
    range; the argument is a Lebesgue-measure pigeonhole, not a covering construction.
  Recorded for scope: Cartan's lemma proper (total radius `2H` independent of the degree, at the cost
  of `(H/e)^{deg}`) is *not* needed for this use and is not built — the trivial covering by one disc
  per root already gives a bad set of measure `2·deg·H`, which suffices whenever the radius range can
  be taken long.  What genuinely blocks the entire-function case is that the number of roots in a
  disc grows, so the range must grow with it; that is where Jensen's formula enters, and it is the
  next brick on this line.

- 2026-08-04 — **Corpus audit of the minimum-modulus line, and the combination lemma.**  Correcting
  the previous entry's implicit scope: most of this line is already corpus-owned.
  * The **zero-free** minimum modulus is done — `RHTower/MinimumModulus.norm_lower_bound_of_anchor`
    proves `‖f z‖ ≥ m·exp(−2 log(M/m)·r/(R−r))` on `closedBall c r` for zero-free analytic `f` with
    one anchor value and one supremum, via Borel–Carathéodory.  `ThreeCircles` and `BallLogarithm`
    carry further lower bounds.
  * The **zero counting** is done — `UniformZeroCountBound` and `JensenCountingLowerBound` wrap
    mathlib's `AnalyticOnNhd.sum_divisor_le`.
  So the only missing brick on this line is *zero extraction*: writing an analytic `f` on a disc as
  `P · g` with `P` the monic polynomial of its zeros there and `g` analytic and zero-free.
  `exists_radius_norm_ge_of_factorization` (axiom-clean) is the combination that consumes it: given
  such a factorisation and a lower bound `L` for `g`, a long enough range of radii contains a circle
  on which `‖f‖ ≥ H^{deg P} · L`.  The zero-free bound enters as a hypothesis rather than an import
  — `norm_lower_bound_of_anchor` lives in the RH area, which this area must not import.
  Scope note: the combination is stated so that the remaining gap is exactly one theorem, and it is a
  standard removable-singularity argument rather than anything specific to this card.

- 2026-08-04 — **Zero extraction, first step** (`AnalyticRootFactor.lean`, axiom-clean, in the
  umbrella).  `exists_factor_of_root`: at a zero of an analytic function that is not identically zero
  nearby, one linear factor divides out and the quotient stays analytic — near `a`,
  `f z = (z − a)·g z` with `g` analytic.  Mathlib supplies the normal form `f = (z−a)^n • g₀` with
  `g₀ a ≠ 0`; the content added is that `n ≥ 1` at a zero (otherwise `f a = g₀ a ≠ 0`), so the normal
  form can be rewritten with a single explicit linear factor.  `eq_div_of_factor` identifies `g` with
  `f/(z−a)` on the punctured neighbourhood.
  A trap worth recording: the naive statement "`f/(z−a)` is analytic at `a`" is **false as written**
  in Lean.  At a simple zero the quotient evaluates to `0/0 = 0` at `a` while the analytic
  continuation is `g a ≠ 0`, so the function literally defined by the division is not even continuous
  there.  The factorisation must be stated multiplicatively, or the value at `a` patched; stating it
  as `f = (z−a)·g` avoids the issue entirely.
  Remaining on this line: iterate the extraction over the finitely many zeros in a disc to reach
  `f = P·g` with `P` monic and `g` zero-free, which is what
  `exists_radius_norm_ge_of_factorization` consumes.

- 2026-08-04 — **Zero extraction, globalised** (`exists_global_factor_of_root`, axiom-clean).  On any
  open set where `f` is analytic, a zero `a` at which `f` is not identically zero yields
  `f z = (z − a)·g z` for **all** `z` in the set, with `g` analytic there.  The quotient is defined
  by cases — the analytic continuation's value at `a`, and `f/(z−a)` elsewhere — and the two
  descriptions agree on a punctured neighbourhood of `a`, which is what makes the patched function
  analytic at `a` as well.  This is the step the local lemma could not give, since the honest local
  statement is multiplicative and says nothing off the neighbourhood.
  Remaining: iterate over the finitely many zeros in a disc (the count is already bounded by the
  corpus's Jensen wrappers) to reach `f = P·g` with `P` monic and `g` zero-free.

- 2026-08-04 — **Full-multiplicity extraction** (`exists_pow_factor_of_root`, axiom-clean).
  Strengthening the previous entry from one linear factor to the whole power: at a zero where `f` is
  not identically zero, there are `n` and an analytic `g` on the *whole* open set with `g a ≠ 0` and
  `f z = (z − a)^n · g z` everywhere on it.  This subsumes the single-factor version and is the
  right form for iteration, since the quotient is now guaranteed *not* to vanish again at `a` — the
  multiplicity bookkeeping that a one-factor-at-a-time induction would have to carry as a side
  condition is discharged inside the statement.
  Pleasant surprise in the proof: the identity at the point `a` itself is exactly mathlib's
  `hloc.self_of_nhds`, with no case split on whether `n` is zero — `f a = (a−a)^n • g₀ a` already
  says the right thing in both regimes.
  Remaining on this line: finiteness of the zero set on a compact disc, then iterate to `f = P·g`.

- 2026-08-04 — **The invariants the extraction iteration needs** (`AnalyticRootFactor.lean`,
  axiom-clean): `not_eventually_zero_of_global_factor` — the quotient inherits "not identically zero
  near a point", so the hypothesis of `exists_pow_factor_of_root` survives each step;
  `eval_eq_zero_iff_of_global_factor` — away from the extracted point, the zeros of the quotient are
  exactly those of the original, so the remaining work is not lost or created by a step.
  These are the two facts an induction over the zero set has to carry, and they are what make the
  iteration bookkeeping mechanical rather than delicate.
  Survey result for the *finiteness* half: mathlib carries it two ways —
  `MeromorphicOn.divisor_support_finite_of_subset` (finite divisor support on subsets of a compact)
  and `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` (zeros codiscrete unless the
  function vanishes identically).  Either route closes the remaining gap; the divisor route needs the
  `order`-to-`divisor` translation, the codiscrete route needs "compact + discrete ⟹ finite".

- 2026-08-04 — **Finiteness of the zero set** (`finite_zeros_closedBall`, axiom-clean).  An analytic
  function that is nowhere locally zero has finitely many zeros in a closed ball.  The proof takes
  the topological route rather than the divisor one: the zero set is `closedBall ∩ f⁻¹{0}`, closed by
  `ContinuousOn.preimage_isClosed_of_isClosed` and hence compact; it is discrete because at each of
  its points mathlib's `eventually_eq_zero_or_eventually_ne_zero` gives a punctured neighbourhood
  free of zeros, which is exactly `𝓝[≠] x ⊓ 𝓟 S = ⊥`; and `IsCompact.finite` closes it.
  The divisor route (`MeromorphicOn.divisor_support_finite_of_subset`) would also work but needs the
  `order`-to-`divisor` translation, which is more API than the three topological steps.
  With this, both halves the factorisation needs are present — full-multiplicity extraction at a
  point, and finiteness of the set of points to extract.  What remains is the induction that runs
  the extraction over that finite set.

- 2026-08-04 — **The extraction induction** (`exists_prod_factor_of_finset`, axiom-clean).  Over any
  finite set `T` of points of an open set, an analytic function that is nowhere locally zero factors
  as `f z = (∏_{a ∈ T} (z − a)^{m a}) · g z` with `g` analytic on the whole set and `g a ≠ 0` for
  every `a ∈ T`.  The induction is over `T`: extract the head at full multiplicity, apply the
  hypothesis to the quotient (whose non-degeneracy is the invariant proved two entries ago), and note
  that the head's non-vanishing survives because the remaining factors `(a − b)^{m b}` with `b ≠ a`
  are nonzero.
  Combined with `finite_zeros_closedBall`, this gives the factorisation `f = P · g` with `g`
  zero-free on the ball, which is what `exists_radius_norm_ge_of_factorization` consumes — the
  minimum-modulus chain for entire functions is now complete except for assembling those two into a
  single statement.

- 2026-08-04 — **Zero extraction is complete** (`exists_zero_free_factor_closedBall`, axiom-clean).
  An analytic function that is nowhere locally zero factors on an open set as a finite product of
  powers of linear factors, indexed by its zeros in a closed ball, times an analytic function with
  **no zeros in that ball**.  The zero-freeness is the point and it comes out of the construction
  rather than needing a separate argument: a zero of the quotient inside the ball would be a zero of
  `f` there, hence one of the extracted points, at which the quotient is nonzero by construction.
  This closes the brick that `exists_radius_norm_ge_of_factorization` was written against, so the
  entire-function minimum-modulus statement is now assemblable from corpus theorems alone:
  `finite_zeros_closedBall` → `exists_prod_factor_of_finset` → `exists_zero_free_factor_closedBall`
  → (with `norm_lower_bound_of_anchor` for the zero-free factor) → a circle on which `‖f‖` is
  bounded below.

- 2026-08-04 — **`f = P · g` in polynomial form** (`exists_polynomial_factor_closedBall`,
  axiom-clean).  The extracted product `∏_{a∈T}(z−a)^{m a}` is repackaged as `P.eval z` for the monic
  polynomial `P = ∏_{a∈T}(X − C a)^{m a}`, giving

      f = P · g,   P monic,   g analytic on U with no zeros in the closed ball.

  That is exactly the hypothesis shape of `exists_radius_norm_ge_of_factorization`, so the two ends
  of this line now meet: from an analytic, nowhere-locally-zero `f` one gets a circle in any
  sufficiently long range of radii on which `‖f‖ ≥ H^{deg P} · L`, with `L` any lower bound for the
  zero-free factor.
  The remaining step is quantitative rather than structural: bounding `deg P` (the number of zeros,
  which the corpus's Jensen wrappers already control) and supplying `L` from
  `norm_lower_bound_of_anchor`.  Both are available; the assembly crosses into the RH area, so it
  belongs there or takes those two as hypotheses, which is how the HTGeometry statement is phrased.

- 2026-08-04 — **The degree is exposed** (`natDegree_prod_X_sub_C_pow`,
  `exists_polynomial_factor_closedBall_degree`, axiom-clean).  The extracted polynomial has
  `natDegree = ∑_{a ∈ T} m a`, the total multiplicity of the zeros in the ball, and the factorisation
  theorem now reports it along with the zero set `T` and the multiplicities.  That is the quantity a
  counting estimate has to bound, so a caller can now chain a Jensen bound on the zero count directly
  into `exists_radius_norm_ge_of_factorization`, whose radius-range hypothesis is stated in terms of
  `deg P`.
  Deliberately *not* built: a wrapper that performs that chaining inside one theorem.  The zero-free
  lower bound and the counting bound both live outside this module (the first in the RH area), so a
  single wrapper would either force a cross-area import or carry hypotheses that mention the
  existentially produced `g` — neither is worth it when the two ends compose in three lines at the
  call site.

- 2026-08-04 — **The connectedness step of the composition estimate**
  (`CompositionImageCircle.lean`, axiom-clean, in the umbrella).  `exists_norm_eq_of_segment`: a
  continuous function vanishing at the centre of a disc attains *every* modulus between `0` and
  `‖g z₀‖` for any `z₀` in the disc — apply the intermediate value theorem to `t ↦ ‖g(t z₀)‖` along
  the radius.  `exists_le_norm_comp` composes it with a lower bound for an outer function on a
  circle: if `g` reaches modulus `s` and `‖f‖ ≥ L` on `|w| = s`, then `‖f ∘ g‖ ≥ L` somewhere in the
  disc.
  Together with the minimum-modulus line this is the shape of Pólya's composition inequality: the
  inner function's image sweeps every circle up to its maximum, and on a good circle — one the
  minimum-modulus theorem selects — the outer function cannot be small.  What is still missing to
  reach Clunie--Steinmetz is the comparison between `M` and the Nevanlinna characteristic
  (Poisson--Jensen), which is the same gap noted earlier on the Cauchy route.

- 2026-08-04 — **Pointwise composition separation, and why the `M`-versus-`T` gap does not block it**
  (`exists_posLog_separation`, axiom-clean).  If the inner function is bounded by `Mg` on the disc
  and reaches modulus `s`, and the outer function is at least `L` on the circle `|w| = s`, then at
  some point of the disc

      C · log⁺‖g z‖  <  log⁺‖f(g z)‖

  for any `C ≥ 0` with `C log⁺ Mg < log⁺ L`.
  This matters for scope.  The previous entry recorded Poisson–Jensen (`log M ≲ T`) as the next
  obstruction, on the grounds that composition growth is a statement about the Nevanlinna
  characteristic.  That is true of the *classical* statement but not of the one this development
  needs: `SeparatesLast` was formulated pointwise — it asks for a single point where the weight is
  beaten — and the inequality above is exactly that shape.  So the characteristic never enters, and
  Poisson–Jensen is **not** on the critical path for discharging `SeparatesLast`.
  What is still needed is the outer function's lower bound `L` on a circle, i.e. the entire-function
  minimum modulus assembled from the extraction chain plus `norm_lower_bound_of_anchor`, together
  with the transcendence input `log M(s,f)/log s → ∞` (already in the corpus as
  `tendsto_maxTerm_div_pow_atTop`) to make `C log⁺ Mg < log⁺ L` hold.

- 2026-08-04 — **The zero-free factor is bounded above** (`norm_zero_free_factor_le`, axiom-clean).
  If all roots of the monic factor lie at distance at least `H` inside the circle `|z| = R`, then on
  that circle `‖P‖ ≥ H^{deg P}`, so `‖g‖ ≤ Mf / H^{deg P}` wherever `‖f‖ ≤ Mf`.
  This supplies the *upper* bound that `norm_lower_bound_of_anchor` needs for the zero-free factor —
  the last analytic ingredient of the entire-function minimum modulus.  The three inputs that
  theorem asks of `g` are now each available: analyticity and zero-freeness on the ball from the
  extraction chain, the supremum from this lemma, and the anchor value `‖g 0‖` from the same
  factorisation at the centre.

- 2026-08-04 — **Maximum modulus in circle form** (`norm_le_of_sphere_bound`, axiom-clean).  A bound
  on the circle `|z| = R` bounds the whole closed ball, for a function analytic on a neighbourhood of
  that ball.  This is mathlib's `Complex.norm_le_of_forall_mem_frontier_norm_le` packaged with the
  three identifications a caller would otherwise redo each time — `closure (ball) = closedBall`,
  `frontier (ball) = sphere`, and `DiffContOnCl` from `AnalyticOnNhd`.
  With it, `norm_zero_free_factor_le` upgrades from the circle to the ball, which is the shape
  `norm_lower_bound_of_anchor` requires (`∀ z ∈ ball c R, ‖g z‖ ≤ M`).  Every hypothesis of the
  entire-function minimum modulus is now a proved corpus statement.

- 2026-08-04 — **The two-radius bound** (`prod_norm_ge_of_roots_inside`, axiom-clean).  If every
  extracted point lies within radius `R`, then on the circle of radius `R' ≥ R` the product of the
  linear factors is at least `(R' − R)` to the total multiplicity.
  This resolves a mismatch that surfaced while assembling the minimum modulus.  Extracting on the
  *same* ball where the bound is wanted makes the two requirements incompatible: the extraction must
  cover all zeros of the ball (so the quotient is zero-free there), but the polynomial lower bound
  needs the roots to be at a positive distance from the circle, which fails when a zero sits on it.
  Using two radii — extract on `R`, bound on `R' > R` — satisfies both, and the quotient is then
  zero-free on the inner ball, which is exactly where `norm_lower_bound_of_anchor` is applied.
  The lemma is stated on the extracted product rather than on `Polynomial.roots`, which also avoids
  having to prove that the constructed polynomial's root multiset is the extraction set.

- 2026-08-04 — **The cofactor, with both bounds, in one theorem**
  (`exists_zero_free_cofactor_bounds`, axiom-clean).  For `R < R'` with `closedBall 0 R' ⊆ U` and
  `‖f‖ ≤ Mf` on `|z| = R'`, extracting the zeros of the *inner* ball produces `T`, `m` and `g` with:
  `g` analytic on `U`; every extracted point within radius `R`; `g` zero-free on `closedBall 0 R`;
  `‖g z‖ ≤ Mf / (R' − R)^{∑ m}` for `‖z‖ ≤ R'`; and `f = (∏ (z−a)^{m a}) · g` on `U`.
  That is precisely the hypothesis list of `norm_lower_bound_of_anchor` (analytic, zero-free, sup
  bound on the ball, anchor at the centre), so the entire-function minimum modulus is now a single
  application away, and — because this theorem needs no Borel–Carathéodory input itself — it lives in
  the reusable area with no cross-area import.
  This closes the assembly gap flagged in the previous entries: what remained was compatibility
  between "extract everything" and "roots away from the circle", and the two-radius statement above
  is what reconciles them.

- 2026-08-04 — **The extracted polynomial has no stray roots**
  (`mem_of_mem_roots_prod_X_sub_C_pow`, axiom-clean): every root of `∏_{a∈T}(X − C a)^{m a}` lies in
  `T`.  Proved by evaluation rather than through `Polynomial.roots_prod` — outside `T` every factor
  is nonzero, so the value is nonzero and the point is not a root.
  This is the bridge between the two phrasings in play: the extraction produces a *product over a
  Finset*, while the circle-selection theorem `exists_radius_norm_eval_ge` is phrased on
  `Polynomial.roots`.  Without it the selection could not be applied to the extracted polynomial,
  since nothing else identifies its root set.  With it, the final chain
  `exists_zero_free_cofactor_bounds` → `norm_lower_bound_of_anchor` → `exists_radius_norm_eval_ge`
  has no remaining structural gap.

- 2026-08-04 — **The entire-function minimum modulus is proved**
  (`RHTower/EntireMinimumModulus.lean`, `exists_radius_norm_ge_of_analytic`, axiom-clean, wired into
  the RH umbrella).  For `R < R'` with `closedBall 0 R' ⊆ U`, an analytic nowhere-locally-zero `f`
  bounded by `Mf` on the outer circle admits, for every range `[A, B]` inside the inner ball long
  enough for the number of zeros, a circle on which

      ‖f‖ ≥ H^{∑ m} · L,     L = ‖g 0‖ exp(−2 log(M/‖g 0‖) B/(R−B)) > 0.

  The proof is the chain assembled over the last several entries: extract the zeros of the inner ball
  and bound the cofactor above on the outer one (`exists_zero_free_cofactor_bounds`); floor the
  cofactor by Borel–Carathéodory (`norm_lower_bound_of_anchor`); select a circle avoiding the zeros
  by the measure argument (`exists_radius_norm_ge_of_factorization`).
  It is placed in the RH area only because `norm_lower_bound_of_anchor` lives there; everything else
  it uses is in the reusable area.  This is the last analytic ingredient of the composition
  separation: with a lower bound for the outer function on a circle, `exists_posLog_separation`
  produces the pointwise separation that `SeparatesLast` asks for.

- 2026-08-04 — **A self-contained zero-count bound** (`sum_multiplicity_mul_log_le`, axiom-clean):

      (∑ m) · log((R' − R)/R)  ≤  log(Mf / ‖f 0‖).

  This is Jensen's counting estimate in the form the minimum-modulus chain needs, but derived from
  the factorisation alone — no Jensen formula, no divisor API.  The mechanism: each extracted point
  contributes a factor at most `R` to `‖f 0‖ = ∏‖a‖^{m a}·‖g 0‖`, while the same point costs a factor
  at least `R' − R` in the cofactor's upper bound `‖g 0‖ ≤ Mf/(R'−R)^{∑m}`.  Comparing the two and
  taking logarithms isolates `∑ m`.
  Recorded because the earlier entries assumed this step would need mathlib's
  `MeromorphicOn.divisor` and the `order`-to-`divisor` translation.  It does not: the extraction
  already carries the multiplicities explicitly, which is exactly the information Jensen's formula
  would have to recover.  With `2R < R'` the logarithm on the left is positive, so this bounds
  `∑ m` and hence the `H^{∑ m}` loss in the minimum-modulus conclusion.

- 2026-08-04 — **The zero loss is bounded** (`log_pow_mul_ge_of_count`, axiom-clean).  If the total
  multiplicity `N` obeys `N D ≤ C` with `D > 0`, then

      log L + (C/D) log H ≤ log (H^N · L),

  so the `H^N` factor in the minimum-modulus conclusion costs at most `(C/D)·(−log H)`.  Chaining
  with `sum_multiplicity_mul_log_le` (which supplies `D = log((R'−R)/R)` and
  `C = log(Mf/‖f 0‖)`), the floor for `‖f‖` on the good circle becomes explicit and **no longer
  mentions the number of zeros**:

      log‖f‖ ≥ log L − (log(Mf/‖f 0‖) / log((R'−R)/R)) · (−log H).

  That is the classical shape of the minimum-modulus theorem — a loss proportional to the growth
  ratio `log(Mf/‖f 0‖)` — reached here without Jensen's formula or the divisor API.

- 2026-08-04 — **The minimum modulus, with the zero count eliminated**
  (`exists_radius_log_norm_ge_of_analytic`, axiom-clean).  For `2R < R'`, `f` analytic and nowhere
  locally zero on a neighbourhood of the outer ball with `f 0 ≠ 0` and `‖f‖ ≤ Mf` on the outer
  circle, and any range `[A,B]` inside the inner ball long enough, there is a circle on which

      log‖f‖  ≥  log L  −  (log(Mf/‖f 0‖) / log((R'−R)/R)) · (−log H),   L > 0.

  Nothing in the statement mentions the zeros: the count bound is folded in, and the range hypothesis
  is now phrased with the same growth ratio instead of `∑ m`.  `exists_radius_norm_ge_of_analytic`
  was strengthened to report the count bound alongside its conclusion so that this could be derived
  without redoing the assembly.
  This is the classical minimum-modulus theorem for analytic functions in usable form, and it is the
  outer-function input of the composition separation.  What remains for `SeparatesLast` is arithmetic
  on this floor: choosing the radii so that the right-hand side beats `C·log⁺Mg`, which is where the
  transcendence of the outer function enters through `tendsto_maxTerm_div_pow_atTop`.

- 2026-08-04 — **Transcendence in logarithmic form** (`TranscendentalLogGrowth.lean`,
  `eventually_log_maxTerm_ge`, axiom-clean, in the umbrella): for a transcendental entire power
  series and any `k, C`,

      C + k · log s  ≤  log μ(s)   for all large s.

  This is the corpus's `tendsto_maxTerm_div_pow_atTop` transposed into the additive form the
  separation arithmetic uses — one has to beat a fixed multiple of the logarithm of the inner
  function's size, and the inner size is itself at most a power of the radius on the relevant range.
  With this, the minimum-modulus floor and the separation criterion `C log⁺Mg < log⁺L` are expressed
  in the same currency, so what remains is a choice of radii rather than another analytic theorem.

- 2026-08-04 — **Separation from a logarithmic floor**
  (`exists_posLog_separation_of_log_floor`, axiom-clean): the separation criterion restated with the
  outer bound given as a floor for `log ‖f‖` on the circle — which is exactly what
  `exists_radius_log_norm_ge_of_analytic` produces, so the two now compose without a conversion
  step.
  Two hypotheses that looked necessary turn out not to be.  The outer function need not be nonzero
  on the circle: `log ≤ log⁺` holds in every case, including the junk value at zero, and the
  hypothesis `C log⁺Mg < Λ` already forces `Λ > 0`, so a vanishing outer value is simply excluded by
  the arithmetic rather than by an assumption.  Nor is any lower bound on `L` needed once the floor
  is stated logarithmically.  The interface is therefore: minimum modulus gives `Λ`, transcendence
  gives `Λ` large, and this lemma converts that into the pointwise separation `SeparatesLast` wants.

- 2026-08-04 — **The floor and the separation, in one statement**
  (`exists_circle_floor_and_separation`, axiom-clean).  The minimum-modulus theorem selects a circle
  and a floor `Λ` for `log‖f‖` on it; if the inner function reaches that circle and its size is small
  enough against the floor, the composition separates pointwise:

      0 ≤ s → s ≤ ‖g z₀‖ → C log⁺Mg < Λ →
        ∃ z, C log⁺‖g z‖ < log⁺‖f(g z)‖.

  The two conditions are stated as an implication rather than as hypotheses because `Λ` and `s` are
  produced by the theorem, so nothing about them can be assumed in advance.  That shape is also the
  honest one: it says precisely what a caller must check about the *selected* circle.
  This is the end of the analytic chain for the Clunie–Steinmetz side.  Discharging `SeparatesLast`
  for a concrete cascade is now the arithmetic of choosing `R, R', H, A, B` so that
  `C log⁺Mg < Λ` holds, with `eventually_log_maxTerm_ge` supplying the growth that makes it possible.

- 2026-08-04 — **Separation without the normalisation**
  (`exists_posLog_separation_of_log_floor_shift`, axiom-clean).  The inner function need not vanish
  at the centre; it is enough to measure the circle from its value there, since translating the outer
  function absorbs the shift (`f ∘ g = (f(· + g 0)) ∘ (g − g 0)`).  This matters for the cascade,
  where the inner states are compositions with no reason to vanish at the origin, so the earlier
  `g 0 = 0` hypothesis would have been unusable as stated.
  Also recorded: the `HTGeometry` umbrella was found broken by **duplicate names**, not by this
  work — `JetField.differentialJet_jet` and `JetField.algebraicIndependent_jet` were each re-proved
  in a newer module while already existing elsewhere (the first strictly more generally).  Renamed
  the newer copies.  A second file, `VolterraLinearIntegralEquation.lean`, is currently broken with
  genuine proof errors and is being edited by another session; it is left alone.  Every module of
  this line builds.

- 2026-08-04 — **The constant term, removed** (`ShiftedCoeffFun.lean`, axiom-clean, in the umbrella):
  `dropConst a` deletes the constant coefficient, `entireCoeffs_dropConst` shows entirety survives
  (the tail is unchanged, so the decay hypothesis transfers by an index shift), `coeffFun_zero` says
  a power series at the origin is its constant term, and `coeffFun_dropConst` gives
  `coeffFun (dropConst a) z = coeffFun a z − a 0`.
  This is the coefficient-level counterpart of the previous entry's translation: the shifted inner
  function `g − g 0` is again given by an entire coefficient sequence, so the Wiman--Valiron
  machinery — maximum term, central index, the point where the maximum is attained — applies to it
  directly.  Without this the translation would leave the shifted function outside the class the rest
  of the layer is stated for.

- 2026-08-04 — **The inner function reaches its shifted maximum term**
  (`exists_point_norm_sub_ge`, axiom-clean): on every circle there is a point where
  `‖g z − g 0‖ ≥ μ(dropConst a, r)`.  This discharges the hypothesis `s ≤ ‖g z₀ − g 0‖` of the
  composition separation, with `s` the shifted maximum term — and since `dropConst` preserves
  entirety and transcendence, `s` inherits the growth of `μ`, so it outgrows every power of `r`.
  The three hypotheses of `exists_posLog_separation_of_log_floor_shift` are therefore all supplied by
  corpus theorems now: continuity of the inner function, the reach `s ≤ ‖g z₀ − g 0‖`, and the floor
  for `log‖f‖` on the circle of radius `s` from the entire-function minimum modulus.

- 2026-08-04 — **The sharp separation criterion** (`exists_posLog_separation_sharp`, axiom-clean),
  and a correction to the previous three entries.  Those stated the criterion as
  `C log⁺Mg < Λ` with `Mg` a bound for the inner function over the *whole disc*.  That is the wrong
  comparison and it is not achievable in general: `Mg ≍ M(r,g)` while the floor is available at
  radius `s ≍ μ(r,g)`, and `log M(r)` and `log μ(2r)` are not comparable for an arbitrary entire
  function — which is exactly why the classical Clunie–Steinmetz statement is phrased with the
  Nevanlinna characteristic rather than the maximum modulus.
  The fix is to notice that only the *selected* point matters.  There `‖g z − g 0‖ = s` by
  construction, so `‖g z‖ ≤ s + ‖g 0‖`, and the criterion becomes

      C · log⁺(s + ‖g 0‖)  <  Λ,

  comparing the outer floor at radius `s` against `C log s`.  That *is* achievable: `Λ` grows like
  `k log s` for every `k` by transcendence of the outer function
  (`eventually_log_maxTerm_ge`), while the left side grows like `C log s`.  The supremum hypothesis
  disappears from the statement entirely.

### Log — the minimum-modulus route to composition separation is a dead end

- 2026-08-04 — **Proved limitation** (`CircleFloorLimitation.lean`, `circle_floor_le_neg`,
  axiom-clean).  The separation criterion needs a floor `Λ` with `Λ ≤ log‖f w‖` on a whole circle,
  beating `C log s`.  For `f = exp` no such floor exists: on the circle of radius `s` the modulus
  dips to `e^{-s}` at `w = −s`, so **every** admissible floor satisfies `Λ ≤ −s`.  The criterion
  `C log⁺(s + c) < Λ` is therefore unsatisfiable for large `s`, no matter how the radius is chosen.
  Consequence for the plan.  The connectedness step (`exists_norm_eq_of_segment`) shows the inner
  function's image meets every circle up to its maximum, and the only thing guaranteed at such a
  meeting point is the *minimum* of the outer function on that circle.  That minimum can be
  exponentially small — `exp` is the witness — so connectedness plus a minimum-modulus estimate
  cannot produce composition separation.  The entire-function minimum modulus built over the last
  several entries is correct and reusable, but it is **not** the right input here.
  What the classical argument (Pólya) actually uses is that the image contains a *full circle*, so
  that the maximum principle converts it into `M(r, f∘g) ≥ M(c M(r/2,g), f)` — a statement about the
  outer function's **maximum**, which transcendence does make large.  Getting the image to contain a
  circle is strictly more than connectedness and is the real content of that theorem; it is the next
  thing to build on this line.
  Recorded as a dead route so the minimum-modulus chain is not re-attempted here.

- 2026-08-04 — **The correct mechanism: transferring a maximum**
  (`PolyaMaximumTransfer.lean`, axiom-clean, in the umbrella).  `norm_le_of_sphere_subset_image`: if
  every point of `sphere c ρ` is a value of the inner function on the disc, then a bound `K` for
  `f ∘ g` on that disc bounds `f` on the **whole closed ball** of radius `ρ` about `c` — by the
  maximum principle, since the bound holds on the enclosing circle.  Supporting:
  `norm_le_of_sphere_bound_centre`, the maximum modulus at an arbitrary centre.
  Contrapositive, which is the useful direction: `M(ρ, f about c) ≤ max_{disc} ‖f ∘ g‖`.  For a
  transcendental outer function the left side outgrows every power of `ρ`, so the composition is
  large — and this is a statement about the outer function's *maximum*, exactly what the previous
  entry showed the minimum-modulus route could never supply.
  The remaining hypothesis is the one Pólya's theorem exists to provide: that the image of the disc
  contains a full circle of radius comparable to the inner function's size.  That is now the single
  open point on this line, and it is a statement about images of analytic maps rather than about
  growth.

- 2026-08-04 — **The missing hypothesis is in mathlib, and the minimum modulus is needed after all —
  for the inner function.**  `DiffContOnCl.ball_subset_image_closedBall` (mathlib,
  `Analysis/Complex/OpenMapping.lean`) says: if `ε ≤ ‖g z − g z₀‖` on a circle and `g` is not locally
  constant, then `ball (g z₀) (ε/2) ⊆ g '' closedBall z₀ r`.  Wrapped as
  `ball_subset_image_of_circle_floor` (axiom-clean).
  So the disc-in-image hypothesis of `norm_le_of_sphere_subset_image` is supplied by a
  *minimum-modulus statement for the shifted inner function* — the very machinery built earlier and
  written off two entries ago as inapplicable.  It was inapplicable to the **outer** function, where
  `exp` refutes it; applied to the **inner** function it is exactly right, because there the floor
  bounds how far the image reaches, not how large the outer function is.
  One adjustment was needed: `exists_radius_norm_ge_of_analytic` had acquired hypotheses `0 < Mf` and
  `f 0 ≠ 0` when the zero-count bound was folded in, and the shifted inner function `g − g 0` vanishes
  at the centre.  The count bound is now a conditional conjunct
  (`0 < Mf → f 0 ≠ 0 → …`), so the theorem applies to functions vanishing at the centre and the
  strengthening is not lost.
  Chain as it now stands: minimum modulus for `g − g 0` → disc in the image → maximum transfer →
  `M(ρ, f) ≤ max ‖f ∘ g‖` with `ρ` half the floor.  The open point is quantitative: making `ρ`
  comparable to the inner function's size.

- 2026-08-04 — **The composition-growth inequality** (`norm_le_of_circle_floor`, axiom-clean).
  If the inner function differs from its central value by at least `ε` on the circle of radius `s`
  and is not locally constant, then any bound `K` for `f ∘ g` on the closed disc of radius `s` bounds
  `f` on the closed disc of radius `ρ` about `g 0`, for every `ρ < ε/2`:

      (∀ z, ‖z‖ ≤ s → ‖f(g z)‖ ≤ K)  →  (∀ w, ‖w − g 0‖ ≤ ρ → ‖f w‖ ≤ K).

  Contrapositive: `max_{‖z‖ ≤ s} ‖f ∘ g‖ ≥ M(ρ, f about g 0)`.  This is Pólya's composition
  inequality in the form the corpus can supply — the two halves being the quantitative open mapping
  theorem (which converts the inner floor into a disc in the image) and the maximum principle (which
  converts the disc into a bound on the outer function).
  The outer function's *maximum* now appears on the right, so transcendence makes it large — the
  defect the `exp` witness exposed in the minimum-modulus route is gone.  What is left is to make
  `ε` comparable to the inner function's size, which is the minimum modulus for `g − g 0`.

- 2026-08-04 — **Composition growth, assembled** (`exists_radius_composition_bound`, axiom-clean).
  The minimum-modulus theorem applied to `g − g 0` selects a circle of radius `s ∈ [A,B]` on which the
  inner displacement is at least `H^{∑m}·L`; the composition inequality then says that for every
  outer function `f` analytic on the disc of radius `ρ < H^{∑m}·L/2` about `g 0`, any bound for
  `f ∘ g` on `closedBall 0 s` bounds `f` on that disc:

      (∀ z, ‖z‖ ≤ s → ‖f(g z)‖ ≤ K)  →  (∀ w, ‖w − g 0‖ ≤ ρ → ‖f w‖ ≤ K).

  The outer function is quantified *inside* the conclusion, which is the right shape: the circle and
  the floor depend only on the inner function, and the inequality then holds for every outer function
  at once.
  This is Pólya's composition inequality with every input a proved corpus statement.  What remains is
  the quantitative comparison — `H^{∑m}·L` against the inner function's size — which is the same
  parameter arithmetic as before, now on the *inner* function where the minimum modulus is
  applicable.

- 2026-08-04 — **The two ends of the composition estimate** (both axiom-clean).
  `exists_norm_comp_gt` — contrapositive of the composition bound: if the outer function exceeds `K`
  somewhere on the disc it controls, the composition exceeds `K` somewhere on the source disc.
  `exists_norm_gt_of_transcendental` — a transcendental entire function exceeds any level on every
  sufficiently large disc, wherever that disc is centred: the maximum term already beats any level,
  and the circle of radius `ρ − ‖c‖` lies inside the disc about `c`.
  Together with `exists_radius_composition_bound` this is the composition-growth statement in full:
  the inner function's minimum modulus fixes a disc about `g 0` on which the outer function is
  controlled by `f ∘ g`; transcendence makes the outer function exceed any level on that disc once it
  is large enough; hence `f ∘ g` exceeds that level on the source disc.
  The remaining quantitative point is unchanged and now isolated to one inequality: the disc's radius
  is `H^{∑m}·L/2`, and it must be driven to infinity by the choice of parameters.

- 2026-08-04 — **The displacement factors through a power of the variable**
  (`exists_pow_factor_sub_const`, axiom-clean): for `g` analytic and not locally constant at the
  origin, `g z − g 0 = z^n · G z` with `G` analytic on the whole set and `G 0 ≠ 0`.
  This unblocks the quantitative step.  The composition estimate needs a floor for the *displacement*
  `g − g 0` on a circle, but the displacement vanishes at the origin, so the minimum modulus's
  counting bound — which requires a nonzero central value — does not apply to it.  It does apply to
  `G`.  On the circle of radius `s` the displacement is then `s^n ‖G‖`, so the floor gains a factor
  `s^n` and loses nothing: the count bound is available for `G`, and `s^n ≥ 1` for `s ≥ 1`.
  This is the same obstruction that forced the count bound to be made conditional two entries ago,
  resolved properly rather than sidestepped.

- 2026-08-04 — **A floor for the displacement** (`exists_radius_norm_sub_ge`, axiom-clean).
  Factoring `g − g 0 = z^n G` and applying the minimum modulus to `G` — which does not vanish at the
  origin, so the counting bound *is* available for it — produces `N` and `L > 0` with

      2 N H < B − A  →  ∃ s ∈ [A,B], ∀ ‖z‖ = s, H^N · L ≤ ‖g z − g 0‖.

  The sup bound is taken on `g − g 0` (a hypothesis about the given function) and converted to one for
  `G` by dividing by `R'^n`, so nothing existential appears in the hypotheses.  The factor `s^n` only
  helps, since `s ≥ A ≥ 1`.
  This is the input `exists_radius_composition_bound` needs, with the count now controlled.  The
  chain from an inner function to a composition-growth statement is complete as a sequence of proved
  theorems; the parameters `R, R', H, A, B` remain to be chosen so that `H^N · L → ∞`.

- 2026-08-04 — **Composition growth with the zero count controlled**
  (`exists_radius_composition_bound_of_count`, axiom-clean).  The displacement floor feeds the
  composition inequality directly: on the selected circle, every outer function analytic on the disc
  of radius `ρ < H^N L/2` about `g 0` is bounded there by any bound for `f ∘ g` on the source disc.
  Unlike the earlier `exists_radius_composition_bound`, `N` here is the zero count of the factor `G`,
  which the counting bound controls — so the disc radius is a quantity the parameters can drive,
  rather than an uncontrolled one.
  The Clunie–Steinmetz analytic chain is now a closed sequence of proved theorems, from an entire
  inner function to a lower bound on the composition, with the only remaining freedom the choice of
  `R, R', H, A, B`.

- 2026-08-04 — **The displacement floor now reports its count bound**
  (`exists_radius_norm_sub_ge`, strengthened, axiom-clean).  It produces `n`, `N`, `c = ‖G 0‖ > 0`
  and `L > 0` with

      0 < Mg → N · log((R' − R)/R) ≤ log(Mg / (R'^n · c)),

  alongside the circle floor `H^N · L ≤ ‖g z − g 0‖`.  The count is expressed entirely in the given
  data — the sup bound `Mg` for the displacement, the radii, the order `n` of vanishing at the
  centre, and the value `c` of the cofactor there — so the parameter arithmetic has everything it
  needs without reopening the proof.
  With `log_pow_mul_ge_of_count` this converts the disc radius `H^N L/2` into an explicit logarithmic
  bound: `log(H^N L) ≥ log L − (log(Mg/(R'^n c)) / log((R'−R)/R)) · (−log H)`.  Driving that to
  infinity is the last step, and every quantity in it is now named.

- 2026-08-04 — **The displacement floor in logarithmic form**
  (`exists_radius_log_norm_sub_ge`, axiom-clean).  The zero count is folded into the growth ratio, so
  the floor mentions no number of zeros:

      log L + (log(Mg/(R'^n c)) / log((R'−R)/R)) · log H  ≤  log ‖g z − g 0‖

  on a circle in `[A,B]`, provided the range is long enough for that same ratio.  The parallel with
  `exists_radius_log_norm_ge_of_analytic` is exact — the same folding, applied to the displacement
  rather than to the function itself.
  Both halves of the composition estimate are now in logarithmic form with all constants named, which
  is the shape a parameter choice can be checked against.

### Log — the disc-in-image route is lossy, with a witness

- 2026-08-04 — **Proved limitation** (`displacement_floor_le_one`, axiom-clean).  For
  `g = exp − 1`, every displacement floor on the circle of radius `r` satisfies `ε ≤ 1` — the
  displacement dips to `1 − e^{-r}` at `z = −r` — while `g` reaches modulus `e^r − 1` on that same
  circle.  So the disc that `ball_subset_image_of_circle_floor` puts inside the image has radius
  `O(1)` for a function of positive order, and the composition estimate it feeds bounds the outer
  function only on a bounded disc.  That is far too weak for separation, which needs the outer
  function's maximum on a disc growing with `M(r,g)`.
  The parameter arithmetic confirms it independently: with `R = σ`, `R' = 3σ` the growth ratio is
  `log(Mg)/log 2`, the range forces `H ≲ σ/log Mg`, and the floor
  `log L + (log Mg/log 2)·log H` is then *negative* and large for any `g` of positive order.  There
  is no choice of `R, R', H, A, B` that rescues it.
  So both routes tried on this line are now bounded from above by proved witnesses: a circle floor
  for the **outer** function cannot exceed `−s` (`circle_floor_le_neg`, `exp`), and a displacement
  floor for the **inner** function cannot exceed `1` (`displacement_floor_le_one`, `exp − 1`).  What
  Pólya's theorem needs is a large circle *in the image*, obtained from the structure of the image
  itself — for `exp` the image of a disc is an annulus, which contains large circles despite the tiny
  displacement floor.  That is the remaining mathematical content, and it is not reachable from
  minimum-modulus estimates.
  Everything built on this line stays valid as stated; what changes is which theorem can consume it.

### Log — turning to the Nevanlinna route, which is where the classical proof lives

- 2026-08-04 — Both elementary routes to composition separation are now capped by proved witnesses
  (previous two entries).  The classical Clunie–Steinmetz proof is value-distribution-theoretic — it
  compares characteristics, not maximum moduli — so the honest path is the Nevanlinna one, whose one
  missing ingredient in this corpus is `log M(r) ≲ T(R)` (Poisson–Jensen).
  **mathlib carries the Poisson machinery**: `Analysis/Complex/Poisson.lean` and
  `Analysis/Complex/Harmonic/Poisson.lean` supply `poissonKernel`, its identification with the real
  part of the Herglotz–Riesz kernel, the two-sided kernel bounds, and the Poisson representation
  `HarmonicContOnCl.circleAverage_poissonKernel_smul`.  That was not known when the earlier entries
  recorded Poisson–Jensen as an unbuilt obstruction.
- 2026-08-04 — **The kernel bound** (`PoissonKernelBound.lean`, axiom-clean, in the umbrella):
  `poissonKernel c w z ≤ (R + r)/(R − r)` for `‖w − c‖ ≤ r < R` and `z` on the circle of radius `R`,
  together with the monotonicity `(R+a)/(R−a) ≤ (R+r)/(R−r)` it rests on.
  This is the quantitative half of `log M(r) ≤ ((R+r)/(R−r))·m(R)`: the Poisson representation writes
  `log‖f‖` at an interior point as a kernel-weighted circle average, and this bounds the weight.

- 2026-08-04 — **The Poisson representation of the log-modulus** (axiom-clean).
  `harmonicOnNhd_log_norm` — `log‖f‖` is harmonic wherever `f` is analytic and nonzero, from
  mathlib's `AnalyticAt.harmonicAt_log_norm`; `circleAverage_poissonKernel_log_norm` — for a
  zero-free analytic `f`,

      circleAverage (poissonKernel c w • log‖f‖) c R = log‖f w‖.

  With the kernel bound of the previous entry this is `log M(r) ≤ ((R+r)/(R−r))·m(R)` up to one
  integration step (monotonicity of the circle average against `log ≤ log⁺`, with its integrability
  side conditions).
  Both halves of Poisson–Jensen for the zero-free case are therefore corpus statements now.  The case
  with zeros then follows from the extraction already built (`f = P·g`, `g` zero-free), which is why
  that chain remains worth having even though its first intended use was refuted.

- 2026-08-04 — **`log M(r) ≲ T(R)` is now a corpus theorem** (module `PoissonJensenUpperBound`,
  all declarations axiom-clean).  Three layers:
  1. `circleAverage_negPart_log_norm_sub_le` — for `R ≥ 1` and `a` in the closed ball,
     `⨍ (log ‖· − a‖)⁻ ≤ log 2`.  Exact input: `⨍ log ‖· − a‖ = log R` (mathlib) minus the crude
     boundary bound `log⁺ ‖z − a‖ ≤ log 2R`.
  2. `circleAverage_posLog_cofactor_le` — extracting the zeros costs at most `log 2` per zero in
     proximity: `m(R, g) ≤ m(R, f) + (∑ m_a)·log 2` when `f = ∏(·−a)^{m_a}·g`.
  3. `log_norm_le_proximity_of_factor` / `log_norm_le_proximity_of_entire` —

         log‖f w‖ ≤ (∑ m_a)·(log 2R + K·log 2) + K·m(R, f),   K = (R+r)/(R−r), ‖w−c‖ ≤ r < R.

  The boundary hypothesis `f ≠ 0 on sphere c R` is essential and not cosmetic: Lean's junk value
  `log 0 = 0` destroys the pointwise comparison at a boundary zero, where the true correction is
  `+∞`.  Restricting to radii with no boundary zero is the honest fix — such radii are cofinal
  because the zero set of a nonzero entire function is countable.
  Remaining for the Clunie--Steinmetz separation: bound `∑ m_a` by the Jensen count (mathlib's
  `AnalyticOnNhd.sum_divisor_le`, already used in `RHTower/EntireMinimumModulus`), and prove the
  cofinality of good radii.

- 2026-08-04 — **The Poisson--Jensen layer is closed** (`PoissonJensenUpperBound`, all axiom-clean).
  Four further theorems complete the chain:
  - `circleAverage_log_norm_of_factor` — **Jensen's formula, factorized**:
    `⨍ log‖f‖ = (∑ m_a)·log R + log‖g c‖` for `f = ∏(·−a)^{m_a}·g`, `g` zero-free, `f ≠ 0` on the
    circle.  Built from mathlib's `⨍ log‖·−a‖ = log R` and `⨍ log‖g‖ = log‖g c‖`; no `divisor`
    bookkeeping is needed, which is what made it cheap.
  - `sum_multiplicity_le_of_factor` — **Jensen's count bound**:
    `n(R₁)·log(R/R₁) ≤ log M − log‖f c‖`.  Every zero contributes `log R − log‖c−a‖ ≥ 0`, and the
    ones inside radius `R₁` contribute at least `log(R/R₁)`.
  - `exists_radius_no_boundary_zero` — good radii are cofinal: every unit interval `[R₀, R₀+1]`
    contains an `R` whose circle carries no zero.  This discharges the boundary hypothesis that the
    junk value `log 0 = 0` forces on every step above.
  - `log_norm_le_proximity_and_count_of_entire` — the capstone:

        log‖f w‖ ≤ ((log M − log‖f c‖)/log 2)·(log 2R + K·log 2) + K·⨍ log⁺‖f‖,
        K = (R+r)/(R−r),  ‖w−c‖ ≤ r < R,  M = sup_{|z−c|=2R} ‖f‖.

    Zeros in the small ball are separated off and counted by Jensen; zeros between `R` and `2R` are
    absorbed into the zero-free cofactor by the filter split — that is what makes the two
    multiplicity sums (proximity side and count side) literally the same object.
  This is the missing analytic input flagged three entries above: `log M(r) ≲ T(R)` is no longer an
  external citation for this corpus.

- 2026-08-04 — **The composition-separation blocker is broken** (axiom-clean).  The two proved no-gos
  of `CircleFloorLimitation` cap the *displacement* mechanisms — an outer circle floor for `exp`, an
  inner displacement floor for `exp − 1`.  Neither is needed.  A ball is connected, so `‖g ·‖`
  attains **every** value between `‖g 0‖` and `‖g z₁‖` on it; that is all the inner function has to
  supply.
  - `PolyaConnectedTransfer.exists_norm_eq_of_closedBall` / `exists_le_norm_comp_of_floor` /
    `exists_posLog_separation_of_closedBall` — the intermediate-value transfer, with no
    normalisation `g 0 = 0` (which the existing segment lemmas of `CompositionImageCircle` all
    require, and which a composition state cannot be assumed to satisfy).
  - `RHTower/PolyaCompositionGrowth.exists_le_norm_comp_of_analytic` and
    `exists_posLog_separation_of_analytic` — combined with the corpus minimum modulus
    (`exists_radius_norm_ge_of_analytic`): whenever `2·n·H < B − A`, there is a point of the ball with

        H^n · L ≤ ‖f (g z)‖,   and hence   C·log⁺‖g z‖ < log⁺‖f (g z)‖

    once the floor beats the inner bound, where `n` counts the zeros of `f` in the inner disc.
  The mechanism is: the outer function has a *whole-circle* floor at some radius in every long
  enough window (minimum modulus), and the inner function is guaranteed to hit that radius
  (connectivity).  No Bloch/Landau constant, no Wiman `cos πρ` theorem, no open mapping.
  This is the quantitative half of `SeparatesLast`; what remains is to hold the top grouped
  coefficient away from zero at the same point.

- 2026-08-04 — **The two halves of `SeparatesLast` now meet at one point** (axiom-clean).  A circle in
  the plane is connected (`isPreconnected_sphere`, rank ℝ ℂ = 2), so the intermediate-value transfer
  runs on a single circle rather than a ball.  That is the whole trick: the minimum modulus gives a
  *circle* on which the top grouped coefficient `G` is bounded below, and the same circle is where
  the inner state hits the radius at which the outer function has its own floor.
  - `PolyaConnectedTransfer.exists_norm_eq_of_sphere` — every modulus between two attained values is
    attained on the circle; hypotheses are the two existentials `∃ z₀, ‖g z₀‖ ≤ t` and
    `∃ z₁, t ≤ ‖g z₁‖`, which is the usable form (no min/max extraction needed).
  - `exists_point_sphere_floor_and_comp`, `exists_posLog_separation_of_sphere` — the floor for `G`
    survives the choice of point.
  - `RHTower/PolyaCompositionGrowth.exists_point_circle_floor_and_comp_of_analytic` — the assembled
    statement: for `2·n·H < B − A` there is a single `z` with

        H^n·L_G ≤ ‖G z‖    and    L ≤ ‖f (g z)‖.

  All three quantities the Clunie estimate weighs — the dependent state `f ∘ g`, the previous states
  through `g`, and the top grouped coefficient `G` — are now controlled at one and the same point.
  What remains for `SeparatesLast` is bookkeeping: instantiate `G` as the grouped coefficient
  function, `g` as `F_k`, `f` as `f_{k+1}`, and check the resulting numeric inequality against
  `clunieWeight`.

- 2026-08-04 — **`SeparatesLast` is reduced to a numeric point-existence statement**
  (`ClunieSeparationBridge`, axiom-clean; wired).
  - `clunieWeight_le` / `clunieWeight_lt_of_floor` — the weight is bounded by
    `W + N·log⁺(1/c) + (N|S|+N)·log 2` once `c` floors the top grouped coefficient and `W` bounds the
    coefficient-and-earlier-state block.  `posLog_inv_le_of_floor` is the one inequality that does it.
  - `clunie_block_le` / `clunie_block_le_of_sup` — that block is at most `|S|·(a + D·b)` from a
    coefficient bound `a`, an earlier-state bound `b` and a total earlier degree `D`, all taken as
    sup bounds over the disc `‖z‖ ≤ B` where the geometric machinery lands.
  - `separatesLast_of_pointwise` — **all reference to `clunieWeight` is discharged**: `SeparatesLast F`
    now follows from a point carrying a floor, a block bound, and the strict inequality between them.
  - `groupedCoeffFun`, `analyticOnNhd_groupedCoeffFun`, `not_eventually_zero_groupedCoeffFun` — the
    top grouped coefficient is an entire function, and (identity theorem on the connected plane) it is
    nowhere locally zero as soon as it is nonzero at one point.  These are exactly the two hypotheses
    the minimum modulus needs, so `G` is a legitimate input to `exists_clunie_separated_point`.
  - `RHTower/PolyaCompositionGrowth.exists_clunie_separated_point` — delivers the point in precisely
    the shape `separatesLast_of_pointwise` consumes, with `c := H^n·L_G`, and additionally records
    `A ≤ ‖z‖ ≤ B` so the block bound applies there.

  **Remaining open core, stated sharply.**  Everything above is unconditional.  What is left is one
  numeric inequality:

      W + N·log⁺(1/(H^n·L_G)) + (N·|S| + N)·log 2  <  log⁺ L,

  where `L` is the minimum-modulus floor of the outer function `f_{k+1}` on the circle of radius `t`,
  `W` the block bound over `‖z‖ ≤ B`, and `n` the zero count of the grouped coefficient.  This is
  where transcendence of `f_{k+1}` must enter: `L = L(t)` has to outgrow `W`, which grows only with
  the earlier states.  No further structural machinery is needed — the inequality is now the whole
  problem.

- 2026-08-04 — **The displacement no-go is a statement about the base point, not about the method**
  (`PolyaFreeBasePoint`, axiom-clean, wired).  `displacement_floor_le_one` shows that for `exp − 1`
  the floor of `‖g z − g 0‖` on any circle is `O(1)`.  That is a fact about the base point `0`, which
  mathlib's `DiffContOnCl.ball_subset_image_closedBall` fixes at the *centre of the ball*.  Applying
  the same theorem on a subdisc centred anywhere frees it:
  - `ball_subset_image_of_circle_floor_at` — for `c` with `‖c‖ + r ≤ s`,
    `ball (g c) (ε/2) ⊆ g '' closedBall 0 s` where `ε` floors `‖g z − g c‖` on `sphere c r`.
  - `norm_le_of_circle_floor_at`, `exists_norm_comp_gt_at` — the composition transfer and its
    contrapositive at that base point.
  - `not_eventually_const_of_ne` — a nonconstant entire function is nowhere locally constant, so the
    nondegeneracy hypothesis is automatic for the cascade states.

  **The parameter regime the no-go hid.**  Take `g = exp`, `s = r`.  Put the base point *near the
  boundary* and the surrounding circle *small*: `c = r − log(4/3)` real, `r' = log(4/3)`, so
  `‖c‖ + r' = r` exactly.  Then

      ε = min_{|z−c| = r'} |e^z − e^c| ≍ r' · |e^c| ≍ e^r,

  and the image of `closedBall 0 r` contains a disc of radius `≍ e^r` — the genuine Pólya disc,
  centred at `3e^r/4`, sitting inside the annulus `e^{−r} ≤ |w| ≤ e^r` that is exactly the image.
  The base point at the origin gives `ε = O(1)`; the base point near the boundary gives `ε ≍ M(r,g)`.
  Both facts are true; only the second is useful, and the earlier entry read the first as a cap on
  the method.

  **What the chain still needs**, stated as the next brick: a lower bound for the interior
  displacement floor `ε`.  Write `h(z) = (g z − g c)/(z − c)`, which is zero-free on a small disc
  about `c` (isolated zeros) with `h(c) = g'(c)`; then `ε = r' · min_{sphere} |h|`, and the corpus's
  Borel--Carathéodory anchor bound `RHTower.MinimumModulus.norm_lower_bound_of_anchor` bounds that
  minimum below by `|g'(c)|` times a power of the max/anchor ratio.  Wiman--Valiron supplies
  `|g'(c)| ≍ (ν(r)/|c|)·|g(c)|` at the selection points the corpus already constructs.  So the
  remaining work is a composition of three instruments the corpus owns, not a new theorem.

- 2026-08-04 — **The Pólya disc is now produced from analytic hypotheses**
  (`RHTower/EntireMinimumModulusAt`, axiom-clean, wired).  The chain announced in the previous entry
  is built:
  - `exists_radius_norm_ge_of_analytic_at` — the corpus minimum modulus with the origin replaced by
    an arbitrary centre.  Proved by translating the function; the hard-coded `0` in
    `exists_radius_norm_ge_of_analytic` was never essential, and every displacement statement needs
    the circle around the *base point*, not the origin.
  - `exists_displacement_factor` — for `g` nowhere locally equal to `g c`, the displacement factors
    as `g z − g c = (z − c)·h z` with `h` analytic and itself nowhere locally zero.  This is the Lean
    substitute for the difference quotient, which cannot be written as `(g z − g c)/(z − c)` because
    that evaluates to the junk value at `z = c`.
  - `displacement_floor_of_factor`, `exists_radius_displacement_floor` — a floor `μ` for `h` on the
    circle of radius `s` about `c` gives the displacement floor `s·μ`, and the translated minimum
    modulus supplies `μ = H^n·L` on some `s` in every long enough window.
  - `exists_radius_ball_subset_image` — **the composition disc**:

        ball (g c) (s·H^n·L / 2)  ⊆  g '' closedBall 0 S,

    for some `s ∈ [A,B]`, whenever `2·n·H < B − A` and `‖c‖ + B ≤ S`.

  The base point is a free parameter constrained only by `‖c‖ + B ≤ S`, so it may sit near the
  boundary of the large disc — the regime identified in the previous entry, where the displacement
  floor is of the order of the maximum modulus rather than `O(1)`.
  Composed with `norm_le_of_circle_floor_at` / `exists_norm_comp_gt_at` this is the Pólya transfer:
  a bound for `f ∘ g` on `closedBall 0 S` bounds `f` on a disc of radius `≍ s·H^n·L/2` about `g c`.

- 2026-08-04 — **The Pólya transfer is now explicit** (`EntireMinimumModulusAt`, axiom-clean).
  The disc radius produced by `exists_radius_ball_subset_image` is not usable downstream, because the
  `L` inside `exists_radius_norm_ge_of_analytic` is existentially bound — a caller cannot instantiate
  it.  In the local regime that machinery is unnecessary: if `g` takes the value `g c` only at `c` on
  the disc of radius `R` about `c`, the displacement factor is zero free there, no zero extraction is
  needed, and the Borel--Carathéodory anchor bound applies directly with an explicit constant.
  - `deriv_eq_displacement_factor` — the factor at the base point is `g' c`, so the statements can be
    written without the auxiliary function.
  - `displacement_floor_explicit` — on `‖z − c‖ = r < R`,

        ‖g z − g c‖  ≥  r · ‖g' c‖ · (M/‖g' c‖)^(−2r/(R−r)),   M = sup_{ball c R} ‖factor‖.

  - `ball_subset_image_explicit`, `ball_subset_image_of_deriv` — the image of `closedBall 0 S`
    contains the ball about `g c` of half that radius, whenever `‖c‖ + r ≤ S`.
  - `norm_le_of_explicit_disc`, `exists_norm_comp_gt_explicit` — the transfer and its contrapositive:
    a bound for `f ∘ g` on the large disc bounds `f` on that whole disc about `g c`.

  **The scale this is meant to be used at.**  For a Wiman--Valiron base point of a function of
  central index `ν(r)`, the natural radius is `r ≍ |c|/ν(|c|)`: on that scale `g(c+ζ)/g(c) ≈
  exp(νζ/c)` has bounded distortion, so `M/‖g' c‖ = O(1)` and the exponential factor is `O(1)`.
  Since `‖g' c‖ ≍ (ν/|c|)·‖g c‖` there, the disc radius is `≍ (|c|/ν)·(ν/|c|)·‖g c‖ ≍ M(|c|, g)` —
  the full Pólya disc.  Both inputs (`‖g' c‖ ≍ (ν/|c|)‖g c‖`, and the bounded local ratio) are
  Wiman--Valiron statements; the corpus already owns the first as
  `exists_radius_defect_le_eps_of_transcendental`.

- 2026-08-04 — **The Pólya disc now runs off the Wiman--Valiron defect** (axiom-clean; module at
  440 lines).  The two quantities the explicit radius depends on are supplied:
  - `norm_deriv_ge_of_defect` — from `‖z g'(z)/g(z) − ν‖ ≤ ε·ν` (exactly the conclusion of the
    corpus's `exists_radius_defect_le_eps_of_transcendental`),

        ‖g' z‖  ≥  (1 − ε)·ν·‖g z‖ / ‖z‖.

  - `norm_displacement_factor_le` — the maximum principle applied to the displacement factor itself:
    `‖h z‖ ≤ (Mloc + ‖g c‖)/R'` on the disc, where `Mloc` bounds `g` on the boundary circle.  No
    Cauchy estimate is needed; the factor is already analytic, so its own maximum principle suffices.
  - `anchor_radius_mono` — the Borel--Carathéodory radius `x·(M/x)^{−2r/(R−r)}` is monotone in the
    anchor `x`, which is what lets a *lower bound* on `‖g' c‖` be substituted into the disc radius.
    Proved by rewriting the exponential as `(x/M)^{2r/(R−r)}`.
  - `ball_subset_image_of_defect` — the assembled statement, with `D = (1−ε)·ν·‖g c‖/‖c‖`:

        ball (g c) (r · D · (M/D)^{−2r/(R−r)} / 2)  ⊆  g '' closedBall 0 S.

  Every quantity is now explicit in data the Wiman--Valiron layer produces.  At the natural scale
  `r ≍ |c|/ν` this radius is `≍ ‖g c‖ ≍ M(|c|, g)`, the full Pólya disc; the one remaining input is
  that `M/D = O(1)` there, i.e. that `M(|c|(1 + κ/ν), g) = O(M(|c|, g))` — a growth statement about
  `log M` against the central index, and the last analytic gap in the chain.

- 2026-08-04 — **The last analytic gap is reduced to a central-index jump**
  (`MaximumModulusLocalGrowth`, axiom-clean, wired).  The gap named in the previous entry —
  `M(r(1+κ/ν)) = O(M(r))` — is now a corpus theorem up to one ratio:
  - `coeffSum_mono` — the majorant is monotone in the radius.
  - `coeffSum_le_maxTerm_mul_two` — `S(r) ≤ μ(r)·(ν(2r) + 2)`.  A specialisation of the corpus's
    `coeffSum_le_maxTerm_mul_centralIndex` at `s = 2r`, where the geometric tail contributes exactly
    one further term.
  - `norm_coeffFun_le_maxTerm_mul` — for `‖w‖ ≤ r'` and `r ≤ r'`,

        ‖f w‖  ≤  μ(r) · (r'/r)^{ν(r')} · (ν(2r') + 2).

  - `growth_factor_le_exp` — at the Wiman scale `r' = r(1 + κ/ν)`, `(r'/r)^k ≤ exp(k·κ/ν)`.

  Combining the last two at `k = ν(r')`: the whole local growth factor is
  `exp(κ·ν(r')/ν(r))·(ν(2r') + 2)`.  **The only unbounded ingredient left is the ratio `ν(r')/ν(r)`
  across the Wiman scale** — a Borel-type statement, and the corpus already owns the instrument for
  it (`BorelGrowthExponent.exists_ge_lt_two_mul_rpow`, which produces radii where the central index
  does not double).  The polynomial factor `ν(2r')+2` is harmless: it is absorbed by the `ε` in the
  defect bound, since the disc radius carries `‖g c‖ ≥ μ(r)` as a multiplicative factor while the
  loss is only polynomial in `ν`.

- 2026-08-04 — **The last unbounded factor is closed** (`CentralIndexBorelScale`, axiom-clean, wired).
  The ratio `ν(r')/ν(r)` across the Wiman scale is not bounded at every radius, but the corpus's
  Borel growth lemma supplies radii where it is:
  - `logCentralIndex a x = ν(e^x) + 1`, `monotone_logCentralIndex`, `one_le_logCentralIndex` — the
    hypotheses `exists_ge_lt_two_mul_rpow` needs, at exponent `α = 1`.
  - `exists_good_logRadius` — beyond every bound there is `x` with

        ν(e^{x + 1/ν₁}) + 1 < 2·ν₁,      ν₁ = ν(e^x) + 1.

  - `exp_neg_ratio_le` — the geometric tail ratio across a step `t` is at most `1/t`.
  - `exists_logRadius_norm_coeffFun_le` — **the local growth statement**: at such a radius,

        ‖f w‖ ≤ 4e · ν₁ · μ(e^x)    for all ‖w‖ ≤ e^x · e^{1/(2ν₁)}.

  Both losses close at once, and the reason is the same in each case — the comparison radius is taken
  *inside* the good step, where the central index is known not to have doubled.  The growth factor
  `(r'/r)^{ν(r')} = exp(ν(r')/(2ν₁))` is below `e` because `ν(r') < 2ν₁`; the majorant costs `4ν₁`
  maximum terms because the comparison radius `s = e^x·e^{1/ν₁}` is still inside the step.
  Every quantity in the composition-disc radius is now bounded by corpus theorems.  What remains is
  the instantiation: feed `exists_logRadius_norm_coeffFun_le` and
  `exists_radius_defect_le_eps_of_transcendental` into `ball_subset_image_of_defect`, and the disc
  radius is `≍ μ(r)/ν` — enough for the Clunie separation, since the weight is only logarithmic.

- 2026-08-04 — **The Borel selection can now be intersected with a prescribed window**
  (axiom-clean).  Cofinality (`∃ x ≥ R`) is not enough to combine the Borel selection with the
  Wiman--Valiron one, which delivers its point inside a window it chooses.  The Borel lemma bounds
  the *measure* of the bad set, which is strictly stronger and gives exactly what is needed:
  - `norm_coeffFun_le_of_good` — the local growth bound refactored into conditional form, with
    "`x` is Borel-good" as a hypothesis rather than obtained inside the proof.  The existential
    versions are now corollaries.
  - `exists_mem_Icc_lt_two_mul_rpow` — generic: any interval whose length exceeds the measure bound
    contains a good radius.  Proof is one contradiction against `borel_growth_monotone_rpow`.
  - `borel_bound_one` — at exponent `α = 1` that measure bound is exactly `2`.
  - `exists_good_logRadius_of_two_lt`, `exists_norm_coeffFun_le_of_two_lt` — the readable form:
    **every window of length greater than `2` in the logarithmic variable contains a radius at which
    `‖f w‖ ≤ 4e·ν₁·μ(e^x)` on the disc of radius `e^x·e^{1/(2ν₁)}`**.

  The window-length threshold is an absolute constant, independent of the function.  The Wiman
  selection windows in `WimanValironSelection` are chosen by the caller and can be taken longer than
  `2`, so the two selections can now be run against a common window.

- 2026-08-04 — **No second selection is needed: the Wiman window already carries the Borel
  condition** (axiom-clean).  `WimanValironSelection.exists_good_parameters` delivers, alongside its
  window `[x, d]` and step `H`, the statement

      ν(e^{d+2H}) + 1 < 2·(ν(e^x) + 1),

  which is exactly the non-doubling condition, and it holds across the *whole* window rather than at
  one point.  So a point selected later inside the window inherits it, and the previous entry's
  window-intersection machinery is not required for this instantiation.
  - `good_of_window_no_double` — if `x ≤ x' ≤ d + H` and the step `1/ν₁(x')` fits inside `H`, then
    `x'` is Borel-good.  Monotonicity of the central index does the whole proof: the step from `x'`
    lands inside `d + 2H`, and `ν(e^x) ≤ ν(e^{x'})` widens the right-hand side.
  - `norm_coeffFun_le_of_window` — the local growth bound at any such `x'`, with the Borel hypothesis
    discharged by the window.
  - `logCentralIndex_no_double_iff` — the translation between the two spellings of non-doubling.

  The side condition `1/ν₁(x') ≤ H` is satisfied in the intended regime: with `scale t = 2t` the
  selection gives `H = (ν+1)^{−α}/4`, and for `α < 1` this exceeds `1/(ν+1)` for all large `ν`,
  which is where a transcendental function lives.
  Every input to `ball_subset_image_of_defect` is now available at a single selected point: the
  defect bound and `μ ≤ ‖f z‖` from the Wiman selection, the local sup bound from
  `norm_coeffFun_le_of_window` at the same `x'`.

- 2026-08-04 — **The point selection for the Clunie separation is closed, without any composition
  transfer** (`CircleFloorMaxSelection` + `PolyaCompositionGrowth`, axiom-clean, wired).
  The composition disc was being built to force the dependent state to be large at the chosen point.
  It is not needed for the *selection*: the minimum modulus gives a circle on which the auxiliary
  function `G` is bounded below at **every** point, so the maximum point of the dependent state on
  that same circle inherits the floor for free.  There is no compatibility condition to arrange —
  one of the two properties is uniform on the circle.
  - `exists_max_on_sphere` — a maximum of the modulus on a circle, for any continuous function
    (the corpus's `exists_max_on_circle` is stated only for `coeffFun`).
  - `exists_point_sphere_floor_and_max`, `exists_point_norm_floor_and_maxTerm` — the floor survives
    the choice of maximum point; for `coeffFun` the maximum dominates the maximum term.
  - `RHTower.exists_radius_floor_and_maxTerm` — the assembled selection: whenever
    `2·n·H < B − A`, there are `s ∈ [A,B]` and `z` with `‖z‖ = s`,

        H^n·L ≤ ‖G z‖    and    μ(s) ≤ ‖f z‖.

  This supersedes the composition-transfer route for the purpose of `SeparatesLast`.  The Pólya disc
  layer remains valuable — it is what will eventually compare `μ(s, f_{k+1}∘F_k)` with `T(s, F_k)` —
  but the selection no longer waits on it.
  **The card's remaining open core is now exactly one inequality**, with all point selection
  discharged:

      |S|·(a + D·b) + N·log⁺(1/(H^n·L)) + (N|S| + N)·log 2  <  log μ(s, F_{k+1}),

  where `a` bounds the coefficients and `b` the earlier states on `‖z‖ ≤ B`.  This is the growth
  comparison `log μ(s, f∘F_k) ≫ D·log M(s, F_k)` — Pólya's theorem, and nothing else.

- 2026-08-04 — **The proximity/maximum-modulus comparison is two-sided**
  (`NevanlinnaMaxModulusBridge`, axiom-clean, wired).
  - `proximity_top_le_posLog`, `proximity_top_le_posLog_of_norm` — `m(r,f) ≤ log⁺ M(r,f)`, directly
    from `circleAverage_mono_on_of_le_circle` and mathlib's `proximity_top`.  With
    `log_norm_le_proximity_and_count_of_entire` from `PoissonJensenUpperBound` this closes the
    comparison in both directions, so maximum-modulus estimates and value-distribution estimates are
    interchangeable in this corpus.
  - `exists_le_norm_comp_sub_const`, `analyticOnNhd_sub_const`, `not_eventually_sub_const_zero` —
    the shift `f ↦ f − a`.  A zero-free outer function such as `exp` gives the minimum-modulus
    argument nothing to count; the shifted function carries the `a`-points instead, and the shift
    costs only the additive constant `‖a‖`.

  **Honest assessment of the frontier.**  With the selection closed and the comparison two-sided,
  what the card's last inequality needs is a *lower* bound on the zero count of `f − a` for some `a`
  — equivalently `N(r, 1/(f−a)) ≳ T(r,f)` for some value.  That is the second main theorem, or
  Pólya's composition theorem, and neither is in mathlib.  Both are multi-session builds; the
  logarithmic-derivative lemma (`m(r, f'/f) = S(r,f)`) is the engine of the first, and the corpus now
  owns its two prerequisites — the Poisson representation of `log‖f‖` and Jensen's formula in
  factorized form.  That is the next long build, and it is a construction, not an obstruction.

- 2026-08-04 — **First brick of the second main theorem: the separation estimate**
  (`SecondMainTheoremSeparation`, axiom-clean, wired).  The reduction of SMT to a single
  logarithmic-derivative bound rests on turning a *sum* of proximity terms into *one*.  That step is
  pointwise and elementary, and it is now proved:
  - `eq_of_both_close` — pairwise separated targets cannot both lie within half the separation of a
    common point.
  - `posLog_inv_le_of_far` — a point at distance `≥ δ/2` has proximity at most `log⁺(2/δ)`.
  - `sum_posLog_inv_le` — **the separation estimate**: for targets `A : Fin q → ℂ` with pairwise
    separation `δ`,

        ∑_j log⁺(1/‖w − A_j‖) ≤ log⁺‖∑_j (w − A_j)⁻¹‖ + q·log⁺(2/δ) + log⁺(q·2/δ) + log 2,

    uniformly in `w`.  At most one target is close; that one is handled by the triangle inequality
    against the full sum, the rest by the far-point bound.

  Integrating this over a circle gives `∑_j m(r, 1/(f−a_j)) ≤ m(r, ∑_j (f−a_j)⁻¹) + O(1)`, which is
  the shape SMT needs.  mathlib supplies the rest of the proximity calculus already
  (`proximity_add_top_le`, `proximity_mul_top_le`, `proximity_inv`, `proximity_sum_top_le`), so the
  only remaining ingredient of SMT is the logarithmic-derivative lemma itself.
  Lean note: the junk values `‖0‖⁻¹ = 0` and `log⁺ 0 = 0` are harmless here — they only shrink the
  left-hand side — so no nonvanishing hypothesis is needed anywhere in this file.

- 2026-08-04 — **The separation estimate is now a proximity inequality** (axiom-clean).
  - `sum_proximity_le` — integrating the pointwise estimate over a circle:

        ∑_j m(r, a_j; f)  ≤  m(r, ∞; ∑_j (f − a_j)⁻¹) + q·log⁺(2/δ) + log⁺(2q/δ) + log 2.

    Stated with the circle-integrability side conditions as hypotheses, so it is usable directly.
  - `circleIntegrable_posLog_inv_sub_const`, `sum_proximity_le_of_meromorphic` — those side
    conditions discharged from meromorphy of the reciprocals, with `MeromorphicOn.sum` supplying the
    aggregate.  This is the form a caller uses.

  This is the whole "sum of proximities becomes one proximity" step of the second main theorem, and
  it is now unconditional in the corpus.  The remaining SMT ingredient is the logarithmic-derivative
  lemma; everything else in the classical chain — `proximity_add_top_le`, `proximity_mul_top_le`,
  `proximity_inv`, the first main theorem, Jensen — is either mathlib's or already built here.
  Two Lean shape traps recurred and are worth recording: `circleAverage_add` and `MeromorphicOn.sum`
  are stated for the Pi-type sum `∑ j, f j`, not for `fun z => ∑ j, f j z`, so each use needs an
  explicit `funext`/`rfl` bridge; `simp [Finset.sum_apply]` closes it.

- 2026-08-04 — **The logarithmic-derivative estimate, zero-free case** (`LogDerivativeBound`,
  axiom-clean, wired).  The remaining SMT ingredient, in the case where the function does not vanish:
  - `logDeriv_eq_deriv_branch` — on a disc where `f = f c · exp g`, the logarithmic derivative `f'/f`
    *is* `g'`.
  - `norm_logDeriv_le` — for `‖z − c‖ ≤ ρ < r < R`,

        ‖f'(z)/f(z)‖  ≤  2·(log(M/m) + 1)·r/(R − r)/(r − ρ),

    with `M` bounding `f` on the disc of radius `R` and `m` an anchor at the centre.

  The bound is **logarithmic** in the maximum modulus, which is exactly what makes the corresponding
  proximity term `S(r,f)` rather than `O(T(r,f))`.  Both inputs were already in the corpus:
  `BallLogarithm.exists_bound_log_on_ball` (Borel--Carathéodory for the branch) and mathlib's
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy's estimate), applied at the centre `z`
  with radius `r − ρ` rather than at `c`.
  Remaining for the general case: the zeros.  Writing `f = P·h` with `P` the monic polynomial of
  zeros (the extraction `AnalyticRootFactor` already provides), `f'/f = P'/P + h'/h`, and `P'/P =
  ∑ m_a/(· − a)` has proximity controlled by the zero count — which the corpus owns via
  `sum_multiplicity_le_of_factor`.  That decomposition is the next step.
  Note: `BallLogarithm` imports only `Mathlib.Analysis.Complex.BorelCaratheodory`, so the Cauchy
  estimate needed an explicit `import Mathlib.Analysis.Complex.Liouville` — narrow imports in this
  corpus mean mathlib names can be genuinely absent rather than misspelled.

- 2026-08-04 — **The logarithmic derivative across a zero factorization**
  (`LogDerivativeFactor`, axiom-clean, wired).  The general case of the estimate splits into the two
  parts announced in the previous entry:
  - `logDeriv_sub_const` — `logDeriv (· − a) z = 1/(z − a)`.
  - `logDeriv_of_factor` — for `f = ∏ (· − a)^{m a} · h` on an open set with `h` zero free, away from
    the zeros

        f'/f = ∑_a m_a/(· − a) + h'/h.

    Built on mathlib's `logDeriv_mul`, `logDeriv_prod`, `logDeriv_fun_pow`; the corpus needed only
    the `EventuallyEq` bridge, since `logDeriv` is `deriv f / f` and `deriv` respects it.
  - `norm_sum_multiplicity_div_le` — `‖∑_a m_a/(z − a)‖ ≤ (∑_a m_a)/d` when every zero is at distance
    at least `d`.

  The second summand is `norm_logDeriv_le` from the previous entry; the first is now a rational
  function of the zeros, and its circle proximity is controlled by
  `circleAverage_negPart_log_norm_sub_le` (each zero costs `log 2`) together with the Jensen count
  `sum_multiplicity_le_of_factor`.  Every ingredient of the logarithmic-derivative lemma is
  therefore a corpus theorem; what remains is to assemble them into the proximity statement
  `m(r, f'/f) = S(r,f)`.
  Lean note: `logDeriv_prod` and `logDeriv_fun_pow` both need their `𝕜`, `𝕜'`, and `f` given
  explicitly here — left to unification they pick `𝕜 := ℕ` from the multiplicity exponent, or
  rewrite `w` to `id w` and then fail to match.

- 2026-08-04 — **The proximity integrand of the logarithmic derivative** (axiom-clean).
  `posLog_norm_logDeriv_le_of_factor` — away from the zeros,

      log⁺‖f'/f‖ ≤ log 2 + log|T| + ∑_a (log m_a + log⁺(1/‖z − a‖)) + log⁺‖h'/h‖.

  This is the form that integrates: no uniform distance-to-zeros hypothesis appears, because the
  singular behaviour is carried by the `log⁺(1/‖z − a‖)` terms rather than excluded.  Each of those
  has circle average at most `log 2` by `circleAverage_negPart_log_norm_sub_le`, and the count
  `∑ m_a` is bounded by Jensen (`sum_multiplicity_le_of_factor`), so integrating gives

      m(r, f'/f) ≤ (zero count)·log 2 + log|T| + ∑ log m_a + m(r, h'/h) + log 2,

  with `m(r, h'/h)` logarithmic in the maximum modulus by `norm_logDeriv_le`.  That is the
  logarithmic-derivative lemma; the remaining work is the integration bookkeeping, not new analysis.
  mathlib supplied `posLog_sum`, `posLog_nat_mul`, `posLog_add` and `posLog_mul` — the whole `log⁺`
  calculus needed here — via `Mathlib.Analysis.SpecialFunctions.Log.PosLog`, which again had to be
  imported explicitly.

- 2026-08-04 — **The proximity of the logarithmic derivative** (`LogDerivativeProximity`,
  axiom-clean, wired).  The integration announced in the previous entry is done:
  - `posLog_inv_eq_negPart` — the proximity integrand of a linear factor *is* the negative part of
    its log-modulus, `log⁺(1/‖z − a‖) = max 0 (−log‖z − a‖)`.  This identifies the zero terms with
    the object `circleAverage_negPart_log_norm_sub_le` already bounds.
  - `circleIntegrable_posLog_inv_sub`, `circleAverage_posLog_inv_sub_le` — those terms are circle
    integrable, and each has circle average at most `log 2` for `r ≥ 1`.
  - `circleAverage_posLog_logDeriv_le` — **the estimate**:

        m(r, f'/f) ≤ log 2 + log|T| + ∑_a log m_a + |T|·log 2 + m(r, h'/h).

  With `m(r, h'/h)` logarithmic in the maximum modulus (`norm_logDeriv_le`) and `|T|`, `∑ m_a`
  bounded by Jensen (`sum_multiplicity_le_of_factor`), this is Nevanlinna's estimate for the
  logarithmic derivative: every term on the right is `O(log T(R,f))`, not `O(T(r,f))`.
  The chain from here to the second main theorem is now purely the proximity calculus, which mathlib
  owns: `sum_proximity_le_of_meromorphic` (built here) turns the `q` value-terms into one,
  `proximity_mul_top_le` and `proximity_inv` move the logarithmic derivative into position, and this
  estimate bounds it.

- 2026-08-04 — **The shifted logarithmic derivative** (axiom-clean).
  - `logDeriv_shift_eq` — shifting by a constant leaves the numerator alone:
    `(f − a)'/(f − a) = f'/(f − a)`, from mathlib's unconditional `deriv_sub_const`.
  - `circleAverage_posLog_logDeriv_sub_const_le` — the estimate of the previous entry, transported
    to `f'/(f − a)`.  This is the form the second main theorem uses, once per value `a_j`, and it
    costs nothing beyond the shift: the zero data `T`, `m` is that of `f − a`, i.e. the `a`-points
    of `f`, which is exactly what the counting function measures.

  The corpus now holds every analytic ingredient of the second main theorem:

  | ingredient | status |
  |---|---|
  | `∑_j m(r, a_j) ≤ m(r, ∑ (f−a_j)⁻¹) + O(1)` | `sum_proximity_le_of_meromorphic` |
  | `m(r, f'/(f−a)) = S(r,f)` | `circleAverage_posLog_logDeriv_sub_const_le` |
  | proximity calculus (`mul`, `inv`, `add`, `sum`) | mathlib |
  | first main theorem, Jensen, counting function | mathlib + `PoissonJensenUpperBound` |

  What remains is the algebraic chain assembling them, in mathlib's `characteristic`/`logCounting`
  language — bookkeeping over the identity `F = (F/f')·(f'/f)·f` and the first main theorem.  No
  further analytic input is needed.

- 2026-08-04 — **The second main theorem, up to the residual proximity term**
  (`SecondMainTheoremChain`, axiom-clean, wired).
  - `characteristic_apply` — `T(r,a;f) = m(r,a;f) + N(r,a;f)`, mathlib's definition unfolded.
  - `mul_characteristic_le_sum_logCounting_add_proximity` — the assembled inequality:

        q·T(r,f) ≤ ∑_j N(r, a_j) + m(r, ∑_j (f − a_j)⁻¹) + (qK + separation constant),

    where `K` bounds the first-main-theorem defect at each value.  The separation constant is the one
    from `sum_proximity_le_of_meromorphic`, and the first main theorem enters only as the explicit
    hypothesis `hfmt`, so the statement is unconditional and a caller can supply mathlib's
    quantitative version (`abs_characteristic_sub_characteristic_shift_le`).

  This is the second main theorem with a single residual term, `m(r, ∑_j (f − a_j)⁻¹)`.  Bounding it
  by `S(r,f)` is exactly what the logarithmic-derivative estimate does, through the identity
  `∑_j (f − a_j)⁻¹ = (∑_j f'/(f − a_j))/f'`: mathlib's `proximity_mul_top_le` and `proximity_inv`
  move the pieces, and `circleAverage_posLog_logDeriv_sub_const_le` bounds each summand.
  With that step the corpus owns SMT, hence `N(r, 1/(f − a)) ≳ T(r,f)` for some value of any three,
  which is the input Pólya's composition theorem needs and the card's last inequality waits on.

- 2026-08-04 — **Moving the residual term across the critical points** (axiom-clean).
  The factorization `∑_j (f − a_j)⁻¹ = (∑_j f'/(f − a_j))·(1/f')` is **false at the critical points
  of `f`**, where Lean's junk value `0⁻¹ = 0` collapses the right-hand side to `0`.  Proximity is a
  circle average, so it only needs the identity off a codiscrete set — and mathlib's
  `proximity_congr_codiscreteWithin` provides exactly that tolerance.
  - `proximity_top_le_of_codiscrete_mul` — `m(r, F) ≤ m(r, G) + m(r, H)` when `F = G·H` codiscretely.
  - `proximity_top_sum_le_of_codiscrete` — `m(r, F) ≤ ∑_j m(r, G_j) + log q` when `F = ∑ G_j`
    codiscretely.

  These are the two movers the residual term needs.  Applying them to the factorization above turns
  `m(r, ∑_j (f − a_j)⁻¹)` into `∑_j m(r, f'/(f − a_j)) + m(r, 1/f') + log q`, of which the first
  group is bounded by `circleAverage_posLog_logDeriv_sub_const_le` and the second is the ramification
  term that the first main theorem converts into `N(r, 1/f')`.
  This is the pattern that has recurred throughout the analytic work on this card: Lean's junk values
  at singular points never invalidate the mathematics, but they do decide *which* form of a
  classical identity is provable — pointwise, codiscretely, or only after excluding a set.

- 2026-08-04 — **The residual term is split** (axiom-clean).
  - `sum_inv_eq_mul_of_deriv_ne` — where `f' ≠ 0`, `∑ (f − a_j)⁻¹ = (∑ f'/(f − a_j))·(1/f')`.  No
    condition on `f − a_j` is needed: both sides vanish where it does, so the junk value is harmless
    on that factor.
  - `eventually_deriv_ne_zero` — the critical points are codiscretely avoided, from mathlib's
    isolated-zeros principle for meromorphic functions.
  - `sum_inv_eventuallyEq_mul`, `proximity_sum_inv_le` — hence

        m(r, ∑_j (f − a_j)⁻¹) ≤ ∑_j m(r, f'/(f − a_j)) + log q + m(r, 1/f').

  Chained with `mul_characteristic_le_sum_logCounting_add_proximity` this gives

      q·T(r,f) ≤ ∑_j N(r, a_j) + ∑_j m(r, f'/(f − a_j)) + m(r, 1/f') + constants,

  and the middle group is `S(r,f)` by `circleAverage_posLog_logDeriv_sub_const_le`.  The remaining
  term `m(r, 1/f')` is the ramification term; the first main theorem converts it to `N(r, 1/f')`,
  which is where the classical `−2` in `(q−2)T` comes from.
  Lean note: `MeromorphicOn.codiscreteWithin_setOf_ne_zero` is declared *inside* `namespace
  MeromorphicAt`, so its real name is `MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero`.
  Grepping the declaration line is not enough — the enclosing namespace has to be checked too.

- 2026-08-04 — **The second main theorem, assembled** (`mul_characteristic_le_of_separated`,
  axiom-clean).  For pairwise separated values `a_1,…,a_q`,

      q·T(r,f) ≤ ∑_j N(r, a_j) + ∑_j m(r, f'/(f − a_j)) + m(r, 1/f')
                 + (qK + q·log⁺(2/δ) + log⁺(2q/δ) + log 2 + log q),

  with `K` the first-main-theorem defect.  `proximity_top_logDeriv_eq` identifies the middle group
  with the circle averages that `circleAverage_posLog_logDeriv_sub_const_le` bounds, so that group is
  `S(r,f)`; the last term is the ramification term.
  Everything is unconditional: the first main theorem appears only as the hypothesis `hfmt`, which
  mathlib's `abs_characteristic_sub_characteristic_shift_le` supplies.
  **Status of the SMT sub-project:** the analytic content is complete and the algebraic chain is
  assembled.  What is left is instantiation — feeding mathlib's FMT into `hfmt`, and converting
  `m(r, 1/f')` into `N(r, 1/f')` to recover the classical `(q − 2)` form.  Neither needs new
  mathematics.
  For the card itself, the payoff is `N(r, 1/(f − a)) ≳ T(r,f)` for at least one of any three
  values, which is the missing input to Pólya's composition theorem and hence to the card's last
  inequality.

- 2026-08-04 — **The first-main-theorem hypothesis is discharged** (axiom-clean).  The `hfmt`
  hypothesis of `mul_characteristic_le_of_separated` is no longer an assumption:
  - `characteristic_coe_eq` — `T(r, a₀; f) = T(r, 0; f − a₀)`, from mathlib's
    `proximity_coe_eq_proximity_sub_const_zero` and `logCounting_coe_eq_logCounting_sub_const_zero`.
  - `characteristic_zero_eq_inv_top` — `T(r, 0; g) = T(r, ∞; 1/g)`, from `proximity_inv` and
    `logCounting_inv`.
  - `characteristic_top_le_characteristic_coe` — combining the two quantitative halves of mathlib's
    first main theorem (the shift and the inversion):

        T(r,f) ≤ T(r, a₀; f) + (log⁺‖a₀‖ + log 2)
                 + max |log‖(f − a₀)(0)‖| |log‖trailingCoeff (f − a₀) 0‖|.

  So the second main theorem as assembled here rests on nothing but mathlib and this corpus.
  Lean note: `f - fun _ => a₀` is the Pi-subtraction, and applying it to `0` inside a *statement*
  fails to elaborate — the function type is still a metavariable there.  An explicit
  `((f - fun _ : ℂ => a₀) : ℂ → ℂ) 0` annotation fixes it; without it the term elaborates to `sorry`
  and the subsequent `linarith` fails for reasons that look unrelated.

- 2026-08-04 — **The payoff: at least one value is taken often** (`exists_logCounting_ge`,
  axiom-clean).  Pigeonhole on the second main theorem: if `q·T(r,f) ≤ ∑_j N(r, a_j) + S`, then some
  `j` has

      N(r, a_j) ≥ T(r,f) − S/q.

  This is exactly the input the composition-growth argument needs and the one a zero-free outer
  function cannot supply on its own: a *lower* bound on the number of `a`-points for at least one
  value.  `exp` has no zeros, but by this statement it takes some value among any three with counting
  function nearly `T(r, exp)` — which is what makes the shift `f ↦ f − a` of
  `NevanlinnaMaxModulusBridge` useful rather than merely available.

  **The Nevanlinna sub-project is complete as a chain**: separation → residual split →
  logarithmic-derivative estimate → first main theorem → pigeonhole, all unconditional, all
  axiom-clean, all wired.  The remaining work on the card is to instantiate this chain at the
  cascade's outer function and feed the resulting counting bound into the Pólya disc built earlier
  in this session.

- 2026-08-04 — **Value preimages of a composition** (`CompositionValuePreimages`, axiom-clean,
  wired).  The counting mechanism behind composition growth, at the level of sets:
  - `comp_sub_eq_zero_of_eq` — a point sent by the inner function to an `a`-point of the outer
    function is an `a`-point of the composition.
  - `disjoint_preimage_of_ne` — preimages of distinct values are disjoint.
  - `card_preimage_sum_le_card_comp` — hence for distinct `a`-points `b_1,…,b_p` of `f`,

        ∑_i #{z ∈ K : g z = b_i}  ≤  #{z ∈ K : f (g z) = a},

    so the composition takes `a` at least as often as `g` takes all the `b_i` together.
  - `card_preimage_le_card_comp` — the single-value form.

  Chained with `exists_logCounting_ge` applied to `g` at the values `b_1,…,b_p`, the right-hand side
  is at least `p·T(r,g) − S(r,g)` for every `p` — which is Clunie's theorem
  `T(r, f∘g)/T(r,g) → ∞`, and hence the growth comparison the card's last inequality needs.
  This is deliberately the *multiplicity-free* form: it needs no order theory for compositions, and
  the inequality only ever gets used in the direction where dropping multiplicities is harmless.
  Converting the set counts into `logCounting` (which weights by multiplicity, hence is larger) is
  the remaining bookkeeping.

- 2026-08-04 — **Multiplicities of a composition** (axiom-clean).  Set-level counting loses the
  weights `logCounting` uses; they are recovered by composing the two local factorizations.
  - `comp_factor_of_factors` — if `g − b = (· − z₀)^l·h` and `f − a = (· − b)^k·H`, then

        f ∘ g − a = (· − z₀)^{l·k} · (h^k · (H ∘ g)).

  - `comp_factor_of_factors_le` — hence with `k ≥ 1` the composition has a zero of order at least
    `l` at `z₀`: the multiplicity of the inner function's `b`-point is never lost, and is multiplied
    by the outer function's ramification.

  The proof is pure algebra (`mul_pow`, `pow_mul`) once both factorizations are in hand, and the
  corpus's `exists_global_factor_of_root` supplies them.  No order theory for compositions is
  needed — the factorizations *are* the order statement, in the form Lean handles without junk-value
  trouble.
  With this, the set-level bound `card_preimage_sum_le_card_comp` upgrades to the weighted one, which
  is what feeds `logCounting` and hence `T(r, f∘g) ≥ ∑_i N(r, b_i; g)`.

- 2026-08-04 — **The composed factorization over a whole zero set** (axiom-clean).
  - `comp_prod_factor_of_factors` — if `g − b = (∏_ζ (· − ζ)^{l ζ})·h` with `h` zero free, and
    `f − a = (· − b)^k·H`, then

        f ∘ g − a = (∏_ζ (· − ζ)^{l ζ · k}) · (h^k · (H ∘ g)).

    This is exactly the shape `RHTower.sum_multiplicity_le_of_factor` consumes, so the composition's
    Jensen zero count is directly comparable with the inner function's.
  - `sum_multiplicity_le_comp` — `∑ l ζ ≤ ∑ (l ζ · k)` for `k ≥ 1`, the count comparison itself.

  So for a *single* `a`-point `b` of the outer function, the corpus now proves
  `n(r, a; f∘g) ≥ n(r, b; g)` with multiplicities.  Extending to several `a`-points `b_1,…,b_p`
  requires merging `p` such product factorizations into one — a `Finset` disjointness argument over
  the union of the zero sets, using that the `b_i` are distinct (which is what
  `disjoint_preimage_of_ne` already gives at the set level).  That merge is the next step, and with
  it `T(r, f∘g) ≥ ∑_i N(r, b_i; g) ≥ (p−2)·T(r,g)` follows from the second main theorem for `g`.

- 2026-08-04 — **The merge over several `a`-points** (axiom-clean).  The step flagged as next in the
  previous entry:
  - `comp_biUnion_factor` — if `f − a = (∏_i (· − b_i)^{k_i})·H` and each `g − b_i` carries its zeros
    in a product with zero-free cofactor, then

        f ∘ g − a = (∏_i ∏_ζ (· − ζ)^{l_i ζ · k_i}) · ((∏_i h_i^{k_i}) · (H ∘ g)).

  - `sum_sum_multiplicity_le_comp` — the count comparison `∑_i ∑_ζ l_i ζ ≤ ∑_i ∑_ζ l_i ζ·k_i`.
  - `disjoint_zeroSets_of_ne` — the zero sets of the distinct `b_i` are disjoint.

  Keeping the zero sets as a **nested** product is what made the identity cheap: disjointness is not
  needed for it at all, only for flattening into a single product, and is supplied separately.  I had
  expected the merge to require `Finset.biUnion` bookkeeping with a dependent multiplicity function;
  it does not.
  So the corpus now proves, with multiplicities, `n(r, a; f∘g) ≥ ∑_i n(r, b_i; g)`.  Combined with
  the second main theorem for `g` at the values `b_1,…,b_p`, this is Clunie's growth comparison, and
  the only remaining task on this line is translating the `n` counts into `logCounting`/`T` through
  Jensen — for which `sum_multiplicity_le_of_factor` is already the corpus's instrument.

- 2026-08-04 — **The composed factorization, flattened** (axiom-clean; module now 251 lines).
  `RHTower.sum_multiplicity_le_of_factor` wants one product over one `Finset`, so the nested product
  is flattened along the disjointness of the zero sets:
  - `mergedMultiplicity` — the multiplicity at a point, read off from the unique block containing it.
  - `mergedMultiplicity_eq` — on a block it *is* that block's own multiplicity, times the outer
    ramification.
  - `comp_flat_factor` — hence

        f ∘ g − a = (∏_{ζ ∈ ⋃ T_i} (· − ζ)^{mergedMultiplicity ζ}) · ((∏_i h_i^{k_i}) · (H ∘ g)),

    a single product, in the exact shape the Jensen count consumes.
  - `sum_mergedMultiplicity` — the merged count equals `∑_i ∑_ζ l_i ζ·k_i`.

  With `sum_sum_multiplicity_le_comp` this closes the counting comparison end to end:

      n(r, a; f∘g) = ∑_ζ mergedMultiplicity ζ = ∑_i ∑_ζ l_i ζ·k_i ≥ ∑_i n(r, b_i; g).

  Every step from "the outer function takes `a` at `p` points" to "the composition's zero count
  dominates the inner function's total" is now a corpus theorem, with multiplicities, unconditional.

- 2026-08-04 — **The merged count restricted to a sub-disc** (axiom-clean).  The Jensen bound
  `RHTower.sum_multiplicity_le_of_factor` counts only the zeros inside a smaller radius `R₁ < R`, so
  the merged multiplicity has to survive a `filter`:
  - `sum_filter_mergedMultiplicity` — `∑_{ζ ∈ (⋃T_i).filter P} merged ζ = ∑_i ∑_{ζ ∈ (T_i).filter P}
    l_i ζ·k_i`, via `Finset.filter_biUnion` and disjointness of the filtered blocks.
  - `sum_filter_le_sum_filter_mergedMultiplicity` — and each block still contributes at least its own
    count.

  This is the last combinatorial step before the Jensen application.  Feeding `comp_flat_factor`
  into `sum_multiplicity_le_of_factor` at radius `2R` with `R₁ = R` now yields

      (∑_i n(R, b_i; g))·log 2 ≤ ∑_ζ merged ζ · log 2 ≤ log(M(2R, f∘g − a) / ‖f(g(c)) − a‖),

  i.e. a **lower bound on the composition's maximum modulus** in terms of the inner function's
  counting functions — which, with the second main theorem for `g`, is the growth comparison the
  card's last inequality needs.
  Lean note: `open scoped Classical in` does not reach the *statement* of the following declaration,
  so a `filter` in the statement needs an explicit `[DecidablePred P]` binder.

- 2026-08-04 — **The composition's maximum modulus, bounded below by the inner counts**
  (`CompositionCountLowerBound`, axiom-clean, wired).  `log_norm_comp_ge_count`: with `b_i` the
  `a`-points of the outer function and `T i` the zeros of `g − b_i`,

      (∑_i ∑_{ζ ∈ T i, ‖ζ − c‖ ≤ R₁} l_i ζ) · log(R/R₁)  ≤  log M − log‖f (g c) − a‖,

  where `M` bounds `f ∘ g − a` on the circle of radius `R`.  Jensen's count bound is being used in
  the *reverse* direction from usual: normally it caps the number of zeros by the growth, here the
  zeros are known to be many (they include every `g`-preimage of every `b_i`) and the conclusion is
  that the composition must be large.
  This is composition growth in counting form, and it needs no Pólya disc, no minimum modulus and no
  connectivity — only the factorization chain of `CompositionValuePreimages` and the corpus's own
  Jensen bound.
  With the second main theorem for `g` making `∑_i n(R, b_i; g)` comparable to `p·T(R,g)`, the
  left-hand side grows like `p·T(R,g)`, so `log M(R, f∘g)` outgrows every multiple of `T(R,g)` —
  which is exactly the growth comparison the card's last inequality waits on.

- 2026-08-04 — **The raw count against the integrated one** (axiom-clean).
  `sum_mul_log_le_sum_mul_log` — the elementary comparison `n(r)·log(R/r) ≤ N(R)` in explicit form:

      (∑_{ζ ∈ T, ‖ζ‖ ≤ r} m_ζ)·log(R/r)  ≤  ∑_{ζ ∈ T, ‖ζ‖ ≤ R} m_ζ·log(R/‖ζ‖).

  The hypothesis `0 ∉ T` is essential rather than cosmetic: Lean's `log (R/0) = 0` would let a zero
  at the origin contribute nothing to the right-hand side, breaking an inequality that is true (with
  an infinite contribution) in mathematics.  This is the standard Nevanlinna normalisation `g(0) ≠ b`
  appearing as a Lean necessity.
  This is the bridge between the *raw* counts that the composition factorization produces and the
  *integrated* counting functions that the second main theorem bounds.  Both directions of the
  comparison now exist in the corpus: Jensen (`sum_multiplicity_le_of_factor`) caps the raw count by
  the growth, and this caps it by the integrated count.

- 2026-08-04 — **The count comparison is two-sided** (axiom-clean; module now 151 lines).
  - `sum_mul_log_le_card_mul_log` — `N(r) ≤ n(r)·log(r/t₀)` when every zero has modulus at least
    `t₀`.
  - `le_sum_of_le_sum_mul_log` — hence a *lower* bound on the integrated count gives one on the raw
    count: `N ≤ N(r)` implies `N/log(r/t₀) ≤ n(r)`.

  This is the direction the chain actually needs.  The second main theorem bounds `N` from below;
  `log_norm_comp_ge_count` consumes a raw count; this converts between them at the cost of the
  logarithmic range `log(r/t₀)`, where `t₀` is the modulus of the innermost zero.
  The full chain for the card's growth comparison is now assembled from corpus theorems:

      SMT for g          →  N(r, b_i; g) large
      le_sum_of_le_sum_mul_log →  n(r, b_i; g) large
      comp_flat_factor + Jensen (log_norm_comp_ge_count) →  log M(R, f∘g) large,

  each step unconditional and axiom-clean.  What remains is to instantiate the chain end to end with
  the cascade's own functions and constants — assembly, with no analytic gap left in it.

- 2026-08-04 — **The composing interface** (axiom-clean).
  - `le_of_counts_and_bound` — if each block has at least `N i` zeros in the sub-disc, the growth
    bound holds with `∑ N i` in place of the exact counts.  Stated against an abstract weight and
    bound so it composes with `log_norm_comp_ge_count` *without repeating its fifteen hypotheses* —
    the alternative was a theorem whose statement was longer than its proof.
  - `log_div_nonneg` — the logarithmic weight is nonnegative on the intended range.

  With these the chain is callable as three steps rather than one monolith:

      (1) SMT for g                              gives  N(r, b_i; g) ≥ …
      (2) le_sum_of_le_sum_mul_log               gives  n(r, b_i; g) ≥ …
      (3) le_of_counts_and_bound ∘ log_norm_comp_ge_count
                                                 gives  log M(R, f∘g) ≥ (∑_i …)·log(R/R₁).

  Every link is unconditional and axiom-clean.  The card's remaining work is choosing the constants
  (`p`, the values `b_i`, the radii) so that the right-hand side beats the Clunie weight, and that is
  arithmetic over statements the corpus already owns.

- 2026-08-04 — **From the logarithmic bound to a modulus bound** (axiom-clean).
  `exp_mul_le_of_log_bound` — `B ≤ log M − log‖F c‖` implies `exp B · ‖F c‖ ≤ M`.  This exponentiates
  the growth bound into the form the Clunie weight comparison consumes: the circle supremum of
  `f ∘ g − a` is at least `exp(∑_i n(R, b_i; g)·log(R/R₁))` times its centre value.

  A correction to the shape I first tried: the maximum-point variant `‖F c‖ ≤ ‖F z‖` does **not**
  follow from `hmax`, because the centre `c` is not on the sphere.  Positivity of `‖F z‖` has to come
  from elsewhere (the selection already supplies it via `μ(s) ≤ ‖F z‖`), so the single
  `exp_mul_le_of_log_bound` with an explicit positivity hypothesis is the right interface and the
  variants I sketched were redundant.

- 2026-08-04 — **The growth chain meets the Clunie weight** (axiom-clean).
  - `lt_posLog_of_exp_mul_le` — `exp B · C ≤ x` and `W < B + log C` give `W < log⁺ x`.  This is where
    the two halves join: the growth chain produces a *modulus* bound, the Clunie separation needs a
    `log⁺` inequality, and the logarithm is the only bridge required.
  - `clunieWeight_lt_of_exp_mul_le` — the packaged form: a floor `c₀` for the top grouped
    coefficient, a block bound `W`, and a modulus bound `exp B · C ≤ ‖F_last z‖` together give
    `clunieWeight < log⁺‖F_last z‖`, which is exactly the hypothesis of
    `separatesLast_of_pointwise`.

  So the card's remaining obligation has become a single numeric statement with no analysis in it:

      W + N·log⁺(1/c₀) + (N|S| + N)·log 2  <  B + log C,

  where `B = (∑_i n(R, b_i; g))·log(R/R₁)` from the composition growth and `W`, `c₀`, `C` come from
  the selection.  Every quantity on both sides is now produced by a corpus theorem; what is left is
  to choose the number of values `p` large enough that `B` exceeds the fixed left-hand side, which
  the second main theorem permits for every `p`.

- 2026-08-04 — **The Archimedean step** (axiom-clean; `ClunieSeparationBridge` now 228 lines).
  - `exists_gt_of_linear` — a linear quantity `p·β − γ` with `β > 0` eventually beats any fixed
    bound.
  - `exists_separation_index` — hence there is a number of values `p` for which the hypothesis of
    `clunieWeight_lt_of_exp_mul_le` is met.

  This is the step that converts "the second main theorem holds for every `q`" into "the separation
  holds".  The weight is fixed once the relation `(S, A, N)` is fixed; the growth quantity is linear
  in the number of values with positive slope `β = T(R,g)·log(R/R₁)`; so the inequality is a matter
  of choosing `p`, and Archimedes settles it.

  **The structural chain for `SeparatesLast` is now complete**, every link unconditional and
  axiom-clean:

      exists_radius_floor_and_maxTerm      selection: floor for G, maximum for F_last
      SMT + le_sum_of_le_sum_mul_log       many zeros for each g − b_i
      log_norm_comp_ge_count               ⇒ log-growth bound B, linear in p
      exp_mul_le_of_log_bound              ⇒ modulus bound exp B · C ≤ ‖F_last z‖
      exists_separation_index              ⇒ weight < B + log C for some p
      clunieWeight_lt_of_exp_mul_le        ⇒ clunieWeight < log⁺‖F_last z‖
      separatesLast_of_pointwise           ⇒ SeparatesLast F
      coeff_eq_zero_of_relation            ⇒ the Clunie induction step
      polyIndependent_of_chain             ⇒ ord_DA(F_n) = n.

  What is left is to write the single Lean theorem that walks this chain with the cascade's own
  functions substituted — no further mathematics, and no further infrastructure.

- 2026-08-04 — **The assembled criterion, and cascade independence from it** (axiom-clean;
  `ClunieSeparationBridge` now 283 lines).
  - `separatesLast_of_modulus_bound` — `SeparatesLast F` from a point together with four constants:
    a floor `c₀` for the top grouped coefficient, a block bound `W`, and a modulus bound
    `exp B · C ≤ ‖F_last z‖` whose exponent beats the weight.  All reference to `clunieWeight` and
    to `log⁺` is discharged.
  - `polyIndependent_of_modulus_bound` — feeding that into the Clunie induction
    (`polyIndependent_of_chain`): if at each level the growth chain produces such a point, the whole
    family of cascade states is polynomially independent over `ℂ[z]`.

  That is the criterion the card's theorem applies — `PolyIndependent` for the states is exactly the
  statement that no nontrivial polynomial relation holds among them, which is what pins
  `ord_DA(F_n) = n`.
  The entire structural argument is now a single named chain from geometric data to the cascade
  conclusion, unconditional and axiom-clean at every link.  What is genuinely left is the analytic
  instantiation: producing the four constants at each level from the Wiman--Valiron selection, the
  minimum modulus, and the composition growth — all of which are corpus theorems, none of which is
  yet wired to this interface with the cascade's own functions substituted.

- 2026-08-04 — **The analytic instantiation begins: three constants at one point** (axiom-clean).
  `RHTower.exists_radius_floor_maxTerm_block` — at a single point of a selected circle,
  simultaneously:
  - `H^n·L ≤ ‖G z‖` — the floor `c₀` for the top grouped coefficient, from the minimum modulus;
  - `μ(s) ≤ ‖f z‖` — the dependent state dominates its maximum term, from the circle maximum;
  - `block ≤ |S|·(α + D·β)` — the bound `W`, from the sup bounds over the disc.

  So two of the four constants `separatesLast_of_modulus_bound` needs (`c₀` and `W`) are now produced
  together, at a point that also carries the maximum-term lower bound.  Only the modulus bound
  `exp B · C ≤ ‖F_last z‖` remains, and that is what the composition-growth chain supplies.
  The hypotheses are the honest ones: analyticity and non-degeneracy of `G`, a boundary bound for it,
  and sup bounds for the coefficient polynomials and the earlier states on the disc — all data the
  cascade provides directly, none of it an assumption about the composition.

- 2026-08-04 — **The fourth constant: the modulus bound at the selection point** (axiom-clean).
  The growth chain is about the shifted function `f ∘ g − a`, while the Clunie separation wants
  `‖F_last z‖` itself.
  - `norm_sub_le_of_max` — at the circle maximum of `F`, the supremum of `‖F − a‖` on that circle is
    at most `‖F z‖ + ‖a‖`.  This is what lets the growth bound be applied with an `M` expressed
    through the selection point.
  - `exp_mul_sub_le_of_max` — hence `exp B · ‖F c − a‖ − ‖a‖ ≤ ‖F z‖`: the modulus bound
    `separatesLast_of_modulus_bound` consumes, with `C := ‖F c − a‖` and the shift `‖a‖` subtracted.

  The subtraction is harmless — it is absorbed as soon as `B` is large, which is what the Archimedean
  step arranges.  This also settles why the *maximum* variant of the selection
  (`exists_point_sphere_floor_and_max`) is the one to use rather than the maximum-term variant: the
  growth bound controls a circle supremum, and only the maximum point identifies that supremum with a
  value of `F_last`.
  All four constants of `separatesLast_of_modulus_bound` are now produced by corpus theorems.

- 2026-08-04 — **A shape-independent separation interface** (axiom-clean; `ClunieSeparationBridge`
  now 338 lines).  The growth chain delivers a lower bound on `‖F_last z‖` whose exact shape varies —
  `exp B · C`, or that minus the shift `‖a‖`.  Taking the bound as a single positive number `v`
  removes the dependence:
  - `lt_posLog_of_le` — `0 < v ≤ x` and `W < log v` give `W < log⁺ x`.
  - `separatesLast_of_value_bound` — `SeparatesLast F` from a point with a floor `c₀`, a block bound
    `W`, and *any* positive lower bound `v ≤ ‖F_last z‖` with `weight < log v`.
  - `polyIndependent_of_value_bound` — the corresponding cascade statement.

  This supersedes the `exp B · C` form of the previous entries as the interface to target: it is
  strictly more general, and the chain's `exp B · ‖F c − a‖ − ‖a‖` instantiates it directly with no
  algebraic massaging.  The earlier `separatesLast_of_modulus_bound` remains as the specialised form.

- 2026-08-04 — **The criterion in terms of the maximum term** (`CascadeSeparationCriterion`,
  axiom-clean, wired).
  - `separatesLast_of_maxTerm_bound` — with the dependent state given as `coeffFun a`, and at a
    selected point a floor `c₀`, a block bound `W`, and `μ(s) ≤ ‖coeffFun a z‖`, the separation
    follows from the single inequality

        W + N·log⁺(1/c₀) + (N|S| + N)·log 2  <  log μ(s).

  - `polyIndependent_of_maxTerm_bound` — the cascade form.

  **This is the sharpest statement of what remains.**  The whole Clunie argument for the card is now
  reduced to one inequality between the Clunie weight and `log μ(s, F_last)` at the selected point.
  Everything else — the selection, the floor, the block bound, the induction, the passage from
  `SeparatesLast` to `ord_DA(F_n) = n` — is proved.
  The growth of the composition enters *only* through that inequality: `μ(s, F_last)` is the maximum
  term of `f_{k+1} ∘ F_k`, and the composition-growth chain built earlier this session is what makes
  its logarithm outgrow the weight, which depends only on the earlier states and the relation's own
  data.

- 2026-08-04 — **The floor term, decomposed** (axiom-clean).
  - `posLog_inv_pow_mul_le` — for `0 < H ≤ 1`, `log⁺(1/(H^n·L)) ≤ n·log(1/H) + log⁺(1/L)`.  No
    hypothesis on `L` is needed: the splitting is an identity and `posLog` is submultiplicative
    unconditionally, so the positivity of the Borel--Carathéodory constant never enters.
  - `clunie_weight_le_of_floor_shape` — hence the Clunie weight is bounded by an expression **linear
    in the zero count `n`** of the top grouped coefficient.

  This is what makes the final comparison tractable.  The weight now reads

      |S|·(α + D·β) + N·(n·log(1/H) + log⁺(1/L)) + (N|S| + N)·log 2,

  in which `α` is logarithmic in the radius, `β` is the earlier states' growth, and `n` is bounded by
  Jensen in terms of the same data.  So the whole weight is `O(β)` with a constant depending only on
  the relation `(S, N, D)` and the selection parameters — while `log μ(s, F_last)` outgrows every
  multiple of `β` by the composition-growth chain.  That is the shape of the remaining inequality,
  now with every term explicit.

- 2026-08-04 — **The grouped coefficient's own growth** (axiom-clean).
  `posLog_norm_groupedCoeff_le_of_sup` — `log⁺‖G z‖ ≤ |S|·(α + D·β) + |S|·log 2`, combining the
  corpus's existing `posLog_norm_groupedCoeff_le` with `clunie_block_le` over the filtered exponent
  set.
  (Checked the corpus first: `posLog_norm_groupedCoeff_le` was already there, bounding `log⁺‖G‖` by
  the block over the filtered set plus `|S|·log 2`.  Only the composition with the sup bounds was
  missing.)
  This closes the last dependency in the weight.  The zero count `n` of `G` is bounded by Jensen in
  terms of `log⁺ M_G`, which this bounds by `|S|·(α + D·β) + |S|·log 2` — the same data as the block.
  So every term of

      |S|·(α + D·β) + N·(n·log(1/H) + log⁺(1/L)) + (N|S| + N)·log 2

  is now bounded by an explicit function of `α`, `β` and the relation data, with no circularity: the
  weight never refers to the dependent state.  The remaining inequality is therefore exactly
  `log μ(s, F_last)` against a fixed multiple of `β`, and the composition-growth chain is what
  settles it.

- 2026-08-04 — **The zero count, bounded by the block data** (axiom-clean).
  - `norm_le_exp_of_posLog_le` — a `log⁺` bound is an exponential modulus bound, `‖x‖ ≤ exp B`.  The
    junk case `‖x‖ = 0` is harmless: `exp B > 0` covers it.
  - `count_mul_log_le_of_sup` — Jensen's count bound with the boundary maximum replaced by the
    exponential of the block bound.
  - `count_le_of_sup` — hence `n ≤ (Bd − log‖G c‖)/log(R/R₁)`.

  With `Bd = |S|·(α + D·β) + |S|·log 2` from the previous entry, the zero count of the top grouped
  coefficient is now bounded by the same `α`, `β` data as everything else in the weight.  The weight
  is therefore a *fixed* function of the relation and the earlier states — the closure I set out to
  establish three entries ago — and the only quantity that grows with the dependent state is
  `log μ(s, F_last)` on the other side of the inequality.

- 2026-08-04 — **The Clunie weight, fully explicit** (`clunie_weight_le_explicit`, axiom-clean;
  module now 198 lines).  Assembling the block bound, the floor decomposition and the zero-count
  bound:

      weight ≤ |S|·(α + D·β)
               + N·(((Bd − log‖G c‖)/log(R/R₁))·log(1/H) + log⁺(1/L))
               + (N|S| + N)·log 2,

  in which **no term refers to the dependent state**.  `α` is the coefficient polynomials' growth,
  `β` the earlier states', `Bd` the grouped coefficient's own bound from those two, and the rest are
  the relation's and the selection's constants.
  Combined with `separatesLast_of_maxTerm_bound`, the card's obligation is now a single inequality
  between that explicit expression and `log μ(s, F_last)` — both sides written out, with the growth
  of the composition the only thing that can make the right side win.
  (The positivity `0 < log(R/R₁)` turned out not to be needed here: the zero-count bound is taken as
  a hypothesis, so the algebra is monotone without it.)

- 2026-08-04 — **The final criterion** (`separatesLast_of_explicit_bound`, axiom-clean; module now
  236 lines).  Everything the Clunie argument needs, with the weight written out.  A caller supplies
  a selected point `z` with `‖z‖ = s`, the selection constants `(α, β, D, H, L, R, R₁, Bd, Gc, n)`,
  and the single inequality

      |S|·(α + D·β) + N·(((Bd − Gc)/log(R/R₁))·log(1/H) + log⁺(1/L)) + (N|S| + N)·log 2
        <  log μ(s),

  together with the routine side conditions (`0 < H ≤ 1`, the floor, the block bound,
  `μ(s) ≤ ‖coeffFun a z‖`, the zero-count bound).  `SeparatesLast F` follows.

  **This is the terminal reduction for the card.**  From here `polyIndependent_of_chain` gives the
  cascade independence and hence `ord_DA(F_n) = n`; below here every step of the Clunie argument, the
  Nevanlinna theory, the composition growth and the selection is proved, unconditional and
  axiom-clean.  What is left is not a gap in the argument but an instantiation: choosing the
  constants for the cascade's own `f_{k+1} ∘ F_k` so that the displayed inequality holds, which the
  composition-growth chain (`log_norm_comp_ge_count` with the second main theorem for `F_k`) is built
  to deliver.

- 2026-08-04 — **The final criterion against a free value bound** (axiom-clean; module now 292
  lines).
  - `separatesLast_of_explicit_value_bound` — the same explicit weight, but with the dependent
    state's lower bound left free as `v` rather than fixed to `μ(s)`.
  - `polyIndependent_of_explicit_value_bound` — the cascade form.

  This corrects a loss in the previous entry.  The composition-growth chain bounds the *circle
  supremum* of `f ∘ g − a` from below, and at the selected point that supremum **is** `‖F_last z‖`;
  routing it through `μ(s) ≤ ‖F_last z‖` would give away the gap between the maximum term and the
  maximum modulus — which for a function of large central index is exactly the factor the estimate
  can least afford.  The value-bound form takes `v := ‖F_last z‖` directly.
  The maximum-term form (`separatesLast_of_explicit_bound`) is kept: it is the right interface when
  the lower bound comes from a Wiman--Valiron selection rather than from composition growth.

- 2026-08-04 — **Absorbing the shift** (axiom-clean).  The composition-growth chain delivers
  `v = exp B · C − sh` with `sh = ‖a‖` the shift of the value.
  - `lt_log_sub_of_lt` — once `2·sh ≤ exp B · C`, the subtraction costs exactly `log 2`: it suffices
    that `W < B + log C − log 2`.
  - `exp_mul_sub_pos` — and the bound is then positive, which the criterion needs.

  So the shift, which entered when the argument moved from `f ∘ g` to `f ∘ g − a`, is paid for by a
  single additive `log 2` — the same currency as every other bookkeeping loss in the weight.  With
  `B` linear in the number of values, `exists_gt_of_linear` settles the resulting inequality.
  (`0 ≤ sh` is not needed for the positivity: `2sh ≤ exp B·C` already forces `sh < exp B·C`.)

- 2026-08-04 — **The criterion in terms of the growth exponent** (`separatesLast_of_growth_exponent`,
  axiom-clean; module now 354 lines).  The interface the composition-growth chain feeds directly: the
  dependent state's lower bound is `exp B · C − sh`, and the whole obligation is

      |S|·(α + D·β) + N·(((Bd − Gc)/log(R/R₁))·log(1/H) + log⁺(1/L)) + (N|S| + N)·log 2
        <  B + log C − log 2.

  Left side: the relation's data and the earlier states' growth.  Right side: the growth exponent of
  the composition, which `log_norm_comp_ge_count` makes equal to `(∑_i n(R, b_i; g))·log(R/R₁)` and
  the second main theorem makes linear in the number of values.
  Nothing but this comparison stands between the corpus and `ord_DA(F_n) = n`, and both sides of it
  are now produced by named, axiom-clean theorems.

- 2026-08-04 — **The cascade form, and achievability of the exponent** (axiom-clean; module now 390
  lines).
  - `polyIndependent_of_growth_exponent` — the theorem the card's proof invokes: if at every level of
    the cascade the composition growth beats the relation's weight, the states are polynomially
    independent, hence `ord_DA(F_n) = n`.
  - `exists_growth_exponent` — and when the exponent is linear in the number of values with positive
    slope, that comparison holds for some number of values.  This is `exists_gt_of_linear` in the
    criterion's own shape, so the last step of the argument is a one-line application rather than a
    re-derivation.

  **Summary of the card's state.**  The full argument is present in the corpus as a chain of named,
  unconditional, axiom-clean theorems: Wiman--Valiron selection, minimum modulus, Poisson--Jensen,
  Nevanlinna's first and second main theorems, the logarithmic-derivative estimate, composition
  growth by counting, the Clunie induction, and the reduction of the cascade statement to a single
  growth comparison which is itself achievable.  What has never been done in one place is the
  substitution of the cascade's own `f_{k+1} ∘ F_k` into that chain with all constants fixed; that
  remains the outstanding work, and it is instantiation rather than mathematics.

- 2026-08-04 — **The cascade itself** (`EntireCascade`, axiom-clean, wired).  The instantiation needs
  the object the card is about, and the corpus did not have it: the only `cascade` in the tree is the
  abstract triangular-power one of `TerminalPowerCascadeInduction`, a different structure.
  - `entireCascade f` — `F_0 = id`, `F_{k+1} = f_k ∘ F_k`.
  - `analyticOnNhd_entireCascade`, `analyticOnNhd_cascadeFamily` — every state is entire when the
    constituents are.
  - `cascadeFamily f n` — the states indexed by `Fin n`, and `cascadeFamily_castLE_last` /
    `cascadeFamily_castLE`, which say that under the truncation `Fin.castLE` the last index names
    `f_m ∘ F_m` and the earlier ones name the earlier states.

  Those two `castLE` lemmas are what will let `polyIndependent_of_growth_exponent` be applied to the
  cascade: its hypothesis quantifies over truncations, and the composition structure has to be
  visible through the truncation map for the growth argument to apply at each level.

- 2026-08-04 — **The criterion for the cascade** (`polyIndependent_cascadeFamily`, axiom-clean).
  The separation criterion with the cascade's states substituted, so the growth hypothesis reads

      exp B · C − sh  ≤  ‖f_m (F_m z)‖

  with the composition explicit rather than hidden behind the truncation map.  The earlier states
  appear as `entireCascade f (i+1)` throughout.
  Two things fell out cheaply: `cascadeFamily_castLE` handles the last index as well as the earlier
  ones (`Fin.last m` is just an index), and `entireCascade f (m+1) z` is *definitionally*
  `f m (entireCascade f m z)`, so no rewriting is needed to expose the composition — `exact` accepts
  it.
  The criterion is now stated entirely in the card's own vocabulary: constituents `f_m`, states
  `F_m`, and one growth inequality per level.

- 2026-08-04 — **The chain rule along the cascade** (axiom-clean).
  - `deriv_entireCascade_succ` — `F_{k+1}' = f_k'(F_k)·F_k'`.
  - `differentiable_entireCascade` — the states are differentiable everywhere.

  This is the first step of the bridge from `PolyIndependent` to the card's conclusion.  The corpus's
  notion of the conclusion is `ExactDifferentialOrder f n` in
  `ExactDifferentialOrderAffine.lean`, defined as `DifferentiallyAlgebraicOfOrder f n` together with
  no relation of smaller order — literally `ord_DA(f) = n`.
  **The bridge that remains**: a relation of order `m` for `F_n` involves `F_n, F_n', …, F_n^{(m)}`;
  iterating the chain rule and using each `f_k`'s first-order equation (which makes `f_k'` algebraic
  over `ℂ(z, f_k)`) expresses all of those in the algebraic closure of `ℂ(z, F_1, …, F_n)`, turning
  the relation into a polynomial one among the states — which `PolyIndependent` forbids.  That
  derivation is differential algebra, not analysis, and it is the last unbuilt component; the
  analytic side of the card is complete.
  (Checked: `PolyIndependent` currently has no downstream consumer in the corpus, so this bridge is
  genuinely absent rather than misplaced.)

- 2026-08-04 — **Clearing the chain-rule denominator** (`CascadeRelationClearing`, axiom-clean,
  wired).  The algebraic half of the passage from a differential relation for the last state to a
  polynomial relation among all of them:
  - `sum_mul_div_pow_eq_zero` — a vanishing polynomial in `w/t` of degree `≤ d` becomes, after
    multiplying by `t^d`, a vanishing polynomial in `w` and `t`.
  - `deriv_eq_div_of_cascade` — where `F_n' ≠ 0`, the constituent's derivative *at the state* is the
    quotient `F_{n+1}'/F_n'`.
  - `cascade_relation_cleared` — hence the constituent's first-order equation, evaluated at the
    state, becomes

        ∑_c A_c · (F_{n+1}')^c · (F_n')^{d−c} = 0,

    a polynomial relation among the two states' derivatives with no division.

  The hypothesis `F_n' ≠ 0` is where this will need care: it holds off a discrete set, and the
  separation argument selects its points, so the two selections have to be made compatible — the same
  pattern as the codiscrete handling in the second main theorem.
  This is the first concrete step of the differential-algebra bridge named in the previous entry.

- 2026-08-04 — **Non-constancy along the cascade** (axiom-clean).
  - `exists_ne_comp` — non-constancy is preserved by composition of entire functions: a non-constant
    inner function has open image (open mapping), and an entire outer function constant on an open
    set is constant everywhere (identity theorem).
  - `exists_ne_entireCascade` — hence every cascade state is non-constant when every constituent is.

  This is what discharges the `F_n' ≠ 0` hypothesis of `cascade_relation_cleared`: a non-constant
  entire function has a derivative that is entire and not identically zero, so the bad set is
  discrete — the same codiscrete handling used for the critical points in the second main theorem.
  Note the base case is `F_0 = id`, non-constant by inspection, so the induction needs no hypothesis
  about the cascade beyond the constituents.

- 2026-08-04 — **The derivative is nowhere locally zero** (axiom-clean; module now 164 lines).
  - `not_eventually_deriv_eq_zero` — a non-constant entire function's derivative is nowhere locally
    zero, via the identity theorem for `deriv g` (analytic by `AnalyticOnNhd.deriv`) and mathlib's
    `is_const_of_deriv_eq_zero`.
  - `not_eventually_deriv_entireCascade_eq_zero`, `not_eventually_entireCascade_eq_const` — the same
    for every cascade state.

  These are exactly the hypothesis shapes `exists_radius_norm_ge_of_analytic` and the codiscrete
  selection consume (`∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, · = 0`), so the cascade's own states can now be fed to
  the minimum modulus and to `eventually_deriv_ne_zero` without any further side conditions.
  With this the `F_n' ≠ 0` requirement of `cascade_relation_cleared` is fully discharged from
  non-constancy of the constituents alone.

- 2026-08-04 — **The second derivative along the cascade** (axiom-clean; module now 202 lines).
  `deriv2_entireCascade_succ` —

      F_{n+1}'' = f_n''(F_n)·(F_n')² + f_n'(F_n)·F_n''.

  This is the pattern the induction follows: differentiating a state introduces only further
  derivatives of the same objects — the constituent's derivatives *at the previous state* and the
  previous state's own derivatives.  No new transcendental data appears, which is exactly why a
  relation of order `m` for the last state collapses to a polynomial relation among the states once
  each `f_k'` is eliminated by its own first-order equation.
  Lean note: `HasDerivAt.mul` produces the Pi-form product `f * g`, not `fun w => f w * g w`, so the
  `rw [hprod.deriv]` only matches once the intended type is written out in the `have`.  Same shape
  trap as `circleAverage_add` and `MeromorphicOn.sum` earlier in this session.

- 2026-08-04 — **Expressions in the cascade data** (`CascadeExpression`, axiom-clean, wired).
  `CascadeExpr f n` — the functions reachable from the states `F_i` and the constituents' iterated
  derivatives *at those states*, by constants, sums and products.  Defined inductively rather than as
  a `Subring.closure`, so that differentiability and closure under `deriv` are proved by the same
  structural induction rather than by a closure-induction with side conditions.
  - `analyticOnNhd_iteratedDeriv` — iterated derivatives of an entire function are entire.
  - `differentiable_cascadeExpr` — every expression is entire.
  - `cascadeExpr_deriv_state` — the derivative of a state is an expression: `F_0' = 1`, and
    `F_{i+1}' = f_i'(F_i)·F_i'` is a product of a generator with an expression.

  Next is the general closure `CascadeExpr f n g → CascadeExpr f n (deriv g)`, which needs only the
  Leibniz rule and the two generator cases already handled — after which every derivative of the last
  state is an expression, and the differential relation becomes a relation among the states and the
  constituents' derivatives at them.

- 2026-08-04 — **The expression class is closed under differentiation** (axiom-clean; module now 144
  lines).
  - `cascadeExpr_deriv` — `CascadeExpr f n g → CascadeExpr f n (deriv g)`.  The two generator cases
    are the chain rule (`deriv^[d](f_i) ∘ F_i` differentiates to `deriv^[d+1](f_i) ∘ F_i` times
    `F_i'`); the rest is Leibniz, with differentiability supplied by `differentiable_cascadeExpr`.
  - `cascadeExpr_iteratedDeriv_state` — hence **every iterated derivative of every state is an
    expression**.

  This is the structural heart of the differential-algebra bridge.  A relation of order `m` for the
  last state is a polynomial in `z` and `F_n^{(0..m)}`, and all of those are now known to be
  expressions in the states and the constituents' derivatives at them.  What remains is to eliminate
  those derivatives using each constituent's first-order equation — for which
  `cascade_relation_cleared` is the tool — leaving a polynomial relation among the states alone,
  which `PolyIndependent` forbids.

- 2026-08-04 — **Polynomials of states, and the constituents' equations at the states**
  (axiom-clean; module now 193 lines).
  - `cascadeExpr_pow`, `cascadeExpr_polynomial` — powers and polynomials of expressions are
    expressions, by `Polynomial.induction_on'`.  So the coefficient polynomials `a_{b,c}(F_i)` of the
    card's first-order equations are expressions.
  - `cascade_constituent_relation` — the substitution step: a first-order equation
    `∑ a_{b,c}(u)·f_i(u)^b·f_i'(u)^c = 0` evaluated at `u := F_i w` reads

        ∑ a_{b,c}(F_i w)·(F_{i+1} w)^b·(f_i'(F_i w))^c = 0,

    a polynomial relation between the two states and the constituent's derivative there.  The proof
    is `hP (entireCascade f i w)` — the identity `f_i (F_i w) = F_{i+1} w` is definitional, so no
    rewriting is needed.

  Combined with `cascade_relation_cleared`, this eliminates `f_i'(F_i w)` in favour of
  `F_{i+1}'/F_i'` and clears the denominator, leaving a polynomial relation among the states and
  their first derivatives — and those derivatives are expressions by
  `cascadeExpr_iteratedDeriv_state`.

- 2026-08-04 — **The constituent's equation, grouped by the derivative's exponent** (axiom-clean;
  module now 226 lines).  `cascade_constituent_grouped` — collecting the terms of each power of
  `f_i'(F_i)`:

      ∑_{c ≤ d} ( ∑_{p : p₂ = c} a_p(F_i)·F_{i+1}^{p₁} ) · (f_i'(F_i))^c = 0,

  a polynomial in the single quantity `f_i'(F_i)` whose coefficients are expressions in the two
  states.  Proved by `Finset.sum_fiberwise_of_maps_to` over the fibres of the exponent map, with the
  power pulled out of each fibre.
  This is exactly the shape `cascade_relation_cleared` consumes: substituting `f_i'(F_i) =
  F_{i+1}'/F_i'` and multiplying by `(F_i')^d` gives a polynomial relation among `F_i`, `F_{i+1}`,
  `F_i'` and `F_{i+1}'` — all of which are expressions.  The two halves of the elimination now meet.

- 2026-08-04 — **The relation among the states alone** (axiom-clean; module now 287 lines).
  - `cascade_state_relation` — composing the grouping with the denominator clearing, the
    constituent's first-order equation becomes

        ∑_{c ≤ d} ( ∑_{p₂ = c} a_p(F_i)·F_{i+1}^{p₁} ) · (F_{i+1}')^c · (F_i')^{d−c} = 0,

    with **no reference to the constituent's derivative**.
  - `cascadeExpr_state_relation_coeff` — and each coefficient is a `CascadeExpr`, by induction over
    the exponent set with the `filter_insert` case split.

  So the elimination is complete: each constituent's first-order equation has been converted into a
  polynomial identity among two consecutive states and their derivatives, every term of which is an
  expression in the cascade data.  This is the differential-algebra content of Reduction I on the
  card, and it is now Lean-complete.
  The remaining link to `PolyIndependent` is the passage from "a relation among states and their
  derivatives" to "a relation among the states", which is where each `F_i'` gets eliminated in turn
  by the same identity one level down — the induction the card's Reduction II performs.

- 2026-08-04 — **The state's derivative is algebraic over the cascade data** (axiom-clean; module now
  329 lines).
  - `stateRelationCoeff`, `cascadeExpr_stateRelationCoeff` — the coefficient of the state relation
    with the lower state's derivative absorbed, and the proof that it is a `CascadeExpr`.
  - `cascade_deriv_poly_relation` — hence

        ∑_{c ≤ d} stateRelationCoeff(c)·(F_{i+1}')^c = 0,

    a polynomial for `F_{i+1}'` whose coefficients are expressions.

  **No separate notion of "algebraic over the states" is needed.**  I had expected to introduce one
  and induct on it; that turned out to be unnecessary, because `cascadeExpr_iteratedDeriv_state`
  already puts every `F_i'` in the expression class, so the absorbed coefficients are in the class
  outright.  The induction that seemed to be required is subsumed by the closure of the class under
  differentiation.

- 2026-08-04 — **Polynomials in the states** (`StatePolynomial`, axiom-clean, wired).
  `statePoly F P` — the function defined by `P : MvPolynomial (Fin n) (Polynomial ℂ)` evaluated at
  the states, with the coefficients specialised at `z`.  Packaging the relation this way lets
  mathlib's ring structure carry the sums and products, so `statePoly_add` and `statePoly_mul` are
  one `simp` each rather than hand-rolled convolutions over exponent multisets.
  - `statePoly_eq_sum` — the monomial expansion,

        statePoly F P z = ∑_{e ∈ supp} (coeff e P).eval z · ∏_i (F_i z)^{e_i},

    which is exactly the shape `PolyIndependent` speaks about.

  This is the vocabulary bridge: `CascadeExpr` elements built only from states and constants are
  `statePoly`s, and a vanishing `statePoly` is a monomial relation among the states.  What the
  bridge still needs is the elimination of the remaining generators — the constituents' derivatives
  at the states — which `cascade_deriv_poly_relation` makes algebraic over the same data.

- 2026-08-04 — **Polynomial independence characterised** (axiom-clean).
  - `statePoly_eq_sum_support` — the monomial expansion indexed by the polynomial's own support; the
    terms killed by specialising the coefficients at `z` contribute nothing.
  - `eq_zero_of_polyIndependent` — **`PolyIndependent F` says exactly that no nonzero
    `P : MvPolynomial (Fin n) (Polynomial ℂ)` has `statePoly F P` identically zero.**

  This is the usable form of the independence conclusion.  Everything downstream of the Clunie
  induction can now be phrased as "produce a nonzero `P` with `statePoly F P = 0`", which is what a
  low-order differential relation for the last state must yield once the constituents' derivatives
  are eliminated.
  Lean note: `MvPolynomial` supports are `Finsupp`s, so `PolyIndependent`'s exponent map is the
  coercion `Finsupp → (Fin n → ℕ)` and its injectivity is `DFunLike.coe_injective`, not
  `Set.injOn_id`.

- 2026-08-04 — **The cascade order theorem, assembled** (`CascadeOrderTheorem`, axiom-clean, wired).
  The card's statement in the corpus's own vocabulary:
  - `exactDifferentialOrder_of_cascade` — with an order-`n` equation for the last state, polynomial
    independence of the states, and the elimination step, `ExactDifferentialOrder (F_n) n` — that is,
    `ord_DA(F_n) = n`.
  - `not_differentiallyAlgebraicOfOrder_of_cascade` — the lower bound on its own.

  The two named obligations are exactly the card's two reductions:
  1. `hup` — the order-`n` equation for the composition (the card's constructive upper bound);
  2. `helim` — a low-order equation yields a nonzero polynomial relation among the states, i.e. the
     elimination of the constituents' derivatives.

  Everything else in the argument — the Clunie induction, `SeparatesLast`, the growth chain, the
  Nevanlinna theory, the expression calculus, the independence characterisation — is proved,
  unconditional and axiom-clean.  The top-level theorem now exists and names precisely what is left.

- 2026-08-04 — **First-order equations as multivariate polynomials** (`FirstOrderMvPoly`,
  axiom-clean, wired).  The card writes a first-order equation as `∑ a_p(z)·g^{p₁}·(g')^{p₂} = 0`;
  the corpus's `DifferentiallyAlgebraicOfOrder` uses an `MvPolynomial (Fin 3) ℂ` in `(z, g, g')`.
  - `firstOrderMvPoly` — the translation, sending `z ↦ X 0`, `g ↦ X 1`, `g' ↦ X 2` via
    `Polynomial.eval₂ C (X 0)` on the coefficients.
  - `eval_firstOrderMvPoly` — the two evaluate to the same thing.
  - `differentiallyAlgebraicOfOrder_one_of_relation` — hence a first-order relation *is* an
    order-one algebraic differential equation, which is the `n = 1` case of the card's upper bound
    `hup`.

  Lean note: `Fin.cons z t 2` does not reduce under `fin_cases`, because the numeral `2` is not
  syntactically `Fin.succ 1` and `Fin.cons_succ` therefore does not fire.  Rewriting with
  `Fin.cons_succ` *before* the case split fixes it; this cost three iterations and is worth
  remembering for any `iteratedDeriv` vector.

- 2026-08-04 — **Order zero is algebraicity** (axiom-clean).
  - `norm_le_of_order_zero`, `posLog_norm_le_of_order_zero` — from an order-zero relation, at points
    where the leading coefficient does not vanish, the value is bounded by the normalised lower
    coefficients.  These are instances of the corpus's existing `norm_le_max_sum_of_root` and
    `posLog_norm_le_of_root` (`AlgebraicRootGrowth`), so no new estimate was needed.

  **What the `n = 1` case of the card reduces to.**  `DifferentiallyAlgebraicOfOrder g 0` says `g` is
  algebraic over `ℂ(z)`.  So the lower bound at `n = 1` is exactly: *a transcendental entire function
  is not algebraic over `ℂ(z)`* — equivalently, an entire algebraic function is a polynomial.  The
  growth half is the bound above (an algebraic entire function has polynomial growth off a finite
  set); the missing half is the Liouville-type step from polynomial growth to being a polynomial.
  This is worth recording because it is the *simplest* instance of the card's lower bound, and it is
  already a genuine theorem rather than bookkeeping — a useful calibration of what the general case
  costs.

- 2026-08-04 — **Liouville at polynomial growth** (`PolynomialGrowthLiouville`, axiom-clean, wired).
  `iteratedDeriv_eq_zero_of_polynomial_growth` — if `‖f z‖ ≤ M(1 + ‖z‖)^d` for an entire `f`, then
  every derivative of order above `d` vanishes identically.

  mathlib carries only the *bounded* case of Liouville's theorem; the polynomial-growth
  generalisation is absent, and it is what identifies an entire algebraic function as a polynomial.
  Proof: on `sphere c R` with `R ≥ 1 + ‖c‖` the growth bound gives `‖f‖ ≤ M·2^d·R^d`, so Cauchy's
  iterated estimate gives `‖f^{(n)}(c)‖·R^{n−d} ≤ n!·M·2^d` for every such `R`; taking `R` past
  `A/‖f^{(n)}(c)‖` contradicts positivity.  No limit is taken — the Archimedean choice of `R` does the
  work directly.
  This closes the growth half of the `n = 1` lower bound; what remains there is the passage from
  "all derivatives above `d` vanish" to "is a polynomial", which is a Taylor-expansion statement.

- 2026-08-04 — **Formal antiderivatives of polynomials** (`PolynomialAntiderivative`, axiom-clean,
  wired).  mathlib does not record the surjectivity of `Polynomial.derivative` over a
  characteristic-zero field, so the primitive is built here by dividing each coefficient by its
  shifted exponent.
  - `polyAntideriv`, `derivative_polyAntideriv` — the antiderivative differentiates back.
  - `deriv_polyAntideriv_eval` — and as a function, `d/dz (polyAntideriv p)(z) = p(z)`.

  This supplies the inductive step of "all derivatives above `d` vanish ⟹ is a polynomial": the
  derivative is a polynomial by induction, its primitive is a polynomial, and the difference has zero
  derivative hence is constant.  With `iteratedDeriv_eq_zero_of_polynomial_growth` from the previous
  entry, the two halves of "entire algebraic ⟹ polynomial" — the `n = 1` lower bound of the card —
  are both in place.

- 2026-08-04 — **Vanishing high derivatives means polynomial** (axiom-clean; module now 97 lines).
  `exists_polynomial_of_iteratedDeriv_eq_zero` — an entire function whose derivatives above `d`
  vanish agrees with a polynomial.  Induction on `d`: the base case is
  `is_const_of_deriv_eq_zero`; the step uses `iteratedDeriv_succ'` to pass to `deriv f`, the
  induction hypothesis to make it a polynomial, and `polyAntideriv` to subtract a primitive, leaving
  a function with zero derivative.

  Combined with `iteratedDeriv_eq_zero_of_polynomial_growth`, this gives **entire + polynomial
  growth ⟹ polynomial** — the Liouville statement mathlib lacks, and the exact tool that turns an
  entire algebraic function into a polynomial.  The `n = 1` lower bound of the card is now reachable:
  an order-zero relation gives polynomial growth off the leading coefficient's zeros
  (`norm_le_of_order_zero`), hence polynomiality, contradicting transcendence.

- 2026-08-04 — **Liouville at polynomial growth, final form** (axiom-clean).
  - `exists_polynomial_of_polynomial_growth` — **an entire function of polynomial growth is a
    polynomial**.  This is the generalisation of Liouville's theorem that mathlib does not carry, and
    it is now a corpus theorem: the Cauchy estimate kills the high derivatives, the antiderivative
    construction integrates back.
  - `exists_norm_gt_of_not_polynomial` — the contrapositive: a transcendental entire function exceeds
    every polynomial bound.  This is the form in which transcendence is used against a growth
    estimate, and it is what the card's hypothesis on the constituents supplies.

  Beyond this card, the pair is generally useful: every argument in the corpus that wants
  "transcendental ⟹ grows faster than any polynomial" can now cite it instead of assuming it.

- 2026-08-04 — **Two-variable polynomials as polynomials in the second variable**
  (`TwoVariableDecomposition`, axiom-clean, wired).
  - `twoVarCoeff P k` — the coefficient of `u^k`, as a polynomial in the first variable.
  - `eval_eq_sum_twoVarCoeff` — evaluating a two-variable polynomial equals evaluating the
    one-variable polynomial in `u` whose coefficients are those.

  The device is the same fibrewise grouping of the support used for the constituents' equations
  (`Finset.sum_fiberwise_of_maps_to`), applied to the second exponent; `MvPolynomial.finSuccEquiv`
  would have split off the *first* variable and needed a rename to be useful here.
  This turns an order-zero relation into the coefficient form `∑_k a_k(z)·g(z)^k = 0` that
  `norm_le_of_order_zero` consumes, so the growth bound for an algebraic entire function is now
  reachable from the corpus's own definition of differential order.

- 2026-08-04 — **Order-zero equations in coefficient form** (axiom-clean).
  `exists_coeff_relation_of_order_zero` — an order-zero algebraic differential equation
  `P(z, g z) = 0` is a polynomial relation `∑_k a_k(z)·g(z)^k = 0` with the degree taken as the
  support's supremum in the second exponent.
  This connects the corpus's `DifferentiallyAlgebraicOfOrder` directly to the algebraic root
  estimate.  What the statement does *not* yet carry is nondegeneracy — that some `a_k ≠ 0`, which
  needs the coefficient identification `Polynomial.coeff j (twoVarCoeff P k) = MvPolynomial.coeff
  (fin₂ j k) P`.  Without it the relation could be vacuous, so that identification is the next step
  for this branch.
  (The `Fin.cons z t` reduction trap recurred here for `Fin 1`; the same `Fin.cons_succ`-before-
  `fin_cases` fix applies.)

- 2026-08-04 — **Coefficient identification for the two-variable decomposition** (axiom-clean;
  module now 138 lines).
  - `fin2Exp`, `fin2Exp_eq`, `fin2_ext` — an exponent vector on `Fin 2` is determined by its two
    entries.
  - `coeff_twoVarCoeff` — hence `Polynomial.coeff j (twoVarCoeff P k) = MvPolynomial.coeff
    (fin2Exp j k) P`: the fibre sum collapses to a single term, because within a fibre the first
    exponent determines the vector.

  This closes the nondegeneracy gap flagged in the previous entry.  A nonzero `P` has some nonzero
  coefficient `coeff m P`, and `coeff_twoVarCoeff` at `(j, k) = (m 0, m 1)` makes the corresponding
  `twoVarCoeff P (m 1)` nonzero — so the coefficient form of an order-zero equation is never vacuous.

- 2026-08-04 — **The order-zero equation in nondegenerate coefficient form** (axiom-clean; module
  now 180 lines).  `exists_nonzero_coeff_relation_of_order_zero` — an order-zero algebraic
  differential equation for `g` yields

      ∃ d, ∃ a : ℕ → ℂ[X], (∃ k ≤ d, a k ≠ 0)  ∧  ∀ z, ∑_{k ≤ d} a_k(z)·g(z)^k = 0.

  The nondegeneracy comes from `coeff_twoVarCoeff`: a nonzero `P` has a nonzero coefficient at some
  exponent vector `m`, and that same value is the `m 0`-th coefficient of `twoVarCoeff P (m 1)`.
  This is the complete translation of the corpus's order-zero notion into the form the algebraic root
  estimate consumes, with no hypothesis left implicit.  For the `n = 1` case of the card what remains
  is the growth argument itself: the estimate bounds `g` by the normalised coefficients off the
  leading coefficient's zeros, and `exists_polynomial_of_polynomial_growth` then contradicts
  transcendence.

- 2026-08-04 — **Explicit growth bounds for polynomials** (`PolynomialGrowthBound`, axiom-clean,
  wired).
  - `coeffNormSum` — the sum of a polynomial's coefficient norms.
  - `norm_eval_le_coeffNormSum` — `‖p(z)‖ ≤ coeffNormSum p · (1 + ‖z‖)^{deg p}`.
  - `norm_eval_le_of_family` — the same with a common degree bound for a finite family.

  This is the elementary input the `n = 1` growth argument needs on the numerator side.  What is
  still missing there is the denominator: a *lower* bound for `‖a_d(z)‖` away from its zeros, which
  is where the minimum-modulus material already in the corpus (`norm_lower_bound_of_anchor`,
  `PolynomialMinimumModulus`) applies — the polynomial case is the easy one, since a polynomial's
  zeros are finite and explicit.

- 2026-08-04 — **Polynomial lower bound far from the roots** (axiom-clean; module now 118 lines).
  `norm_eval_ge_of_large` — for `p ≠ 0`, once `‖z‖ ≥ 1` and
  `2·coeffNormSum(eraseLead p)·2^{deg−1} ≤ ‖leadingCoeff p‖·‖z‖`,

      ‖leadingCoeff p‖/2 · ‖z‖^{deg p}  ≤  ‖p(z)‖.

  The radius is explicit — no "for large enough `z`" existential — which is what lets it compose with
  the numerator bound to give a genuine polynomial bound for the normalised coefficients.
  With `norm_eval_le_coeffNormSum` this closes the rational-function asymptotic named two entries
  ago: off an explicit disc, `∑‖a_k/a_d‖` is bounded by a polynomial in `‖z‖`, so an entire solution
  of an order-zero equation has polynomial growth there, and `exists_polynomial_of_polynomial_growth`
  applies.
  Lean note: `norm_sub_norm_le` gives `‖a‖ − ‖b‖ ≤ ‖a − b‖`, which is the *wrong* direction for
  extracting a leading term; the right tool is `norm_sub_le` on `(a + b) − b`.

### `HTGeometry/EntireOrderZeroTranscendence.lean` — the lower bound at `n = 1`

`not_differentiallyAlgebraicOfOrder_zero_of_transcendental`: an entire `g` that is not a polynomial
satisfies no order-zero algebraic differential equation. Unconditional, axiom-clean
(`propext, Classical.choice, Quot.sound`).

The chain, all corpus-owned:

1. `exists_nonzero_coeff_relation_of_order_zero` reads `P(z, g z) = 0` as `∑_{k≤d} a_k(z) g(z)^k = 0`
   with some `a_k ≠ 0` (two-variable decomposition).
2. `exists_top_relation` (new) truncates at the **largest** index with `a_D ≠ 0`. This is the step the
   coefficient form does not give for free: the root estimate needs a nonvanishing *top* coefficient,
   and "some coefficient is nonzero" is not that. `Finset.max'` on the nonzero-support supplies it,
   and `Finset.sum_subset` discards the vanishing tail.
3. `D = 0` is impossible: the relation becomes `a_0(z) = 0` for every `z`, and `Polynomial.funext`
   (valid because `ℂ` is infinite) forces `a_0 = 0`.
4. For `D ≥ 1`, `norm_le_max_sum_of_root` bounds `‖g z‖` by `max 1 ∑_{k<D} ‖a_k(z)/a_D(z)‖`, and
   `norm_div_le_of_growthRadius_le` makes each quotient polynomially bounded beyond
   `growthRadius (a_D)`.
5. Inside that disc `g` is bounded by compactness (`IsCompact.exists_bound_of_continuousOn`), so the
   two halves glue into a single global bound `‖g z‖ ≤ M (1+‖z‖)^N`.
6. `exists_polynomial_of_polynomial_growth` (Liouville at polynomial growth, built here) makes `g` a
   polynomial — contradiction.

Supporting additions to `PolynomialGrowthBound.lean`: `norm_div_le_of_large`,
`growthRadius`, `hyps_of_growthRadius_le`, `eval_ne_zero_of_growthRadius_le`,
`norm_div_le_of_growthRadius_le`. Packaging the two hypotheses of the lower bound into one radius is
what makes the estimates composable — the nonvanishing of `a_D` far out is then a *consequence* of the
same inequality that bounds the quotients, so no separate root-avoidance argument is needed.

Lean note: `Finset.range_subset` is **not** the iff `range m ⊆ range n ↔ m ≤ n` in this toolchain —
`refine Finset.range_subset.mpr ?_` leaves the unfolded `∀ x < m, x ∈ range n`, which is why `omega`
reported a counterexample mentioning a phantom `x`. Prove range inclusions by `intro`/`Finset.mem_range`
instead. Second note: after `rw [hD0]` with `hD0 : D = 0`, the sum bound reads `Finset.range (0 + 1)`,
and `Finset.sum_range_one` does not fire until `zero_add` is in the `simp only` set.

### `HTGeometry/TranscendentalEntireOrderOne.lean` — the card's theorem at `n = 1`, unconditionally

`exactDifferentialOrder_one_of_relation`: a transcendental entire `f` satisfying
`∑_{p∈S} a_p(z) f(z)^{p₁} f'(z)^{p₂} = 0` (nonzero relation) has `ord_DA(f) = 1`. No hypotheses beyond
the card's own. Axiom-clean.

`TranscendentalEntire f := Differentiable ℂ f ∧ ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z` — the card's
notion, named so downstream statements read as the paper does. The upper bound is
`differentiallyAlgebraicOfOrder_one_of_relation`; the lower bound is the order-zero theorem of the
previous entry; the two meet at `ExactDifferentialOrder` after `m < 1 → m = 0`.

**The class is inhabited.** Per the vacuity discipline, an existence witness is proved, not assumed:
`exactDifferentialOrder_exp_one : ExactDifferentialOrder Complex.exp 1`. Its two halves:

- `differentiallyAlgebraicOfOrder_one_exp` — `y' − y = 0` in the card's shape, with
  `S = {(0,1),(1,0)}` and `A = ±1`. Nonvanishing of the constructed `firstOrderMvPoly` is checked by
  evaluating at `(z,u,v) = (0,0,1)`, where the sum collapses to `1`: a *value* certificate, not a
  support computation, which is why it is a single `norm_num`.
- `transcendentalEntire_exp` — a polynomial agreeing with `exp` has no roots (`Complex.exp_ne_zero`),
  hence degree `≤ 0` by `Complex.exists_root`, hence is constant by `Polynomial.degree_le_zero_iff`,
  hence has zero derivative; but `Complex.deriv_exp` says that derivative *is* `exp`, which is never
  zero. The derivative closes the argument without any appeal to `exp_eq_one_iff` or to periodicity.

Also `entireCascade_one : entireCascade f 1 = f 0` holds by `rfl` (eta), so
`exactDifferentialOrder_cascade_one` states the same result in the cascade's own vocabulary.

Remaining for `n ≥ 2`: the two named obligations of `exactDifferentialOrder_of_cascade` — `hup`
(construct the order-`n` equation for the composition) and `helim` (elimination of the constituents'
derivatives from a low-order equation).

### `HTGeometry/FirstOrderDerivativeDegree.lean` + `CascadeEdgeRelation.lean` — the nondegeneracy the upper bound needs

`exists_deriv_top_relation_of_order_one`: a transcendental entire `f` with a first-order equation
satisfies `∑_{c ≤ e} B_c(z, f) (f')^c = 0` with `e ≥ 1` and `B_e ≠ 0` in `MvPolynomial (Fin 2) ℂ`.
Unconditional, axiom-clean.

This is the separant-adjacent fact the upper bound was waiting on, and it is *cheap* once the
order-zero theorem is available: the degree in `f'` cannot be `0`, because a degree-`0` reading is
literally a two-variable relation `B_0(z, f) = 0`, i.e. an order-zero equation — impossible for a
transcendental entire function. No irreducibility, no minimal polynomial, no separant computation.

Mechanism: `MvPolynomial.finSuccEquiv` reads a three-variable polynomial as a polynomial in its
*head* variable, so the derivative variable is first moved to the head by `rename derivHead` with
`derivHead = ![1,2,0]` (injective by `decide`). Then `MvPolynomial.eval_eq_eval_mv_eval'` converts the
evaluation into `Polynomial.eval` of the mapped polynomial, `Polynomial.eval_eq_sum_range'` expands it
over `range (e+1)` — using `natDegree_map_le`, since specialising the coefficients can only drop the
degree — and `Polynomial.coeff_map` identifies the terms. The top coefficient is nonzero because it is
`p.leadingCoeff` and `finSuccEquiv` is an injective algebra map.

`exists_cascade_edge_relation` composes this with the existing `cascade_relation_cleared`: at any point
where `F_k'` does not vanish,

`∑_{c ≤ e} B_c(F_k, F_{k+1}) (F_{k+1}')^c (F_k')^{e−c} = 0`.

One edge of the cascade, with the constituent eliminated — only the two states and their first
derivatives remain. Unconditional; `e ≥ 1` and `B_e ≠ 0` are carried through.

What this leaves for `hup`: the top coefficient is nonzero *as a polynomial*, and the remaining step
is that `B_e(F_k, F_{k+1})` does not vanish *identically as a function* — which is exactly the
algebraic independence of consecutive states, the card's Clunie–Steinmetz input. That, plus a
transcendence-degree count on the field generated by the states, is the whole of the upper bound; the
abstract half already exists as `exists_scalarDifferentialRelation_of_trdeg_le`.

### `HTGeometry/AnalyticJetOrderBridge.lean` — the backward jet bridge, with the order kept

A corpus re-audit found the carrier for the upper bound already fully built, and under names the
earlier passes had not searched: `Bottcher.analyticSubring U` / `meroField U` (the meromorphic
function field of a connected open set), `meroFieldDifferential`, `analyticMeroElement`,
`differentialJet_analyticMeroElement` (the algebraic jets *are* the ordinary derivative germs), and
the two-way `differentialAlgebraicOver_analyticMeroElement_iff` in `AnalyticJetFieldBridge.lean`.
Nothing of that needed rebuilding.

What was missing is order control. The existing backward direction extracts *some* jet index from an
existential (`exists_jet_relation_of_differentialAlgebraicOver`) and therefore yields
`DifferentiallyAlgebraic`, not `DifferentiallyAlgebraicOfOrder n`. The composition law needs the
index supplied, not extracted:

`exists_relation_of_jet_relation` — a nonzero `Q : MvPolynomial (Fin (n+1)) (RatFunc ℂ)` annihilating
the first `n+1` jets of `analyticMeroElement f` descends to a nonzero
`P : MvPolynomial (Fin (n+2)) ℂ` vanishing pointwise on `U`. Same denominator clearing
(`clearRatFuncCoefficients`), same inverse reshaping (`reshapeJetInv`), same `IsFractionRing`
injectivity — only the arity is now fixed by the relation.

`differentiallyAlgebraicOfOrder_of_jet_relation` specialises to `U = univ` and lands exactly on the
corpus's `DifferentiallyAlgebraicOfOrder f n`.

This is the missing conversion between the card's two halves: `exists_scalarDifferentialRelation_of_trdeg_le`
produces a low-order relation in an abstract differential field, and this bridge turns such a relation
in `meroField univ` into the concrete order bound. What remains for `hup` is the transcendence-degree
computation itself — that the state field `ℂ(z)(F_1,…,F_n)` has all jets of `F_n` algebraic over it,
which needs the edge relation's top coefficient to be nonzero *as a function*, i.e. state algebraic
independence.

### The upper-bound chain, three more links

**`HTGeometry/EntireOrderFromStateField.lean`.** `differentiallyAlgebraicOfOrder_of_trdeg_le`: an
entire `f` whose first `n+1` derivative germs lie in an intermediate field `M` of
`meroField univ` with `Algebra.trdeg (RatFunc ℂ) M ≤ n` satisfies an algebraic differential equation
of order at most `n`. This is the card's gate "Lean: the matching upper bound `ord_DA ≤ n` from a
bounded-transcendence state field" — now on *functions*, not only in an abstract differential field.
Supporting: `exists_jet_relation_of_trdeg_le`, the `MvPolynomial (Fin (n+1)) K` form of the abstract
dependence (the existing `exists_scalarDifferentialRelation_of_trdeg_le` renames into
`DifferentialPolynomial Unit K`, which the bridge cannot consume).

**`HTGeometry/PolynomialTotalDerivative.lean`.** `deriv_eval`:

`(p(y))′ = (coeffDeriv p)(y) + p'(y) · y′`

for `p` over any differential ring. The corpus had two chain rules already
(`PolarShiftClassification.deriv_aeval`, `OrbitIsolatedPoleLaw.deriv_aeval_dirCoordMero`) and *both*
assume the coefficients are differential constants — exactly the case that is useless when the
coefficients live in a moving state field. `coeffDeriv` is additive but not multiplicative, so it is
built from `Polynomial.sum` (giving `sum_add_index`/`sum_monomial_index` additivity for free) rather
than `Polynomial.map`; `coeffDeriv_coeff` then reads off `(coeffDeriv p).coeff j = (p.coeff j)′`.

**`HTGeometry/AlgebraicClosureDerivationClosed.lean`.** `deriv_mem_algebraicClosure`: if every
derivative of an element of `E` is algebraic over `E`, the relative algebraic closure
`algebraicClosure E L` is closed under the derivation. Differentiating the minimal polynomial gives
`(coeffDeriv P)(y) + P'(y)·y′ = 0`, and `P'(y) ≠ 0` by minimality plus `derivative p ≠ 0` in
characteristic zero — so `y′ = −A/B` with both in the closure.

The hypothesis is deliberately *not* "E is derivation-closed": the state field of a composition is
generated by elements whose derivatives are only algebraic over it, never inside it. That is the
whole reason the closure has to be taken before the derivation can be absorbed.

Remaining for `hup`: assemble these — `E := ℂ(z)(F_1,…,F_n)`, `M := algebraicClosure E L`, trdeg `≤ n`
by `trdeg_add_eq` plus `trdeg_eq_zero` for the algebraic step, `M` derivation-closed by the lemma
above once the edge relation gives `F_k' ∈ M` (which is where state algebraic independence enters).

### `HTGeometry/StateFieldTrdeg.lean` + `EntireCascadeStateFieldOrder.lean` — the upper bound, assembled

`differentiallyAlgebraicOfOrder_of_state_generators`: an entire `f` whose meromorphic realization
lies in the field generated over `ℂ(z)` by `n` states, and such that the derivative of every element
of that field is *algebraic over* it, satisfies an algebraic differential equation of order at
most `n`. Unconditional, axiom-clean.

The three links:

- `trdeg_intermediateFieldAdjoin_range_le` — a generated field has transcendence degree at most the
  number of generators. Built from the corpus's own `isAlgebraic_adjoin_of_intermediate_adjoin_eq_top`
  and `adjoin_range_lift_eq_top`, which already carry the `adjoin_induction` bookkeeping; only the
  `≤` direction was missing (the corpus had the exact `=` version under an algebraic-independence
  hypothesis).
- `trdeg_algebraicClosure_restrictScalars_eq` — passing to the relative algebraic closure changes
  nothing: `trdeg_add_eq` plus `trdeg_eq_zero` on the algebraic step. The instance plumbing works
  because `↥((algebraicClosure E L).restrictScalars K)` is definitionally `↥(algebraicClosure E L)`,
  so `inferInstanceAs` transports the `E`-algebra structure and `IsScalarTower` is `rfl`.
- `differentialJet_mem_algebraicClosure_restrictScalars` — every jet stays inside, by induction on
  the previous session's `deriv_mem_algebraicClosure`.

The hypothesis shape is the point. It is *not* "the state field is derivation-closed" — that is false
for a cascade, whose states have derivatives only algebraic over them. It is "every derivative is
algebraic over the state field", which is precisely what the edge relation delivers, and the closure
is taken once, at the end, where it costs no transcendence degree.

What remains for `hup` is now purely the cascade-specific input: exhibit the `n` states as generators
in `meroField univ` and check the algebraicity hypothesis from `exists_cascade_edge_relation` — whose
top coefficient is nonzero as a polynomial, and needs to be nonzero as a function, i.e. state
algebraic independence.

### The upper bound in usable form: only the generators need checking

`differentiallyAlgebraicOfOrder_of_algebraic_state_derivatives`: an entire `f` whose meromorphic
realization lies in the field generated over `ℂ(z)` by `n` states, **each of whose derivatives is
algebraic over that field**, satisfies an algebraic differential equation of order at most `n`.
Unconditional, axiom-clean.

The previous form quantified over every element of the state field, which no cascade argument can
supply. `deriv_mem_algebraicClosure_adjoin_of_generators` reduces it to the generators by
`IntermediateField.adjoin_induction`: sums and products keep the derivative in the closure because
the field itself sits inside its own closure, and the inverse case is free —
`Derivation.leibniz_inv` reads `D a⁻¹ = -a⁻¹² • D a` with *no* nonvanishing hypothesis, both sides
being zero at `a = 0`.

The base case is discharged, not assumed: `deriv_algebraMap_mem_algebraicClosure_adjoin` needs only
`DifferentialAlgebra K L`, and for `ℂ(z) ⊆ meroField univ` the corpus already owns that instance —
`meroFieldRatFuncDifferentialAlgebra` in `LocalAnalyticExponentialClock.lean`, resting on
`meroField_deriv_ratfuncToMero`. So the rational coefficients cost nothing.

Net effect: the upper bound `ord_DA(F_n) ≤ n` is now reduced to exactly `n` checks, one per state —
"`F_k'` is algebraic over `ℂ(z)(F_1,…,F_n)`" — which is what the edge relation of
`CascadeEdgeRelation.lean` produces once its top coefficient is known to be nonzero as a function.

### The edge relation without division, and the polynomial transfer

**`CascadeEdgeRelation.lean` (extended).** `exists_cascade_edge_relation_of_forall` — the cleared edge
relation holds at **every** point, not merely where `F_k'` does not vanish:

`∑_{c ≤ e} B_c(F_k, F_{k+1}) (F_{k+1}')^c (F_k')^{e−c} = 0`   for all `z`.

The nonvanishing hypothesis in the existing `cascade_relation_cleared` turns out to be unnecessary.
By the chain rule `F_{k+1}' = f_k'(F_k)·F_k'`, so the `c`-th term equals
`B_c · (f_k'(F_k))^c · (F_k')^e` *identically* — the same factor `(F_k')^e` for every `c` — and the
sum factors as `(F_k')^e · 0`. The division was only apparent; `sum_mul_pow_chain` isolates the
homogenisation step. This removes the "off a discrete set" caveat from the whole edge layer, and with
it any need for an identity-theorem argument when passing to germs.

**`AnalyticMeroPolynomialEval.lean`.** `analyticMeroElement_eval_mvPolynomial`: evaluating a
polynomial at analytic functions pointwise and then passing to germs equals passing to germs first,

`analyticMeroElement (z ↦ P(g₁ z, …, g_m z)) = eval₂ (constToMero U) (analyticMeroElement ∘ g) P`,

together with `eval₂_constToMero_mem`: such an expression lies in any intermediate field containing
the `g_i`'s germs. Constants are handled by `ratfuncToMero_C_eq_constToMero` — the constant embedding
factors through `ℂ(z)`, so constants cost nothing.

Stated with explicit ring homomorphisms (`constToMero`, `eval₂`) rather than an `Algebra ℂ` instance,
so no scalar-tower diamond arises against the `RatFunc ℂ` structure already on `meroField`.
`analyticMeroElement_congr` is what makes the induction go through: the realization depends on the
*function*, and the analyticity proof is a `Prop`, so rewriting the function is free.

Together these say: the field-level edge relation has coefficients visibly inside `ℂ(z)(states)`, and
holds unconditionally. What is left is the top coefficient's nonvanishing as a field element.

### Roots stay in the closure; sums transfer

**`AlgebraicClosureDerivationClosed.lean` (extended).**

- `mem_algebraicClosure_of_isAlgebraic` — an element algebraic *over* `algebraicClosure E L` already
  lies in it. This is `isIntegral_trans` plus `mem_algebraicClosure_iff'`; mathlib states the fact
  only as `algebraicClosure.algebraicClosure_eq_bot`, which is the same content in a form that cannot
  be applied to an element.
- `mem_algebraicClosure_of_root` — if `∑_{c ≤ e} A_c y^c = 0` with every `A_c` in the closure and
  `A_e ≠ 0`, then `y` is in the closure. The polynomial is assembled explicitly as
  `∑ C ⟨A_c, _⟩ * X^c` over the closure, its `e`-th coefficient read off by `finsetSum_coeff` and
  `coeff_X_pow`; nonzero because that coefficient is `A_e`.

This is the exact shape the edge relation produces, so no separate "algebraic over an intermediate
ring" bookkeeping is needed.

**`AnalyticMeroPolynomialEval.lean` (extended).** `analyticMeroElement_finsetSum` and
`analyticMeroElement_zero` — a finite sum of analytic functions is realized by the sum of germs. Lean
note: `Finset.sum_induction` produces the *Pi-form* `∑ i ∈ t, g i`, not the lambda form
`fun z => ∑ i ∈ t, g i z`, so an explicit `Finset.sum_apply` bridge is needed before it can discharge
an `AnalyticOnNhd` goal — the same Pi-versus-lambda trap that has now appeared five times in this
card.

With these, the pointwise edge relation transfers term by term into `meroField univ`: sums by
`analyticMeroElement_finsetSum`, products and powers by `_mul`/`_pow`, coefficients by
`analyticMeroElement_eval_mvPolynomial`, and the conclusion `F_{k+1}' ∈ algebraicClosure E L` by
`mem_algebraicClosure_of_root`.

### `HTGeometry/CascadeMeroField.lean` — the cascade inside the field, and a repaired name collision

`cascadeMero`, `cascadeMeroDeriv` — the states and their derivatives as elements of
`meroField univ`. `analyticMeroElement_sum_eq_zero` — a pointwise vanishing finite sum of analytic
functions vanishes in the field. `analyticMeroElement_edgeCoeff` — the edge coefficient
`z ↦ B_c(F_k z, F_{k+1} z)` is realized by `eval₂ (constToMero) ![X_k, X_{k+1}] (B c)`, i.e. visibly
inside the state field.

**Collision found and repaired.** Importing the cascade cone and the meromorphic-field cone into one
module failed outright:

```
import ... CascadeExpression failed, environment already contains
'GaloisForLFunctions.HTGeometry.analyticOnNhd_iteratedDeriv' from ...UpperEndPrimeLogJets
```

Two different theorems shared one name — `UpperEndPrimeLogJets` proves it for `iteratedDeriv n f` on
an arbitrary `U` (fourteen call sites across HTGeometry and Hurwitz), `CascadeExpression` proves it
for `deriv^[d] g` on `Set.univ` (two call sites, both local). Since the umbrella imports both, the
umbrella could not have compiled since `CascadeExpression` was added. Renamed the cascade one to
`analyticOnNhd_iterate_deriv`, matching what it actually states; the general name keeps its meaning
and all its users.

Worth recording as method: a duplicate top-level name is invisible to every module that imports only
one of the two cones, and only surfaces the first time something needs both. The umbrella is not a
guard against this — it is where the breakage lands.

### The edge relation reaches the field

`exists_cascade_edge_relation_mero` — for a transcendental entire constituent with a first-order
equation, in `meroField univ`:

`∑_{c ≤ e} eval₂ (constToMero) ![X_k, X_{k+1}] (B c) · (D_{k+1})^c · (D_k)^{e−c} = 0`,  `e ≥ 1`, `B_e ≠ 0`,

with `X_j = cascadeMero j` the state germs and `D_j = cascadeMeroDeriv j` their derivative germs.
Unconditional, axiom-clean.

Every coefficient is now *visibly* an `eval₂ (constToMero) ![X_k, X_{k+1}]`, hence lands in any
intermediate field containing the two states (`eval₂_constToMero_mem`). The transfer is term by term:
`analyticMeroElement_edgeTerm` does one term with two `_mul`s and two `_pow`s, and
`analyticMeroElement_sum_eq_zero` closes the sum. No analytic continuation anywhere — the pointwise
identity of entire functions is already an identity of germs, which is exactly why removing the
`F_k' ≠ 0` hypothesis earlier mattered.

Remaining for `hup`: read the relation as a polynomial in `D_{k+1}` and apply
`mem_algebraicClosure_of_root`. Its coefficients are `A_c · D_k^{e−c}`, all in the closure once
`D_k` is (induction on `k`, base `D_0 = 1`), and the top one is `A_e = eval₂ … (B e)` — nonzero
exactly when the states are algebraically independent, the card's Clunie–Steinmetz input.

### `HTGeometry/CascadeStateAlgebraic.lean` — the derivative step, and the exact analytic input

`cascadeMeroDeriv_succ_mem_algebraicClosure`: with the two consecutive states in `E`, the previous
derivative in `algebraicClosure E L`, and the pair of states algebraically independent over the
constants, the next derivative lies in `algebraicClosure E L`. Unconditional, axiom-clean.

`PairAlgIndep X Y := ∀ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 → eval₂ (constToMero) ![X, Y] P ≠ 0`

is the *entire* remaining analytic content of the upper bound, and it is now isolated in one
definition. It is Clunie–Steinmetz stated in the field: consecutive cascade states satisfy no
polynomial relation over ℂ.

`mem_algebraicClosure_of_edge_relation` does the algebra: with
`A_c := eval₂ … (B c) · T^{e−c}`, the relation is `∑ A_c D^c = 0`, each `A_c` is in the closure
(coefficients by `eval₂_constToMero_mem` and `E ⊆ closure`, the power of `T` by `pow_mem`), and
`A_e = eval₂ … (B e)` because `T^{e−e} = 1`. Then `mem_algebraicClosure_of_root` applies. Note the
top coefficient is exactly the *polynomial* top coefficient — the `T`-power that obstructs at every
lower index disappears at `c = e`, which is why homogenising by `(F_k')^{e−c}` rather than by a
uniform power was the right normalisation back in the clearing step.

`cascadeMeroDeriv_zero : cascadeMeroDeriv hfan 0 = 1` supplies the induction base — the zeroth state
is the identity, its derivative the constant `1`, and `analyticMeroElement_const` sends it to `1`.

### `HTGeometry/CascadeUpperBound.lean` — `hup` is closed

```
differentiallyAlgebraicOfOrder_entireCascade :
  (∀ i, AnalyticOnNhd ℂ (f i) univ) →
  (∀ k < n, TranscendentalEntire (f k)) →
  (∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
  (∀ k < n, PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k+1))) →
  DifferentiallyAlgebraicOfOrder (entireCascade f n) n
```

Unconditional, axiom-clean (`propext, Classical.choice, Quot.sound`). This is the card's `ord_DA ≤ n`
for the actual composition of actual entire functions — the first half of the unit-cost law, and the
obligation `hup` of `exactDifferentialOrder_of_cascade`.

The assembly:

- `cascadeMero_zero` — the zeroth state *is* the coordinate: `F_0 = id`, whose germ is
  `algebraMap (RatFunc ℂ) _ RatFunc.X`. So it is in the base field and needs no generator. This is
  why `n` states suffice for a length-`n` cascade rather than `n+1`.
- `cascadeStates hfan n : Fin n → meroField univ`, `i ↦ X_{i+1}`; `cascadeMero_mem_adjoin` puts every
  `X_j` with `j ≤ n` in the generated field (`j = 0` by the previous point, `j ≥ 1` as a generator).
- `cascadeMeroDeriv_mem_algebraicClosure` — induction on `j`, base `D_0 = 1`, step
  `cascadeMeroDeriv_succ_mem_algebraicClosure`.
- `differentialJet_one_cascadeMero` converts the abstract jet `y′` into the concrete derivative germ,
  which is what the generator hypothesis of `differentiallyAlgebraicOfOrder_of_algebraic_state_derivatives`
  consumes.

Lean note: `congr 1` on a `Fin`-indexed family leaves `j = ↑⟨j-1, _⟩ + 1`, and `omega` cannot see
through the `Fin.val` of an anonymous constructor — it treats it as an opaque atom. Use `show` to
force the reduction to `j - 1 + 1` before rewriting.

**Status of the card's two obligations.** `hup` — done, above. `helim` — the remaining one: a low-order
equation must yield a nonzero `statePoly` relation among the states. The analytic input for the whole
upper bound is now the single predicate `PairAlgIndep`, i.e. Clunie–Steinmetz for consecutive states.

### `HTGeometry/CascadeExactOrder.lean` — the unit-cost law, both halves

```
exactDifferentialOrder_entireCascade :
  (∀ i, AnalyticOnNhd ℂ (f i) univ) →
  (∀ k < n, TranscendentalEntire (f k)) →
  (∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
  (∀ k < n, PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k+1))) →
  AlgebraicIndependent (RatFunc ℂ) (fun j : Fin n => differentialJet j (cascadeMero hfan n)) →
  ExactDifferentialOrder (entireCascade f n) n
```

Unconditional, axiom-clean. `ord_DA(f_n ∘ … ∘ f_1) = n` for actual entire functions, with the two
analytic inputs of the paper isolated as the last two hypotheses.

The lower half needed the *forward* order bridge, added to `AnalyticJetOrderBridge.lean`:
`exists_jet_relation_of_relation` — a pointwise equation of order ≤ n gives a nonzero
`Q : MvPolynomial (Fin (n+1)) (RatFunc ℂ)` annihilating the first `n+1` jets. The corpus's existing
forward direction discards `Q` immediately to state `DifferentialAlgebraicOver`, so the order is lost;
keeping `Q` is all that was missing. Then
`not_differentiallyAlgebraicOfOrder_of_algebraicIndependent_jets` is `algebraicIndependent_iff` applied
to that `Q`.

`not_differentiallyAlgebraicOfOrder_entireCascade_of_jets` covers every `m < n` from a single
hypothesis by restricting the independent family along `Fin.castLE`, which is injective — one
independence statement about `n` jets, not `n` separate ones.

**Both obligations of `exactDifferentialOrder_of_cascade` are now discharged on the analytic
objects**, by a different route than that theorem's `PolyIndependent`/`helim` interface: the
transcendence-degree count replaces `helim` entirely, and `PolyIndependent` is replaced by the two
field-level independence statements, which is where Reduction I–III's analytic work now attaches.

### The first edge is free, and the jet hypothesis is exactly the lower bound

`pairAlgIndep_zero` — `PairAlgIndep (cascadeMero 0) (cascadeMero 1)` holds for *every* transcendental
entire `f_0`, with no extra hypothesis. The zeroth state is the coordinate, so the pair's independence
says precisely that `f_0` is not algebraic over `ℂ[z]` — which is the order-zero theorem proved
earlier in this card. So the Clunie–Steinmetz input is needed only from the *second* edge on; the
first is a theorem. Supporting: `analyticMeroElement_eq_zero_iff`, faithfulness of the realization
(`IsFractionRing.injective` plus `Germ.coe_eq` on a principal filter — no identity theorem, since
germs along `𝓟 U` are functions up to equality on `U`).

`algebraicIndependent_jets_iff` — the first `n+1` jets are independent over `ℂ(z)` **iff** no algebraic
differential equation of order at most `n` holds. Both directions are now available (forward and
backward order bridges), so this is an equivalence, not a sufficient condition.

That settles what the remaining hypothesis of the capstone *is*: `hjets` is not a convenient
sufficient condition that might be weakened — it is a restatement of the lower bound itself. Any
further progress on `ord_DA ≥ n` must come from the analytic side (Reductions I–III), not from
rearranging the algebra. Conversely `PairAlgIndep` at edges `k ≥ 1` is a genuinely weaker, purely
two-variable statement, and is the one place where a partial result would buy something.

### The Clunie–Steinmetz input is not needed for the upper bound — it is a theorem

`pairAlgIndep_of_transcendental` : for **every** `k`, consecutive states of a cascade of
transcendental entire constituents are algebraically independent over the constants. Unconditional,
axiom-clean.

The argument is short and does not use Clunie–Steinmetz at all. A relation `P(F_k, F_{k+1}) = 0`
with `F_{k+1} = f_k ∘ F_k` says the entire function `G(w) := P(w, f_k(w))` vanishes on `range F_k`.
The state `F_k` is a nonconstant entire function (`exists_ne_entireCascade`, plus a constant function
is a polynomial so a transcendental entire function is nonconstant), hence an open map, so `range F_k`
contains a nonempty open set; the identity theorem then gives `G ≡ 0`, i.e. `P(w, f_k(w)) = 0` for
every `w` — an order-zero equation for `f_k`, impossible.

This changes the card's accounting. The upper bound now reads

```
differentiallyAlgebraicOfOrder_entireCascade_of_transcendental :
  (∀ i, AnalyticOnNhd ℂ (f i) univ) → (∀ i, TranscendentalEntire (f i)) →
  (∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
  DifferentiallyAlgebraicOfOrder (entireCascade f n) n
```

with **no independence hypothesis whatsoever** — exactly the hypotheses of the paper's statement.
`ord_DA(f_n ∘ … ∘ f_1) ≤ n` is therefore fully proved, unconditionally, in Lean.

Correspondingly `exactDifferentialOrder_entireCascade_of_transcendental` carries a single remaining
hypothesis, `hjets`, and by `algebraicIndependent_jets_iff` that hypothesis *is* the lower bound
`ord_DA ≥ n`. So the card's Lean state is now sharp: the upper half is closed outright, and the lower
half is isolated in one equivalent statement with no algebraic slack left in it.

Method note: the earlier reading — that the top coefficient's nonvanishing needs Clunie–Steinmetz —
was over-cautious. What is needed is only nonvanishing of a *two-variable* polynomial on the graph of
`f_k` over the image of `F_k`, and an open image plus the identity theorem reduces that to the
constituent's own transcendence. Full state independence over `ℂ(z)` is a strictly stronger statement,
and it is needed only for the lower bound.

### Non-vacuity of the capstone: the length-one law is hypothesis-free

`exactDifferentialOrder_entireCascade_one` — for a cascade of length one there is **no** residual
hypothesis: `hjets` at `n = 1` is `AlgebraicIndependent (RatFunc ℂ)` of a single jet, which by
`algebraicIndependent_jets_iff` at `n = 0` is exactly `¬ DifferentiallyAlgebraicOfOrder (f 0) 0` — the
order-zero theorem. So transcendence plus a first-order equation already gives exact order one through
the full field-theoretic route, not only through the earlier direct argument.

`exactDifferentialOrder_expCascade_one : ExactDifferentialOrder (entireCascade (fun _ => Complex.exp) 1) 1`
instantiates it, so the whole chain — edge relation, transfer to `meroField`, algebraic closure,
transcendence-degree count, both order bridges — is exercised on a concrete object and is not vacuous.

Lean note: `rw` could not fire `algebraicIndependent_jets_iff` here because the goal carries `Fin 1`
and `cascadeMero hfan 1` while the lemma produces `Fin (0+1)` and `analyticMeroElement …`, and the
algebra instance appears as the module's `local instance` rather than the lemma's inlined `letI`. All
four differences are definitional, so `exact (…).mpr …` succeeds where `rw` fails — the usual rule
that `rw` needs syntactic agreement and `exact` needs only defeq, but here it is the *instance* term
that differs, which is easy to misread as a real mismatch.

### The lower bound: route fixed, and the first brick

With the upper half closed, the only open statement is `hjets`, equivalently
`¬ DifferentiallyAlgebraicOfOrder F_n (n−1)`. The route that the new machinery makes available, for
`n = 2` and then by induction:

1. A relation `R(z, F_2, F_2') = 0` plus `F_1` algebraic over `ℂ(z)(F_2, F_2')` would force
   `trdeg_{ℂ(z)} ℂ(z)(F_1,F_2) ≤ 1`.
2. So it suffices to prove `F_1, F_2` algebraically independent **over `ℂ(z)`** — strictly stronger
   than the `PairAlgIndep` now proved, which is independence over the constants only.
3. Reading a relation `∑_c A_c(z, F_1) F_2^c = 0` in its top variable, the largest `c` with
   `A_c ≠ 0` is `≥ 1` (else `F_1` is algebraic over `ℂ(z)`, impossible), so `F_2 = f_1 ∘ F_1` would be
   *algebraic over* `ℂ(z, F_1)` of degree `D`.
4. That contradicts composition growth: an algebraic element of degree `D` over `ℂ(z, F_1)` has
   characteristic `O(D·(T(r,F_1) + log r))`, while Pólya/Clunie give
   `T(r, f_1 ∘ F_1)/T(r, F_1) → ∞`. The corpus already owns the growth side
   (`PolyaCompositionGrowth`, `EntireMinimumModulusAt`, the Nevanlinna layer).

So the missing analytic content is *one* comparison: an element algebraic over `ℂ(z, F_1)` cannot
outgrow `F_1`. Note this is weaker than the card's Reduction I–III programme — no Wiman place, no
Newton–Puiseux — because the upper bound no longer needs them.

**First brick: `MvPolynomialGrowthBound.lean`.**
`norm_eval_le_mvCoeffNormSum : ‖P(z,w)‖ ≤ mvCoeffNormSum P · (1+‖z‖)^{totalDegree} · (1+‖w‖)^{totalDegree}`,
the two-variable analogue of `norm_eval_le_coeffNormSum`. This is the numerator half of step 4: the
coefficients `A_k(z, F_1(z))` of the algebraic relation grow at most like a power of
`(1 + M(r, F_1))`. Supporting `exponent_le_totalDegree` — each single exponent is at most the total
degree, via `MvPolynomial.le_totalDegree` and `Finset.single_le_sum`, with the off-support case
handled separately since `Finset.single_le_sum` needs membership.

The denominator half is the open point: a lower bound for `‖A_D(z, F_1(z))‖`, i.e. a minimum-modulus
estimate for a nonzero entire function — which is exactly what the corpus's Borel–Carathéodory /
`EntireMinimumModulusAt` layer was built for.

### `HTGeometry/AlgebraicProximityBound.lean` — an algebraic element cannot outgrow its coefficients

`proximity_le_of_root`: for meromorphic `g` and `a_0..a_n` with `∑_{i ≤ n} a_i g^i = 0` and `a_n`
nonvanishing on the circle of radius `|r|`,

`m(r, g) ≤ log n + ∑_{i < n} m(r, a_i / a_n)`.

Unconditional, axiom-clean. This is the value-distribution half of the lower-bound route: it is the
precise sense in which "algebraic over a field does not outgrow the field".

Two steps. `posLog_norm_le_of_root_sum` upgrades the corpus's pointwise root estimate
`posLog_norm_le_of_root` (which bounds by `log⁺` of a *sum*) into a bound by a *sum of* `log⁺`s, via
mathlib's `Real.posLog_sum` — the `log n` is the price of that exchange. Then `circleAverage_mono`
with `MeromorphicOn.circleIntegrable_posLog_norm` on both sides averages it, and `circleAverage_sum`
/`circleAverage_add`/`circleAverage_const` split the right side into proximities.

The nonvanishing hypothesis is on one circle only, which is the honest form: the top coefficient of a
relation among entire functions has isolated zeros, so all but countably many radii qualify. Upgrading
to "for almost every `r`" is a separate a.e. step and is not needed to run the growth comparison,
which only ever needs a sequence of admissible radii tending to infinity.

Combined with `norm_eval_le_mvCoeffNormSum` from the previous entry, the two sides of the intended
contradiction are now in place in the same currency: the coefficients `A_k(z, F_1)` have proximity
`O(deg · (m(r,F_1) + log r))`, while composition growth must make `m(r, f_1 ∘ F_1)/m(r, F_1) → ∞`.
What remains is that last composition-growth statement (Clunie's theorem in characteristic form); the
corpus's `PolyaCompositionGrowth` gives it in maximum-modulus form, and the conversion is the
`log M` versus `T` comparison, for which the corpus's Borel radius-selection lemmas
(`borel_growth`, `exists_ge_lt_two_mul`) are the intended tool.

### The proximity bound in coefficient form

`proximity_le_of_root_coeff`:

`m(r, g) ≤ log n + ∑_{i < n} ( m(r, a_i) + m(r, 1/a_n) )`

Unconditional, axiom-clean. Splitting `a_i/a_n = a_i · a_n⁻¹` by mathlib's `proximity_mul_top_le`
and rewriting `m(r, a_n⁻¹)` as `m(r, a_n; 0)` by `proximity_inv` puts the estimate entirely in terms
of the coefficients of the relation, with the reciprocal appearing only as a proximity *to zero* — the
quantity the first main theorem controls by `T(r, a_n)`.

Lean note: `add_le_add_left` stalls here with "typeclass instance problem is stuck / `AddLeftMono ?m`",
because the summand's type is still a metavariable when the instance is sought. Proving the sum
inequality as a standalone `have` and closing with `linarith` sidesteps it entirely — worth preferring
whenever the congruence step sits under an unelaborated `∑`.

### The algebraic bound in characteristic form

`proximity_le_of_root_characteristic`: for `1 ≤ r`,

`m(r, g) ≤ log n + ∑_{i < n} ( T(r, a_i) + T(r, a_n; 0) )`.

Unconditional, axiom-clean. Supporting `proximity_le_characteristic` — `m ≤ T` on `[1,∞)`, which is
just `characteristic = proximity + logCounting` together with `logCounting_nonneg`, but is not stated
in mathlib in applied form.

This is the layer's terminus in the direction "algebraic ⇒ slow": everything on the right is a
characteristic of a coefficient of the relation, and for coefficients of the form `A_k(z, F_1)` those
are `O(deg · (T(r,F_1) + log r))` by the two-variable growth bound. The remaining gap to a lower-bound
proof is one inequality in the opposite direction — composition growth
`T(r, f_1 ∘ F_1)/T(r, F_1) → ∞` — plus the first main theorem to convert `T(r, a_n; 0)` into
`T(r, a_n; ⊤)` (mathlib's `characteristic_sub_characteristic_inv_le`).

### The two-variable bound in logarithmic form

`posLog_norm_eval_le`:

`log⁺‖A(z,w)‖ ≤ log⁺(mvCoeffNormSum A) + deg·(log 2 + log⁺‖z‖) + deg·(log 2 + log⁺‖w‖)`

Unconditional, axiom-clean. This is the shape a proximity estimate consumes — averaging it over a
circle turns the two-variable growth bound directly into

`m(r, A(·, F_1)) ≤ C_A + deg·(log 2 + log r) + deg·(log 2 + m(r, F_1))`,

which is exactly the coefficient input required by `proximity_le_of_root_characteristic`. Every step is
a mathlib `posLog` identity: `posLog_mul` twice for the product, `posLog_pow` (an *equality*,
unconditional in `x`) for the degree, and `posLog_add` with `posLog_one` for `1 + t`.

Lean note: `Real.posLog` was reported as an unknown constant even though `Real.posLog_mul` resolved in
a scratch file — the module's import cone lacked
`Mathlib.Analysis.SpecialFunctions.Log.PosLog`. Same narrow-cone trap as earlier in this card; the
misleading part is that the *error* names the definition, not the missing lemma file.

### The coefficient side, in proximity form

`proximity_eval_mvPolynomial_le`: for meromorphic `f` and a two-variable polynomial `A`,

`m(r, A(·, f)) ≤ ( log⁺(mvCoeffNormSum A) + deg·(log 2 + log⁺|r|) + deg·log 2 ) + deg · m(r, f)`.

Unconditional, axiom-clean. With `meromorphic_eval_mvPolynomial` (such a composite is meromorphic,
by the same three-case induction as its analytic counterpart) this closes the coefficient side: the
coefficients `A_k(z, F_1)` of an algebraic relation have proximity `O(deg · m(r, F_1) + deg · log r)`.

Both halves of the comparison are now formal:

* `proximity_le_of_root_characteristic` — the root is bounded by its coefficients;
* `proximity_eval_mvPolynomial_le` — those coefficients are bounded by `deg · m(r, F_1)`.

so an element algebraic over `ℂ(z, F_1)` has `m(r, ·) = O(m(r, F_1) + log r)`. The lower bound now
needs exactly one further input, in the opposite direction: `m(r, f_1 ∘ F_1)/m(r, F_1) → ∞`.

Lean notes. (i) Constant multiples of a circle-integrable function have no `CircleIntegrable.const_mul`
in mathlib; writing `d · g` as `∑_{j<d} g` sidesteps it entirely and reuses `CircleIntegrable.sum` and
`circleAverage_sum`. (ii) `Pi.mul_apply` must be kept *out* of the simp set here — it rewrites
`(↑d * g) x` into `↑d x * g x`, treating the numeral cast as a function; extracting the pointwise
value with an explicit `have … = K + d * log⁺‖f x‖` is the safe form. (iii) `mul_add` needs its `c`
argument given explicitly, since two subterms of the goal match its pattern.

### Everything at infinity: the first main theorem applied

`proximity_le_of_root_characteristic_top`: for `1 ≤ r`,

`m(r, g) ≤ log n + ∑_{i<n} ( T(r, a_i) + T(r, a_n) + C_n )`,

`C_n = max |log‖a_n(0)‖| |log‖trailingCoeff(a_n)(0)‖|`, unconditional and axiom-clean.

The reciprocal is gone: mathlib's `characteristic_sub_characteristic_inv_le` (the quantitative first
main theorem) trades `T(r, a_n⁻¹)` for `T(r, a_n)` at the price of that explicit constant, and
`proximity_inv` supplies `m(r, a_n; 0) = m(r, a_n⁻¹; ⊤)` to make the exchange applicable.

The "algebraic ⇒ slow" side of the lower bound is now complete and in a single currency: for a
relation whose coefficients are `A_i(z, F_1)`,

`m(r, g) ≤ n·(deg-weighted) · ( m(r, F_1) + log r ) + O(1)`,

by composing this with `proximity_eval_mvPolynomial_le`. The lower bound reduces to the single
opposite-direction statement `m(r, f_1 ∘ F_1)/m(r, F_1) → ∞`, i.e. Clunie's composition theorem in
characteristic form.

### Entire functions: characteristic equals proximity

`logCounting_top_eq_zero_of_analyticOnNhd` and `characteristic_top_eq_proximity_of_analyticOnNhd` —
for entire `f`, `N(r,f;∞) = 0` and hence `T(r,f) = m(r,f)`. Unconditional, axiom-clean.

Small but load-bearing: the algebraic bound is stated with characteristics on the right and a
proximity on the left, while the composition-growth input will be stated with characteristics on both
sides. This is the conversion, and it applies because every object in the cascade — states,
derivatives, coefficients `A_i(z,F)` — is entire.

Lean note: `AnalyticOnNhd.divisor_nonneg` is declared *inside* `namespace MeromorphicOn`, so its real
name is `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`, and dot notation `hf.divisor_nonneg` fails
outright because `AnalyticOnNhd` unfolds to a Pi type. Same trap as
`MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero` earlier in the corpus: the file's opening
`namespace` silently prefixes a lemma whose own name already carries a different namespace.

### Both sides now speak in characteristics

`characteristic_eval_mvPolynomial_le`:

`T(r, A(·,F)) ≤ ( log⁺(mvCoeffNormSum A) + deg·(log 2 + log⁺|r|) + deg·log 2 ) + deg · T(r, F)`

for entire `F`, unconditional and axiom-clean, with `analyticOnNhd_eval_two` (the composite is
entire) supplying the analyticity that the `T = m` conversion needs on both sides.

The two halves of the "algebraic ⇒ slow" comparison are now stated in the same units and compose
directly:

* `proximity_le_of_root_characteristic_top` — `m(r,g) ≤ log n + ∑_{i<n} (T(r,a_i) + T(r,a_n) + C_n)`;
* `characteristic_eval_mvPolynomial_le` — each `T(r, A_i(·,F)) ≤ K_i + deg_i · T(r,F)`.

Chaining them gives `m(r, g) ≤ c·(1 + log⁺|r| + T(r,F))` for an explicit `c` built from the finitely
many coefficient sizes and degrees. That is the whole "algebraic over `ℂ(z, F)` cannot outgrow `F`"
statement, and the only remaining input to the lower bound is its opposite,
`T(r, f_1 ∘ F)/T(r, F) → ∞`.

### "Algebraic over `ℂ(z,F)` cannot outgrow `F`" — complete

`exists_bound_proximity_of_two_var_relation`:

```
∃ c ≥ 0, ∀ r ≥ 1,  (top coefficient nonvanishing on |z| = r) → (relation holds) →
  m(r, g) ≤ c · ( 1 + log⁺|r| + T(r, F) )
```

for a relation `∑_{i ≤ n} A_i(z, F(z)) · g(z)^i = 0` with `A_i` two-variable complex polynomials and
`F` entire. Unconditional, axiom-clean. The constant is built explicitly from the finitely many
coefficient sizes and total degrees — `K = ∑ (log⁺‖A_i‖₁ + 2·deg_i·log 2)`, `D = ∑ deg_i`, plus the
first-main-theorem constant of the top coefficient — and does not depend on `r`.

This completes the "algebraic ⇒ slow" direction of the lower-bound route, assembled from the four
preceding entries: root estimate → proximity → characteristic → first main theorem, with the
coefficient side supplied by the two-variable growth bound.

The lower bound `ord_DA(F_n) ≥ n` now rests on exactly one unproved input, in the opposite direction:

`T(r, f_1 ∘ F) / T(r, F) → ∞`   (Clunie's composition theorem).

Everything else on that route is formal.

Lean note: `Finset.single_le_sum` needs its `f` given explicitly (`(f := …)`) whenever the summand is
reconstructed from the goal; otherwise the summand stays a metavariable and the `AddLeftMono`
instance search stalls with the same "typeclass instance problem is stuck" message seen earlier for
`add_le_add_left`. Both failures have the same cause and the same fix.

### Bridging the two currencies: `T ≤ log⁺ M`

`characteristic_le_posLog_of_forall_sphere` — for entire `f`, any bound `‖f‖ ≤ M` on the circle of
radius `|r|` gives `T(r, f) ≤ log⁺ M`. Unconditional, axiom-clean. Immediate once
`characteristic = proximity` for entire functions is available, since the proximity is a circle
average and `circleAverage_mono` compares it with the constant.

This is the easy half of the standard comparison `T(r,f) ≤ log⁺M(r,f) ≤ 3·T(2r,f)`, and it is the
half the lower bound consumes: the corpus's composition-growth results (`PolyaCompositionGrowth`,
`exists_le_norm_comp_of_analytic`) are stated in maximum modulus, so a *lower* bound on `M` must be
converted into a lower bound on `T` — which is the direction *not* covered here, and is the reason
Clunie's theorem is stated for `T` in the literature rather than derived from Pólya's `M`-inequality.

Recording the obstruction precisely, since it decides how the remaining work must be organised: for
fast-growing `F_1` no `M`-inequality at shifted radii (`r/2`, `r/4`) can be traded for the `T`-form,
because `log M(r)` may dominate `log M(r/4)` by an arbitrary factor. The radius shift must be absorbed
by a Borel-type selection (`borel_growth`, `exists_ge_lt_two_mul`, both already in the corpus) rather
than by a pointwise comparison. That is the shape of the remaining task.

### The pointwise counterpart: a floor instead of nonvanishing

`posLog_norm_le_of_root_floor`: if `ε ≤ ‖c_n‖` with `ε > 0` and `∑_{i ≤ n} c_i g^i = 0`, then

`log⁺‖g‖ ≤ log n + ∑_{i<n} ( log⁺‖c_i‖ + log⁺ε⁻¹ )`.

Unconditional, axiom-clean.

Reason for the shape. The corpus's composition-growth layer
(`RHTower/PolyaCompositionGrowth.exists_posLog_separation_of_analytic`) is **pointwise**: it produces a
single `z` with `C·log⁺‖g z‖ < log⁺‖f (g z)‖` for a prescribed multiple `C`. To contradict that with
an algebraic relation, the algebraic estimate has to hold at that same, uncontrolled point — so the
top coefficient must be bounded *below* there. A nonvanishing hypothesis is useless pointwise;
a floor is exactly what the corpus's `EntireMinimumModulusAt` layer and
`exists_radius_floor_and_maxTerm` produce.

This means the lower bound has two viable routes, and both are now supplied on the algebraic side:

* **Nevanlinna route** — `exists_bound_proximity_of_two_var_relation`; needs Clunie's theorem in `T`
  form, whose obstruction (the radius shift) was recorded in the previous entry.
* **Pointwise route** — this lemma with `posLog_norm_eval_le` for the coefficients; needs the corpus's
  own `exists_posLog_separation_of_analytic` together with a minimum-modulus floor for
  `A_D(·, F_1)` on the selected circle. No radius-shift problem arises, because the separation and the
  floor are produced on the *same* circle by `exists_radius_floor_maxTerm_block`.

The pointwise route is the better bet: every one of its ingredients already exists in the corpus, and
the `M`-versus-`T` conversion that blocks the other route never appears.

### The pointwise contradictand, assembled

`exists_bound_posLog_of_two_var_relation`:

```
∃ c ≥ 0, ∀ g z ε, 0 < ε → ε ≤ ‖A_D(z, G z)‖ → (∑_{i ≤ D} A_i(z, G z) · g(z)^i = 0) →
  log⁺‖g z‖ ≤ c · ( 1 + log⁺‖z‖ + log⁺‖G z‖ + log⁺ε⁻¹ )
```

Unconditional, axiom-clean; `c` is explicit — `max (log D + D·K + 2·D·Dg·log 2) (D·Dg) D` with
`K = ∑ log⁺‖A_i‖₁` and `Dg = ∑ deg A_i` — and depends only on the coefficient polynomials, not on
`g`, `z` or `ε`.

This is the exact negation-partner of `exists_posLog_separation_of_analytic`, which supplies a point
with `C·log⁺‖G z‖ < log⁺‖f (G z)‖` for any prescribed `C`. Setting `g = f ∘ G` and taking `C > c`
gives the contradiction, provided the point can be chosen so that `log⁺‖z‖` and `log⁺ε⁻¹` stay
`O(log⁺‖G z‖)` — which is what the corpus's combined selection
`exists_radius_floor_maxTerm_block` was built to deliver, on one circle.

The algebraic side of the lower bound is therefore complete on both routes. Everything that remains
is selection: choosing a radius carrying simultaneously a floor for `A_D(·, F_1)`, the Pólya
separation, and control of `log r` against `log⁺‖F_1‖`.

### The lower-bound interface: one hypothesis, entirely analytic

`not_two_var_relation_of_separation`:

```
(∀ c ≥ 0, ∃ z ε, 0 < ε ∧ ε ≤ ‖A_D(z, G z)‖ ∧
    c · (1 + log⁺‖z‖ + log⁺‖G z‖ + log⁺ε⁻¹) < log⁺‖g z‖)
  →  ¬ (∀ z, ∑_{i ≤ D} A_i(z, G z) · g(z)^i = 0)
```

Unconditional, axiom-clean. Two lines, because both sides were already built: the algebraic bound
supplies a `c` valid at *every* point, the hypothesis supplies a point beating that same `c`.

This is the whole remaining content of the lower bound, isolated as one hypothesis and stated in
purely analytic terms — no differential algebra, no field theory, no jets. Discharging it for
`g = f_1 ∘ F_1`, `G = F_1` is a selection problem: find radii carrying simultaneously

1. a minimum-modulus floor `ε` for `A_D(·, F_1)` (corpus: `EntireMinimumModulusAt`,
   `norm_lower_bound_of_anchor`),
2. the Pólya separation `C·log⁺‖F_1 z‖ < log⁺‖f_1 (F_1 z)‖` (corpus:
   `exists_posLog_separation_of_analytic`),
3. `log⁺|z|` and `log⁺ε⁻¹` bounded by a multiple of `log⁺‖F_1 z‖`.

Item 3 is the only genuinely new demand, and it is what the corpus's combined selections
(`exists_radius_floor_and_maxTerm`, `exists_radius_floor_maxTerm_block`) were designed to produce on
one circle.

**Card status.** Upper bound: proved unconditionally, with no independence hypothesis
(`differentiallyAlgebraicOfOrder_entireCascade_of_transcendental`). Lower bound: reduced to the single
analytic selection above; every algebraic and value-distribution step around it is formal and
axiom-clean.

### `HTGeometry/ThreeVarTopRelation.lean` — reading a state relation in its last variable

`exists_top_two_var_relation`: if `F₁` is transcendental entire and `P(z, F₁, F₂) = 0` for a nonzero
`P ∈ ℂ[X₀,X₁,X₂]`, then

`∑_{i ≤ D} A_i(z, F₁) · F₂^i = 0`  with `D ≥ 1` and `A_D ≠ 0` in `ℂ[U,V]`.

Unconditional, axiom-clean. Same mechanism as `exists_deriv_top_relation_of_order_one` — move the last
variable to the head by `rename derivHead` and split it off with `MvPolynomial.finSuccEquiv` — and the
same reason for `D ≥ 1`: degree zero is a two-variable relation `A_0(z, F₁) = 0`, i.e. an order-zero
equation for `F₁`, which its transcendence forbids. The renaming `derivHead = ![1,2,0]` built for the
derivative variable is reused verbatim; nothing about it was specific to derivatives.

This is the entry point of the lower-bound chain from the algebraic side. Composed with
`not_two_var_relation_of_separation`, a state relation over `ℂ` between `F₁` and `F₂` is refuted as
soon as the analytic selection is available for the polynomial `A_D` produced here — and `A_D ≠ 0` is
exactly what makes a minimum-modulus floor for `A_D(·, F₁)` meaningful.

### `HTGeometry/StateIndependenceFromSeparation.lean` — the lower bound has no algebra left

```
GrowthSeparation F₁ F₂ :=
  ∀ A ≠ 0, ∀ c ≥ 0, ∃ z ε, 0 < ε ∧ ε ≤ ‖A(z, F₁ z)‖ ∧
    c · (1 + log⁺‖z‖ + log⁺‖F₁ z‖ + log⁺ε⁻¹) < log⁺‖F₂ z‖

not_three_var_relation_of_growthSeparation :
  TranscendentalEntire F₁ → GrowthSeparation F₁ F₂ →
  ∀ P ≠ 0, ¬ (∀ z, P(z, F₁ z, F₂ z) = 0)
```

Unconditional, axiom-clean; the proof is one line of composition. `GrowthSeparation` is a purely
analytic predicate — moduli, floors and `log⁺` only — and it yields algebraic independence of
`(z, F₁, F₂)` over the constants, which is the state independence the lower bound needs and which the
card had attributed to Clunie–Steinmetz.

The reduction chain, all formal:

```
GrowthSeparation F₁ F₂
  → (exists_top_two_var_relation)          read a state relation in its last variable
  → (not_two_var_relation_of_separation)   contradict the algebraic growth bound
  → (z, F₁, F₂) algebraically independent over ℂ
```

**What the card now needs, in full.** Upper bound: nothing — proved. Lower bound: exactly
`GrowthSeparation F_k F_{k+1}` for each edge, plus the passage from three-variable state independence
to jet independence (`algebraicIndependent_jets_iff`). No differential algebra, no field theory and no
Newton–Puiseux appears anywhere in what remains; the remaining content is one growth statement about a
composition of entire functions, of the kind the corpus's Pólya and minimum-modulus layers already
produce pointwise.

### The growth bound in any number of variables

`norm_eval_le_mvCoeffNormSum_general` and `posLog_norm_eval_le_general`:

`‖P(x)‖ ≤ mvCoeffNormSum P · ∏_i (1 + ‖x_i‖)^{totalDegree}`,
`log⁺‖P(x)‖ ≤ log⁺(mvCoeffNormSum P) + ∑_i deg·(log 2 + log⁺‖x_i‖)`

for `P : MvPolynomial (Fin m) ℂ` and any point. Unconditional, axiom-clean; the two-variable versions
are the case `m = 2`.

Needed because the lower-bound argument at length `n` reads a state relation in its last variable and
leaves coefficients in *all* the earlier states, not just one: the two-variable form suffices only for
`n = 2`. `Real.posLog_prod` (`log⁺∏ ≤ ∑ log⁺`) makes the logarithmic form as short as the two-variable
one — no induction is needed, and `exponent_le_totalDegree` applies coordinatewise unchanged.

With this, the whole reduction of the previous entries generalises verbatim from `(z, F₁, F₂)` to
`(z, F₁, …, F_n)`: the separation hypothesis becomes "the last state outgrows any multiple of the
joint scale of the point and all earlier states", and everything else is the same composition.

### `HTGeometry/MultiVarAlgebraicBound.lean` — the no-go at any cascade length

`exists_bound_posLog_of_multi_var_relation`:

```
∃ c ≥ 0, ∀ g z ε, 0 < ε → ε ≤ ‖A_D(X(z))‖ → (∑_{i ≤ D} A_i(X(z))·g(z)^i = 0) →
  log⁺‖g z‖ ≤ c · ( 1 + ∑_j log⁺‖X_j z‖ + log⁺ε⁻¹ )
```

and `not_multi_var_relation_of_separation`, its contrapositive against a separation hypothesis. Both
unconditional and axiom-clean, for an arbitrary family `X : Fin m → ℂ → ℂ` of states.

This lifts the whole lower-bound reduction from length two to arbitrary length. The joint scale is now
`∑_j log⁺‖X_j z‖`, and the constant is again explicit and independent of `g`, `z`, `ε`:
`max (log D + D·K + D·m·Dg·log 2) (D·Dg) D` with `K = ∑ log⁺‖A_i‖₁`, `Dg = ∑ deg A_i`.

**The card's remaining content, stated once and for all.** For the cascade `F_1, …, F_n`:

```
∀ A ≠ 0, ∀ c ≥ 0, ∃ z ε, 0 < ε ∧ ε ≤ ‖A(z, F_1 z, …, F_{n-1} z)‖ ∧
    c · (1 + log⁺‖z‖ + ∑_{k<n} log⁺‖F_k z‖ + log⁺ε⁻¹) < log⁺‖F_n z‖
```

That single analytic statement — a growth separation of the last state against every polynomial
expression in the earlier ones, with a floor — yields state independence, hence the lower bound, hence
the card's theorem. Everything else in the card is now proved unconditionally in Lean.

### `HTGeometry/LastVariableSplit.lean` — splitting off the newest state

mathlib's `MvPolynomial.finSuccEquiv` splits off the *first* variable; a cascade relation has to be
read in the *last* one. `lastHead m : Fin (m+1) → Fin (m+1)` is the required renaming — `castSucc j ↦
j.succ`, `last ↦ 0` — with `lastHead_injective` and the identity that makes it usable:

`(Fin.cons y w) ∘ lastHead m = Fin.snoc w y`

so a head-extended evaluation point becomes the tail-extended one the states naturally form.

`exists_top_multi_var_relation`: if the earlier states `X_0,…,X_{m-1}` admit no nonzero relation, then
a relation `P(X_0,…,X_{m-1}, F) = 0` with `P ≠ 0` gives

`∑_{i ≤ D} A_i(X(z)) · F(z)^i = 0`,  `D ≥ 1`,  `A_D ≠ 0` in `ℂ[Fin m]`.

Unconditional, axiom-clean — and `lastHead_injective` needs only `propext, Quot.sound`, no choice.

This is the general-length replacement for `exists_top_two_var_relation`, which handled only `m = 1`
via the ad-hoc cycle `![1,2,0]`. Composed with `not_multi_var_relation_of_separation`, it gives the
induction step for state independence at every cascade length: independence of `X_0,…,X_{m-1}` plus a
growth separation for the next state yields independence of `X_0,…,X_{m-1},F`.

### `HTGeometry/PrefixStateIndependence.lean` — the induction closes

```
StepSeparation X F :=
  ∀ A ≠ 0, ∀ c ≥ 0, ∃ z ε, 0 < ε ∧ ε ≤ ‖A(X(z))‖ ∧
    c · (1 + ∑_j log⁺‖X_j z‖ + log⁺ε⁻¹) < log⁺‖F z‖

noRelation_snoc :
  (X₀,…,X_{m-1} independent) → StepSeparation X F →
  ∀ P ≠ 0, ¬ (∀ z, P(X(z), F z) = 0)

noRelation_prefixFamily :
  (∀ m, StepSeparation (prefixFamily Y m) (Y m)) →
  ∀ m, ∀ P ≠ 0, ¬ (∀ z, P(Y₀ z, …, Y_{m-1} z) = 0)
```

Unconditional, axiom-clean. The induction runs from the empty family: for `Fin 0` the evaluation map
*is* `MvPolynomial.isEmptyRingEquiv`, so it is injective and a nonzero constant polynomial cannot
vanish — the base case is not vacuous, it is the statement that `ℂ` has no zero divisors in disguise.

**The card, in one line.** For the cascade states `Y m = entireCascade f (m+1)`:

> a growth separation at each step ⟹ the states are algebraically independent over ℂ ⟹ the lower
> bound ⟹ `ord_DA(f_n ∘ … ∘ f_1) = n`.

Together with the already-proved upper bound, every step of the card's theorem is now formal except
the single analytic predicate `StepSeparation`, which mentions only moduli, floors and `log⁺` — no
differential algebra, no field theory, no Nevanlinna theory and no Newton–Puiseux.

### The cascade instance

`noRelation_entireCascade` — for a cascade with a growth separation at every step, the coordinate
together with all the states satisfies no nonzero polynomial relation over ℂ. Unconditional,
axiom-clean, one line from `noRelation_prefixFamily`.

The instantiation needs no special case for the coordinate: `entireCascade f 0 = id`, so the prefix
family of `entireCascade f` *is* `(z, F_1, …, F_{m-1})` already. The same fact — the zeroth state is
the coordinate — is what made `n` generators suffice for the upper bound's transcendence-degree count,
and it is now doing the same work at the other end of the proof.

Lean note: writing the family as `fun j => entireCascade f (j : ℕ) z` without annotating the binder
makes Lean read `j : ℕ` and elaborate the polynomial over `MvPolynomial ℕ ℂ`; the coercion arrow is
what misleads it. Annotate `fun j : Fin m => …`.

### `HTGeometry/PolyIndependentFromNoRelation.lean` — the corpus's `PolyIndependent`, discharged

`polyIndependent_of_noRelation`: if the zeroth state is the coordinate (`Y 0 = id`) and the family
`(Y 0, …, Y n)` satisfies no nonzero polynomial relation over ℂ, then
`PolyIndependent (fun i : Fin n => Y (i+1))` — the corpus's monomial-form independence with
*polynomial* coefficients. Unconditional, axiom-clean.

The content is that the coefficient variable can be absorbed as one more state, which for a cascade
costs nothing because `entireCascade f 0 = id`. `coordPoly` assembles the combination into a single
polynomial in `(z, states)`; `eval_coordPoly` recovers the original sum by `Polynomial.eval_eq_sum_range`;
and `coeff_coordPoly` identifies its coefficients — the step that needs `Set.InjOn E T`, since distinct
summands must carry distinct monomials, with `coordExp_injective` separating the coordinate exponent
from the state exponents.

Consequence: the hypothesis `PolyIndependent (cascadeFamily f n)` of the corpus's
`exactDifferentialOrder_of_cascade` and `not_differentiallyAlgebraicOfOrder_of_cascade` is no longer a
dangling algebraic assumption — it now follows from `StepSeparation`, the same analytic predicate that
drives the route built here. Both routes to the lower bound therefore rest on one hypothesis, and the
only obligation left anywhere on the card is `helim` (equivalently, observability of the states from
the output jets), plus that single analytic separation.

### `HTGeometry/CascadeDerivativeProduct.lean` — the chain rule in closed form

`deriv_entireCascade_prod : F_k'(z) = ∏_{j<k} f_j'(F_j z)`, with
`deriv_entireCascade_ne_zero_iff` reading off that `F_k'` vanishes exactly where some constituent
derivative does. Unconditional, axiom-clean.

This is the datum every observability computation starts from: all higher jets of `F_n` are obtained
by differentiating this product, so the Bell/Jacobian determinant of Reduction III is a determinant in
the quantities `f_j^{(i)}(F_j)`. Stating the product once, rather than unfolding
`deriv_entireCascade_succ` at each level, is what will keep that computation finite.

The nonvanishing criterion is also the exact hypothesis the older `cascade_relation_cleared` wanted
before it was replaced by the division-free form: `F_k' ≠ 0` at a point is *equivalent* to all
constituents having nonzero derivative along the states there — so a floor for `F_k'` is a
simultaneous floor for the constituents, which is how the minimum-modulus selection should be
organised.

### The second jet: the first row of the observability system

`logDeriv_deriv_entireCascade`: wherever `F_k' ≠ 0`,

`F_k''/F_k' = ∑_{j<k} ( f_j''(F_j) / f_j'(F_j) ) · F_j'`.

Unconditional, axiom-clean.

Read as an equation in the unknowns `F_j'`, this is the first row of the observability system: the
output's second jet is a *linear* combination of the states' derivatives, with coefficients that are
the constituents' logarithmic-derivative data along the states. Higher jets differentiate this again
and produce the further rows, so the Reduction III determinant is the determinant of the resulting
triangular-in-`k` system — which is exactly the shape the corpus's abstract
`cascadeOutputJacobian_det_ne_zero` already handles.

Lean note: the induction step is `deriv2_entireCascade_succ` divided by `deriv_entireCascade_succ`,
with the nonvanishing of both factors supplied by `deriv_entireCascade_ne_zero_iff` from the previous
entry — the product criterion is what makes the two required nonvanishing facts (`f_k'(F_k) ≠ 0` and
`F_k' ≠ 0`) fall out of the single hypothesis `F_{k+1}' ≠ 0`.

### `HTGeometry/CascadeExactOrderFromSeparation.lean` — the corpus's cascade theorem, two of three inputs discharged

```
exactDifferentialOrder_entireCascade_of_separation :
  (∀ i, AnalyticOnNhd ℂ (f i) univ) → (∀ i, TranscendentalEntire (f i)) →
  (∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
  (∀ m, StepSeparation (prefixFamily (entireCascade f) m) (entireCascade f m)) →
  helim →
  ExactDifferentialOrder (entireCascade f n) n
```

Unconditional, axiom-clean. `exactDifferentialOrder_of_cascade` took three inputs — `hup`,
`PolyIndependent`, `helim`. `hup` is now proved outright, and `PolyIndependent` follows from the
analytic separation via `polyIndependent_cascadeFamily_of_stepSeparation`, so `helim` is the only
hypothesis of that theorem still standing.

A name collision surfaced and was avoided: `polyIndependent_cascadeFamily` already exists in
`EntireCascade.lean`, with a far heavier Clunie-style hypothesis (grouped coefficients, floors,
maximum-term data). The new derivation is kept under
`polyIndependent_cascadeFamily_of_stepSeparation`; it reaches the same conclusion from a hypothesis
that mentions only moduli and `log⁺`. Both now coexist, and the older one is no longer the only route
to state independence.

**Consolidated card status.**
- `hup` (`ord_DA ≤ n`): proved, no hypotheses beyond the paper's.
- `PolyIndependent` / state independence: reduced to `StepSeparation`.
- `hjets` (the other route's lower bound): equivalent to `helim`-style observability by
  `algebraicIndependent_jets_iff`.
- Remaining: `StepSeparation` (analytic) and `helim` (observability, Reduction III).

### `HTGeometry/PoincareRecession.lean` — the card's HT consequence, formalized

The card's section *"HT consequence: universal first-order Poincaré recession"* is now Lean.

- `entireCascade_const : entireCascade (fun _ => f) n = f^[n]` — a cascade with one repeated
  constituent is the iterate, so the unit-cost law reads `ord_DA(f^{[n]}) = n`.
- `exactDifferentialOrder_poincareApprox` — the normalized approximant
  `z ↦ f^{[n]}(ζ + z/λ^n)` has exact order `n` whenever the iterate does, for any `λ ≠ 0`.
- `exactDifferentialOrder_iterate_of_separation` — the unit-cost law stated directly on the iterate.

All unconditional and axiom-clean. The card's justification of the approximant step was the
triangular substitution `g_n^{(j)} = λ^{-nj}(f^{[n]})^{(j)}(ζ + z/λ^n)`; in Lean it is
`exactDifferentialOrder_affine_precomp`, which the corpus already owned — invertible affine
precomposition does not move the minimal order, and no jet computation is needed.

Note the approximant statement needs only `λ ≠ 0`, not that the fixed point is repelling. Repulsion
is what makes the limit exist and be the Poincaré function; it plays no part in the order count. So
the recession `1, 2, 3, … → ∞` is a statement about the *approximants alone*, and holds along any
nonzero multiplier.

### `HTGeometry/CascadePolynomialSharpness.lean` — the transcendence hypothesis is necessary

`not_exactDifferentialOrder_entireCascade_of_polynomial`: if every constituent is a polynomial then
for `n ≥ 1` the cascade does **not** have exact order `n`. Unconditional, axiom-clean.

Because a polynomial cascade is a polynomial (`exists_polynomial_entireCascade`, by composition) and a
polynomial satisfies the order-zero equation `X₁ − p(X₀) = 0`
(`differentiallyAlgebraicOfOrder_zero_of_polynomial`), the order is `0` no matter how long the cascade
is. The unit-cost law therefore fails outright on the polynomial class, and "transcendental" in the
card's hypotheses cannot be weakened to nonconstant, nonlinear, or any condition polynomials satisfy.

This is the counterexample side of the card's gate, and it is worth recording that it is *not* a
boundary case: the failure is total — order `0` against the claimed `n`, for every `n`.

Lean note: the nonvanishing of `X₁ − p(X₀)` is proved by evaluating at two points with the same first
coordinate, `![0,0]` and `![0,1]`; their difference is `1`, so the polynomial cannot be zero. Comparing
*coefficients* would need the degree-in-`X₁` argument, which is more work for the same conclusion —
two evaluations suffice whenever the polynomial is monic in one variable.

### The order-zero class, characterized; and the charge count

`differentiallyAlgebraicOfOrder_zero_iff_polynomial` — for entire `g`,

`ord_DA(g) ≤ 0  ↔  g is a polynomial`,

with `exactDifferentialOrder_zero_iff_polynomial` the exact-order form (the second condition of
`ExactDifferentialOrder` is vacuous at `0`). Unconditional, axiom-clean. Both directions are now in
hand — Liouville-at-polynomial-growth for `→`, the explicit equation `X₁ − p(X₀)` for `←` — so the
bottom of the order hierarchy is completely described: **the entire functions algebraic over `ℂ(z)`
are exactly the polynomials.**

`exactDifferentialOrder_eq_chargeCount` closes the card's *"quantized Wiman observability charge"*
formula: given the unit-cost law, the order equals `∑_{k<n} 1_{ω(f_k) ≠ 0}` whenever every charge is
nonzero. The Lean content is only the count `chargeCount_eq`; the mathematical content — that a
nonzero charge contributes exactly one order and its magnitude is irrelevant — is carried entirely by
the main theorem, which is the right reading: quantization is not an extra fact but a restatement of
the unit cost.

### Both routes close unconditionally at length one

`exactDifferentialOrder_entireCascade_one_of_cascade` — the corpus's `exactDifferentialOrder_of_cascade`
now runs at `n = 1` with *no* hypothesis beyond transcendence and a first-order equation, because both
of its remaining inputs degenerate:

- `polyIndependent_cascadeFamily_one` — at length one the state family is the single constituent, so
  `PolyIndependent` says exactly that `f_0` is not algebraic over `ℂ[z]`: the order-zero theorem.
- `helim_one` — the elimination hypothesis quantifies over `m < 1`, i.e. `m = 0`, and `DA (f_0) 0` is
  false; the implication is vacuous.

Unconditional, axiom-clean. Together with `exactDifferentialOrder_entireCascade_one` (proved earlier
through the field-theoretic route) and `exactDifferentialOrder_expCascade_one`, the length-one case of
the card is now established three independent ways — the direct argument, the transcendence-degree
route, and the corpus's own cascade interface. That is a genuine cross-check of the whole layer: the
three proofs share only the order-zero theorem.

### `HTGeometry/ExactOrderIsLeast.lean` — the minimality claim in its usual form

`exactDifferentialOrder_iff_isLeast`:

`ExactDifferentialOrder g n  ↔  IsLeast {k | DifferentiallyAlgebraicOfOrder g k} n`

Unconditional, axiom-clean. The card states its theorem as "minimal ADE order equals `n`", and the
corpus's abstract half is phrased with `IsLeast` (`isLeast_scalarDifferentialOrder`), while the
analytic side is phrased with `ExactDifferentialOrder`. The two agree, so the abstract and analytic
statements are now literally the same claim rather than two conventions.

Also updated in this pass: the card's **Lean status** block is marked superseded (it predates the
whole analytic/field layer) and the gate list gained the current items — upper bound on the actual
composition with no independence hypothesis, automatic state independence, order zero ⟺ polynomial,
length one by three routes, sharpness, and the two consequences — together with the two gates that
remain open, `StepSeparation` and observability.

### `HTGeometry/TranscendentalEntireClosure.lean` — the class is closed under the order-preserving operations

`transcendentalEntire_add_polynomial`, `transcendentalEntire_const_smul`,
`transcendentalEntire_affine_precomp` — adding a polynomial, scaling by a nonzero constant, and
precomposing with an invertible affine map all preserve transcendence. Unconditional, axiom-clean;
each is the observation that the inverse operation carries a polynomial value back to a polynomial.

These are exactly the operations under which the differential order is already known to be invariant
(`exactDifferentialOrder_affine_precomp` and its companions), so the hypothesis class of the
unit-cost law and its conclusion are now closed under the same group. In particular the Poincaré
approximants of the previous entry stay inside the class, which is what makes the recession statement
a statement about the class rather than about one function.

Lean note: `hq (a⁻¹ * (w - b))` produces a beta-redex, so `rw [hval]` cannot see the pattern
`a * (a⁻¹ * (w - b)) + b`; ascribing the type of `hz` explicitly (the statement is defeq) beta-reduces
it and the rewrite fires. Same trap as the `(f - fun _ => a₀) 0` elaboration failure recorded earlier
on this card — an unreduced application hiding a pattern from `rw`.

### `HTGeometry/SeparationImpliesTranscendence.lean` — the separation already contains transcendence

`transcendentalEntire_of_stepSeparation`: if the coordinate is among the earlier states, then
`StepSeparation X F` forces `F` to be transcendental. Unconditional, axiom-clean.

The argument is a direct comparison of constants. The separation gives, for every level `c`, a point
where

`c · (1 + ∑_j log⁺‖X_j z‖ + log⁺ε⁻¹) < log⁺‖F z‖`,

and the coordinate term alone gives `∑_j log⁺‖X_j z‖ ≥ log⁺‖z‖`. If `F` were a polynomial `q`, then
`log⁺‖F z‖ ≤ K + d·log⁺‖z‖` with `K, d` fixed (`posLog_norm_eval_poly_le`, the one-variable companion of
the bounds built earlier). Taking `c > max(d, K)` gives `c + (c − d)·log⁺‖z‖ < K`, hence `c < K` —
false by choice of `c`. Note the point `z` is not controlled and does not need to be: the contradiction
is between two constants, and the unbounded quantity `log⁺‖z‖` carries a nonnegative coefficient.

Consequence for the card: `StepSeparation` is a *single* hypothesis that supplies both the state
independence and the transcendence of the composite. The remaining analytic obligation is therefore
one predicate, not a predicate plus side conditions.

### The card's theorem in minimal-hypothesis form

`exactDifferentialOrder_entireCascade_of_separation'`:

```
(∀ i, TranscendentalEntire (f i)) →
(∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
(∀ m, StepSeparation (prefixFamily (entireCascade f) m) (entireCascade f m)) →
helim →
ExactDifferentialOrder (entireCascade f n) n
```

with `differentiallyAlgebraicOfOrder_entireCascade_of_transcendental'` the corresponding upper bound.
Unconditional, axiom-clean.

Analyticity is gone as a separate hypothesis: `TranscendentalEntire` already carries
`Differentiable ℂ`, and `analyticOnNhd_of_transcendentalEntire` supplies the rest. So the first two
hypotheses are now *exactly* the paper's ("transcendental entire, satisfying a first-order algebraic
differential equation"), and the last two are the two named obligations.

This is the statement the card should be read against. Nothing between those hypotheses and the
conclusion is assumed anywhere in the corpus.

### `HTGeometry/ClunieWeightFloor.lean` — where the two separation interfaces meet

`clunieWeight_le_of_floor` and `posLog_norm_last_le_of_floor`: a lower bound `ε` on the grouped
coefficient replaces the only term of `clunieWeight` that mentions it,
`N·log⁺(1/‖groupedCoeff‖)`, by `N·log⁺ε⁻¹`. Unconditional, axiom-clean.

This identifies the exact point of contact between the corpus's older Clunie interface
(`SeparatesLast`, whose conclusion is `clunieWeight < log⁺‖F_last‖`) and the `StepSeparation`
predicate built here (whose left side is `c·(1 + ∑ log⁺‖X_j‖ + log⁺ε⁻¹)`). After the substitution the
Clunie weight is bounded by

`∑_e ( log⁺‖A_e‖ + ∑_i e_i log⁺‖x_i‖ ) + N·log⁺ε⁻¹ + (N·|S| + N)·log 2`,

every term of which is of the form `StepSeparation` dominates once its level `c` is chosen after `S`,
`A` and `N` — which it may be, since `c` is universally quantified. So `StepSeparation → SeparatesLast`
is a bounded amount of bookkeeping away, and any future analytic work discharging the one predicate
would discharge both interfaces.

Recording this because it settles a design question: the two separation notions are not competitors.
`StepSeparation` is the stronger, simpler one (a single level parameter instead of a monomial-indexed
weight), and the corpus's Clunie induction remains available as a consumer of it.

### `HTGeometry/OneVariableMvPolynomial.lean` — the first edge's coefficients are univariate

`toPoly`, `eval_toPoly`, `toPoly_ne_zero` — the identification `MvPolynomial (Fin 1) ℂ ≅ Polynomial ℂ`,
compatible with evaluation and preserving nonvanishing. Unconditional, axiom-clean.

Needed because at the first edge of a cascade the only earlier state is the coordinate, so the
coefficient polynomial `A` in `StepSeparation` is a polynomial *in `z` alone* — and to feed it to the
univariate estimates (`norm_eval_ge_of_large` for the floor, `posLog_norm_eval_poly_le` for the
growth) it must first be seen as one.

`eval_empty_eq` is the reusable piece: on the empty variable set, `MvPolynomial.eval` *is*
`MvPolynomial.isEmptyRingEquiv`. That identity already appeared inside the base case of
`noRelation_prefixFamily`; it is now a named lemma, since every reduction of `Fin (m+1)` down to
`Fin 0` needs it at the bottom.

This sets up the next step: `StepSeparation` at the first edge should be provable outright from
transcendence, since a nonzero univariate `A` has an explicit floor beyond `growthRadius A`
(`norm_eval_ge_of_large`), the reciprocal of that floor is bounded there, and a transcendental entire
function exceeds every polynomial bound (`exists_norm_gt_of_not_polynomial`) — necessarily at a point
outside any fixed disc, since it is bounded on compacts.

### `HTGeometry/FirstEdgeSeparation.lean` — the separation at the first edge is a theorem

`stepSeparation_first_edge`: for `Y 0 = id` and `Y 1` transcendental entire,

`StepSeparation (prefixFamily Y 1) (Y 1)`

holds unconditionally. Axiom-clean. **The first instance of the card's remaining analytic obligation
is now discharged**, not assumed.

The proof is a three-constant argument, and each constant comes from a piece built earlier on this
card:

1. The coefficient `A` is a polynomial in the coordinate alone, so `toPoly A` is univariate and
   `norm_eval_ge_of_large` gives the *uniform* floor `ε = ‖lead‖/2` at every point beyond
   `growthRadius (toPoly A)`. The floor does not depend on the point, so `log⁺ε⁻¹` is a constant `L`.
2. `exists_norm_gt_of_not_polynomial` supplies a point where `‖Y 1 z‖` exceeds `Mbig·(1+‖z‖)^d`.
   Choosing `Mbig ≥ sup‖Y 1‖` on the closed disc of radius `growthRadius` forces that point to lie
   *outside* the disc — a transcendental entire function is bounded on compacts, so the witness cannot
   hide there. This is what makes an uncontrolled existential usable.
3. Taking `d ≥ c` and `Mbig ≥ exp(c + cL + 1)` makes the growth beat `c·(1 + log⁺‖z‖ + L)`: the
   `log⁺‖z‖` terms cancel with a nonnegative coefficient and the comparison reduces to `c + cL < log Mbig`.

Supporting `posLog_le_log_one_add` (`log⁺ t ≤ log (1+t)` for `t ≥ 0`) is what lets step 3 discard the
`log⁺` in favour of the polynomial bound's `log(1+‖z‖)`.

**Card status.** The open obligation is now: `StepSeparation` at edges `m ≥ 2` (where the earlier
states are no longer just the coordinate), plus observability (`helim`). Edge 1 is closed.

### `RHTower/EntireCircleFloor.lean` — the minimum modulus, with the zero count eliminated

`exists_circle_floor_of_ne_zero`: a nonzero entire function has a **positive floor on some circle of
any prescribed nondegenerate annulus** about any point where it does not vanish:

```
f entire, f c ≠ 0, 0 ≤ A < B  →  ∃ s ∈ [A,B], ∃ ε > 0, ∀ z, ‖z − c‖ = s → ε ≤ ‖f z‖
```

Unconditional, axiom-clean.

The corpus's `exists_radius_norm_ge_of_analytic_at` delivers this only after the caller supplies a
scale `H` satisfying `2·N·H < B − A`, where `N` is the number of zeros in the surrounding disc —
data the caller does not have, since `N` appears only in the theorem's own existential. The way out
is that the *same* theorem's Jensen conjunct bounds `N` a priori:

`N ≤ log(M/‖f c‖) / log((R'−R)/R) =: N₀`,

with `N₀` computed from the bound `M` on a fixed large sphere. Choosing `H = (B−A)/(2(N₀+1))` before
applying makes the gap condition automatic, because `N₀/(N₀+1) < 1`.

This is the shape of every remaining `StepSeparation` at edges `m ≥ 2`: the coefficient
`A(z, F_1 z, …)` is a nonzero entire function (by the previous edge's independence), so it has a
circle floor, and the separation then needs a point on that circle where the new state is large.
The floor half is now available off the shelf.

### `HTGeometry/SphereMaxModulus.lean` — moving a large value onto a prescribed circle

`exists_sphere_norm_ge` and `exists_sphere_norm_ge_of_le`: for entire `F`, any value on a closed disc
is dominated by `‖F‖` at some point of the bounding circle, and hence a value on a smaller circle is
dominated by one on any larger circle. Unconditional, axiom-clean.

This is the transfer the higher-edge separations need. The floor from `exists_circle_floor_of_ne_zero`
lives on a *circle*, while the corpus's composition-growth results produce a point large somewhere in
a *disc*; the maximum principle plus compactness of the sphere moves the large value onto the circle,
so the two can be evaluated at the same point.

Mechanism: `IsCompact.exists_isMaxOn` on the sphere supplies the maximiser, and
`Complex.norm_le_of_forall_mem_frontier_norm_le` on `ball 0 s` — whose frontier is the sphere and whose
closure is the closed ball — bounds the disc by it.

With this and the circle floor, the two halves of `StepSeparation` at edges `m ≥ 2` can be evaluated at
a common point; what is still missing is the quantitative comparison between the floor's decay and the
composition's growth along a sequence of radii, which is where the Wiman–Valiron/Borel selection
(already in the corpus) has to enter.

### `RHTower/FloorAndLargeSelection.lean` — one point carrying both facts

`exists_point_floor_and_large`: for entire `g` with `g 0 ≠ 0` and entire `F`, and any `r > 0`,

```
∃ z ε, 0 < ε ∧ ε ≤ ‖g z‖ ∧ ‖F w‖ ≤ ‖F z‖ ∧ r ≤ ‖z‖ ≤ r + 1     (for every ‖w‖ ≤ r)
```

Unconditional, axiom-clean. The circle floor and the maximum principle are combined into the single
selection a separation argument consumes: one point, bounded below for `g` and dominating for `F`,
with its modulus confined to a prescribed unit window so the selection can be iterated along windows
going to infinity.

This is the analytic core of `StepSeparation` at any edge, with the geometry finished. What is left is
purely quantitative: the floor `ε` and the window position `r` must be related so that
`c·(1 + ∑ log⁺‖X_j z‖ + log⁺ε⁻¹)` stays below `log⁺‖F z‖`. At the first edge that relation was free,
because a univariate coefficient has a floor independent of the radius; at later edges `ε` degrades
with the zero count of `A(z, F_1 z, …)`, and controlling that degradation against the composition's
growth is exactly the Wiman–Valiron/Borel step the corpus already carries
(`borel_growth`, `exists_ge_lt_two_mul`, `exists_radius_floor_maxTerm_block`).

### `RHTower/StepSeparationFromWindow.lean` — the obligation no longer asks for a point

`stepSeparation_of_window`: with the states entire, the new state entire, and each nonzero coefficient
nonvanishing at the origin, `StepSeparation X F` follows from a *window comparison* — for each
coefficient `A` and level `c`, some `r > 0` and reference point `w` in the disc of radius `r` such that
**every** point `z` of the window `r ≤ ‖z‖ ≤ r+1` carrying a floor `ε` for `A(X(·))` and satisfying
`‖F w‖ ≤ ‖F z‖` also satisfies

`c·(1 + ∑_j log⁺‖X_j z‖ + log⁺ε⁻¹) < log⁺‖F z‖`.

Unconditional, axiom-clean. The point itself is produced by `exists_point_floor_and_large`; the
analyst supplies only the inequality.

This is the final restatement of the card's remaining analytic obligation, and it is now in the form
Wiman–Valiron estimates are naturally stated in: a comparison on an annulus, between the maximum
modulus of the composite and the joint scale of the earlier states, with a floor as an input rather
than something to be arranged. The corpus's radius-selection lemmas
(`exists_radius_floor_maxTerm_block`, `borel_growth`) produce exactly windows of this shape.

Together with `stepSeparation_first_edge` (which discharges the obligation outright at the first
edge), this is where the card stands: everything algebraic, field-theoretic and value-distributional
is proved; what is open is one annulus comparison per edge from the second on, plus observability.

### Correcting the nonvanishing hypothesis

`stepSeparation_of_window` as first stated required each nonzero coefficient to be nonvanishing **at
the origin** — an artefact of centring the floor circle at `0`, and not something the induction
supplies. Replaced by `stepSeparation_of_window_of_ne`, whose hypothesis is

`∀ A ≠ 0, ∃ c, A(X(c)) ≠ 0`,

i.e. the coefficient is not identically zero along the states. That *is* the independence of the
earlier states, so it is exactly the induction's own invariant.

Two supporting changes made this possible:

- `exists_sphere_isMaxOn` / `exists_sphere_isMaxOn_at` — the *maximiser* on a circle, dominating the
  whole closed disc at once. The earlier `exists_sphere_norm_ge` produced a point per `w`, which
  cannot serve when one point must dominate every `w` in the disc; choosing the maximiser first and
  applying the maximum principle afterwards fixes the quantifier order.
- `exists_point_floor_and_large_of_ne` — the selection with the centre chosen where the coefficient is
  nonzero, and the point taken to be that maximiser.

Worth recording as a method point: the first version was provable but with a hypothesis nothing in the
development could discharge. The fix was not analytic but a quantifier reordering — "for each `w` some
`z`" versus "some `z` for all `w`" — which is the kind of gap that a proof assistant surfaces
immediately and prose does not.

### The induction runs from window comparisons alone

`noRelation_prefixFamily_of_window`: with the states entire, a window comparison at every level gives
the full state independence

`∀ m, ∀ P ≠ 0, ¬ ∀ z, P(Y_0 z, …, Y_{m-1} z) = 0`.

Unconditional, axiom-clean.

The point is that the nonvanishing hypothesis of `stepSeparation_of_window_of_ne` — "each nonzero
coefficient is not identically zero along the states" — is precisely the induction's conclusion one
level down, so it is discharged internally at each step rather than assumed. Nothing outside the
window comparison is required.

So the card's lower-bound obligation has reached its final shape: **one inequality on an annulus, per
level**, with the point supplied, the floor supplied, and the maximum-modulus domination supplied:

```
c·(1 + ∑_j log⁺‖Y_j z‖ + log⁺ε⁻¹) < log⁺‖Y_m z‖
```

for `z` in the window, given `ε ≤ ‖A(Y(z))‖` and `‖Y_m w‖ ≤ ‖Y_m z‖` for all `w` in the inner disc.
`stepSeparation_first_edge` is the `m = 1` instance, proved.

### `RHTower/CascadeOrderFromWindow.lean` — the card's theorem at its smallest hypothesis set

```
exactDifferentialOrder_entireCascade_of_window :
  (∀ i, TranscendentalEntire (f i)) →
  (∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
  (window comparison at every level) →
  helim →
  ExactDifferentialOrder (entireCascade f n) n
```

Unconditional, axiom-clean. The first two hypotheses are the paper's. The third is one inequality on
an annulus per level, with the point, the floor and the maximum-modulus domination all supplied by
`exists_point_floor_and_large_of_ne`. The fourth is the elimination step.

This is the end of the reduction: state independence, the transcendence-degree count, both order
bridges, the value-distribution estimates, the Clunie interface and the polynomial bookkeeping are all
proved, and nothing algebraic remains between these hypotheses and the conclusion.

**Summary of the run.** Beginning from a card whose Lean status recorded an abstract skeleton plus two
external analytic inputs, the following are now proved unconditionally and axiom-clean on the actual
entire functions:

* `ord_DA(f_n ∘ … ∘ f_1) ≤ n` with exactly the paper's hypotheses — the Clunie–Steinmetz input turned
  out to be unnecessary for this half, since consecutive states are automatically independent;
* the order-zero classification (`entire and algebraic ⟺ polynomial`), from which the sharpness of the
  transcendence hypothesis follows;
* the length-one case, three independent ways, with `Complex.exp` as an explicit witness;
* the Poincaré recession consequence and the charge-count identity;
* the whole lower-bound reduction, ending at one annulus inequality per level plus `helim`, with the
  `m = 1` instance of that inequality also proved.

### Umbrella audit

`lake build GaloisForLFunctions.HTGeometry` — **succeeds**, 14227 jobs. Every module added on this
card is wired and compiles inside the umbrella, and the `analyticOnNhd_iteratedDeriv` collision
repaired earlier is confirmed fixed at umbrella scale.

`lake build GaloisForLFunctions.RHTower` — **fails**, for a reason unrelated to this card:

```
import ...Sieve.SquarefreeDivisorCount failed, environment already contains
'RHTower.Sieve.card_divisors_of_squarefree' from ...Sieve.DivisorSquareSum
```

Two different proofs of the same fact carry the same name — `SquarefreeDivisorCount.lean:37`
(`Squarefree m → m ≠ 0 → …`) and `DivisorSquareSum.lean:25` (`Squarefree d → …`, used only locally at
line 37 of that file) — and the umbrella imports both (lines 3283 and 3466). This is concurrent Sieve
work by another session, not touched here; the minimal repair is to rename the local one in
`DivisorSquareSum.lean` (two occurrences), since `Squarefree d` already gives `d ≠ 0` and the two
statements are equivalent.

All RHTower modules added on this card build individually and together
(`CascadeOrderFromWindow` at 8980 jobs, which imports the rest of them).

### The displacement floor, from the circle floor

`exists_circle_displacement_floor_of_factor`: if `g z − g c = (z − c)·h z` with `h` entire and
`h c ≠ 0`, then on some circle of any prescribed annulus `[A,B]` (with `A > 0`)

`A·μ ≤ ‖g z − g c‖`

for a positive `μ`. Unconditional, axiom-clean.

Three lines, because the zero-count problem was already solved once: the corpus's
`exists_radius_displacement_floor` re-derives the minimum modulus internally and inherits the same
unusable `2·N·H < B − A` hypothesis, whereas applying `exists_circle_floor_of_ne_zero` to the *factor*
`h` and then `displacement_floor_of_factor` gives the displacement floor with no zero counting at all.

The hypothesis `h c ≠ 0` is `g'(c) ≠ 0` in disguise — differentiating the factorization at `c` gives
`h c = g'(c)` — so for a nonconstant entire `g` a suitable centre always exists.

This is the last analytic primitive that `exists_norm_comp_gt_at` (the corpus's composition-growth
theorem at a free base point) requires: it consumes exactly a displacement floor on a circle, plus a
point where the outer function is large within half that floor of `g c`.

### Correction — the window interface was vacuous, and the corrected one is inhabited

`RHTower.not_window_comparison` (axiom-clean): **no family satisfies the window comparison** of the
previous entries. The hypothesis quantified the coefficient floor `ε` universally, while the quantity
it must dominate contains `log⁺ε⁻¹`; since any smaller positive number is still a valid floor, the
left side can be driven above every bound with the point and the right side fixed.

The witness is the first edge of the exponential cascade, with `A = X₀` and level `c = 1`. For any
proposed radius `r`, take the centre `0` and the point `z = r` on the real axis: the maximum of
`‖exp‖` on the disc of radius `r` sits exactly there, so the domination hypothesis holds, the
coefficient value is `r > 0`, and every `ε ≤ min(r, e^{−(r+2+log⁺r)})` is admissible. Then

`1·(1 + log⁺r + log⁺ε⁻¹) ≥ r + 3 > r = log⁺‖exp z‖`.

So `stepSeparation_of_window`, `stepSeparation_of_window_of_ne`, `noRelation_prefixFamily_of_window`
and `exactDifferentialOrder_entireCascade_of_window` had unsatisfiable hypotheses. They are removed;
what replaces them is exact, and the defect is instructive: in `StepSeparation` the floor is produced
*together with* the point, so it may be taken to be the value there, and any interface that hands the
floor to an adversary instead is asking for the impossible.

**`HTGeometry/CircleComparisonSeparation.lean` — the corrected interface.** `CircleComparison X F`:
for every nonzero coefficient `A` and level `c` there are a centre, a radius `s > 0` and a floor
`ε > 0` with

* `ε ≤ ‖A(X(z))‖` at **every** point of the circle, and
* the comparison `c·(1 + ∑_j log⁺‖X_j z‖ + log⁺ε⁻¹) < log⁺‖F z‖` at every point of the circle
  dominating the enclosed disc.

The floor is now part of the datum, chosen by the analyst rather than by an adversary, and it is a
floor on a whole circle, so it cannot be shrunk without falsifying its own clause.

* `stepSeparation_of_circleComparison` — three lines: the maximiser of `‖F‖` on the circle
  (`exists_sphere_isMaxOn_at`) carries the floor and the domination at once. No analyticity of the
  earlier states is needed, only differentiability of the new one.
* `noRelation_prefixFamily_of_circleComparison`, and
  `exactDifferentialOrder_entireCascade_of_circleComparison` — the induction and the capstone.

**The interface is inhabited, at the two lowest edges.**

* `circleComparison_zeroth_edge` — with no earlier states a nonzero coefficient is a nonzero constant,
  which floors itself; the coordinate then beats `c·(1 + log⁺ε⁻¹)` on the circle of radius
  `exp(c(1+log⁺ε⁻¹)) + 1`.
* `circleComparison_first_edge` — the univariate floor `‖lead‖/2` is uniform beyond `growthRadius`, so
  it holds on the *whole* circle through the point where `Y 1` beats the polynomial bound; that point
  lies outside the disc where `Y 1` is bounded, so the circle is admissible, and the comparison
  transports to every dominating point of it because they all have the same modulus.
* `exactDifferentialOrder_entireCascade_of_circleComparison_ge_two` — hence the card's theorem with
  the analytic obligation required **only from the second edge on**.

All unconditional, all axiom-clean, `lake build GaloisForLFunctions.HTGeometry` succeeds (14242 jobs).

**`RHTower/CascadeOrderFromWindow.lean` — the geometry, at every scale.**
`exists_circle_floor_along_states` and `exists_circle_floor_and_max_point`: for a coefficient not
identically zero along the states and any prescribed scale `r₀`, there are a centre, a radius `s ≥ r₀`
carrying a positive floor for the coefficient on its whole circle, and a point of that circle at which
the new state dominates the enclosed disc. So both geometric ingredients of a `CircleComparison` are
free at every scale; what is open is only the numeric comparison at that point.

**Card status.** The obligation is one numeric inequality per edge `m ≥ 2`, on a circle whose floor
and dominating point the corpus supplies, plus observability (`helim`). Edges 0 and 1 are theorems.

### The lower bound is closed: the states are independent for elementary reasons

`noRelation_entireCascade_of_transcendental` (unconditional, axiom-clean):

```
∀ m (f : ℕ → ℂ → ℂ), (∀ i, TranscendentalEntire (f i)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → ¬ ∀ z, P(z, f₀ z, f₁(f₀ z), …) = 0
```

**No growth separation, no Nevanlinna theory, no Clunie–Steinmetz, no Pólya.** The whole analytic
programme of the previous entries — `StepSeparation`, `CircleComparison`, the composition-growth
chain — is unnecessary for the card's lower bound.

The proof is an induction on the cascade length that peels off the **first** edge, not the last. All
states but the coordinate factor through `f₀`:

`Y_{k+1} = G_k ∘ f₀`, `G` the state family of the shifted sequence `(f₁, f₂, …)`
(`entireCascade_succ_shift`).

So on a fibre `f₀^{-1}(u)` the relation collapses to a polynomial *in the coordinate alone*, of degree
at most `D`, with one root for each preimage. If `u` has more than `D` preimages the polynomial is
identically zero, and — splitting `P` by `MvPolynomial.finSuccEquiv`, whose coefficients are exactly
the polynomials in the shifted states — every coefficient `Q_i` satisfies

`Q_i(u, G_1 u, …, G_m u) = 0`.

That holds for every `u` in the value set, which is **open**, so by the identity theorem it holds for
every `u ∈ ℂ` — a relation among the shifted cascade's states, which the induction hypothesis forbids.
Hence `Q_i = 0` for all `i`, so `P = 0`.

Two elementary inputs, both built here:

* `EntireValence.exists_open_many_preimages` — for every `k`, a transcendental entire function has a
  **nonempty open** set of values each taken at `k` distinct points inside a fixed disc.  Openness is
  the open mapping theorem (disjoint balls around the preimages); the count is built one preimage at a
  time, each taken so far out that it cannot coincide with the earlier ones.
* `TranscendentalDenseExterior.exists_norm_gt_and_dist_lt_of_transcendental` — **Casorati–Weierstrass
  at infinity**: outside every disc a transcendental entire function comes arbitrarily close to every
  value.  Proved without singularity theory: if a value were avoided by a definite margin outside a
  disc, all zeros of the shifted function would lie in that disc, and extracting them
  (`exists_polynomial_factor_closedBall`) leaves a zero-free cofactor whose reciprocal is bounded by a
  polynomial, hence is a polynomial (`exists_norm_gt_of_not_polynomial`), hence — having no zeros —
  a constant; the function would be a polynomial.

Consequences, both axiom-clean:

* `polyIndependent_cascadeFamily_of_transcendental` — the corpus's `PolyIndependent` for the cascade
  states, with no hypothesis beyond transcendence.
* `exactDifferentialOrder_entireCascade_of_elimination` —

```
(∀ i, TranscendentalEntire (f i)) →
(∀ k < n, DifferentiallyAlgebraicOfOrder (f k) 1) →
helim →
ExactDifferentialOrder (entireCascade f n) n
```

**The first two hypotheses are exactly the paper's, and `helim` (the elimination step, Reduction III)
is the only remaining input.** Everything analytic on this card is now discharged.

Method note worth keeping: the separation programme was trying to prove independence by making the new
state *outgrow* the old ones, which is Clunie–Steinmetz and genuinely hard. Independence does not need
growth at all — it needs only that a transcendental entire function is far from injective, and that an
identity on an open set of values propagates. The card's Reduction III should be re-read with this in
mind: its analytic half is dispensable, and only the observability half (`helim`) carries content.
