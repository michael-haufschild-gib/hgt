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
- [ ] Lean: bound `D` and `E` at a Borel-good radius, making the remainder `o(nu)`
- [ ] Lean: Newton--Puiseux places at `U = infinity`, hence the nondegenerate Wiman place
- [ ] Lean: Clunie--Steinmetz composition separation and state algebraic independence
- [x] Lean: the order lower bound `ord_DA >= n` from `n` algebraically independent jets
- [x] Lean: the matching upper bound `ord_DA <= n` from a bounded-transcendence state field
- [x] Lean: `IsLeast`, the exact minimal order, given the two analytic inputs as hypotheses

### Lean status

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

The analytic inputs that supply the *measured weights themselves*, and the state independence, are
not formalized, and none of them exists in mathlib either:

- Wiman--Valiron asymptotics and the central index (Reduction I's top-symbol reduction);
- Goldberg's finite-order theorem and Strelitz's positive-order theorem;
- Newton--Puiseux places at `U = infinity` for an algebraic function field;
- Clunie--Steinmetz composition-growth separation (state algebraic independence);
- Nevanlinna characteristic and the algebraic-function root estimate.

Each of these is a self-contained analytic build.  Until they are in place, Reduction I and the
Clunie induction enter the Lean layer as the explicit hypotheses `hq : forall k, 0 < q k` and the
triangularity package, which is exactly how the paper proof uses them.

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
