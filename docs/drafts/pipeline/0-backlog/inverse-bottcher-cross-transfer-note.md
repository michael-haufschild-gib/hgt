# Inverse-Böttcher Cross-Transfer Note

- **ID:** inverse-bottcher-cross-transfer-note
- **Stage:** 0-backlog
- **Type:** CANDIDATE / theorem note
- **Source:** research chat 2026-06-23; Nguyen Question 6.2; Xie/Nguyen value-product audit; Baker-DeMarco unlikely-intersection audit
- **Statement:** Algebraic dependence of inverse Böttcher coordinates for `f_c(z)=z^2+c` is controlled, if at all, by the cross-transfer germ `H_12=phi_c2 o psi_c1`, whose exact defect equation lies outside the direct `psi_f(u(t))` substitution class in Nguyen's theorem.

## Formal Setting

Let `K=Qbar(c1,c2)` unless a specialization field is explicitly stated. Work in Laurent germs at infinity.

For

`f_c(z)=z^2+c`,

let `psi_c(t)` be the local conjugacy

`psi_c(t^2)=psi_c(t)^2+c`, `psi_c(t)=t+O(t^-1)`,

and let `phi_c=psi_c^-1`, so

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)=z+O(z^-1)`.

Exceptional parameters: `c=0` (monomial/power map) and `c=-2` (Chebyshev conjugacy). The diagonal `c1=c2` is trivial.

## Cross-Transfer Germ

Define

`H_12(t)=phi_c2(psi_c1(t))`.

Then

`psi_c2(H_12(t))=psi_c1(t)`

and the exact defect equation is

`psi_c2(H_12(t^2)) = psi_c2(H_12(t)^2) + (c1-c2)`.

Equivalently,

`H_12(t^2)=phi_c2(psi_c2(H_12(t)^2)+(c1-c2))`.

This is the precise non-transfer obstruction: Nguyen's `psi` theorem controls algebraic dependence of `psi_f(u(t))` for monomial/polynomial substitutions `u`; inverse-coordinate dependence introduces the unknown substitution `H_12` and an additive parameter defect inside the `c2` Böttcher chart.

## Relation-To-Cross-Transfer Implication

A putative relation

`P(z,phi_c1(z),phi_c2(z))=0`

with coefficients in `K` gives, after substituting `z=psi_c1(t)`,

`P(psi_c1(t), t, H_12(t))=0`.

After clearing denominators this implies at least one of:

1. `H_12` is algebraic over `K(t,psi_c1(t))`; or
2. `psi_c1(t)` is algebraic over `K(t,H_12(t))`; or
3. the chosen polynomial relation was degenerate and must be divided by the specialization factor before it is meaningful.

The missing theorem is to turn this implication into rigidity for the defect equation. In particular, one must specify a field/class for `H_12` that is actually forced by the original relation and then prove that the defect equation forces `c1=c2` or the monomial/Chebyshev exceptions.

## Generic Variable Route

[CONJECTURE / proof-sketch, not yet promoted]

Over `Qbar(c1,c2)`, generic all-degree independence should follow by specializing `c1 -> 0`, where `phi_c1(z)` becomes `z`. Any relation surviving this specialization would make `phi_c2` algebraic over `Qbar(c2,z)`, contradicting Becker-Bergweiler for nonexceptional `c2`.

Open technical step: prove a `c1`-adic valuation descent showing that a relation cannot vanish entirely into the factor `phi_c1-z` after specialization. The fact that

`phi_c1(z)-z = c1/(2z)+O(c1*z^-3)`

suggests the descent is possible, but it must be written. If this closes, the generic-variable result is a corollary of known individual hypertranscendence, hence **search/BRIDGE**, not new HGT knowledge.

## Special-Fiber Route

For algebraic nonexceptional values `(c1,c2)`, generic specialization does not decide whether a special relation appears only at that fiber. This is the arithmetic/unlikely-intersection residue aligned with Nguyen Question 6.2. Low-degree determinant checks do not settle it.

Any special-fiber theorem must avoid confusing:

1. a chosen-minor failure locus;
2. the full relation/Fitting locus where all relevant maximal minors drop rank;
3. an actual dynamical correspondence locus.

The `D<=2` polynomial `R(c1,c2)` from the companion card is category 1 only and has already been killed as a proposed relation locus.

## Source Audit

- Nguyen 2013/2015 proves algebraic independence for local conjugacies `psi_f` under Medvedev-Scanlon style hypotheses and explicitly asks the inverse-coordinate `phi_f=psi_f^-1` problem as Question 6.2.
- Nguyen 2021/2022 on polynomial canonical heights treats algebraic products of Böttcher-coordinate values and canonical heights, not the function-field relation `P(z,phi_c1(z),phi_c2(z))=0`.
- Xie 2022 treats algebraicity criteria for products of Böttcher-coordinate values/geometric invariants; this does not appear to directly settle inverse-coordinate function-field relations.
- Baker-DeMarco unlikely-intersection work controls simultaneous preperiodicity/common preperiodic-point structure; it informs the special-fiber analogy but does not directly state the inverse-Böttcher function-field independence theorem.

## Theatre Status

Current status: **HOLD / theorem note**, not NOVEL x SIGNIFICANT.

Promotion requires one of:

1. a complete rigidity theorem for `H_12` derived from a putative inverse-coordinate algebraic relation;
2. a written valuation-descent proof of generic all-degree independence plus a source-grade verdict that the result is only search/BRIDGE;
3. a prior-art reduction showing Nguyen/Xie/Medvedev-Scanlon/Baker-DeMarco already covers the function-field inverse-coordinate case;
4. a source-new special-fiber theorem for algebraic `(c1,c2)` that survives the full relation-locus and literature gates.

No finite rank table or sampled determinant can promote this lane by itself.

## Log

- 2026-06-23 — created after the `D<=2` rank guard and the killing of `R(c1,c2)` as a proposed exceptional variety. The note freezes the cross-transfer equation and the exact open dependencies.

## 2026-06-23 coefficient-class gate

Haiku's audit sharpens the cross-transfer note: the identity is exact, but it is not yet a Mahler/Nishioka reduction.

First rewrite the defect in difference form. Since

`H_12(t)=phi_c2(psi_c1(t))`,

we have

`H_12(t^2)=phi_c2(psi_c1(t)^2+c1)`

and, using `phi_c2(f_c2(w))=phi_c2(w)^2`,

`H_12(t)^2=phi_c2(psi_c1(t)^2+c2)`.

Therefore

`H_12(t^2)-H_12(t)^2 = phi_c2(psi_c1(t)^2+c1)-phi_c2(psi_c1(t)^2+c2)`.

The right-hand side is a `delta=c1-c2` translation defect inside the `c2` Böttcher chart. It is not presently known to lie in `K(t)`, in an algebraic extension of `K(t)`, or in a named Mahler class.

### Source implication lemma

Let `c1,c2` be nonexceptional and let `K` be the declared coefficient field. If `phi_c1` and `phi_c2` are algebraically dependent over `K(z)`, then, because `phi_c1` is transcendental over `K(z)`, `phi_c2` is algebraic over `K(z,phi_c1)`. Substituting `z=psi_c1(t)` gives

`H_12(t)=phi_c2(psi_c1(t))`

algebraic over

`K(t,psi_c1(t))`.

This is the bridge back to the original inverse-coordinate problem. It is also weaker than the condition needed by standard Mahler reductions over `K(t)`. Any proposed prior-art reduction must therefore cover this coefficient field/class exactly, or prove a descent from `K(t,psi_c1(t))` to a known Mahler/algebraic class.

Updated promotion gate:

1. Prove a rigidity theorem for `H_12` algebraic over `K(t,psi_c1(t))`, not merely over `K(t)` unless a descent is supplied.
2. Or prove that the translation defect belongs to a known coefficient class covered by Mahler/Nishioka-style results.
3. Or show that the mismatch itself defines a source-new invariant of inverse-Böttcher cross-transfer.

## 2026-06-23 valuation-descent obstruction

The proposed generic proof by specializing `c1 -> 0` has a real obstruction; it is not mere bookkeeping.

Let `a=c1` and write

`phi_a(z)=z+a u_0(z)+O(a^2)`.

Differentiating

`phi_a(z^2+a)=phi_a(z)^2`

at `a=0` gives

`u_0(z^2)+1=2z u_0(z)`.

Thus

`u_0(z)=1/(2z)+1/(4z^3)+1/(8z^7)+1/(16z^15)+...`

more generally

`u_0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`.

Consequently, if a putative relation `P(a,b,z,phi_a,phi_b)=0` specializes at `a=0` to a nonzero relation not divisible by `X-z`, Becker-Bergweiler gives a contradiction. But if the specialization vanishes along `X=z`, the first nonzero `a`-adic term after writing `P` in powers of `(X-z)` involves powers of `u_0(z)`.

The descended relation then lives over an enlarged field such as

`Qbar(b,z,u_0(z))`,

not over `Qbar(b,z)`. Becker-Bergweiler's individual hypertranscendence of `phi_b` over `Qbar(b,z)` does not by itself rule this out.

Updated status of the generic-variable route:

- easy case: specialization not divisible by `X-z` -> contradiction from individual transcendence;
- hard case: specialization divisible by `X-z` -> descent introduces the lacunary Mahler series `u_0`;
- missing theorem: prove `phi_b` is algebraically independent from `u_0` over `Qbar(b,z)`, or find another descent avoiding this coefficient-field enlargement.

Therefore the `c1=0` proof is not banked. The obstruction is exactly another coefficient-class problem, parallel to the `K(t,psi_c1)` issue in the cross-transfer note.

## 2026-06-23 source check on `u_0`

A quick source search for the exact obstruction class found broad Mahler/lacunary-function literature, including work on algebraic independence of Mahler functions and standard lacunary natural-boundary phenomena, but no direct statement covering algebraic independence between

`u_0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`

and a nonexceptional quadratic Böttcher coordinate `phi_b(z)`.

This absence is not evidence of novelty. It only sharpens the next gate: either locate an existing Mahler/lacunary theorem that applies to the mixed pair `(u_0,phi_b)`, or prove a new independence/descent lemma. A source search must include at least Nishioka/Kubota-style Mahler algebraic-independence results and Becker-Bergweiler/Fernandes Böttcher hypertranscendence references before any promotion.

## 2026-06-23 `u_0` natural-boundary sublemma and mismatch

The monomial-tangent series `u_0` has a standard lacunary transcendence proof, but this closes only a small dependency.

Set `x=1/z` and

`U_0(x)=u_0(1/x)=sum_{n>=0} 2^{-(n+1)} x^{2^{n+1}-1}`.

The exponents `p_n=2^{n+1}-1` satisfy a Hadamard gap condition, since `p_{n+1}/p_n -> 2`, and the coefficients satisfy

`limsup |2^{-(n+1)}|^{1/p_n}=1`.

Thus `U_0` has radius of convergence `1` and the unit circle is a natural boundary by the Ostrowski-Hadamard gap theorem. Hence `u_0` is transcendental over `C(z)`; an algebraic function over `C(z)` has only finitely many branch/singular points and cannot have the full unit circle as a natural boundary.

This does **not** prove the required independence from `phi_b`. The obstruction is the mismatch of dynamics:

- `u_0` is adapted to `z -> z^2`:

  `u_0(z^2)=2z u_0(z)-1`.

- `phi_b` is adapted to `z -> z^2+b`:

  `phi_b(z^2+b)=phi_b(z)^2`.

If `P(z,u_0(z),phi_b(z))=0`, applying `z -> z^2` gives an equation involving `phi_b(z^2)`, which is not controlled by the Böttcher equation. Applying `z -> z^2+b` gives an equation involving `u_0(z^2+b)`, which is not controlled by the Mahler equation. Therefore the mixed pair `(u_0,phi_b)` is not a standard one-map Mahler system without an additional transfer/descent theorem.

Exceptional controls:

- `b=0`: `phi_0(z)=z`, so no independence question remains.
- `b=-2`: `phi_{-2}(z)=(z+sqrt(z^2-4))/2` is algebraic over `C(z)`, so independence fails for the Chebyshev control.

Updated target:

`[CONJECTURE] For nonexceptional b, u_0(z)` and `phi_b(z)` are algebraically independent over `Qbar(b,z)`.

This target is not promoted. The natural-boundary lemma only proves `u_0` is not rational/algebraic; it does not settle mixed algebraic independence.

## 2026-06-23 mixed-map product gate

A useful prior-art boundary comes from the integrable/nonintegrable split in Medvedev-Scanlon style dynamics.

Let

`M(z)=z^2`, `F_b(z)=z^2+b`.

For `b notin {0,-2}`, `M` is integrable/monomial and `F_b` is nonintegrable/disintegrated. Nguyen's 2021/2022 canonical-height paper summarizes the Medvedev-Scanlon classification in the needed form: for a product containing nonintegrable factors and integrable factors, preperiodic subvarieties split as a product between the two blocks; nontrivial coupling curves live only among compatible nonintegrable factors or inside the integrable block.

Consequence for this note:

- Any attempt to convert a relation between `u_0` and `phi_b` into an algebraic curve preperiodic under the pure product map `(M,F_b)` should die by known classification, unless `b=0` or `b=-2`.
- This does **not** kill the actual target, because `u_0` is not a coordinate on the monomial dynamical line alone. It is a section of the skew affine extension

  `S_M(z,u)=(z^2, 2z u - 1)`

  over `M`.

- Meanwhile `phi_b` is controlled by the Böttcher cover over `F_b`, not over `M`.

Thus a relation `P(z,u_0(z),phi_b(z))=0` is not automatically a preperiodic subvariety of `(M,F_b)`. Applying `M` controls `u_0` but leaves `phi_b(z^2)` uncontrolled; applying `F_b` controls `phi_b` but leaves `u_0(z^2+b)` uncontrolled.

Updated gate:

A valid proof must either:

1. build an algebraic skew-product dynamical system containing both sections and prove a rigidity theorem there;
2. reduce that skew system to known Medvedev-Scanlon / Mahler / difference-Galois machinery with hypotheses checked; or
3. prove that no such reduction exists and isolate the skew-extension obstruction as a new invariant.

The pure product-map route is search-killed; the skew mixed-map route remains HOLD.

## 2026-06-23 exact source-boundary ledger

This ledger replaces vague references to "Medvedev-Scanlon-style" coverage.

### Nguyen 2013/2015: `psi` local conjugacies, not inverse `phi`

Nguyen defines the Böttcher coordinate as the inverse `phi_f=psi_f^-1` and explicitly asks the inverse-coordinate algebraic-independence problem in Question 6.2(a): give necessary and sufficient conditions for `phi_1,...,phi_n` to be algebraically independent over `K(t)`.

The proved theorem is for local conjugacies `psi_f` with monomial substitutions. Nguyen Theorem 1.2 states, for disintegrated `f,g`, that there exist `u in M_d`, `v in M_e` such that `psi_f(u(t))` and `psi_g(v(t))` are algebraically dependent over `K(t)` iff iterates of `f` and `g` are semiconjugate to a common polynomial. Theorem 1.3 gives the common-degree multi-polynomial version. This does not cover inverse-coordinate relations `P(z,phi_c1(z),phi_c2(z))=0`.

The proof mechanism also explains the mismatch: algebraic dependence of `psi_i(u_i(t))` creates an invariant hypersurface for the split polynomial map `(t^d,f_1,...,f_n)` and then invokes Medvedev-Scanlon. For inverse coordinates, substituting `z=psi_c1(t)` introduces the cross-transfer `H_12`, not a monomial substitution `u(t)`.

### Nguyen 2021/2022: exact product split used for pure product route

Nguyen's canonical-height paper summarizes the Medvedev-Scanlon classification as follows: if `f_1,...,f_m` are nonintegrable and `g_1,...,g_n` are integrable, then every preperiodic subvariety for the split map `(f_1,...,f_m,g_1,...,g_n)` is a product `V_1 x V_2` between the nonintegrable and integrable blocks. It further states that lower-dimensional preperiodic subvarieties in the nonintegrable block project to preperiodic curves, and such curves are parametrized by semiconjugacy data.

For this note, `M(z)=z^2` is integrable and `F_b(z)=z^2+b` is nonintegrable for `b notin {0,-2}`. Therefore any proof reducing `P(z,u_0,phi_b)=0` to a pure preperiodic curve under `(M,F_b)` is killed by this product split. But the actual target is not a pure product curve because `u_0` is a section of the skew affine extension `S_M(z,u)=(z^2,2zu-1)`.

### Xie 2022: values/products, not function-field inverse relations

Xie Theorem 1.10 concerns products of Böttcher-coordinate values `prod phi_fi(ai)^ni`: such a product is either transcendental over `K` or a root of unity, with the root-of-unity case characterized by geometric invariants of the pairs `(fi,ai)`. This is a value theorem, not a function-field theorem for relations `P(z,phi_c1(z),phi_c2(z))=0`.

### Baker-DeMarco: preperiodic unlikely intersections, not inverse-coordinate functions

Baker-DeMarco proves unlikely-intersection results for simultaneous preperiodicity and common preperiodic points. This is relevant background for special-fiber arithmetic, but it does not state algebraic independence of inverse Böttcher coordinate germs.

Current source-boundary verdict:

- `psi` local-conjugacy dependence: covered/search.
- products of Böttcher values and canonical-height algebraicity: covered/search.
- pure product invariant-curve route for `(z^2,z^2+b)`: covered/search-killed.
- inverse-coordinate function-field relation and skew mixed-map obstruction: not covered by the checked statements; status remains HOLD, not promoted.

## 2026-06-23 tangent/leak identity

The monomial-tangent function `u_0` is exactly the leak created by the failed `c1 -> 0` specialization descent.

Let `phi_c` and `psi_c` be inverse germs with

`phi_c(psi_c(t))=t`, `phi_0(z)=z`, `psi_0(t)=t`.

Differentiating at `c=0` gives

`(partial_c phi_c)|_{0}(t) + (partial_c psi_c)|_{0}(t) = 0`.

The earlier equation for `u_0` shows

`u_0(z) = (partial_c phi_c)(z)|_{c=0} = - (partial_c psi_c)(z)|_{c=0}`.

Thus the obstruction is endogenous to the inverse-Böttcher proof route: it is the tangent vector to the Böttcher deformation at the integrable monomial fiber, not an unrelated auxiliary lacunary function.

What is proved:

- `u_0` is transcendental over `C(z)` by the lacunary natural-boundary argument.
- `u_0` is the first-order parameter leak in the degenerate specialization stratum.

What is not proved:

- algebraic independence of `u_0` and `phi_b`;
- impossibility of every finite descent procedure;
- novelty/significance beyond a well-posed obstruction target.

## 2026-06-23 source card: skew mixed-map target

Target conjecture:

`For b notin {0,-2}, no nonzero P in Qbar(b)[z,U,Y] satisfies P(z,u_0(z),phi_b(z))=0.`

Equivalently, `u_0(z)` and `phi_b(z)` are algebraically independent over `Qbar(b,z)` for nonexceptional `b`.

### Nguyen 2013/2015, Theorems 1.2/1.3 and Question 6.2

Statement used: algebraic dependence of local conjugacies `psi_f(u(t))` with monomial substitutions is equivalent to a semiconjugacy/common-polynomial condition; the multi-polynomial common-degree case is analogous. Nguyen explicitly asks the inverse Böttcher coordinate problem as Question 6.2(a).

Mismatch: the target is not `psi_f(u(t))` with monomial substitutions. It is a mixed relation involving the tangent Mahler section `u_0` and the inverse Böttcher germ `phi_b`.

### Nguyen 2021/2022, Medvedev-Scanlon split quoted in proof of Theorem 1.4

Statement used: in split polynomial dynamics, preperiodic subvarieties for products containing nonintegrable factors and integrable factors split as products between those blocks; lower-dimensional nonintegrable-block subvarieties project to preperiodic curves governed by semiconjugacy.

Mismatch: this kills pure product dynamics for `(z^2,z^2+b)` but not the skew affine extension `S_M(z,u)=(z^2,2zu-1)`. The target is not an invariant curve in the pure product of the base maps.

### Xie 2022, Theorem 1.10

Statement used: products of Böttcher-coordinate values are either transcendental or roots of unity, with the root-of-unity case characterized by geometric invariants of the pairs `(f_i,a_i)`.

Mismatch: this is a value/product theorem. The target is function-field algebraic independence of germs `u_0(z)` and `phi_b(z)`.

### Baker-DeMarco 2011, Theorem 1.2 / Corollary 1.3

Statement used: common infinite preperiodic sets force equality of preperiodic sets / Julia-set consequences for rational maps.

Mismatch: the target is not about common preperiodic points. It is a relation between a Mahler tangent section and a Böttcher germ.

### Adamczewski-Faverjon, multivariate Mahler systems

Statement family used: linear Mahler systems in several variables, including sufficiently independent matrix transformations, with multivariate generalizations of Nishioka-type lifting theorems.

Mismatch: `u_0` is a linear Mahler function for `z -> z^2`, but `phi_b` satisfies a nonlinear Böttcher equation for `z -> z^2+b`, not a linear Mahler system for a matrix/power transformation. The map `z -> z^2+b` is not one of the pure Mahler transformations covered by these theorems.

### Dreyfus-Hardouin-Roques 2015, hypertranscendence of Mahler equations

Statement family used: parametrized difference Galois criteria for linear Mahler equations over `z -> z^p`, proving hypertranscendence/algebraic independence of Mahler solutions and derivatives under Galois hypotheses.

Mismatch: again, `u_0` fits a linear Mahler-type equation over `z -> z^2`, but `phi_b` is nonlinear and tied to the shifted map `z -> z^2+b`. The pair is not presented as a single linear Mahler system over one endomorphism.

Current source-card verdict:

- Search can kill if a theorem is found for skew affine extensions coupled to nonintegrable Böttcher germs.
- The checked theorem families do not currently cover the exact target.
- Absence of coverage does not promote the conjecture. Status remains `HOLD / source-gated target`.

## 2026-06-23 formal pullback obstruction lemma

Assume, toward the target conjecture, that

`P(z,u_0(z),phi_b(z))=0`

for some nonzero `P in Qbar(b)[z,U,Y]`, with `b notin {0,-2}`.

Let `U=u_0(z)` and `Y=phi_b(z)`.

### Pullback by the monomial map `M(z)=z^2`

Since

`u_0(z^2)=2z u_0(z)-1`,

pulling the relation back by `M` gives

`P(z^2, 2zU-1, phi_b(z^2))=0`.

The new term `phi_b(z^2)` is not controlled by the Böttcher equation unless `z^2` is of the form `w^2+b` for the same argument `w`; it is not. Thus the pullback by `M` exits the field `Qbar(b)(z,U,Y)` unless one adjoins `phi_b(z^2)`.

### Pullback by the quadratic map `F_b(z)=z^2+b`

Since

`phi_b(z^2+b)=phi_b(z)^2=Y^2`,

pulling the relation back by `F_b` gives

`P(z^2+b, u_0(z^2+b), Y^2)=0`.

The new term `u_0(z^2+b)` is not controlled by the Mahler equation `u_0(z^2)=2z u_0(z)-1`. Thus the pullback by `F_b` exits the field `Qbar(b)(z,U,Y)` unless one adjoins `u_0(z^2+b)`.

### Consequence

A pure invariant-curve argument cannot close inside `Qbar(b)(z,u_0,phi_b)`. Repeated pullbacks generate two cross-orbit families:

- `phi_b(M^n(z)) = phi_b(z^{2^n})`, uncontrolled by the `F_b` Böttcher equation;
- `u_0(F_b^n(z))`, uncontrolled by the `M` Mahler equation.

Therefore a valid proof needs one of:

1. a theorem showing these cross-orbit families are incompatible with algebraic closure unless `b=0` or `b=-2`;
2. a skew-product/difference-Galois framework that includes both pullbacks and proves rigidity;
3. a source reduction to an existing theorem whose hypotheses explicitly allow this mixed pair.

This is an obstruction lemma, not a proof of the conjecture. It formalizes why the direct one-map Mahler and pure product-dynamics approaches fail.

## 2026-06-23 natural-boundary continuation theorem candidate

Status: `HOLD / proof candidate`, with proof shape now materially stronger than the mixed-map pullback route. This is not promoted until source audit and peer vote clear.

Let

`U_0(x)=u_0(1/x)=sum_{n>=0} 2^{-(n+1)} x^{2^{n+1}-1}`.

The unit circle `|x|=1` is a natural boundary for `U_0`.

Conditional theorem candidate:

If the local Böttcher germ `phi_b` can be analytically continued, possibly as a chosen analytic branch, along a path from infinity to a point crossing `|z|=1`, and if `phi_b` is transcendental over `C(z)`, then `u_0(z)` and `phi_b(z)` are algebraically independent over `C(z)`.

Proof sketch:

Assume a nonzero relation

`P(z,u_0(z),phi_b(z))=0`

near infinity. Replace it by the minimal polynomial of `u_0` over the germ field `C(z,phi_b(z))` if the relation has positive degree in `u_0`. In characteristic zero this polynomial is separable, so away from the leading-coefficient/discriminant locus the branch representing `u_0` can be analytically continued wherever the chosen branch of `phi_b` can be continued. Choose the crossing point on `|z|=1` away from this discrete bad locus. Then the relation gives analytic continuation of `u_0`, equivalently of `U_0`, through a point of its natural boundary. Contradiction.

If the relation has degree zero in `u_0`, it is a relation `P(z,phi_b(z))=0`, contradicting transcendence of `phi_b` over `C(z)`.

Therefore no relation exists under the continuation-crossing hypothesis.

Corollary candidate for parameter region:

For `b` outside the Mandelbrot set, the critical orbit escapes and the filled Julia set `K_b` is a Cantor set with empty interior. Hence the basin of infinity `Omega_b=C\K_b` is connected and contains both large points and points with `|z|<1`; a path in `Omega_b` from infinity to such a point crosses `|z|=1` at a point in `Omega_b`. After avoiding the discrete branch/discriminant set, the conditional theorem applies. Since Becker--Bergweiler excludes algebraic Böttcher coordinates except the monomial/Chebyshev cases, and `b outside M` is nonexceptional, this gives the proposed theorem:

`For b outside the Mandelbrot set, u_0(z)` and `phi_b(z)` are algebraically independent over `C(z)`, hence over `Qbar(b,z)`.

Theatre-test caveats:

- This bypasses the mixed-map pullback obstruction rather than resolving it.
- The argument is classical analytic continuation plus natural boundary; it may be source/BRIDGE even if the exact mixed pair is not found in a quick search.
- The continuation hypothesis must be stated on the analytic-continuation surface of the Böttcher germ, not as global single-valuedness on the whole basin.
- The statement does not touch `b=0` or `b=-2`; both are controls where algebraic independence fails because `phi_b` is algebraic over `C(z)`.
- The remaining hard region is not simply `b in M`; it is the nonexceptional set where no continuation path from infinity crosses the `u_0` natural boundary at a regular point. This geometric condition needs separate classification.

## 2026-06-23 correction: disconnected-basin continuation gap

The previous corollary candidate `b outside M -> independence` overclaimed the continuation input.

External source check found the standard qualification: for unicritical polynomials, the Böttcher function extends analytically to the whole basin of infinity when the filled Julia set is connected; when the Julia set is disconnected, it extends only to the maximal nonsingular equipotential neighborhood of infinity

`Delta_b = { z : G_b(z) > G_b(0) }`,

where `G_b` is the Green function and `0` is the critical point. Equivalently, outside the Mandelbrot set the critical point lies in the basin and its Green height is the obstruction level. Thus basin connectedness and the existence of basin points inside `|z|<1` are not enough.

Corrected theorem candidate:

If there is a path in the analytic-continuation domain of the Böttcher germ from infinity to a point with `|z|<1`, crossing `|z|=1` at a point avoiding the discrete algebraic branch/discriminant locus, and if `phi_b` is transcendental over `C(z)`, then `u_0` and `phi_b` are algebraically independent over `C(z)`.

For disconnected quadratic Julia sets this gives the concrete sufficient condition

`exists |zeta|=1 such that G_b(zeta) > G_b(0)`

with a crossing into `|z|<1` inside `Delta_b`. Using `G_b(f_b(z))=2G_b(z)`, this is equivalently

`exists |eta|=1 such that G_b(b+eta) > G_b(b)`.

This condition is plausibly true on a nonempty open subset of `C\M` and likely for sufficiently large `|b|`, but that parameter-region estimate is not yet written. The earlier blanket claim for all `b outside M` is retracted.

Status remains `HOLD / proof candidate`, now with an exact geometric gate instead of a false basin-extension assumption.

## 2026-06-23 explicit large-parameter corollary candidate

The corrected Green-height gate gives an elementary explicit parameter region.

Let `B=|b|` and let

`R_B=(1+sqrt(1+4B))/2`.

If `|z|>R_B`, then

`|f_b(z)| >= |z|^2-B > |z|`,

so the orbit escapes. If `B>2+sqrt(2)`, then

`B-1 > R_B`.

Therefore the closed disk

`Dbar(b,1)={w: |w-b|<=1}`

lies in the basin of infinity. On this disk the Green function `G_b` is harmonic and nonconstant, so by the mean-value property there exists `|eta|=1` such that

`G_b(b+eta) > G_b(b)`.

Choose `zeta` with `zeta^2=eta`. Then `|zeta|=1` and

`G_b(zeta)=1/2 G_b(f_b(zeta))=1/2 G_b(b+eta) > 1/2 G_b(b)=G_b(0)`.

Thus `zeta` lies in the nonsingular Böttcher continuation domain

`Delta_b={G_b>G_b(0)}`,

and a small neighborhood of `zeta` in `Delta_b` crosses the natural-boundary circle `|z|=1` for `u_0`.

Combining this with the natural-boundary continuation theorem candidate gives:

`[THEOREM CANDIDATE] If |b|>2+sqrt(2), then u_0(z)` and `phi_b(z)` are algebraically independent over `C(z)`, hence over `Qbar(b,z)`.

Proof dependencies still to audit before promotion:

1. standard Böttcher-domain fact for disconnected unicritical maps: the germ extends analytically on `Delta_b={G_b>G_b(0)}`;
2. Becker--Bergweiler algebraicity exception list for `phi_b`;
3. source search for whether this exact natural-boundary/Böttcher mixed-pair independence is already recorded.

This is no longer a computation task. The theatre-test risk is novelty, not correctness of the large-parameter Green-height estimate.

## 2026-06-23 connected-parameter continuation corollary candidate

There is a second parameter region, again not yet promoted.

For `b in M`, `K_b` is connected and full, and the Bottcher coordinate extends through the whole basin of infinity. If the basin did not cross `|z|=1`, the unit circle would lie in `K_b`; fullness would then put the closed unit disk in `K_b`. Since monic polynomial filled Julia sets have logarithmic capacity `1`, and the closed unit disk also has capacity `1`, strict capacity monotonicity should force `K_b` to be the closed unit disk. Then `J_b` is the unit circle, and invariance under `z -> z^2+b` forces `|z^2+b|=1` for all `|z|=1`, hence `b=0`.

Thus, conjecturally as a written proof pending capacity-source details, for every connected nonzero parameter the basin crosses `|z|=1` in an arc. Combining with the natural-boundary continuation lemma gives a theorem candidate for

`b in M \ {0,-2}`,

where `b=-2` is excluded because the Bottcher coordinate is algebraic. Together with the large-parameter estimate, the current theorem candidate covers

`b in M \ {0,-2}` or `|b|>2+sqrt(2)`.

Status: `HOLD / proof candidate`; source audit and team proof attack still required.
