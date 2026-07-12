# Entire first-order shadow-recovery rigidity

- **ID:** `entire-first-order-shadow-recovery-rigidity`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; composition constraints
- **Statement:** A transcendental entire first-order outer function never hides any state of an entire DA inner derivative shadow.

## Goal

Classify the remaining compression mechanism after primitive visibility has been removed. The proved two-defect bridge gives

`ord_DA(f o g)=ord_DA(g)+1-aut(f)pi(g)-lambda_f(g).`

The open question is whether the global entire category forces

`lambda_f(g)=0`.

If so, minimal differential order under every first-order entire cap would obey the exact law

`ord_DA(f o g)=ord_DA(g)+1-aut(f)pi(g).`

This would make the derivative-shadow signature a complete composition-cost invariant for first-order entire outer constraints.

## Candidate moves

1. `[CONJECTURE]` **Entire matching rigidity.** Every positive-dimensional algebraic foliation of the composition state that is invariant under the total derivation and invisible to the output forces a global entire right-inverse or a nontrivial entire deck family; either alternative is impossible outside the autonomous primitive compression already removed.
2. `[CONJECTURE]` **Variational matching obstruction.** If an invisible tangent derivation sends `g` to `xi`, then differentiating `h=f(g)` forces the matching equation `D(f'(g)xi)=0`. Show that a nonzero algebraic solution `xi` compatible with the inner state constraint forces `f'` to be algebraic over `C(f)`.
3. `[CONJECTURE]` **Nevanlinna foliation collapse.** A nonzero invisible derivation produces an algebraic one-parameter family of inner states with the same entire composite. Use growth separation to show that such a family must come from input translation of an autonomous outer equation.
4. `[CONJECTURE]` **Counterexample route.** Construct a nonautonomous entire first-order `f` and an entire DA `g` whose inner variational equation contains `1/f'(g)`. If the resulting matching integrates globally, then `lambda_f(g)>0` and the rigidity conjecture is false.

## Evidence already proved

- `[PROVED]` If the outer constraint is autonomous, `lambda_f(g)=0` for every transcendental entire DA `g`; primitive compression is already accounted for separately.
- `[PROVED]` If `g` is first-order DA, the universal Wiman/Bell theorem gives `lambda_f(g)=0` for every first-order entire `f`.
- `[PROVED]` For the primitive Gaussian input, `f(w)=w exp(w)` has `lambda_f(g)=0`; breaking autonomy restores the primitive state.
- `[PROVED]` Local-germ inverses destroy the claim, so global entireness is essential rather than decorative.
- `[BRIDGE]` Newton-corner observability gives broad nonautonomous subclasses with zero defect.
- `[PROVED]` If `g` is a minimal solution of a linear order-two equation `g''=qg'+pg` with `p!=0`, then every genuinely nonautonomous first-order entire outer has `lambda_f(g)=0`. The proof is separated in `2-fully-proven/not_new_scientific_knowledge/nonautonomous-cap-linear-order-two-shadow-rigidity.md`.

## Attack

### Parent reduction

Wang--Sontag identifies differential-equation order with observable realization dimension, and Isidori--Krener--Gori-Giorgi--Monaco describes cascade loss through partial dynamical matching. Those theories name `lambda_f(g)` but do not appear to prove its vanishing from global entireness.

### Fake proof and exact failure

Let `V` be an invisible derivation commuting with `D`, and put `xi=V(g)`. From `V(h)=0` and

`h'=f'(g)g'`

one obtains formally

`D(f'(g)xi)=0`.

Hence

`f'(g)xi=c`.

The tempting conclusion is that `xi` is constant, forcing `f'(g)` to depend only on `h` and making the outer equation autonomous. This is valid when the inner state over its derivative shadow is a pure primitive extension, because a commuting derivation fixing the shadow sends `g` to a constant. It fails for a general higher-order inner state: its variational equation may admit a nonconstant algebraic solution `xi=c/f'(g)`.

`[OPEN CORE]` Exclude such a matched variational solution using global entire-function geometry, or construct one and falsify the conjecture.

### Order-two matching normal form

`[PROVED]` For an order-two inner state `Dg=v`, `Dv=R(z,g,v)` and outer derivative branch `A(g,h)`, the three-jet determinant vanishes exactly when

`R_g-u(vR_v-R)=v^2(u^2-u_g-Au_h)`, `u=A_g/A`.

The proof and the complete separable solution are recorded in `2-fully-proven/not_new_scientific_knowledge/order-two-shadow-matching-normal-form.md`.

If `A(g,h)=alpha(g)beta(h)`, every matched inner equation has the form

`R=-u(g)v^2+alpha(g)^(-1)F(z,alpha(g)v)`.

Thus the transformed velocity

`w=alpha(g)g'`

satisfies the first-order ADE `w'=F(z,w)`, while a local primitive `Psi` with `Psi'=1/beta` satisfies

`(Psi(f(g)))'=w`.

The open core in this separable stratum is the global entire factorization

`Phi(g)=integral w`, `Phi'=alpha`.

`[PROVED]` A zero-free finite-order primitive is itself first-order: Hadamard factorization makes it an exponential of a polynomial. This closes the direct `Phi=id` subcase. A nonaffine factorization `W=Phi o g` remains open even when `W` is zero-free.

`[SEARCH]` Liao--Yang's pseudo-primality theorem for finite-order entire second-order ADE solutions reduces `W=Phi o g` to the rational outer-factor exception whenever `g` is transcendental entire. The first live ramified case is quadratic:

`W=a+g^2`, `W'=w` first-order DA, `ord_DA(W)=2`.

Equivalently, can a primitive-defect-one primitive of a first-order entire DA function have a totally ramified finite value?

`[PROVED]` Not when `w` is autonomous. Writing `w=L(exp(az))`, a primitive-defect-one primitive has nonzero drift under the period `2 pi i/a`. One totally ramified value would then generate infinitely many, contradicting Nevanlinna. The proof is separated in `2-fully-proven/not_new_scientific_knowledge/drifting-periodic-primitive-ramification-exclusion.md`.

`[PROVED]` No rational outer-factor exception survives when a primitive `W` has nonzero polynomial shift drift. The divided difference of `P(g_T)-P(g)` and Hadamard theory force the inner factor into an algebraic extension of a one-hyperexponential first-order field; a unique-pole substitution handles rational outers. This covers every `w=L(exp(cz))+P(z)` and is separated in `2-fully-proven/not_new_scientific_knowledge/polynomial-drift-rational-outer-factor-rigidity.md`.

`[PROVED]` No quadratic factor survives an affine reflection `W o sigma=C-W`. This covers the nonautonomous derivative `w=z sin z`, whose primitive `sin z-z cos z` is odd. See `2-fully-proven/not_new_scientific_knowledge/involutive-reflection-quadratic-rigidity.md`.

### Boundary cases

- Polynomial outer functions are excluded: their order is zero and they can collapse states algebraically.
- Meromorphic logarithmic outers are excluded: they can match multiplicative inner symmetries.
- Autonomous transcendental entire outers are not counterexamples: their one primitive compression is already the explicit `aut(f)pi(g)` term.
- The smallest unresolved stratum is a genuinely nonautonomous first-order entire outer and a nonlinear order-two inner with `pi(g)=0`.

## Strongest next lemma

`[CONJECTURE]` Let `w` be a genuinely nonautonomous transcendental entire first-order DA function and `W` an entire primitive with primitive defect one. Then `W` has no totally ramified finite value. Equivalently, there do not exist `a in C` and a transcendental entire `g` with `W=a+g^2`.

This quadratic ramification statement is the first nontrivial case not settled by primitive-extension, pseudo-primality, linear order-two, or first-order Wiman arguments.

## RH pressure test, not selector

If shadow-recovery rigidity holds, any canonical finite DA approximation built from first-order entire caps has a completely controlled differential-order ledger. An RH application would still require an independently defined zeta/xi approximation and a positivity or reflection constraint; the theorem would only guarantee that no hidden derivative-shadow compression invalidates the order count.

No Euler, divisor, translation-spectrum, or zero-localization claim is made here.

## Gates

- [x] 0 -> 1: exact invariant and counterexample target isolated.
- [x] Parent observability theory identified.
- [x] Autonomous, first-order-inner, Newton-corner, and local-inverse boundaries classified.
- [x] Linear order-two inner stratum proved rigid.
- [x] Exact nonlinear order-two matching PDE and separable normal form proved.
- [x] Direct zero-free primitive subcase excluded.
- [x] Autonomous first-order derivative subcase excluded by period drift.
- [x] Laurent-exponential-plus-polynomial derivative subcase excluded by polynomial drift.
- [x] Affine-reflection quadratic subcase excluded.
- [ ] Prove or falsify the second-order variational matching lemma.
- [ ] Literature audit only after the mathematical core moves beyond standard cascade observability.
- [ ] Lean after a finite algebraic lemma survives; current formal infrastructure already covers primitive affine actions and algebraic primitive descent.

## 2026-07-12 Attack residue on the quadratic ramification lemma

Target: `w` genuinely nonautonomous transcendental entire first-order DA, `W' = w`, `W` of
primitive defect one; exclude `W = a + g^2` with `g` transcendental entire. Write
`P(z, X, Y) = 0` for the minimal ADE of `w`, `D = deg_(X,Y) P`, `N = deg_z P`. WLOG `X` does not
divide `P` (else divide out: `w` is not identically zero).

`[PROVED SKETCH]` **Finitely many zeros of `g` collapse the defect.** If `g` has finitely many
zeros, then by Hadamard (Gol'dberg gives `w`, hence `W`, hence `g`, finite order)
`g = R e^Q` with `R, Q` polynomials, so `(W-a)'/(W-a) = 2Q' + 2R'/R` is rational and `W`
satisfies a first-order rational linear ADE, contradicting defect one. Hence `g` has infinitely
many zeros; each zero of multiplicity `m` is a zero of `w` of odd order `2m-1` and an `a`-point
of `W` of order `2m`.

`[PROVED SKETCH]` **Multiple zeros pin the origin of the curve.** At a zero of `g` of
multiplicity `m >= 2`, `(w, w')(z_0) = (0, 0)`, so `P(z_0, 0, 0) = 0`. Infinitely many multiple
zeros force `P(z, 0, 0) = 0` identically.

`[CONJECTURE]` **Newton-polygon multiplicity bound.** Along a zero of multiplicity `m`, the
solution germ has `w ~ t^(2m-1)`, `w' ~ t^(2m-2)`. Substituting into `P(z_0+t, w, w') = 0`, the
minimal `t`-order among monomials `c_(ij)(z_0+t) X^i Y^j` must be attained twice:
`(2m-1)(i-i') + (2m-2)(j-j') = v' - v` with `|i-i'|,|j-j'| <= D`, `|v'-v| <= N`. Unless the
matching pair has `i+j = i'+j'` (a diagonal block of the Newton polygon, where the condition
degenerates to `i - i' = v' - v` independently of `m`), this forces `2m-2 <= N + D`, a uniform
multiplicity bound. Open sub-case: diagonal-block ADEs.

`[PROVED SKETCH]` **Simple zeros ride one algebraic branch.** At a simple zero `z_n` of `g`,
`(w, w')(z_n) = (0, 2 g'(z_n)^2)`, so `P(z_n, 0, 2g'(z_n)^2) = 0`. Since `P(z, 0, Y)` is not
identically zero, the values `2 g'(z_n)^2` lie on the algebraic curve `P(z, 0, Y) = 0`; by
pigeonhole one algebraic branch `Y = phi(z)` carries infinitely many of them:
`2 g'(z_n)^2 = phi(z_n)`. Equivalently `W'' = phi(z)` at infinitely many `a`-points of `W`.

`[OPEN CORE — sharpened]` Drive the branch constraint to a contradiction with genuine
nonautonomy. Obstruction found: the auxiliary function `H = W'' - phi - (lower ADE terms)`
vanishes identically precisely in the Riccati stratum `w' = a_0 + a_1 w + a_2 w^2` (there
`phi = a_0` is the ADE's own section, so the constraint is a tautology). The decisive test case
is therefore: **does a genuinely nonautonomous Riccati with rational coefficients admit an entire
transcendental solution `w = 2 g g'` with `g` entire and `int w` of defect one?** The Riccati
linearization `w = -u'/(a_2 u)` with `u'' - (a_1 + a_2'/a_2) u' + a_0 a_2 u = 0` puts the
question inside classical second-order linear theory, where the banked linear-order-two rigidity
(`p != 0` stratum) already applies to the inner state; what is missing is the bridge from that
rigidity to the ramification statement for the primitive.

Next move: settle the Riccati test case by combining the linearization with the banked
`nonautonomous-cap-linear-order-two-shadow-rigidity` mechanism; if it survives there, attack the
diagonal-block Newton case, which is the only escape from bounded multiplicities.
