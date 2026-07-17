# Scalar persistent hypertranscendence has a quantized clock character

- **ID:** `scalar-ht-persistent-clock-character-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every nonconstant persistent core of a clock-neutral injective constraint on a
  scalar free differential field carries a canonical nonnegative integer projective-generator
  charge; at positive charge the constraint is multiplication by one constant on a homogeneous
  core generator.

## Goal

Classify what the clock itself permits to survive an indefinitely repeated scalar constraint.  The
result is intrinsic to hypertranscendental fields.  It does not select a special function and has no
RH hypothesis.

## Theorem

Let `C` be an algebraically closed field of characteristic zero, equipped with the zero derivation.
Let `y` be a differential indeterminate and put

```text
F = C<y> = C(y,y',y'',...).
```

For `lambda in C^*`, let `rho_lambda` be the clock-dilation automorphism of the underlying field,

```text
rho_lambda(y^(j)) = lambda^j y^(j).
```

It is semilinear for the derivation:

```text
rho_lambda(Da) = lambda D(rho_lambda(a)).                 (1)
```

Let `Phi:F->F` be an injective differential `C`-endomorphism which commutes with every
`rho_lambda`, and define

```text
T = intersection_(n>=0) Phi^n(F).
```

If `T != C`, then there are a differential transcendental `q in T`, a unique integer
`k>=0`, and a projective transformation `A in PGL_2(C)` such that

```text
T = C<q>,
rho_lambda(q) = lambda^k q,                               (2)
Phi(q) = A(q).                                            (3)
```

The integer `k` is independent of the diagonalizing generator `q`.  More precisely it is the
absolute cocharacter of the induced clock action on the projective line of differential Luroth
generators.

The integer `k` is not the least clock weight occurring anywhere in `T`.  When `k>0`, the
logarithmic current `Dq/q` has weight one; in fact differential closure saturates the raw character
lattice.  The invariant measured by `k` is the projective charge needed to reconstruct a full
differential generator, and in geometric examples it records finite reconstruction holonomy.

There are exactly two non-erased clock phases.

1. **Neutral phase (`k=0`).**  The core has a clock-invariant projective coordinate and `Phi` may
   act by an arbitrary element of `PGL_2(C)`.
2. **Charged phase (`k>0`).**  There is a unique `a in C^*` such that

   ```text
   Phi(q)=a q.                                             (4)
   ```

Thus a positive-charge persistent scalar cannot support nonlinear projective drift.  It is an
exact relative invariant, or eigen-current, of the constraint.

If `T=C`, the phase is **erased** and has no clock charge.

## Proof

### 1. The core is a scalar free field with projective constraint dynamics

The stable-core projective theorem gives

```text
T=C<q_0>
```

for some differential transcendental `q_0`, and proves that `Phi|_T` is a differential
automorphism.  Differential-order additivity applied to this automorphism and its inverse forces
both generator changes to have order zero.  Hence

```text
Phi(q_0)=A_0(q_0),  A_0 in PGL_2(C).                      (5)
```

### 2. Clock dilation preserves the core exactly

Since `rho_lambda Phi = Phi rho_lambda`, it also commutes with every iterate.  Therefore

```text
rho_lambda(Phi^n(F))=Phi^n(F)
```

for every `n`, and hence `rho_lambda(T)=T`.  This exact equality, including the reverse inclusion,
is Lean-formalized by `map_stableRangeCore_eq_of_commuting_algEquiv`.

Put `v_lambda=rho_lambda(q_0)`.  Equation (1) shows

```text
rho_lambda(C<q_0>)=C<v_lambda>.
```

Since the left side equals `T`, both `q_0` and `v_lambda` are differential rational functions of
the other.  Differential-order additivity for the two inverse substitutions gives

```text
0=ord(q_0)=ord(v_lambda as a function of q_0)
             + ord(q_0 as a function of v_lambda).
```

Both orders vanish.  Thus `C(q_0)=C(v_lambda)`, so there is a unique
`M_lambda in PGL_2(C)` satisfying

```text
rho_lambda(q_0)=M_lambda(q_0).                            (6)
```

### 3. The projective clock action is an algebraic cocharacter

The clock action is algebraic on every finite jet field: on
`C(y,...,y^(m))` it is the diagonal algebraic action with weights `0,...,m`.  The element `q_0`
belongs to one such field.  Equation (6) says that its rational subfield `C(q_0)` is stable under
this action.  The induced rational action on its projective model `P^1` is therefore algebraic.
Equivalently,

```text
lambda |-> M_lambda
```

is an algebraic homomorphism `G_m -> PGL_2`.

Every cocharacter of `PGL_2` is conjugate to

```text
lambda |-> [diag(lambda^r,1)]
```

for a unique integer `r` up to sign.  Replace `q_0` by a Mobius transform and, if necessary, by
its reciprocal.  With `k=|r|`, this gives (2).  The kernel is `mu_k` when `k>0`, while the action is
trivial when `k=0`; consequently `k` is intrinsic.

### 4. Positive clock charge linearizes the constraint

Write `Phi(q)=A(q)` as in (3).  Commutation with clock dilation and (2) give

```text
A(lambda^k q)=lambda^k A(q)                              (7)
```

for every `lambda in C^*`.  Since `C` is algebraically closed and `k>0`, the values `lambda^k`
exhaust `C^*`.  Hence `A(tq)=tA(q)` for every `t in C^*`.  A rational self-map of `P^1` with this
equivariance is `q |-> a q`; taking `q=1` in the rational identity determines `a`, and
invertibility gives `a!=0`.  This proves (4).

## Complete scalar clock phase law

Together with positive-differential-order erasure, the theorem gives a universal three-phase law
for scalar clock-neutral constraints:

```text
erased:   T=C;
neutral:  T=C<q>, clock charge 0, projective reversible dynamics;
charged:  T=C<q>, clock charge k>0, multiplicative eigen-current dynamics.
```

For a degree-expanding rational substitution `Phi(y)=R(y)`, the separate complete rational-tail
classification eliminates the neutral branch and restricts the charged branch to the
crystallographic set

```text
k in {1,2,3,4,6}.
```

Those integers are not inserted into the universal theorem.  They arise from the finite holonomy
of the parabolic orbifold forced by rational self-covering.

## No-go and positive residue

**No-go.**  A positive-charge persistent scalar cannot carry a generic `PGL_2` action, a nonlinear
return law, or a continuously variable clock weight.

**Positive theorem.**  Every such survivor has an intrinsic integer charge and is an exact
one-dimensional character of both clock dilation and the constraint.  This supplies a canonical
observable attached to the persistent core rather than merely ruling the core out.

## Significance

This is the first characteristic-class-type invariant of a scalar persistent
hypertranscendental phase.  It converts the metaphor of an observable clock into a classification:
infinite differential freedom can survive an algebraic constraint only through a quantized
projective clock representation.  At positive charge the entire infinite-depth observable field
is generated by one eigen-current.

The short universal theorem is strong enough to organize a paper when combined with the rational
orbifold classification and the higher-rank symbol-descent conjecture.  By itself it is a concise
structural theorem, not yet a Fields-scale classification.

## External novelty gate

The novelty comparison is only against external literature.

- Ritt--Kolchin differential Luroth supplies the scalar generator.  Effective versions bound and
  compute such generators; they do not study intersections of iterated images.
- Classical differential algebra supplies differential-order additivity.
- Classical algebraic transformation-group theory classifies cocharacters of `PGL_2`.
- Reparametrization-invariant jet-differential theory studies weighted jet invariants, and
  differential invariant theory studies fields fixed by changes of derivation.  These theories do
  not impose an indefinitely iterated constraint or classify its persistent differential field.
- Rational `G_m`-action theory identifies integer gradings of ordinary function fields.  It does
  not derive a clock character on a differential stable core.
- Targeted searches for stable intersections of iterated differential-field images, persistent
  differential tails, and semilinear clock actions found no statement of the theorem above.

The candidate-new delta is the chain

```text
iterated constraint -> stable differential core -> projective clock action
                    -> canonical integer charge -> eigen-current rigidity.
```

Because several parents are classical and the proof is short, the novelty label remains
`CANDIDATE` pending specialist database and expert review.  That caution is an external-literature
gate, not a comparison with this project's prior work.

## Higher-rank open core

`[CONJECTURE — CLOCK-SYMBOL DESCENT]` Let a clock-neutral dominant algebraic constraint act on a
finite-rank free differential field.  Every minimal-order element of a nonconstant persistent core
has, after a finite equivariant cover, a nonzero homogeneous principal symbol.  The nonzero clock
characters of these symbols generate a lattice of flat logarithmic tensors on a maximal
semiabelian/log-Calabi--Yau factor; the zero-character quotient is the maximal reversible
birational factor.  The persistent core is the differential field generated by these two factors.

This conjecture would turn the scalar integer `k` into a higher-rank clock-character lattice and
would imply the maximal-special-factor classification of algebraic HT tails.  The exact open point
is symbol extraction from an arbitrary higher-order persistent observable; no existing
log-Calabi--Yau structure theorem supplies it.

## RH pressure test

There is no RH conclusion.  If a completed-zeta constraint system were ever constructed, the
theorem predicts that any scalar persistent observable shared by the different obstruction
representations would have a definite clock charge.  Spectral, monodromy, positivity,
continuation, and boundary-condition models could represent one object only if their candidate
observables induce the same charge.  This is a falsifiable compatibility test, not an RH proof.

## Lean status

The exact invariant-core step is formalized as

```text
map_stableRangeCore_eq_of_commuting_algEquiv
```

in `formal/GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean`.  It proves that a commuting
algebra equivalence maps the stable range core exactly to itself.  The file verifies directly from
the existing cache.

`formal/GaloisForLFunctions/HTGeometry/ScalarLogCurrentReconstruction.lean` now formalizes the
positive-charge current layer: the logarithmic current of a nonzero free scalar is itself
hypertranscendental and nonconstant, the full scalar differential field is reconstructed from its
current field plus one ordinary amplitude, and every positive power has the same current field.
The current-field equality is formalized in the sharper characteristic-free form requiring only
that the exponent have nonzero image in the coefficient field.

`formal/GaloisForLFunctions/HTGeometry/RatFuncScaleFixedField.lean` formalizes the complete
ordinary fixed-field law for that amplitude coordinate: a scalar of finite order `N` fixes exactly
`K(X^N)`, while a scalar of infinite order fixes exactly `K`.  The action is constructed as a
faithful algebra automorphism and its order is proved exactly.

The differential-Luroth, order-additivity, and algebraic-cocharacter parents are not yet available
in this Lean toolchain, and the rational-coordinate action has not yet been transported across the
differential current-field reconstruction, so the card remains at stage 2.  No axiom, `sorry`,
`opaque`, or unsafe placeholder is used for them.

## Gates

- [x] 0 -> 1 in-progress: exact theorem, falsifier, and external parent boundary identified
- [x] 1 -> 2 fully-proven: complete proof with every classical parent isolated
- [x] positive-charge current hypertranscendence and one-amplitude reconstruction formalized
- [x] ordinary finite- and infinite-order scalar fixed fields formalized
- [ ] 2 -> 3 formalized: import differential Luroth/order theory and formalize projective
  cocharacter classification
- [ ] 3 -> 4 publication-ready: specialist external novelty audit and standalone exposition

## Primary literature checked

- J. F. Ritt and E. R. Kolchin, differential Luroth theorem.
- L. D'Alfonso, G. Jeronimo, P. Solerno, *Effective Differential Luroth's Theorem*, Journal of
  Algebra 406 (2014), 1--19.
- U. Bekbaev, *On the field of differential rational invariants of a subgroup of affine group
  (ordinary differential case)*, 2006.
- G. Berczi, F. Kirwan, *A geometric construction for invariant jet differentials*, 2010.
- A. Dubouloz, A. Liendo, *On rational multiplicative group actions*, 2022.

## Log

- 2026-07-15 -- proved the scalar clock-character law, passed the preliminary external-literature
  novelty gate, and formalized exact invariance of the stable core under commuting symmetries.
- 2026-07-17 -- formalized the positive-charge logarithmic-current field and its exact scalar
  reconstruction law.
- 2026-07-17 -- formalized the faithful rational-coordinate scalar action and both sides of its
  finite/infinite holonomy fixed-field dichotomy.
