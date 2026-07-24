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

---

## Lean formalization progress (in-progress, multi-session)

**Route:** analytic-differential-algebra. Target = the full three-phase clock-character
classification `T=C<q>, ρ_λ(q)=λ^k q, Φ(q)=A(q)` with `A∈PGL_2(C)`; charge `k≥0`; `k>0 ⟹ Φ(q)=aq`.

### Already banked in corpus (REUSE — do not re-derive)
- `HTGeometry.StableDifferentialCore`: `stableRangeCore`, `stableRangeCoreAlgEquiv` (Φ is an
  automorphism of the core), `mem_stableRangeCore_iff`, `algebraMap_eigenvector_mem_stableRangeCore`,
  `adjoin_le_stableRangeCore_of_algebraMap_eigenvector` (eigen-current tail inclusion),
  `derivationClosed_stableRangeCore`.
- `HTGeometry.StableCoreFunctoriality`: `map_stableRangeCore_eq_of_commuting_algEquiv` (clock
  preserves the core — proof step §2), `stableRangeCoreDifferentialAlgEquiv`,
  `algHom_preserves_character_of_commuting`, `logDeriv_fixed_of_eigenvector` (charged current is
  Φ-fixed), `logDeriv_unit_character_of_semilinear` (clock weight of `Dq/q` is 1 — proof step §3 tail),
  `pow_fixed_of_eigenvector`, `deriv_pow_fixed_of_eigenvector`, `deriv_fixed_of_translation`.

### DONE this session
`HTGeometry/ClockChargeProjectiveLinearization.lean` [PROVED HERE], axioms
[propext, Classical.choice, Quot.sound], `lake build` clean, lint clean — the **charged-phase
projective-drift no-go** (§4 "positive charge linearizes the constraint", the crux the card brackets
as "classical transformation-group theory classifies cocharacters of PGL_2"):
- `mobius_scaling_coeffs` : coefficient no-go — Möbius matrix `(a b;c d)`, `ad−bc≠0`, intertwining a
  scaling by `μ≠0,1,−1` (the q²/q¹/q⁰ relations) ⟹ `c=0 ∧ b=0`. Pure field algebra
  (linear_combination on the three relations; `q²`→ac=0, `q¹`→bc=0, `q⁰`→bd=0; invertibility+bc=0 ⟹
  diagonal nonzero ⟹ c=b=0).
- `mobius_commuting_scaling_forces_diagonal` : the field-level version — intertwining identity
  `A(μq)=μA(q)` at `q` with `{1,q,q²}` linearly independent over `K` (= transcendence of the Lüroth
  generator, the honest hypothesis) ⟹ `c=0 ∧ b=0`. Coefficient extraction via
  `simp [map_*]` + `linear_combination hcomm`, then `mobius_scaling_coeffs`.
- `mobius_diagonal_eq_scaling` : diagonal Möbius = pure scaling `x↦(a/d)x` (holds unconditionally,
  even d=0, via junk-value `mul_div_right_comm`).

### REMAINING (next sessions) — two mathlib-gap cores
1. **Differential Lüroth / order-zero rigidity** (proof §1): an order-zero differential-rational
   automorphism of `C<q>` is a Möbius map of `q` — bridges the abstract `Φ|_T`/`ρ_λ` (algHom on the
   core) to the concrete `(a,b,c,d)` Möbius coefficients that `mobius_commuting_scaling_forces_diagonal`
   consumes. Needs: differential-order additivity (is `ord`/`differential transcendence degree`
   formalized? search `KolchinExchangeGaugeObstruction`, `ord`, `differentialOrder`) + Lüroth for the
   order-zero subfield. This is the connector that makes the no-go apply to the actual constraint.
2. **PGL_2 cocharacter classification** (proof §3): every algebraic homomorphism `G_m→PGL_2` is
   conjugate to `λ↦diag(1,λ^k)`, yielding the integer charge `k` and (with the diagonalizing
   conjugation) putting `ρ_λ` in the pure-scaling form that `mobius_commuting_scaling_forces_diagonal`
   requires (`ρ_λ(q)=λ^k q`). Concrete finite algebra (Jordan form over alg-closed C + commutation),
   not in mathlib.

### Assembly (final session)
`k=0` neutral branch (A∈PGL_2 arbitrary) vs `k>0` charged branch: feed the diagonalized clock
(`ρ_λ q = λ^k q`, `μ:=λ^k` ranges over `C^*∖{0,±1}` for suitable λ since k>0) + `Φ` commuting into
`mobius_commuting_scaling_forces_diagonal` ⟹ `Φ` diagonal ⟹ `mobius_diagonal_eq_scaling` ⟹ `Φ(q)=aq`;
uniqueness of `a` from `q≠0`. Then `logDeriv_fixed_of_eigenvector` + `logDeriv_unit_character_of_semilinear`
(banked) give the exact eigen-current invariant statement. NEXT concrete step: probe corpus for
differential-order / transcendence-degree infrastructure (`differentialOrder`, Kolchin) to start core #1.

### Session 2 progress
Corpus recheck (per reuse mandate) found §1 order-zero rigidity is ALREADY banked:
`HTGeometry.ScalarDifferentialRationalOrder.differentialAlgEquiv_generator_mem_adjoin_singleton`
(a differential automorphism σ of the scalar free field sends the generator into the ordinary
rational subfield `C(y)` in both directions — i.e. `σ y, σ⁻¹ y ∈ C(y)`), built on
`differentialAlgEquiv_generator_order_zero` + `hasScalarDifferentialOrder_zero_iff`. So proof §1
(`Φ(q₀)=A₀(q₀)`, `A₀` rational) is DONE up to "rational generator ⟹ Möbius", which is ordinary
Lüroth — confirmed NOT in mathlib (no `Luroth`, no fractional-linear RatFunc automorphism theory).

DONE this session — `HTGeometry/ClockChargeProjectiveLinearization.lean` extended, axioms
[propext, Classical.choice, Quot.sound], build+lint clean:
- **`charged_clock_forces_multiplicative`** : `C`-algebra endos `Φ, ρ` of `E`, `ρ q = μ q`
  (`μ ≠ 0,1,-1`), `Φ` acting by the Möbius relation `Φ q·(cq+d) = aq+b` (`ad−bc≠0`), commuting
  `Φ(ρq)=ρ(Φq)`, and `{1,q,q²}` `C`-linearly independent ⟹ `Φ q = (a/d)·q`. This is the card's
  §4/eq(4) headline (positive charge ⟹ multiplication by one constant), assembled from the no-go.
  Key step: the abstract commutation `Φρ=ρΦ` yields the cross-multiplied intertwining identity
  `(aμq+b)(cq+d) = μ(aq+b)(cμq+d)` with NO denominators (apply ρ to the Möbius relation, use
  `ρ(Φq)=μΦq`, then `linear_combination` eliminating `Φq`), which `mobius_commuting_scaling_forces_diagonal`
  collapses to `c=b=0`, then `mobius_diagonal_eq_scaling`.

Discharge status of the §-structure:
- §1 order-zero: banked (mem_adjoin_singleton) — gap: ordinary Lüroth `C(y)`-generator ⟹ Möbius (a,b,c,d∈C).
- §4 charged linearization crux: DONE (no-go + charged_clock_forces_multiplicative), Möbius/scaling as hyps.
- §3 cocharacter `ρ_λ q = λ^k q`, integer charge k: PGL₂-cocharacter classification (finite algebra, mathlib gap).
- §2 clock preserves core: banked (`map_stableRangeCore_eq_of_commuting_algEquiv`).

NEXT concrete step (session 3): ordinary Lüroth bridge — `z ∈ C(y)` with `C(z)=C(y)` ⟹ `∃ a b c d ∈ C,
ad−bc≠0, z=(ay+b)/(cy+d)`. This feeds hΦq of `charged_clock_forces_multiplicative` from the banked
`σy ∈ C(y)`. Needs mathlib RatFunc degree theory: `z` generates `C(y)` ⟹ `[C(y):C(z)]=1` ⟹ the minimal
polynomial of `y` over `C(z)` has degree 1 ⟹ Möbius. Probe `Mathlib.FieldTheory.RatFunc.*`,
`IntermediateField.adjoin`, `Polynomial.degree`, transcendence-degree. This is the classical piece; build it
as `HTGeometry/OrdinaryLuroth.lean` (reusable, general). Then PGL₂ cocharacter as `HTGeometry/Pgl2Cocharacter.lean`.

### Session 3 progress — ordinary Lüroth (mathlib-gap fill)
Corpus recheck: mathlib HAS `Mathlib.FieldTheory.RatFunc.Luroth` (Lüroth's theorem) +
`RatFunc.finrank_eq_max_natDegree` (`[K⟮X⟯:K⟮f⟯] = max(deg num, deg denom)`) + `RatFunc.Degree`
(intDegree). My earlier `#check @Luroth` failed only because I used the wrong name.

DONE — `HTGeometry/OrdinaryLuroth.lean` [PROVED HERE], axioms [propext, Classical.choice, Quot.sound],
build+lint clean:
- `ratFunc_generator_max_natDegree_eq_one` : `f` generates `K⟮X⟯` (`adjoin K {f} = ⊤`) ⟹
  `max(deg num, deg denom) = 1` — via `finrank_eq_max_natDegree` + `IntermediateField.finrank_top`.
- **`ratFunc_generator_mobius`** : `f` generates `K⟮X⟯` ⟹ `∃ a b c d : K, ad−bc≠0 ∧
  f·(C c·X + C d) = C a·X + C b`. The degree-1 Lüroth / "generating rational function is Möbius"
  fact (NOT in mathlib as a corollary). num,denom linear from max-deg-1; `ad−bc≠0` by ruling out
  `f` constant (else `f ∈ ⊥`, contradicting `adjoin K {f}=⊤` via `intDegree X = 1 ≠ 0 = intDegree (C e)`).

Core #1 status: order-zero rigidity (banked `differentialAlgEquiv_generator_mem_adjoin_singleton`,
gives `σy ∈ C(y)`) + rational-generator-⟹-Möbius (DONE this session, in RatFunc). REMAINING for core #1:
the TRANSPORT bridge — the abstract differential subfield `C(y) = IntermediateField.adjoin C {y} ⊆ E`
(y hypertranscendent, so transcendental) is `C`-algebra-isomorphic to `RatFunc C` via `y ↦ X`; under
it `σy ∈ C(y)` generating ⟺ its `RatFunc C` image generates, so `ratFunc_generator_mobius` yields the
Möbius coefficients `a,b,c,d ∈ C` and the relation `σy·(c·y+d)=a·y+b` in `E`. This is what feeds
`charged_clock_forces_multiplicative`'s `hΦq`. 

NEXT concrete step (session 4): the transport. Probe mathlib for `simple transcendental extension ≅
RatFunc`: `IntermediateField.adjoin` of a transcendental element, `Transcendental`,
`IsFractionRing`, `Polynomial.aeval`/`RatFunc` evaluation iso. Likely `IntermediateField.adjoin C {y}`
with `Transcendental C y` gives an `AlgEquiv` to `RatFunc C` (search `Transcendental.aevalEquiv` /
`IsTranscendenceBasis` / `RatFunc`-adjoin). Then push `ratFunc_generator_mobius` across it. Then §3
PGL₂ cocharacter remains for the clock's `ρ_λ q = λ^k q` diagonalization.
