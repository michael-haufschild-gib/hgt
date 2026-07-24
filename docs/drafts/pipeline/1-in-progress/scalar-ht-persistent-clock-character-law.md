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

### Session 4 progress — the transport bridge (core #1 essentially COMPLETE)
Corpus recheck: mathlib HAS `RatFunc.algEquivOfTranscendental (y) (h : Transcendental C y) :
RatFunc C ≃ₐ[C] C⟮y⟯` with `_X : φ X = y` — exactly the transcendental-extension iso.

DONE — `HTGeometry/TranscendentalMobius.lean` [PROVED HERE], axioms
[propext, Classical.choice, Quot.sound], build+lint clean:
- `ratFuncEval (y) (hy : Transcendental C y) : RatFunc C →ₐ[C] E` := `(adjoin C {y}).val ∘ φ` —
  evaluation at `y`; `ratFuncEval_injective`, `ratFuncEval_X` (`↦ y`), `ratFuncEval_C` (`↦ algebraMap`).
- **`adjoin_generator_mobius`** : `y` transcendental over `C`, `z ∈ C(y)`, `y ∈ C(z)` ⟹
  `∃ a b c d : C, ad−bc≠0 ∧ z·(algebraMap c·y + algebraMap d) = algebraMap a·y + algebraMap b`.
  The abstract-field degree-1 Lüroth. Generation transported at the E-level (NO subfield gymnastics):
  `g := φ.symm ⟨z,hz⟩` generates `RatFunc C` because `X ∈ adjoin C {g} ⟺ y ∈ adjoin C {z}` via
  `ratFuncEval` injective + `IntermediateField.adjoin_map` + `mem_map`; then `ratFunc_generator_mobius g`
  and push the relation through `ratFuncEval` (`X↦y`, `C c↦algebraMap c`).

**CORE #1 COMPLETE (modulo trivial wiring):** the banked
`differentialAlgEquiv_generator_mem_adjoin_singleton σ …` gives `σy ∈ C(y)` and `σ⁻¹y ∈ C(y)`; the
latter, hit with σ (AlgEquiv preserves adjoin), gives `y ∈ C(σy)`. Feeding `z:=σy`, these two
memberships into `adjoin_generator_mobius` yields the §1 Möbius relation `Φ(q₀)=A₀(q₀)` in E with
`a,b,c,d ∈ C`, `ad−bc≠0` — the `hΦq` hypothesis of `charged_clock_forces_multiplicative` (session 2).
So the §1→§4 charged path is fully assembled from banked+new lemmas, modulo the `Transcendental C y`
extraction (banked `hypertranscendentalOver_jet_transcendental`) and forming the σ-commutation.

REMAINING: §3 PGL₂ cocharacter — the clock `ρ_λ` gives `ρ_λ q₀ = M_λ(q₀)` (another
`adjoin_generator_mobius` application, ρ_λ semilinear but adjoin-preserving), and classifying the
1-parameter family `λ ↦ M_λ` as `diag(1,λ^k)` (integer charge k). NEXT session: assemble the §1→§4
charged theorem end-to-end (wire banked σ-result + adjoin_generator_mobius + charged_clock_forces_multiplicative)
as `clock_charge_charged_multiplicative` in the differential framework; then tackle §3 cocharacter.

### Session 5 progress — §1 wired end-to-end + §1→§4 charged assembly
`HTGeometry/ClockCharacterSigmaMobius.lean` [PROVED HERE], axioms [propext, Classical.choice, Quot.sound],
build+lint clean, both theorems first-try:
- **`differentialAlgEquiv_generator_mobius`** (§1 fully wired): a differential automorphism `σ` of the
  scalar free field `C⟨y⟩` acts on the generator by a Möbius transform — `∃ a b c d : C, ad−bc≠0 ∧
  σy·(algebraMap c·y+algebraMap d) = algebraMap a·y+algebraMap b`. Reuses banked
  `differentialAlgEquiv_generator_mem_adjoin_singleton` (σy, σ⁻¹y ∈ C(y)) + `adjoin_generator_mobius`
  (session 4). `y ∈ C(σy)` from `σ⁻¹y ∈ C(y)` via `IntermediateField.adjoin_map` + `mem_map`;
  `Transcendental C y` via banked `hypertranscendentalOver_jet_transcendental hy 0`.
- **`differentialAlgEquiv_generator_multiplicative`** (§1→§4 charged, modulo §3): `σ` differential
  automorphism + clock `ρ` with `ρ y = μ y` (μ≠0,1,−1, the §3-diagonalized cocharacter) commuting
  with σ ⟹ `∃ e : C, σ y = algebraMap e · y` — the card's headline §4/eq(4) conclusion in the
  differential framework. Assembles `differentialAlgEquiv_generator_mobius` (hΦq) +
  `charged_clock_forces_multiplicative` (session 2). `hlin` ({1,y,y²} lin indep) derived from
  `transcendental_iff_injective` + coeff extraction.

Card §-structure discharge: §1 (DONE), §2 (banked), §4 charged linearization (DONE session 2),
§1→§4 charged assembly (DONE this session, modulo §3 pure-scaling hyp). 

REMAINING — §3 PGL₂ cocharacter (the LAST mathlib-gap core): produce `ρ_λ q₀ = λ^k q₀` (the `hρy`
hypothesis of `differentialAlgEquiv_generator_multiplicative`) with integer charge k. The clock
`ρ_λ` (semilinear, jet-order-preserving) acts on the core generator q₀ by a Möbius `M_λ` (another
degree-1 Lüroth application — but ρ_λ is semilinear not differential, so needs a semilinear
order-zero variant OR the jet-filtration-preservation argument: ρ_λ maps jetObservableField n to
itself since ρ_λ(y^(j))=λ^j y^(j)); then `λ ↦ M_λ` is a 1-parameter algebraic subgroup of PGL₂,
classified (Jordan form over alg-closed C + commutation) as conjugate to `diag(1,λ^k)`, and choosing
q₀ as the diagonalizing generator gives ρ_λ q₀ = λ^k q₀. NEXT session: the finite PGL₂ cocharacter
algebra — a 1-param subgroup `μ ↦ Möbius M_μ` of PGL₂(C) (M_μ M_ν = M_{μν}, algebraic) is conjugate
to a pure scaling; build as `HTGeometry/Pgl2Cocharacter.lean` (finite matrix/Möbius algebra, mathlib gap).

### Session 6 progress — the §3→§4 interface (eq (2) family form)
`HTGeometry/ClockChargeFamilyMultiplicative.lean` [PROVED HERE], axioms
[propext, Classical.choice, Quot.sound], build+lint clean:
- `exists_pow_ne_one_ne_neg_one` : over `[IsAlgClosed C]`, for `k>0`, `∃ λ≠0, λ^k≠1 ∧ λ^k≠−1` — the
  `k`-th power map isn't confined to `{1,−1}` (bad set = finite root sets of `X^k∓1` ∪ {0}, and
  `IsAlgClosed C ⟹ Infinite C ⟹` complement nonempty). Reusable.
- **`clock_charge_family_multiplicative`** : the card's exact §3-output interface — clock family
  `ρ_λ y = λ^k y` (k>0, the eq (2) cocharacter) with each `ρ_λ` commuting with `σ` ⟹ `∃ e, σ y = e·y`
  (§4). Picks a single `λ` with `λ^k ∉ {0,1,−1}` (the card's "λ^k exhaust C*" step) and applies
  `differentialAlgEquiv_generator_multiplicative` (session 5).

Card §-structure: §1 (done), §2 (banked), §4 charged linearization (session 2), §1→§4 charged
assembly (session 5), §3→§4 eq(2)-interface (this session). The charged branch is now FULLY
formalized GIVEN eq (2) `ρ_λ q₀ = λ^k q₀`.

REMAINING — the single genuine deep core: PRODUCING eq (2), i.e. the PGL₂-cocharacter diagonalization.
Input: the clock family {ρ_λ} acting on the core C(q) by Möbius maps `M_λ` with `M_λ M_ν = M_{λν}`,
`M_1 = id`, algebraic in λ. Output: a Möbius change of generator `q₀ = A(q)` and integer `k≥0` with
`ρ_λ q₀ = λ^k q₀`. Sub-pieces for next sessions:
 (3a) ρ_λ acts on C(q) by a Möbius `M_λ`: ρ_λ is SEMILINEAR (not differential), but jet-order-preserving
   (ρ_λ(y^(j))=λ^j y^(j) maps jetObservableField n→n), so `σy`-style order-zero rigidity has a
   semilinear analog — OR derive directly that ρ_λ preserves C(q₀) (banked `map_stableRangeCore_eq_of_commuting_algEquiv`
   already gives ρ_λ(T)=T) then `adjoin_generator_mobius` gives the Möbius form (needs ρ_λ q, ρ_λ⁻¹ q ∈ C(q)).
 (3b) the diagonalization: a commuting algebraic 1-param family of Möbius maps has a common eigenvector
   (fixed point on P¹); at it the family is a character χ:C*→C*; χ algebraic (Laurent monomial) ⟹ χ(λ)=λ^k.
   This is the PGL₂-torus-cocharacter classification (mathlib gap — matrices/fixed points). Build as
   `HTGeometry/Pgl2Cocharacter.lean`. Start with the field-formulation: `μ ↦ (a(μ),b(μ),c(μ),d(μ))` Möbius
   coeffs rational in μ, homomorphism law, extract common eigenvector.

### Session 7 progress — the automorphism-level Möbius engine (enables §1 and §3a)
`HTGeometry/TranscendentalMobius.lean` extended + `ClockCharacterSigmaMobius.lean` refactored;
axioms [propext, Classical.choice, Quot.sound], build+lint clean:
- **`algEquiv_generator_mobius_of_mem`** : ANY `C`-algebra automorphism `σ` of `E` with
  `σ y ∈ C(y)` and `σ.symm y ∈ C(y)` (i.e. `σ` preserves the ordinary rational subfield `C(y)`),
  `y` transcendental ⟹ `σ y` is Möbius in `y`. This is the automorphism-level engine underlying
  BOTH the differential constraint (§1) and the semilinear clock (§3a): the ONLY input is
  preservation of `C(y)` — no differential/semilinear structure. `differentialAlgEquiv_generator_mobius`
  (§1) now routes through it (memberships from banked order-zero rigidity).

REMAINING — two deep cores (both genuine mathlib/corpus gaps, clock-dilation ρ_λ + jet-preservation
NOT banked; verified by search):
 (3a) **semilinear clock Möbius form**: need `ρ_λ q₀ ∈ C(q₀)` and `ρ_λ.symm q₀ ∈ C(q₀)` to feed
   `algEquiv_generator_mobius_of_mem`. Route: ρ_λ (clock-dilation, `ρ_λ y^(j) = λ^j y^(j)`) is a
   C-algebra field automorphism (fixes C) that is SEMILINEAR for D (`ρ_λ(Da)=λ D(ρ_λ a)`), hence
   PRESERVES the jet filtration `jetObservableField C y n` (it scales each jet `y^(j)↦λ^j y^(j)`, and
   `λ^j` are units so `adjoin C {y,...,y^(n)}` is preserved) ⟹ order-preserving ⟹ `ρ_λ` maps the
   order-0 generator `q₀` to an order-0 element ∈ `C(q₀)`. Needs: (i) DEFINE the clock ρ_λ (a
   `C ≃* (E ≃ₐ[C] E)` family, or per-λ automorphism with `ρ_λ y^(j)=λ^j y^(j)` — NOT banked, build
   it); (ii) `ρ_λ (jetObservableField C y n) = jetObservableField C y n`; (iii) semilinear analog of
   banked `HasScalarDifferentialOrder.map` (the banked one assumes differential `hderiv`; adapt to
   `ρ(Da)=λ D(ρ a)`). Then §3a done via the engine.
 (3b) **PGL₂ cocharacter classification** (the diagonalization producing eq (2)): from ρ_λ Möbius
   `M_λ` with `M_λ M_ν = M_{λν}`, `M_1=id`, algebraic in λ ⟹ ∃ Möbius change `q₀↦A(q₀)` and integer k
   with `ρ_λ (A q₀) = λ^k (A q₀)`. Core sub-facts: (i) the commuting Möbius family has a common
   eigenvector/fixed point on P¹ (over alg-closed C); (ii) at it the eigenvalue is a character
   χ:C*→C*; (iii) an ALGEBRAIC character χ (rational-function `χ(μν)=χ(μ)χ(ν)`) is `χ(μ)=μ^k` (the
   "multiplicative rational function is a monomial" fact — self-contained, reusable, mathlib gap).
   NEXT session: start (3b-iii) as `HTGeometry/MultiplicativeMonomial.lean` (RatFunc functional
   equation ⟹ monomial), the cleanest self-contained piece; then (3a) clock definition.

Charged branch fully formalized modulo eq (2) [sessions 2,5,6]; §1 engine + interface complete [session 7].

### Session 8 progress — (3b-iii) algebraic character is a monomial
`HTGeometry/MultiplicativeMonomial.lean` [PROVED HERE], axioms [propext, Classical.choice, Quot.sound],
build+lint clean:
- **`multiplicative_polynomial_eq_X_pow`** : over `[IsAlgClosed C]`, a nonzero polynomial `P` with
  `P(xy) = P(x)P(y)` equals `X^(deg P)`. This is the positive-charge case of "algebraic character of
  `G_m` is `λ^k`" — the eigenvalue of a diagonalized PGL₂ cocharacter (§3). Proof: `P(1)=1` (from
  `P(1)=P(1)²` + `zero_of_eval_zero`); every root is 0 (a nonzero root `r` forces `P≡0` since
  `P(r·s)=P(r)P(s)=0` on all of `C`); `P` splits (`IsAlgClosed.splits`), roots-all-0 ⟹
  `P = C(lead)·X^n` (`Splits.eq_prod_roots` + `Multiset.map_const'`/`prod_replicate` +
  `splits_iff_card_roots`); `lead = P(1) = 1`.

§3 sub-piece status: (3b-iii) monomial character DONE. Connects to `exists_pow_ne_one_ne_neg_one`
(session 6): `P = X^k` with `k>0` ⟹ `∃λ, P.eval λ = λ^k ∉ {0,1,−1}` — the exact value feeding
`clock_charge_family_multiplicative`. 

REMAINING §3 pieces: (3b-i,ii) the DIAGONALIZATION — from the clock's commuting Möbius family
`{M_λ}` (`M_λ M_ν = M_{λν}`) extract a common eigenvector/fixed point `q₀` on which `ρ_λ q₀ = χ(λ) q₀`
(pure scaling), with χ the algebraic character (then `multiplicative_polynomial_eq_X_pow` ⟹ `χ=λ^k`).
This is PGL₂ fixed-point theory: a non-identity Möbius map has fixed points (roots of `c q² +
(d−a) q − b = 0` over alg-closed C), the commuting family shares them, conjugating to {0,∞}
diagonalizes. NEXT session: (3a) the semilinear-clock Möbius form (define clock ρ_λ + jet-preservation
+ semilinear order-zero) OR (3b-i) the Möbius fixed-point / common-eigenvector lemma. Both are
substantial mathlib gaps; (3b-i) fixed-point analysis is likely the cleaner self-contained next piece
(`HTGeometry/MobiusFixedPoint.lean`: a Möbius map `≠ id` over alg-closed C has a fixed point).

### Session 9 progress — the diagonalization payoff (Möbius with 2 fixed points is a scaling)
`HTGeometry/MobiusDiagonalization.lean` [PROVED HERE], axioms [propext, Classical.choice, Quot.sound],
build+lint clean:
- `mobius_fixed_point_difference` : a fixed point `p` (root of `c p²+(d−a)p−b=0`) of the Möbius map
  `σq·(cq+d)=aq+b` gives `σ(q−p)·(cq+d) = (a−cp)·(q−p)` — the map sends the fixed-point difference
  to a scalar multiple. (Key algebra: `b − p·d = −p(a−cp)` from the fixed-point quadratic.)
- **`mobius_two_fixed_points_scaling`** : with two fixed points `p₁, p₂`, in the fixed-point
  coordinate `x = (q−p₁)/(q−p₂)` the map is a PURE SCALING `σ x = ((a−cp₁)/(a−cp₂))·x`. This is the
  diagonalization step of §3(b): once the clock's Möbius family shares a fixed-point pair, each ρ_λ
  acts diagonally `ρ_λ x = χ(λ)·x`, and `multiplicative_polynomial_eq_X_pow` (session 8) ⟹ `χ(λ)=λ^k`,
  giving eq (2). (`a−cp₂≠0` derived from `σ(q−p₂)≠0`+`cq+d≠0`; ratio via `div_div_div_cancel_right₀`.)

§3(b) status: monomial character (session 8) + diagonalization payoff (this session) DONE. The
diagonalized `ρ_λ x = χ(λ) x` now assembles: χ multiplicative (from ρ_λρ_μ=ρ_{λμ}) + algebraic ⟹
(monomial lemma) χ=λ^k ⟹ (family theorem, session 6) σ x = e·x.

REMAINING §3 pieces:
 (3b-i) COMMON FIXED POINTS existence: the clock family {M_λ} shares a fixed-point pair p₁≠p₂. Route:
   fixed-point quadratic `c_λ p²+(d_λ−a_λ)p−b_λ` has roots over alg-closed C (a non-parabolic M_λ has 2
   distinct roots); commuting family preserves the root set; C* divisible ⟹ no swap ⟹ common. Needs
   the torus/non-parabolic property (M_λ diagonalizable since G_m-cocharacter).
 (3a) SEMILINEAR CLOCK Möbius form: `ρ_λ q₀ ∈ C(q₀)` (feeds `algEquiv_generator_mobius_of_mem`,
   session 7) via jet-order preservation (`ρ_λ y^(j)=λ^j y^(j)`). Needs clock definition + semilinear
   order-zero.
NEXT session: (3b-i) fixed-point existence (`HTGeometry/MobiusFixedPoint.lean`: fixed-point quadratic
has a root over alg-closed C; then the commuting-family common-fixed-point argument). This + the
diagonalization + monomial completes the pure §3(b) chain (modulo (3a) getting the Möbius family).

### Session 10 progress — fixed-point existence + non-parabolic⟹scaling connector
`HTGeometry/MobiusFixedPoint.lean` [PROVED HERE], both theorems axioms
[propext, Classical.choice, Quot.sound], `lake build GaloisForLFunctions.HTGeometry.MobiusFixedPoint`
clean (1919 jobs), lint passed:
- **`mobius_two_distinct_fixed_points`** : over an alg-closed field of char 0, if `c ≠ 0` and the
  discriminant `(d−a)²+4cb ≠ 0`, the Möbius fixed-point quadratic `c p²+(d−a)p−b` has TWO DISTINCT
  roots. Explicit quadratic formula: square root `δ` of the discriminant from
  `IsAlgClosed.exists_pow_nat_eq (·) (n:=2)`, roots `(−(d−a)±δ)/(2c)`; distinctness from `δ≠0`
  (⟸ disc≠0); each root verified via `field_simp` + `linear_combination hδ` (the `c` cancels in the
  common denominator `4c`, so coefficient is 1 not c). Char-0 needed for `2c ≠ 0`.
- **`mobius_nonparabolic_scaling`** : the CONNECTOR — composes `mobius_two_distinct_fixed_points` with
  session-9 `mobius_two_fixed_points_scaling`. A `C`-algebra automorphism `σ` acting on `q` by a
  Möbius transform with `c≠0`, nonzero discriminant, both denominators nonzero (`q` outside `C`) is a
  PURE SCALING in the fixed-point coordinate `x=(q−p₁)/(q−p₂)`: `σ x = ((a−cp₁)/(a−cp₂))·x`, with the
  two distinct fixed points produced internally. The two §3(b) modules are now wired end-to-end.

§3(b) status: single-map chain COMPLETE for the non-parabolic case — Möbius (§1) + non-parabolic
fixed-point existence (this session) + diagonalization (session 9) ⟹ each ρ_λ is a scaling
`ρ_λ x = χ(λ)·x`; then monomial (session 8) ⟹ χ=λ^k; then family theorem (session 6) ⟹ σ x = e·x.

REMAINING §3 pieces:
 (3b-i-common) COMMON fixed points across the family: `mobius_nonparabolic_scaling` diagonalizes ONE
   ρ_λ. For the family to share a SINGLE coordinate `x`, the fixed-point PAIR must be common to all
   ρ_λ. Route: commuting maps permute each other's fixed-point sets; C* divisible / connected torus ⟹
   the permutation is trivial (no swap) ⟹ common pair. Next module `HTGeometry/MobiusCommonFixedPoint.lean`:
   two commuting non-parabolic Möbius maps with the SAME fixed-point pair (or: a commuting map fixes
   the other's fixed points setwise, and no-swap ⟹ pointwise). Formalize "commuting ⟹ shared fixed set".
 (3b-nonparabolic) the clock ρ_λ (λ≠1) IS non-parabolic (disc≠0): a G_m-cocharacter is semisimple.
   Currently an input hypothesis to `mobius_nonparabolic_scaling`; discharge from the torus structure.
 (3a) SEMILINEAR CLOCK Möbius form: `ρ_λ q₀ ∈ C(q₀)` (feeds `algEquiv_generator_mobius_of_mem`,
   session 7) via jet-order preservation. Needs clock definition + semilinear order-zero.
NEXT session: (3b-i-common) `HTGeometry/MobiusCommonFixedPoint.lean` — two commuting Möbius maps share
a fixed-point pair (fixed set is preserved by a commuting map; no-swap from divisibility). This closes
the "common coordinate" gap so the whole family diagonalizes in ONE `x`, completing §3(b) end-to-end.

### Session 11 progress — §3(b) capstone: the clock family is a multiplicative scaling character
`HTGeometry/ClockScalingCharacter.lean` [PROVED HERE], all three theorems axioms
[propext, Classical.choice, Quot.sound], `lake build GaloisForLFunctions.HTGeometry.ClockScalingCharacter`
clean + full `GaloisForLFunctions.HTGeometry` umbrella builds (10726 jobs). (My-cone lint clean; a
separate lint "owned module unreachable" error is an unrelated parallel-agent RHTower file
`ReverseBesselFixedFrequencyBlindness.lean`, not mine — left untouched per independence rule.)

KEY REALIZATION (corpus check): the (3b-i) "common fixed point / shared coordinate" step needs NO new
Möbius machinery — session 2's `charged_clock_forces_multiplicative` IS it. With `Φ := ρ_λ` (another
clock member, Möbius on the generator) and `ρ := ρ_{ν₀}` (the anchor scaling from sessions 9-10), it
forces `ρ_λ q = e_λ q` in the SAME coordinate. So the whole commuting family diagonalizes
simultaneously — no separate permutation/no-swap argument at the coordinate level.

Delivered:
- `commuting_with_scaling_is_scaling` : ∃-form packaging — a Möbius endo `Ψ` commuting with an anchor
  scaling `ρ₀ q = ν q` (ν∉{0,1,-1}) is a scaling `∃ e, Ψ q = e·q`. Thin wrapper of
  `charged_clock_forces_multiplicative` (witness `a/d`), the reusable common-coordinate interface.
- **`scaling_character_multiplicative`** : if `ρ_λ q = e(λ) q` for all λ and the family is a
  homomorphism at q (`ρ_{λμ} q = ρ_λ(ρ_μ q)`), then `e(λμ) = e(λ)e(μ)`. Proof pushes `ρ_λ` through the
  scaling `ρ_μ q = e(μ)q` via `map_mul`+`AlgHom.commutes`, cancels `q≠0` (`mul_right_cancel₀`) and the
  injective `algebraMap` (`map_eq_zero` in the narrow cone; `FaithfulSMul`/`RingHom.injective` NOT in cone).
- **`commuting_family_scaling_character`** : the §3(b) CAPSTONE — a clock family that is a homomorphism
  at q, each member Möbius on the generator + commuting with an anchor scaling ρ_{ν₀} q = ν q
  (ν∉{0,1,-1}), with 1,q,q² independent, yields `∃ e:C→C, (∀λ, ρ_λ q = e(λ)·q) ∧ (∀λμ, e(λμ)=e(λ)e(μ))`.
  Builds `e` by `choose` over `commuting_with_scaling_is_scaling`, multiplicativity from
  `scaling_character_multiplicative`. The whole cocharacter is now a SINGLE multiplicative character.

§3(b) chain status: §1 Möbius → anchor diagonalization (sessions 9,10) → simultaneous family
diagonalization + multiplicative character `e:C→C` (this session) → [GAP: e is POLYNOMIAL] → monomial
lemma (session 8) e(λ)=λ^k → family theorem (session 6) σ y = e·y. The output shape here
(`∀λ, ρ_λ q = e(λ)q`) already matches the `hρ` interface of `clock_charge_family_multiplicative`
(session 6) MODULO identifying e(λ)=λ^k.

REMAINING (the one genuine analytic/algebraic gap left in §3(b)):
 (3b-poly) BRIDGE `e:C→C` multiplicative-and-ALGEBRAIC ⟹ e is a POLYNOMIAL character (then session 8's
   `multiplicative_polynomial_eq_X_pow` gives e=X^k, i.e. e(λ)=λ^k). This is the classification of
   algebraic characters of G_m. e is algebraic because ρ_λ depends algebraically on λ (the cocharacter
   is a morphism of varieties). Formalize: a multiplicative `e:C→C` that agrees with a rational/poly
   map ⟹ monomial. Candidate next module `HTGeometry/AlgebraicCharacterMonomial.lean`.
 (3a) SEMILINEAR CLOCK Möbius form (`ρ_λ q₀ ∈ C(q₀)`) — still open, feeds `hmob` above.
NEXT session: (3b-poly) `HTGeometry/AlgebraicCharacterMonomial.lean` — multiplicative + polynomial
character of C* is X^k. Start from `multiplicative_polynomial_eq_X_pow` (session 8, already done) and
add the bridge from a multiplicative FUNCTION e:C→C that IS given by a polynomial to the eval-form
`P(xy)=P(x)P(y)` hypothesis, discharging `commuting_family_scaling_character`'s `e` into `e(λ)=λ^k`.

### Session 12 progress — (3b-poly) bridge + CHARGED BRANCH end-to-end
`HTGeometry/AlgebraicCharacterMonomial.lean` [PROVED HERE], all three theorems axioms
[propext, Classical.choice, Quot.sound], `lake build GaloisForLFunctions.HTGeometry.AlgebraicCharacterMonomial`
clean (3041 jobs), `formal_tools.py lint` PASSED (RHTower unreachable-module error from session 11 now
resolved upstream; only pre-existing large-file warnings remain).

Delivered:
- `multiplicative_eval_eq_pow` : over alg-closed C, a multiplicative `e:C→C` GIVEN BY a nonzero
  polynomial (`e(λ)=P(λ)`) is `e(λ)=λ^k`, k=deg P. Direct bridge: e mult ⟹ P mult
  (`P(xy)=P(x)P(y)`) ⟹ (session 8 `multiplicative_polynomial_eq_X_pow`) P=X^deg ⟹ eval = λ^deg.
- **`charged_clock_family_pow`** : EQUATION (2). A clock family scaling `q` by a nonzero polynomial
  character `ρ_λ q = P(λ)·q` and homomorphic at q gives `ρ_λ q = λ^k·q` (k=deg P). Multiplicativity of
  P.eval from session 11 `scaling_character_multiplicative`, monomial from session 8. This is exactly
  the `hρ` interface of session 6 `clock_charge_family_multiplicative`.
- **`charged_clock_polynomial_forces_multiplicative`** : the CHARGED BRANCH, END-TO-END. σ differential
  automorphism, ρ clock cocharacter homomorphic at y with polynomial character `ρ_λ y = P(λ)·y`
  (0<deg P = positive charge), commuting with σ ⟹ `∃ e:C, σ y = e·y`. Chains eq(2) into session 6.
  (y≠0 from `hypertranscendentalOver_jet_transcendental hy 0` + `isAlgebraic_zero`; hcomm matches
  session 6's `σ.toAlgHom` form verbatim.)

MILESTONE: the CHARGED PHASE (§4, k>0) of the clock-character law is now formalized end-to-end from a
polynomial-character input. Full charged chain, all [PROVED HERE], all standard axioms:
  §1 Möbius (`differentialAlgEquiv_generator_mobius`, s5/7)
  → anchor diagonalization (`mobius_nonparabolic_scaling`, s9/10)
  → simultaneous family diagonalization + multiplicative character (`commuting_family_scaling_character`, s11)
  → polynomial character ⟹ λ^k = eq(2) (`charged_clock_family_pow`, THIS session)
  → charged rigidity σ y = e·y (`clock_charge_family_multiplicative`, s6;
    assembled as `charged_clock_polynomial_forces_multiplicative`, THIS session).

REMAINING GAPS (the inputs still hypothesized, to discharge for the fully-unconditional card):
 (A) §3a: `ρ_λ q ∈ C(q)` — the clock acts Möbius on the generator (feeds `hmob` of
   `commuting_family_scaling_character`). Via semilinear jet-order-zero + Lüroth, PARALLEL to §1's
   `differentialAlgEquiv_generator_mobius` but for the clock endomorphism ρ_λ. Needs the clock/
   semilinear-order definition in the differential framework.
 (B) The "character is polynomial" hypothesis (`hpoly_scale : ρ_λ y = P(λ)·y` with P a polynomial):
   this is the ALGEBRAICITY of the cocharacter (ρ_λ depends algebraically on λ, a morphism of
   varieties). Currently an input; discharge requires modeling the algebraic family structure.
 (C) The anchor `ν∉{0,1,-1}` existence for a nontrivial cocharacter (session 6's
   `exists_pow_ne_one_ne_neg_one` already gives it ONCE k is known; before that it is the
   nondegeneracy of positive charge).
NEXT session: (A) §3a — `HTGeometry/ClockSemilinearMobius.lean`: the clock endomorphism ρ_λ acts by a
Möbius transform on the generator, mirroring `differentialAlgEquiv_generator_mobius` (s5/7) but for a
semilinear (jet-scaling) clock. Reuse `algEquiv_generator_mobius_of_mem` (s7) if ρ_λ is invertible on
C(q); else build the endomorphism analogue. This discharges `hmob`, the last GEOMETRIC input to §3(b).

### Session 13 progress — (A) §3a foundation: semilinear jet covariance + order rigidity
`HTGeometry/SemilinearJetCovariance.lean` [PROVED HERE], all theorems standard axioms
([propext, Quot.sound] for the jet law; +Classical.choice for the field/order ones),
`lake build GaloisForLFunctions.HTGeometry.SemilinearJetCovariance` clean (3030 jobs). (My-cone lint
clean; a separate lint "owned module unreachable" error is an unrelated parallel-agent RHTower file
`XiWardEdgeImChannelGram`, not mine.)

REALIZATION: the clock ρ_λ is SEMILINEAR (`ρ_λ(w′) = λ·(ρ_λ w)′`), NOT a differential automorphism,
so `differentialAlgEquiv_generator_order_zero` (which needs exact D-commutation `hderiv`) does NOT
apply. But the semilinear map STILL preserves scalar differential order: the n-th jet transforms with
weight λ^n, and since λ^n∈C* are nonzero constants they are absorbed into field generation. So the
whole covariance/order machinery goes through with the semilinear map — this is the missing engine.
(`DifferentialLinearChangeAutomorphism` is the MATRIX change that commutes with D — a different object,
not the clock.)

Delivered (semilinear analogues of `differentialJet_algHom` / `jetObservableField_map_algHom` /
`HasScalarDifferentialOrder.map`):
- `differentialJet_semilinear` : `e(differentialJet n z) = algebraMap C E (λ^n) · differentialJet n (e z)`
  for a semilinear `e` (`e w′ = algebraMap λ · (e w)′`, λ a differential constant `(algebraMap λ)′=0`).
  Induction on n; Leibniz `Derivation.leibniz` + `(algebraMap(λ^n))′=0` (private helper
  `algebraMap_pow_deriv_zero`); pow_succ' to fold λ·λ^n.
- **`jetObservableField_map_semilinear`** : `(jetObservableField C x N).map e = jetObservableField C (e x) N`.
  The λ^n weights are absorbed via mutual `adjoin_le_iff` inclusion (each generator differs by a nonzero
  C-scalar, invertible since λ≠0). This is the KEY lemma — identical CONCLUSION to the differential
  `jetObservableField_map_algHom`, so it drops straight into the order argument.
- **`HasScalarDifferentialOrder.map_semilinear`** : a semilinear clock preserves exact order,
  `HasScalarDifferentialOrder C y z n → HasScalarDifferentialOrder C (e y) (e z) n`. Verbatim copy of
  `.map`'s proof with the semilinear field lemma substituted.

§3a status: with order-preservation for the semilinear clock now in hand, the order-zero reduction
(`ρ_λ q₀ ∈ C(q₀)`) is a near-copy of `differentialAlgEquiv_generator_order_zero` (s?) using
`.map_semilinear` in place of `.map`. That + `algEquiv_generator_mobius_of_mem` (s7) gives §3a Möbius.

NEXT session: (A) §3a completion — `HTGeometry/ClockSemilinearOrderZeroMobius.lean`: prove the clock
ρ_λ (an AlgEquiv, semilinear, with `hsemi`, hconst, λ≠0, and generating hypertranscendental y) sends
the generator by an order-zero rational function (`HasScalarDifferentialOrder C y (ρ_λ y) 0` both
directions) — copy `differentialAlgEquiv_generator_order_zero` swapping `.map`→`.map_semilinear`,
`hderiv`→`hsemi` (the `hm.map σ.toAlgHom hderiv` step becomes `hm.map_semilinear ... hsemi`) — then feed
`algEquiv_generator_mobius_of_mem` to get `ρ_λ y` Möbius, discharging `hmob` of
`commuting_family_scaling_character` (s11). That closes the last GEOMETRIC input to §3(b).

### Session 14 progress — (A) §3a COMPLETE: clock is Möbius on the generator
`HTGeometry/ClockSemilinearOrderZeroMobius.lean` [PROVED HERE], both theorems axioms
[propext, Classical.choice, Quot.sound], `lake build GaloisForLFunctions.HTGeometry.ClockSemilinearOrderZeroMobius`
clean (3037 jobs). (My-cone lint clean + my module reachable in umbrella; a separate lint
"owned module unreachable" error is an unrelated parallel-agent HTGeometry file
`FisherOneCornerCoareaTransform`, not mine — left untouched per independence rule.)

Delivered (the payoff of session 13's semilinear covariance):
- `clockSemilinearAlgEquiv_generator_order_zero` : a semilinear clock dilation σ (`σ w′ = λ·(σ w)′`,
  λ≠0, `(algebraMap λ)′=0`) of a scalar free differential field sends the generator, both directions,
  by order-zero rational functions: `HasScalarDifferentialOrder C y (σ y) 0 ∧ ...(σ.symm y)... 0`.
  VERBATIM copy of `differentialAlgEquiv_generator_order_zero` with the single map step
  `hm.map σ.toAlgHom hderiv` → `hm.map_semilinear σ.toAlgHom hlam hconst hsemi` (session 13). Compiled
  first try — confirms the semilinear order machinery drops in exactly where the differential one sat.
- **`clockSemilinearAlgEquiv_generator_mobius`** : §3(a). The clock σ acts Möbius on the generator,
  `σ y·(c y+d) = a y+b`, ad−bc≠0, a,b,c,d∈C. Order-zero ⟹ `σ y, σ⁻¹ y ∈ C(y)`
  (`hasScalarDifferentialOrder_zero_iff`) ⟹ `algEquiv_generator_mobius_of_mem` (s7). This is the exact
  analogue of §1 (`differentialAlgEquiv_generator_mobius`) for the CLOCK. It discharges `hmob` of
  `commuting_family_scaling_character` (s11): each clock element is Möbius on the generator.

§3(b) GEOMETRIC/ALGEBRAIC CHAIN now COMPLETE as hypothesis-fed theorems (all [PROVED HERE], std axioms):
  §1 Möbius (constraint, s5/7) · §3a Möbius (clock, THIS session, discharges hmob)
  · anchor diagonalization (s9/10) · family diagonalization+multiplicative character (s11)
  · polynomial character ⟹ λ^k = eq(2) (s12) · charged rigidity σ y = e·y (s6, assembled s12).

REMAINING for the FULLY-unconditional card (all about the CONCRETE clock/cocharacter object, not the
abstract chain):
 (B) ALGEBRAICITY: `hpoly_scale : ρ_λ y = P(λ)·y` with P a polynomial (the cocharacter varies
   algebraically in λ). Still an input to `charged_clock_family_pow` (s12).
 (C) CONCRETE CLOCK: the framework's jet-scaling clock actually satisfies hsemi (`σ w′ = λ (σ w)′`),
   hconst (`(algebraMap λ)′=0`, λ∈C constant), λ≠0, and commutes with the constraint — currently
   hypotheses. Needs the concrete semilinear-clock automorphism (jet-dilation) defined + its
   semilinearity proven. `stableRangeCoreSymmetryAlgEquiv` (StableCoreFunctoriality) is the §2
   core-restriction to reuse.
 (D) TOP-LEVEL ASSEMBLY into the card's main statement (k charge, k>0 ⟹ Φ q₀ = a q₀).
NEXT session: assemble §3a into s11 — `HTGeometry/ClockFamilyScalingCharacterFromSemilinear.lean`:
a commuting semilinear clock FAMILY (each ρ_λ an AlgEquiv, hsemi with factor λ, homomorphic at y,
anchor ρ_{ν₀} a scaling with ν∉{0,1,-1}) yields the multiplicative scaling character `e:C→C`, by
feeding `clockSemilinearAlgEquiv_generator_mobius` (THIS session) as `hmob` into
`commuting_family_scaling_character` (s11). This discharges the last GEOMETRIC input and assembles the
family-level §3(b) from clock hypotheses alone.

### Session 15 progress — nonzero-index monomial bridge (clock is indexed by C^*)
`HTGeometry/MultiplicativeMonomialNonzero.lean` [PROVED HERE], both theorems axioms
[propext, Classical.choice, Quot.sound], `lake build ...MultiplicativeMonomialNonzero` clean (1919 jobs),
`formal_tools.py lint` PASSED.

REALIZATION (blocking the naive family assembly): the clock is genuinely indexed by C^* — a
factor-0 semilinear map `σ w′ = 0·(σ w)′ = 0` annihilates every derivative, impossible for an
injective AlgEquiv. So the clock's scaling/Möbius (§3a) and hence its character are defined only for
λ≠0, and multiplicativity holds only on C^*. But s11's `hmob`/`hmul` and s8's monomial lemma quantify
over ALL of C. This session builds the precise C^*-index bridge at the monomial step.

Delivered (nonzero-index analogues of s8 `multiplicative_polynomial_eq_X_pow` / s12
`multiplicative_eval_eq_pow`):
- **`multiplicative_polynomial_eq_X_pow_of_nonzero`** : over alg-closed C, a nonzero P with
  `P(xy)=P(x)P(y)` for all NONZERO x,y is `P = X^(deg P)`. Adapts s8's proof; the two spots that used a
  possibly-zero argument (the `P.eval 1=0` branch and the root-killing step) are rescued by the private
  helper `eq_zero_of_eval_zero_on_nonzero` (a polynomial vanishing on the infinite nonzero locus is 0,
  via `eq_zero_of_infinite_isRoot` + `(finite_singleton 0).infinite_compl`).
- **`multiplicative_eval_eq_pow_of_nonzero`** : `e:C→C` given by a nonzero polynomial and
  multiplicative on C^* is `e(λ)=λ^k` for EVERY λ (incl. 0, since e=P.eval is total). Direct clock
  bridge feeding a nonzero-variant of `charged_clock_family_pow`.

§3(b) status unchanged (chain complete as hypothesis-fed theorems); this session removes the
index-mismatch obstruction to assembling the clock family, which lives on C^*.

NEXT session: nonzero-index rework of the s11 character chain —
`HTGeometry/ClockScalingCharacterNonzero.lean`: `scaling_character_multiplicative_of_nonzero`
(∀ λμ≠0, e(λμ)=e(λ)e(μ) — copy s11's `scaling_character_multiplicative` with nonzero hypotheses on
`hscale`/`hmul`) and `commuting_family_scaling_character_of_nonzero` (feed
`clockSemilinearAlgEquiv_generator_mobius` (s14) as the per-λ≠0 hmob, `commuting_with_scaling_is_scaling`
(s11) per λ≠0, build e by choose). Then `multiplicative_eval_eq_pow_of_nonzero` (THIS session) closes
e=λ^k, assembling the family-level §3(b) from clock hypotheses over C^*.
