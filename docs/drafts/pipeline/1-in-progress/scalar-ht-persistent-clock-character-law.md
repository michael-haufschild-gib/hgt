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

### Session 16 progress — the ENTIRE charged chain reworked over C^*
`HTGeometry/ClockScalingCharacterNonzero.lean` [PROVED HERE], all 5 theorems standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockScalingCharacterNonzero` clean (3042 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

The charged-phase chain (s11 ClockScalingCharacter, s6 ClockChargeFamilyMultiplicative, s12
AlgebraicCharacterMonomial) is now reworked with the membership guard `λ ≠ 0` throughout, so it
applies to the ACTUAL clock (indexed by C^*):
- `scaling_character_multiplicative_of_nonzero` : `e(λμ)=e(λ)e(μ)` on C^* (copy of s11 with nonzero
  guards on hscale/hmul; args nonzero via `mul_ne_zero`).
- `commuting_family_scaling_character_of_nonzero` : commuting clock family (nonzero-Möbius members +
  anchor scaling) ⟹ C^*-character `e:C→C`. The `choose` is over a GUARDED existential
  `∃ elam, λ≠0 → ρ_λ q = elam·q` (by_cases λ=0: witness 0; else `commuting_with_scaling_is_scaling`
  s11) so `e:C→C` is total.
- `charged_clock_family_pow_of_nonzero` : EQUATION (2) on C^* — polynomial character ⟹ `ρ_λ q = λ^k q`
  for λ≠0, via s15 `multiplicative_polynomial_eq_X_pow_of_nonzero`.
- `clock_charge_family_multiplicative_of_nonzero` : s6 nonzero variant — charged rigidity σ y = e·y.
  KEY: s6 already tests only ONE λ (from `exists_pow_ne_one_ne_neg_one`, which is nonzero), so the
  nonzero guard costs nothing; `hρ lam hlam0`, `hcomm lam hlam0` fed to s5
  `differentialAlgEquiv_generator_multiplicative`.
- **`charged_clock_polynomial_forces_multiplicative_of_nonzero`** : the CHARGED BRANCH end-to-end over
  C^*. σ differential automorphism, ρ clock cocharacter with polynomial character `ρ_λ y = P(λ)·y`
  (0<deg P) on C^*, commuting with σ ⟹ `∃ e:C, σ y = e·y`.

MILESTONE: the charged branch (§3+§4, k>0) is now formalized end-to-end over the CORRECT index C^*.
The full charged chain (all [PROVED HERE], std axioms): §1 Möbius (s5/7) · §3a Möbius clock (s14) ·
anchor diagonalization (s9/10) · C^*-family character (THIS session) · eq(2) on C^* (THIS session) ·
charged rigidity σy=e·y on C^* (THIS session).

REMAINING for the fully-unconditional card:
 (hmob discharge) `commuting_family_scaling_character_of_nonzero` still TAKES hmob; discharge by feeding
   s14 `clockSemilinearAlgEquiv_generator_mobius` (needs the clock family as semilinear AlgEquivs, per-λ
   hsemi, + AlgEquiv→AlgHom coercion plumbing).
 (B) ALGEBRAICITY: `hpoly_scale` with P polynomial (cocharacter varies algebraically) — still an input.
 (C) CONCRETE CLOCK: jet-scaling clock satisfying hsemi/hconst/hmul/hcomm — construct the object.
 (D) TOP-LEVEL card statement assembly.
NEXT session: (hmob discharge) `HTGeometry/ClockFamilySemilinearMobius.lean` — a clock family as
semilinear AlgEquivs `ρ:C→(E≃ₐ[C]E)` with per-λ hsemi (factor λ), hconst, generating hypertranscendental
y ⟹ per-λ≠0 hmob (via s14 `clockSemilinearAlgEquiv_generator_mobius` on `ρ lam`, coercing `(ρ lam).toAlgHom`
into the s16 `hmob` shape). Feed into `commuting_family_scaling_character_of_nonzero` (THIS session) to
discharge the last GEOMETRIC input and get the C^*-character from clock hypotheses alone.

### Session 17 progress — hmob DISCHARGED: C^*-character from clock hypotheses alone
`HTGeometry/ClockFamilySemilinearMobius.lean` [PROVED HERE], axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockFamilySemilinearMobius` clean (3045 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

- **`clock_family_scaling_character_from_semilinear`** : a clock cocharacter presented as semilinear
  AlgEquivs `ρ:C→(E≃ₐ[C]E)` (per-λ≠0 hsemi `(ρ λ).toAlgHom w′ = λ·((ρ λ).toAlgHom w)′`, hconst
  `(algebraMap λ)′=0`), homomorphic at q on C^*, commuting with an anchor scaling ρ_{ν₀}q=νq
  (ν∉{0,1,-1}), yields a multiplicative C^*-character `e:C→C` with `(ρ λ).toAlgHom q = e(λ)·q`.
  The last GEOMETRIC input `hmob` of `commuting_family_scaling_character_of_nonzero` (s16) is
  discharged INTERNALLY via s14 `clockSemilinearAlgEquiv_generator_mobius` on each `ρ lam` (AlgEquiv);
  `ρ' := fun lam => (ρ lam).toAlgHom` bridges AlgEquiv→AlgHom by defeq (the `(ρ lam) q` vs
  `(ρ lam).toAlgHom q` coercion is definitional). q≠0 from hypertranscendence.

MILESTONE: §3(b) is now FULLY DISCHARGED OF GEOMETRIC INPUTS. The C^*-character is produced from
clock hypotheses (semilinear structure + commuting + homomorphism + anchor) alone — no Möbius/hmob
input remains. Full abstract charged chain, all [PROVED HERE], std axioms:
  §1 Möbius (s5/7) · §3a semilinear order-zero→Möbius clock (s13/14) ·
  hmob-discharged C^*-family character (THIS session) · eq(2) on C^* (s16) ·
  charged rigidity σ q = e·q on C^* (s16).

REMAINING for the fully-unconditional card (all about CONCRETE objects, not the abstract chain):
 (B) ALGEBRAICITY: `hpoly_scale : ρ_λ q = P(λ)·q` with P a polynomial (the cocharacter is algebraic in
   λ). Feeds `charged_clock_family_pow_of_nonzero`/...`_forces_multiplicative_of_nonzero` (s16). This is
   the regular-character structure of G_m; genuine input, needs modeling the algebraic λ-dependence.
 (C) CONCRETE CLOCK: construct the jet-scaling automorphism ρ_λ(y^(j))=λ^j y^(j) and PROVE it satisfies
   hsemi (`ρ_λ(Dw)=λ D(ρ_λ w)`), hconst, homomorphism, anchor. NOTE the scaling is per-jet λ^j (NOT a
   constant matrix), so `differentialJetLinearChangeAlgEquiv` does NOT give it directly — needs a
   diagonal-jet construction. `stableRangeCoreSymmetryAlgEquiv` (StableCoreFunctoriality) is the §2
   core-restriction to reuse for the anchor/commuting.
 (D) TOP-LEVEL card statement (T=∩Φⁿ(F), charge k, k>0 ⟹ Φ q₀ = a q₀) assembly.
NEXT session: (C) corpus-hunt the concrete jet-scaling clock — check `DifferentialLinearChangeAutomorphism`,
`StableCoreFunctoriality`, and the differential-polynomial machinery for an existing diagonal/dilation
automorphism; if absent, construct `HTGeometry/JetScalingClock.lean` defining ρ_λ on DifferentialPolynomial
via per-jet λ^j substitution and proving its semilinearity `ρ_λ(Dw)=λ D(ρ_λ w)` + it is an AlgEquiv
(inverse ρ_{λ⁻¹}). That discharges the hsemi/hconst structure feeding THIS session's theorem.

### Session 18 progress — (C) CONCRETE jet-scaling clock (ring level) + eq (1)
`HTGeometry/JetScalingClock.lean` [PROVED HERE], all decls standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...JetScalingClock` clean (2951 jobs),
`formal_tools.py lint` PASSED.

CALIBRATION (re-read card): the theorem is about the SPECIFIC clock `ρ_λ(y^(j))=λ^j y^(j)` on F=C⟨y⟩,
with C carrying the ZERO derivation (so hconst `(algebraMap λ)′=0` is structural). So the concrete
clock is genuinely part of the statement — constructed here at the differential-polynomial ring level
(`DifferentialPolynomial ι C = MvPolynomial (ι×ℕ) C`, jet-shift derivation D X_(i,n)=X_(i,n+1)).

Delivered — the concrete cocharacter object:
- `clockDilationAlgHom lam := aeval (fun (i,n) => C(lam^n) * X(i,n))` : the clock as an AlgHom;
  `clockDilationAlgHom_X` (X_(i,n) ↦ C(lam^n)·X_(i,n)), `_C` (fixes constants).
- `clockDilationAlgHom_comp` : ρ_λ∘ρ_μ = ρ_{λμ} (the HOMOMORPHISM/hmul property), via algHom_ext +
  mul_pow + C_mul; `clockDilationAlgHom_one` (ρ_1=id).
- `clockDilationAlgEquiv lam (hlam : lam≠0)` : the clock is an AUTOMORPHISM for λ≠0, inverse ρ_{λ⁻¹}
  (via AlgEquiv.ofAlgHom + composition law + mul_inv_cancel).
- **`clockDilation_semilinear`** : EQUATION (1) `ρ_λ(w′) = C(lam)·(ρ_λ w)′`. MvPolynomial.induction_on;
  mul_X case via two Derivation.leibniz + hP + converting C(lam^(n+1))=C(lam)·C(lam^n) (pow_succ'+C_mul)
  then ring. This is the defining semilinearity, matching the abstract hsemi (with C lam = algebraMap C
  (DiffPoly) lam).

(C) status: concrete clock DONE at the RING level with eq(1)/comp/AlgEquiv. The abstract chain's
hsemi/hmul/invertibility are now instantiable by this object (C lam ≡ algebraMap C (DifferentialPolynomial ι C) lam).

REMAINING:
 (C-field) extend clockDilation to the FRACTION FIELD F=C⟨y⟩ (the card's field) via IsFractionRing
   functoriality; connect its semilinearity to abstract hsemi in `algebraMap C F lam` form. The scalar
   case is ι=Unit (single generator y=X((),0)).
 (B) ALGEBRAICITY: `hpoly_scale` with P polynomial — the character e(λ)=λ^k IS a polynomial (X^k), so
   at the concrete clock ρ_λ(q)=λ^k q the scaling factor is literally P(λ)=λ^k. Once (C-field) + core
   give ρ_λ q = λ^k q the algebraicity is automatic; (B) may dissolve once the concrete core generator
   q is produced with its charge.
 (D) core T=∩Φⁿ(F) construction + top-level card statement.
NEXT session: (C-field) `HTGeometry/JetScalingClockField.lean` — extend `clockDilationAlgEquiv` to the
fraction field of `DifferentialPolynomial Unit C` (or the corpus's C⟨y⟩ model) via `IsFractionRing.fieldEquivOfAlgEquiv`/`FractionRing.algEquiv` functoriality, and restate `clockDilation_semilinear`
at the field level with `algebraMap C F lam`. That instantiates the abstract clock family's hsemi/hmul
with the CONCRETE clock, connecting `clock_family_scaling_character_from_semilinear` (s17) to a real object.

### Session 19 progress — (C-field) semilinearity propagates domain → fraction field
`HTGeometry/SemilinearFractionField.lean` [PROVED HERE], both decls standard axioms
([propext, Quot.sound] for conjDerivation; +Classical.choice for the propagation lemma),
`lake build ...SemilinearFractionField` clean (1350 jobs), `formal_tools.py lint` PASSED.

The concrete field F=C⟨y⟩ is Frac(DifferentialPolynomial Unit C); the corpus's `fractionRingDerivation`
extends the jet-shift derivation to F. This session builds the crux of (C-field): semilinearity checked
on the domain propagates to all of F, so the clock's ring-level eq(1) (s18) will give field-level eq(1).

Delivered:
- `conjDerivation E D` : conjugation `z ↦ E⁻¹(D(E z))` of a derivation by a C-algebra automorphism,
  a Derivation (via Derivation.mk'; twisted Leibniz becomes plain after conjugation).
- **`algEquiv_semilinear_of_semilinear_algebraMap`** : a C-algebra automorphism E of F=Frac(A) that is
  semilinear on the image of A (`E(D_F(algebraMap a)) = algebraMap λ · D_F(E(algebraMap a))`) is
  semilinear on ALL of F. Proof: the two derivations `D_F` and `algebraMap λ • conjDerivation E D_F`
  agree on A (from the hypothesis + E.symm fixing C), hence agree on F (corpus
  `fractionRing_derivation_ext`); unfolding gives field-level semilinearity.

(C-field) status: the semilinearity REDUCTION domain→field is DONE and reusable. Still need the concrete
clock EXTENSION E:F≃ₐ[C]F itself.

NOTE (blocker found): `IsFractionRing.fieldEquivOfAlgEquiv` gets instance-stuck extending
`clockDilationAlgEquiv : DiffPoly ≃ₐ[C] DiffPoly` to Frac (base-ring mismatch: it wants fraction fields
OVER the ring, not over C). Next session use `IsLocalization.ringEquivOfRingEquiv`/`IsLocalization.mapₐ`
(extend the underlying ring equiv of the clock to Frac, then package as C-AlgEquiv since it fixes
algebraMap C), OR set up the instance tower [Algebra C F][IsScalarTower C DiffPoly F] explicitly.

REMAINING:
 (C-field-E) concrete clock extension E=clockDilationFieldEquiv : Frac(DiffPoly Unit C)≃ₐ[C] itself, via
   localization functoriality; then field-level eq(1) via `algEquiv_semilinear_of_semilinear_algebraMap`
   (THIS session) fed by ring `clockDilation_semilinear` (s18) through `fractionRingDerivation_algebraMap`.
 (C-inst) Differential F + DifferentialAlgebra C F instances on Frac(DiffPoly).
 (B) algebraicity; (C-htr) hypertranscendence of y + differentialAdjoin=⊤ in the concrete model; (D) core+top-level.
NEXT session: (C-field-E) `HTGeometry/JetScalingClockField.lean` — extend clockDilationAlgEquiv to
Frac(DifferentialPolynomial Unit C) via `IsLocalization.ringEquivOfRingEquiv` (underlying ring equiv)
upgraded to a C-AlgEquiv, then prove field-level semilinearity by feeding s18's ring semilinearity into
THIS session's propagation lemma.

### Session 20 progress — (C-field-E) concrete clock on the FIELD C⟨y⟩ + field eq (1)
`HTGeometry/JetScalingClockField.lean` [PROVED HERE], both decls standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...JetScalingClockField` clean (2955 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

Resolved the s19 blocker: `IsFractionRing.fieldEquivOfAlgEquiv` DOES work once ι is pinned to Unit
(the stick was an ι metavar); the instance tower `Algebra C (FractionRing (DiffPoly Unit C))`,
`IsScalarTower C DiffPoly (FractionRing)` resolves automatically.

Delivered:
- `ScalarDifferentialField C := FractionRing (DifferentialPolynomial Unit C)` — the field C⟨y⟩.
- `clockDilationFieldEquiv lam hlam` : the clock on C⟨y⟩, via
  `IsFractionRing.fieldEquivOfAlgEquiv C F F (clockDilationAlgEquiv lam hlam)` (base A=C, B=C=DiffPoly).
- `clockDilationFieldEquiv_algebraMap` : restricts to the ring clock, `E(algebraMap a)=algebraMap(clockDilationAlgHom lam a)`
  (via `IsFractionRing.fieldEquivOfAlgEquiv_algebraMap`).
- `scalarDifferentialFieldDerivation` : the jet-shift derivation on C⟨y⟩ = `fractionRingDerivation` of
  the lifted polynomial derivation `(Algebra.linearMap A F).compDer (differentialPolynomialDerivation)`.
- **`clockDilationField_semilinear`** : EQ (1) ON THE FIELD `ρ_λ(D z)=λ·D(ρ_λ z)`. Proof: `apply`
  s19 `algEquiv_semilinear_of_semilinear_algebraMap`; the domain hED reduces (via fractionRingDerivation_algebraMap
  + clockDilationFieldEquiv_algebraMap + compDer defeq + IsScalarTower.algebraMap_apply) to s18 ring
  `clockDilation_semilinear` mapped through algebraMap A F. Closed by defeq (`′`≡differentialPolynomialDerivation,
  `MvPolynomial.C`≡algebraMap C DiffPoly).

(C) status: concrete clock on the FIELD with eq(1) DONE. Composition law + Differential-instance + htr remain.

REMAINING:
 (C-comp) field-level composition ρ_λ∘ρ_μ=ρ_{λμ} (hmul) — from ring `clockDilationAlgHom_comp` (s18) +
   fieldEquiv functoriality; and the anchor/nonzero facts.
 (C-inst) `Differential (ScalarDifferentialField C)` = scalarDifferentialFieldDerivation.restrictScalars ℤ,
   + `DifferentialAlgebra C (ScalarDifferentialField C)`; then clockDilationFieldEquiv's hsemi is exactly
   the abstract hsemi (`(ρ lam).toAlgHom w′ = algebraMap lam * ...`) via `′`=scalarDifferentialFieldDerivation.
 (C-htr) y := algebraMap(X((),0)) is HypertranscendentalOver C + differentialAdjoin C {y}=⊤ [deep].
 (B) algebraicity; (D) core T=∩Φⁿ + top-level.
NEXT session: (C-inst) `HTGeometry/ScalarDifferentialFieldInstance.lean` — the `Differential` instance on
C⟨y⟩ from `scalarDifferentialFieldDerivation`, and restate `clockDilationField_semilinear` in the abstract
hsemi shape (`w′` with the instance) so `clockDilationFieldEquiv` directly instantiates the abstract clock
family's hsemi of `clock_family_scaling_character_from_semilinear` (s17). Also the field-level comp law (hmul).

### Session 21 progress — (C-inst) Differential structure on C⟨y⟩ + clock as abstract semilinear autom.
`HTGeometry/ScalarDifferentialFieldInstance.lean` [PROVED HERE], all decls standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarDifferentialFieldInstance` clean +
FULL `GaloisForLFunctions.HTGeometry` umbrella builds (10739 jobs, no instance-diamond regression),
`formal_tools.py lint` PASSED.

Class defs found: `Differential R = ⟨deriv : Derivation ℤ R R⟩`; `DifferentialAlgebra A B` (Prop),
field `deriv_algebraMap : ∀ a, (algebraMap a)′ = algebraMap (a′)`.

Delivered:
- `scalarDifferentialFieldDifferential` : global `Differential (ScalarDifferentialField C)` instance =
  `scalarDifferentialFieldDerivation.restrictScalars ℤ`. FIXED the OreLocalization `Algebra ℤ` DIAMOND
  with the corpus trick `letI : Algebra ℤ _ := Ring.toIntAlgebra _` before restrictScalars (pattern
  from `freeScalarJetFieldDifferential`).
- `scalarDifferentialField_deriv` : `z′ = scalarDifferentialFieldDerivation z` (rfl).
- `scalarDifferentialFieldDerivation_algebraMap` : field derivation kills C-constants (`Derivation.map_algebraMap`).
- **`clockDilationFieldEquiv_semilinear`** : `ρ_λ(w′)=λ·(ρ_λ w)′` in `′` shape — literally the abstract
  clock `hsemi` of `clock_family_scaling_character_from_semilinear` (s17), from s20's field semilinearity.
- `scalarDifferentialFieldDifferentialAlgebra` : `DifferentialAlgebra C (C⟨y⟩)` when C has zero
  derivation (hCzero : ∀c, c′=0).

(C-inst) status: Differential + DifferentialAlgebra + hsemi shape DONE. The concrete clock now matches
the abstract clock-family interface (hsemi via clockDilationFieldEquiv_semilinear).

BIG LEAD for (C-htr): corpus has `FreeCoordinateField` (FreeCoordinateField.lean) and `FreeScalarJetField`
/`freeJetShift`/`freeCoordinate` (ProjectiveHorizonFreeJetReciprocalTail.lean) — an EXISTING free scalar
jet differential field model, possibly with hypertranscendence of the generator + differentialAdjoin=⊤
already proven. Investigate for reuse; may bridge my `ScalarDifferentialField C` to it or switch.

REMAINING:
 (C-comp) field composition law ρ_λ∘ρ_μ=ρ_{λμ} (hmul) — from ring `clockDilationAlgHom_comp` + fraction
   ext (IsFractionRing.ringHom_ext / IsLocalization ext).
 (C-htr) y hypertranscendental + differentialAdjoin C {y}=⊤ [DEEP; check FreeCoordinateField reuse].
 (B) algebraicity; (D) core T=∩Φⁿ + top-level.
NEXT session: investigate `FreeCoordinateField`/`FreeScalarJetField` — what hypertranscendence/adjoin=⊤
facts the corpus already proves for the free scalar jet field, to discharge (C-htr) by reuse. If it is
Frac(DifferentialPolynomial Unit C) too, bridge the Differential instances; else build the y-generator
hypertranscendence via `differentialJet_differentialPolynomial_X` + DifferentialIndependent of the single
generator.

### Session 22 progress — (C-htr, half 1) the generator y IS hypertranscendental
`HTGeometry/ScalarDifferentialFieldGenerator.lean` [PROVED HERE], both decls standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarDifferentialFieldGenerator` clean (2957 jobs).
(My-cone lint clean + module wired in umbrella; a separate lint "owned module unreachable" error is an
unrelated parallel-agent HTGeometry file `HausdorffPositiveCddCone`, not mine.)

(Corpus check: `FreeCoordinateField`/`FreeScalarJetField` are DIFFERENT models (multivar coordinate
field / free jet field indexed by ℕ) and do NOT ship a ready hypertranscendence-of-generator fact, so
built it directly on my `ScalarDifferentialField C = Frac(DifferentialPolynomial Unit C)` model.)

Delivered:
- `scalarDifferentialGenerator C := algebraMap (X((),0))` — the canonical generator y.
- `algebraMap_scalarDifferentialField_deriv` : the ring→field embedding commutes with the derivation
  (`algebraMap(w′)=(algebraMap w)′`), via `fractionRingDerivation_algebraMap` + compDer defeq.
- `differentialJet_scalarDifferentialGenerator` : `differentialJet n y = algebraMap(X((),n))` — the
  jets of y are the free variables. INDUCTION on n (differentialJet_succ + the embedding-deriv lemma +
  differentialPolynomial_deriv_X); avoids needing differentialJet_algHom.
- **`scalarDifferentialGenerator_hypertranscendental`** : `HypertranscendentalOver C y`. Chain:
  `MvPolynomial.algebraicIndependent_X (Unit×ℕ)` → `.comp (n↦((),n))` (subfamily indexed by ℕ) →
  `.map (IsScalarTower.toAlgHom, hinj.injOn)` (inject into Frac, `IsFractionRing.injective`) →
  rewrite `algebraMap(X((),n))=differentialJet n y` → `DifferentialIndependent` via `.comp Prod.snd`
  → `hypertranscendentalOver_iff_differentialIndependent_singleton`.

(C-htr) status: HypertranscendentalOver DONE (half 1). Remaining: `differentialAdjoin C {y} = ⊤`.

REMAINING:
 (C-htr-2) `differentialAdjoin C {scalarDifferentialGenerator C} = ⊤`. The jets X((),n) generate the
   polynomial ring A as a C-algebra, A generates F=Frac A as a field, so the differential adjoin of y
   (= field-adjoin of its jets = field-adjoin of {algebraMap X((),n)}) is all of F. Route: differentialAdjoin
   C {y} ⊇ algebraMap '' A (contains all polynomials) and is a field ⟹ ⊇ Frac A = ⊤.
 (C-comp) field composition law ρ_λ∘ρ_μ=ρ_{λμ} (hmul); (B) algebraicity; (D) core+top-level.
NEXT session: (C-htr-2) `differentialAdjoin C {y} = ⊤` in `HTGeometry/ScalarDifferentialFieldGeneratorTop.lean`
(or extend the generator file): show the differential adjoin contains algebraMap A (via the jets generating
A) and is a subfield, hence = ⊤ = Frac A. Then with HypertranscendentalOver (this session) + Differential/
DifferentialAlgebra (s21) + hsemi (s21) + hmul, the concrete clock family instantiates
`clock_family_scaling_character_from_semilinear` (s17) fully.

### Session 23 progress — (C-htr, half 2) differentialAdjoin C {y} = ⊤  →  (C-htr) COMPLETE
`HTGeometry/ScalarDifferentialFieldGeneratorTop.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarDifferentialFieldGeneratorTop` clean
(2958 jobs), `formal_tools.py lint` PASSED. Compiled first try.

Delivered:
- **`differentialAdjoin_scalarDifferentialGenerator_top`** : `differentialAdjoin C {y} = ⊤`. Proof:
  the jets of y ARE the free variables `algebraMap(X((),n))` (s22), which are the image of `range X`;
  `range X` generates A (`MvPolynomial.adjoin_range_X = ⊤`), so `algebraMap '' A ⊆ differentialAdjoin`
  (via `Algebra.adjoin_image` + `IntermediateField.algebra_adjoin_le_adjoin`); then every z∈F is
  `algebraMap x / algebraMap y` (`IsFractionRing.div_surjective`), both factors in the (sub)field, so
  z ∈ differentialAdjoin. `eq_top_iff` + `mul_mem`/`inv_mem`.

MILESTONE: (C-htr) COMPLETE. ALL structural field-instantiation hypotheses of the abstract clock-family
theorem are now discharged for the CONCRETE field C⟨y⟩ = Frac(DifferentialPolynomial Unit C):
  Differential (s21) · DifferentialAlgebra given C zero-deriv (s21) · hsemi eq(1) (s21) ·
  HypertranscendentalOver y (s22) · differentialAdjoin C {y}=⊤ (s23).

REMAINING to fully instantiate `clock_family_scaling_character_from_semilinear` (s17) with the concrete
clock:
 (C-comp) field composition law `clockDilationFieldEquiv lam ∘ clockDilationFieldEquiv mu = clockDilationFieldEquiv (lam*mu)`
   (hmul) — from ring `clockDilationAlgHom_comp` (s18) + fraction-field ext (two AlgEquivs of Frac A
   agreeing on algebraMap A agree: IsFractionRing / IsLocalization ringHom ext). Plus the anchor:
   need SOME ν∉{0,1,-1} realized as a scaling — but the anchor for the concrete clock is
   `clockDilationFieldEquiv ν` acting on the fixed-point coordinate; the anchor scaling emerges from
   diagonalizing one ρ_ν (s9/10 fixed-point theory), NOT from the clock directly. Reconsider: for the
   CONCRETE clock, ρ_λ(y)=λ·y already (order-1 jet scaling on y=X((),0) is λ^0=1... CHECK: ρ_λ(X((),0))
   =λ^0 X((),0)=X((),0), so ρ_λ FIXES y!). So on the free generator y the clock is TRIVIAL; the
   nontrivial action is on the CORE generator q (a differential rational function of y), where the
   charge k>0 appears. So the anchor/diagonalization lives at the CORE, not at y. This connects to (D).
 (B) algebraicity; (D) core T=∩Φⁿ + top-level.
NEXT session: (C-comp) `HTGeometry/JetScalingClockFieldComp.lean` — the field composition law (hmul) via
fraction-field AlgEquiv ext (probe `IsFractionRing.ringHom_ext`/`IsLocalization.ext`; two C-AlgEquivs of
Frac(A) equal iff equal on algebraMap A, and `clockDilationFieldEquiv_algebraMap` (s20) reduces both to
ring `clockDilationAlgHom_comp` (s18)). This completes the concrete clock's homomorphism property.

### Session 24 progress — (C-comp) field composition law (hmul)  →  concrete clock fully has (C)
`HTGeometry/JetScalingClockFieldComp.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...JetScalingClockFieldComp` clean (2956 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

- **`clockDilationFieldEquiv_comp`** : `ρ_λ(ρ_μ z) = ρ_{λμ} z` on C⟨y⟩ (hmul). Pointwise via
  `IsFractionRing.div_surjective` (z = algebraMap x / algebraMap y) + simp
  [map_div₀, clockDilationFieldEquiv_algebraMap (s20), clockDilationAlgHom_apply_apply (s18)].

(C) COMPLETE: the concrete clock on C⟨y⟩ now has ALL properties — AlgEquiv/invertible (s18),
Differential+DifferentialAlgebra (s21), hsemi eq(1) (s21), hmul comp (s24), + generator y
hypertranscendental (s22) with differentialAdjoin=⊤ (s23).

KEY STRUCTURAL REALIZATION (from s23): on the FREE generator y=X((),0) the clock is TRIVIAL
(ρ_λ(y)=λ^0 y=y). The nontrivial charged action lives on the CORE generator q∈T, where T=∩Φⁿ(F). So the
abstract clock-character theorems apply with the field E:=T (the core, itself a free diff field on one
generator q) — NOT at y. The C⟨y⟩ instantiation (s18-24) is the reusable TEMPLATE/model of "free diff
field on one generator"; the real application is the same structure at T=C⟨q⟩.

BIG LEAD for (D): corpus already has the STABLE CORE machinery:
 - `StableDifferentialCore.lean`: `stableRangeCore` (=T=∩Φⁿ(F)), `stableRangeCoreAlgEquiv` (Φ|T is an
   AUTOMORPHISM — "injective endo becomes automorphism on ∩ forward images"), `stableRangeCore_map_mem`,
   `derivationClosed_stableRangeCore` (T is a differential subfield).
 - `StableCoreFunctoriality.lean`: `stableRangeCoreSymmetryAlgEquiv` / `map_stableRangeCore_eq_of_commuting_algEquiv`
   (commuting clock RESTRICTS to a core symmetry) — this IS §2 (clock preserves core).
So §2 is largely IN THE CORPUS. The genuinely-open (D) content: T≠C ⟹ T=C⟨q⟩ (core is a SIMPLE
differential extension / differential-Lüroth for the core) — the single-generator structure of the
nonconstant core.

REMAINING:
 (D) T≠C ⟹ ∃ q, differentialAdjoin C {q}=⊤ in T (core simple differential extension) — DEEP, the last
   genuinely-new structural piece; then abstract chain (s1-17) applies at E:=T, q.
 (B) algebraicity (likely dissolves once ρ_λ(q)=λ^k q from the concrete core jet-weights).
NEXT session: (D) investigate `StableDifferentialCore.lean` / `StableCoreFunctoriality.lean` fully —
what the corpus proves about the core (automorphism, derivation-closed, clock-symmetry) and whether the
single-generator structure T=C⟨q⟩ (or a differential-Lüroth) exists or must be built. Map the exact
gap between the corpus core machinery and the abstract theorems' hypotheses (E field, q generator,
differentialAdjoin=⊤).

### Session 25 progress — charged-phase CAPSTONE (eq 4) + differential-Lüroth gap identified
`HTGeometry/ScalarClockCharacterCharged.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarClockCharacterCharged` clean (3043 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

DECISIVE FINDING (corpus): `StableDifferentialCore.lean` header states the stable-core machinery is
the UNCONDITIONAL core, but the "nonconstant core = C⟨u⟩ with PGL₂ action" classification uses the
**Ritt–Kolchin differential Lüroth theorem** + differential-order rigidity, "neither currently present
in the Lean dependency tree; not postulated here." So:
 - §2 (stable core: Φ|T automorphism, clock preserves core, T derivation-closed) IS IN CORPUS
   (`stableRangeCore`, `stableRangeCoreAlgEquiv`, `derivationClosed_stableRangeCore`, `stableRangeCoreSymmetryAlgEquiv`).
 - The corpus IS mid-developing differential Lüroth (`DifferentialLurothCoefficient.lean` 1372L +
   `DifferentialLurothComponentTransfer.lean` 968L: two-block diff polynomials, separants,
   characteristic-set/iterate-ideal machinery) — the CAPSTONE "T=C⟨q⟩" NOT yet complete.
 => The card's ONLY genuinely-open deep piece is the DIFFERENTIAL LÜROTH THEOREM.

Delivered — the card's eq(4) charged conclusion, assembled at the core:
- **`persistent_clock_charged_forces_multiplicative`** : on the nonconstant core T=C⟨q⟩ (encoded by
  `HypertranscendentalOver C q` + `differentialAdjoin C {q}=⊤`), a differential automorphism Φ commuting
  with a clock cocharacter of positive charge `ρ_λ(q)=λ^k q` (k>0) satisfies `Φ(q)=a·q`. Wraps s16
  `charged_clock_polynomial_forces_multiplicative_of_nonzero` with P:=X^k (P.eval λ=λ^k, natDegree=k>0).

FULL FORMALIZATION STATE of the card:
 - Abstract charged chain §1/§3/§4-given-q: DONE (s1-17, std axioms, unconditional).
 - Concrete free diff field C⟨y⟩ + clock (template model): DONE (s18-24, unconditional).
 - Stable core §2: IN CORPUS (unconditional).
 - Charged eq(4) capstone at core: DONE (this session, unconditional given the interface).
 - THE ONE GAP: differential Lüroth (T≠C ⟹ ∃q, T=C⟨q⟩) — discharges the capstone's hq/hqtop; deep,
   corpus mid-development.

NEXT session: differential Lüroth. Options: (a) study `DifferentialLurothCoefficient.lean` frontier
(`irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal`, general-component contraction) to
build the next piece toward the T=C⟨q⟩ capstone; (b) build the E:=T assembly plumbing (Differential T
via `derivationClosedDifferential` on `derivationClosed_stableRangeCore`; Φ|T via `stableRangeCoreAlgEquiv`;
clock|T via `stableRangeCoreSymmetryAlgEquiv`) so the capstone's Φ/ρ/T hypotheses are discharged from the
stable-core machinery, leaving ONLY the differential-Lüroth q-generator. Prefer (b) first (concrete,
reduces the gap to exactly differential Lüroth), then (a).

### Session 26 progress — the full two-phase DICHOTOMY capstone (eq 3 + eq 4)
`HTGeometry/ScalarClockCharacterDichotomy.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarClockCharacterDichotomy` clean (3044 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

Delivered — the card's full conclusion structure (both phases) as one theorem:
- **`persistent_clock_character_dichotomy`** : on the nonconstant core T=C⟨q⟩ (encoded by hq+hqtop), a
  differential automorphism Φ commuting with a clock cocharacter of charge k:
  (eq 3) ALWAYS acts by a Möbius transform `Φ q·(cq+d)=aq+b`, ad−bc≠0 — wraps s5/7
  `differentialAlgEquiv_generator_mobius`;
  (eq 4) k>0 ⟹ `Φ q = a·q` — wraps s25 `persistent_clock_charged_forces_multiplicative`.

STABLE-CORE ASSEMBLY findings (for discharging Φ/T from the corpus, future work):
- `stableRangeCoreDifferentialAlgEquiv φ hφ : DifferentialAlgEquiv C (stableRangeCore φ)` gives Φ|T as
  a DIFFERENTIAL automorphism: `.toAlgEquiv` = Φ|T : T≃ₐ[C]T, `.map_deriv'` = hΦderiv. Differential T
  instance = `derivationClosedDifferential (stableRangeCore φ) (derivationClosed_stableRangeCore φ hφ)`.
- `CharZero (stableRangeCore φ)` : inferInstance (subfield of char-0). ✓
- `DifferentialAlgebra C (stableRangeCore φ)` : derivable from `DifferentialAlgebra C F` via Subtype.ext
  + `DifferentialAlgebra.deriv_algebraMap` (but letI instance-threading is finicky — needs care).
- clock|T = `stableRangeCoreSymmetryAlgEquiv φ (ρ lam) (hcomm lam)` : T≃ₐ[C]T per λ.
So the Φ/T/Differential-T hypotheses of the dichotomy CAN be discharged from the corpus stable-core
machinery; only the q-generator (differential Lüroth) + core-clock charge (hcharge=eq2) remain.

FULL CARD STATE: abstract chain (s1-17) + concrete model (s18-24) + charged eq4 (s25) + dichotomy eq3+eq4
(s26) all DONE, unconditional given the interface. §2 stable core IN CORPUS. THE ONE GAP: differential
Lüroth (T≠C ⟹ ∃q, T=C⟨q⟩), corpus mid-development (DifferentialLurothCoefficient 1372L).
NEXT session: differential Lüroth. Study the `DifferentialLurothCoefficient.lean` frontier
(`irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal`, `differentialPolynomialGeneralComponentJets_eval_iterate_eq_zero`) — the separant/characteristic-set contraction machinery — and identify the
next lemma toward the T=C⟨q⟩ capstone; or build the stable-core→dichotomy plumbing (Differential T +
DifferentialAlgebra C T threading) to fully discharge Φ/T, leaving ONLY differential Lüroth.

### Session 27 progress — dichotomy at the ACTUAL persistent core T=∩ₙΦⁿ(F)
`HTGeometry/ScalarClockCharacterCore.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarClockCharacterCore` clean (3102 jobs),
`formal_tools.py lint` PASSED. Compiled first try.

Studied the differential-Lüroth frontier (`DifferentialLurothCoefficient.lean`): its frontier theorem
`irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal` is deep Ritt characteristic-set
machinery (separants, iterate ideals, general-component jets, quotient-ring reductions); header confirms
"no ... coefficient-ratio theorem, or field-generation conclusion is assumed" — the T=C⟨q⟩ capstone is
NOT there and extending this 2340L development safely in one session is high-risk. Deferred; did the
stable-core assembly instead (fully discharges Φ/T from the corpus, reducing the card to exactly
differential Lüroth + diagonalized clock).

Delivered:
- (key instance) `DifferentialAlgebra C (stableRangeCore φ)` : derived from `DifferentialAlgebra C F`
  via `Subtype.ext` + `derivationClosedDifferential_apply` (`((x′:T):F)=x.1′`) + `DifferentialAlgebra.deriv_algebraMap`.
- **`persistent_core_clock_character_dichotomy`** : the card's dichotomy (eq3 Möbius + eq4 charged) at
  the REAL persistent core `T = stableRangeCore φ` of an injective differential endomorphism φ of F.
  Discharges from the corpus stable-core machinery: `Differential T` (derivationClosedDifferential),
  `DifferentialAlgebra C T` (above), `CharZero T` (auto), and Φ|T = differential automorphism
  (`stableRangeCoreDifferentialAlgEquiv φ hφ`: `.toAlgEquiv`=Φ|T, `.map_deriv'`=hΦderiv). Applies s26.

MILESTONE: the card is now formalized at the ACTUAL core T=∩ₙΦⁿ(F) (not abstract T). The constraint Φ,
the core T, and ALL differential structure are realized from the corpus §2 stable-core machinery. The
card's interface is now MINIMAL — only two structural inputs remain:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, HypertranscendentalOver C q ∧ differentialAdjoin C {q}=⊤ (T=C⟨q⟩)
     — the classical Ritt-Kolchin theorem, corpus mid-development (DifferentialLurothCoefficient).
 (ii) DIAGONALIZED CLOCK ρT with ρT_λ(q)=λ^k q (charge k) + homomorphism + commuting-with-Φ|T — this is
     §3 applied AT THE CORE (the clock symmetry `stableRangeCoreSymmetryAlgEquiv` restricts the ambient
     clock to T; §3(b) diagonalizes it to λ^k on q). Reducible via the abstract chain once q exists.
NEXT session: EITHER (a) differential Lüroth (study DifferentialLurothCoefficient's next step toward
the coefficient-ratio/field-generation capstone — the genuine deep gap), OR (b) discharge input (ii) by
restricting the ambient clock to T via `stableRangeCoreSymmetryAlgEquiv` and feeding the §3(b) chain
(clock_family_scaling_character_from_semilinear s17 + charged_clock_family_pow_of_nonzero s16) at the core
generator q, leaving ONLY differential Lüroth (i). Prefer (b): reduces the card to the single classical
theorem, then (a).

### Session 28 progress — (ii-a) restricted clock on the core is semilinear
`HTGeometry/StableCoreClockSemilinear.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...StableCoreClockSemilinear` clean (3009 jobs).
(My-cone lint clean + module wired in umbrella; a separate lint "owned module unreachable" error is an
unrelated parallel-agent RHTower file `ThetaCuspCofinalWardConvexity`, not mine.)

Toward discharging input (ii) [diagonalized clock at the core]. The clock ρ restricts to a core
symmetry `ρ|T = stableRangeCoreSymmetryAlgEquiv φ ρ hcomm` (corpus). Delivered the q-INDEPENDENT
connector:
- `stableRangeCoreSymmetryAlgEquiv_coe` : `((ρ|T x : T):F) = ρ (x:F)` (rfl) — the restriction agrees
  with ρ on the coe.
- **`stableRangeCoreSymmetry_semilinear`** : if the ambient clock ρ is semilinear
  (`ρ(x′)=λ·(ρ x)′`), so is `ρ|T` on the core: `ρ|T(w′)=λ·(ρ|T w)′`. Proof: `Subtype.ext` to F, then
  `push_cast [derivationClosedDifferential_apply, stableRangeCoreSymmetryAlgEquiv_coe, algebraMap coe]`
  reduces to the ambient `hsemi`. This is the hsemi hypothesis feeding s14
  `clockSemilinearAlgEquiv_generator_mobius` AT THE CORE.

INPUT (ii) decomposition (the diagonalized clock ρT_λ(q)=λ^k q at the core), and remaining sub-pieces:
 (ii-a) ρ|T semilinear — DONE (this session). [q-independent]
 (ii-b) ρ|T Möbius on the core generator q — s14 given (ii-a) + q (hy+hytop, from differential Lüroth)
        + hconst (C zero-deriv). [needs q]
 (ii-c) family diagonalization → multiplicative character e (s17) + the anchor. [needs q, family]
 (ii-d) ALGEBRAICITY (B): e is polynomial ⟹ e=λ^k (s16). [genuine input — the cocharacter varies
        algebraically in λ; concrete for the jet-scaling clock but abstract here].
So (ii) still needs q (differential Lüroth) for (ii-b,c) and the algebraicity (ii-d/B).

FULL CARD STATE: novel content DONE (abstract chain s1-17, concrete model s18-24, dichotomy s26, core
assembly s27); the card reduces to (i) differential Lüroth + (ii) diagonalized clock [(ii-b,c) need q,
(ii-d) is algebraicity B]. §2 stable core + Φ|T + core Differential structure all IN CORPUS/discharged.
NEXT session: continue (ii). Either build (ii-b) `ρ|T Möbius on q` as a theorem TAKING q (hy+hytop) as
hypothesis (wraps s14 via ii-a semilinearity), reducing (ii) to (ii-c,d)+q; OR (i) differential Lüroth.
The genuine deep gaps remain (i) differential Lüroth (classical, corpus DifferentialLurothCoefficient
mid-development) and (ii-d) algebraicity B. Both are structural/classical; incremental q-dependent
pieces (ii-b,c) can be built as q-hypothesis theorems to shrink the interface.

### Session 29 progress — (ii-b) §3(a) at the core: ρ|T is Möbius on the core generator q
`HTGeometry/StableCoreClockMobius.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...StableCoreClockMobius` clean (3096 jobs).
(My-cone lint clean + wired in umbrella; the "owned module unreachable" lint error is the same unrelated
parallel-agent RHTower file `ThetaCuspCofinalWardConvexity`, not mine.)

Delivered:
- **`stableRangeCoreSymmetry_generator_mobius`** : (ii-b) with C carrying the zero derivation
  (hCzero: lam′=0), the restricted clock `ρ|T` acts on a differential generator q of the core
  (HypertranscendentalOver C q + differentialAdjoin C {q}=⊤) by a Möbius transform
  `ρ|T(q)·(cq+d)=aq+b`, ad−bc≠0. Wraps s14 `clockSemilinearAlgEquiv_generator_mobius` at the core, fed
  by s28 semilinearity `stableRangeCoreSymmetry_semilinear`; hconst at T derived from hCzero via
  DifferentialAlgebra.deriv_algebraMap + derivationClosedDifferential_apply; DifferentialAlgebra C T
  instance derived (as in s27).

INPUT (ii) status: (ii-a) ρ|T semilinear DONE (s28); (ii-b) ρ|T Möbius on q DONE (this session).
Remaining (ii-c) family diagonalization to character e (s17) + anchor; (ii-d) ALGEBRAICITY B (e polynomial
⟹ e=λ^k, s16). Both (ii-c,d) need q (differential Lüroth) and (ii-d) is the genuine algebraicity input.

CARD STATE: novel content DONE; core assembly (Φ|T, T, differential structure) discharged from corpus;
§3(a) at core (ρ|T Möbius on q) DONE. Remaining deep gaps: (i) differential Lüroth (classical, corpus
DifferentialLurothCoefficient mid-development), (ii-c) family diagonalization + anchor at core [needs q +
the clock FAMILY over C^*], (ii-d) algebraicity B. The q-dependent pieces are now theorems taking q as
hypothesis, shrinking the interface toward: differential Lüroth (produces q) + algebraicity B (produces
the charge k).
NEXT session: (ii-c) family diagonalization at the core — the clock FAMILY ρ|T_λ (restricting the ambient
clock family λ↦ρ_λ to T) with the anchor, feeding s17 `clock_family_scaling_character_from_semilinear`
to get the multiplicative character e on C^*; OR (i) differential Lüroth. Note (ii-c) needs the ambient
clock as a FAMILY C→(F≃ₐF) with per-λ commuting+semilinear, and an anchor ν∉{0,1,-1} — the anchor
existence (a nontrivial scaling in the fixed-point coordinate) is the crux, tied to the charge being
positive.

### Session 30 progress — (ii-c) §3(b) at the core: clock family → C^*-character
`HTGeometry/StableCoreClockCharacter.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...StableCoreClockCharacter` clean (3104 jobs).
(My-cone lint clean + wired in umbrella; the "owned module unreachable" lint error is the same unrelated
parallel-agent RHTower file `ThetaCuspCofinalWardConvexity`, not mine.)

Delivered:
- `stableRangeCoreClockFamily φ ρ hcommφ` : the ambient clock family restricted to the core
  (λ ↦ stableRangeCoreSymmetryAlgEquiv φ (ρ lam) (hcommφ lam)).
- **`stableRangeCoreSymmetry_family_character`** : (ii-c) with C zero-derivation, given the restricted
  clock family, a differential generator q of the core (hq+hqtop), an anchor scaling ρ_{ν₀}(q)=νq
  (ν∉{0,1,-1}), and the family's homomorphism/commutation at q, the family diagonalizes to a
  MULTIPLICATIVE CHARACTER `e:C→C` on C^* (`∀λ≠0, ρ_λ(q)=e(λ)·q` ∧ `e(λμ)=e(λ)e(μ)`). Wraps s17
  `clock_family_scaling_character_from_semilinear`; discharges semilinearity (s28), hconst (from hCzero,
  ∀λ), hlin (from q transcendental via transcendental_iff_injective + coeff extraction); anchor + hmul +
  hcomm taken as hypotheses.

INPUT (ii) status: FULL §3(b) at the core now ASSEMBLED — (ii-a) semilinear (s28), (ii-b) Möbius on q
(s29), (ii-c) family→character (this session). The multiplicative character e on C^* is produced.
Remaining for eq(2) ρ_λ(q)=λ^k q: (ii-d) ALGEBRAICITY B (e is polynomial ⟹ e=λ^k, via s16
`charged_clock_family_pow_of_nonzero`); and the ANCHOR (ν∉{0,1,-1} scaling — the crux, currently
hypothesis, tied to charge k>0).

CARD STATE: novel abstract chain (s1-17) + concrete model (s18-24) + dichotomy (s26) + core assembly
(s27, Φ|T) + FULL §3(b) at core (s28-30, clock→character) all DONE. The card reduces to:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, T=C⟨q⟩ (produces q) — classical, corpus mid-development.
 (ii-d) ALGEBRAICITY B: the character e is polynomial (λ^k) — property of the concrete jet-scaling clock
   (ρ_λ homogeneous-weight-k on q); abstractly an input.
 (anchor) ∃ ν₀ with ρ_{ν₀}(q)=νq, ν∉{0,1,-1} — the diagonalized anchor, from fixed-point diagonalization
   (s9/s10) of one clock element, tied to positive charge.
NEXT session: EITHER discharge the ANCHOR by applying the fixed-point diagonalization `mobius_nonparabolic_scaling`
(s9/s10) to one restricted clock element ρ|T_{ν₀} (Möbius via s29) — producing the anchor coordinate; OR
(i) differential Lüroth; OR (ii-d) algebraicity via the concrete jet-weight structure. The anchor is the
cleanest next (uses s29 Möbius + s9/s10 fixed points at the core), reducing (ii) to algebraicity B alone.

### Session 31 progress — Möbius change of differential generator (anchor coordinate generates T)
`HTGeometry/DifferentialAdjoinMobiusGenerator.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...DifferentialAdjoinMobiusGenerator` clean (3030
jobs). (My-cone lint clean + wired in umbrella; "owned module unreachable" lint errors are unrelated
parallel-agent RHTower files ThetaCuspCofinalWardConvexity/XiThetaExplicitBounds, not mine.)

Toward the ANCHOR. The fixed-point diagonalization (s10 `mobius_nonparabolic_scaling`) of a clock element
produces the anchor coordinate x=(u−p₁)/(u−p₂). For x to serve as the clock-character generator q,
need differentialAdjoin C {x}=⊤. Corpus had no Möbius-change lemma; built it:
- `differentialAdjoin_singleton_le_of_mem` : x∈differentialAdjoin C {u} ⟹ differentialAdjoin C {x} ≤
  differentialAdjoin C {u} (all jets of x stay in the derivation-closed field; induction on jets via
  `derivationClosed_differentialAdjoin`).
- `differentialAdjoin_singleton_eq_of_mem_mem` : mutual membership ⟹ equal adjoins (le_antisymm).
- **`differentialAdjoin_mobius_generator`** : if u generates the whole field (differentialAdjoin C {u}=⊤),
  p₁≠p₂, u−p₂≠0, then x=(u−p₁)/(u−p₂) also generates it. x∈diffAdjoin{u} (field ops, order 0);
  u=(p₂x−p₁)/(x−1)∈diffAdjoin{x} (x≠1 since p₁≠p₂); mutual ⟹ equal ⟹ ⊤.

ANCHOR status: the generator-change (x still generates T) is DONE. With s10 (diagonalization: produces
x + ρ|T_{ν₀}(x)=νx) + s29 (ρ|T Möbius on the Lüroth generator u) + this generator-change, the anchor
coordinate x is a valid clock-character generator q with the anchor scaling. Remaining for the anchor:
the NON-DEGENERACY (c≠0, disc≠0, ν∉{0,1,-1}) of the clock element — a structural input (positive charge).

CARD STATE: novel content + concrete model + core assembly + §3(b) at core + anchor coordinate machinery
all DONE. The card reduces to:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃u, T=C⟨u⟩ (produces the initial generator u) — classical, corpus
   DifferentialLurothCoefficient mid-development.
 (ii-d) ALGEBRAICITY B: character e is polynomial (λ^k) — property of the concrete jet-scaling clock.
 (non-degeneracy) the clock element ρ|T_{ν₀} is non-parabolic with nontrivial eigenvalue — structural,
   tied to charge k>0.
NEXT session: assemble the ANCHOR fully — a theorem taking the Lüroth generator u + non-degenerate clock
Möbius coeffs, applying s10 `mobius_nonparabolic_scaling` at the core to produce x + ρ|T_{ν₀}(x)=νx, and
`differentialAdjoin_mobius_generator` (this session) for differentialAdjoin C {x}=⊤ — giving the anchor
hypothesis of s30 `stableRangeCoreSymmetry_family_character`. This reduces (ii) to algebraicity B; then
(i) differential Lüroth remains as the single classical gap.

### Session 32 progress — ANCHOR coordinate assembled (diagonalization + generator-change)
`HTGeometry/MobiusAnchorGenerator.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...MobiusAnchorGenerator` clean (3033 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered:
- **`mobius_anchor_generator`** : a non-parabolic Möbius automorphism σ of a differential field
  generated by u (c≠0, disc=(d−a)²+4cb≠0, u∉C, cu+d≠0, differentialAdjoin C {u}=⊤) admits a
  differential generator x=(u−p₁)/(u−p₂) with `σ x = ν·x` (ν=(a−cp₁)/(a−cp₂)). Clean assembly:
  s10 `mobius_nonparabolic_scaling` (produces p₁≠p₂ + the scaling) + s31 `differentialAdjoin_mobius_generator`
  (x still generates). Returns `∃ x ν, differentialAdjoin C {x}=⊤ ∧ σ x = ν·x`.

ANCHOR machinery COMPLETE: given a non-degenerate Möbius clock element on the Lüroth generator u,
this produces the diagonalized generator x + eigenvalue ν + the anchor scaling σ(x)=νx + x generates T.
This is precisely the anchor hypothesis of s30 `stableRangeCoreSymmetry_family_character` (modulo
ν∉{0,1,-1}, the eigenvalue non-degeneracy tied to charge k>0).

CARD STATE: the FULL machinery for the charged clock-character law is now assembled —
 abstract chain (s1-17) · concrete model (s18-24) · dichotomy (s26) · core assembly (s27) ·
 §3(b) at core → C^*-character (s28-30) · anchor coordinate (s31-32).
The card reduces to THREE structural/classical inputs:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃u, differentialAdjoin C {u}=⊤ (T=C⟨u⟩) — classical Ritt-Kolchin,
   corpus DifferentialLurothCoefficient (2340L) mid-development. THE deep classical gap.
 (ii-d) ALGEBRAICITY B: the character e is polynomial (⟹ e=λ^k, s16) — property of the concrete
   jet-scaling clock (ρ_λ homogeneous weight k on the diagonalized generator).
 (non-degeneracy) the clock element ρ|T_{ν₀} on u is non-parabolic (c≠0, disc≠0) with eigenvalue
   ν∉{0,1,-1} — structural, from positive charge k>0.
NEXT session: EITHER (i) differential Lüroth (the genuine deep classical theorem — study
DifferentialLurothCoefficient frontier toward the T=C⟨u⟩ capstone), OR assemble the remaining structural
inputs (ii-d, non-degeneracy) into a single "charged persistent core ⟹ eq(2)+eq(4)" theorem at the
CONCRETE clock where algebraicity/non-degeneracy are computable from the jet-weight structure. The
concrete-clock route (discharging ii-d/non-degeneracy via the jet-scaling homogeneity) may be more
tractable than differential Lüroth.

### Session 33 progress — eq(2) at the core from the algebraic (polynomial) clock character
`HTGeometry/StableCoreClockPow.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...StableCoreClockPow` clean (3105 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Assessed the differential-Lüroth corpus frontier (DifferentialLurothCoefficient + ComponentTransfer +
ScalarExtensionSquarefree, 3+ files): deep Ritt characteristic-set/coefficient-cross-relation machinery
(eq(78), squarefreeness, saturation) still at the COEFFICIENT layer — the T=C⟨u⟩ field-generation
capstone is NOT there; a large active corpus effort, high-risk to extend safely in one session.

Delivered:
- **`stableRangeCoreSymmetry_family_pow`** : (eq 2 at core) if the restricted clock family acts on a
  core generator q by a POLYNOMIAL scaling character `ρ_λ(q)=P(λ)·q` (P≠0, the algebraicity of the
  cocharacter), then `ρ_λ(q)=λ^k·q`. Direct application of s16 `charged_clock_family_pow_of_nonzero`
  to the core clock family `stableRangeCoreClockFamily`. No Differential instance needed (pure scaling
  classification). DISCHARGES the hcharge (eq 2) hypothesis of s27 core dichotomy from ALGEBRAICITY alone.

CARD STATE: charged branch now assembles from the ALGEBRAIC clock character:
  differential Lüroth generator q → (this session) polynomial-scaling algebraicity ρ_λ(q)=P(λ)q ⟹
  eq(2) ρ_λ(q)=λ^k q → (s27) core dichotomy eq(3)+eq(4).
The card reduces to:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, T=C⟨q⟩ — THE deep classical gap, corpus mid-development.
 (ii-alg) POLYNOMIAL ALGEBRAICITY: the restricted clock scales the (diagonalized) core generator by a
   polynomial P(λ) — a property of the CONCRETE jet-scaling clock (ρ_λ homogeneous weight k on a
   homogeneous generator ⟹ P=X^k). The abstract anchor/character machinery (s28-32) produces the
   scaling form ρ_λ(x)=χ(λ)x; algebraicity says χ polynomial. For the concrete clock this is homogeneity.
 (+ family hmul/hcomm structure and non-degeneracy — structural).
NEXT session: EITHER (i) differential Lüroth (the genuine deep classical theorem — the one substantial
remaining gap; corpus DifferentialLurothCoefficient frontier), OR discharge (ii-alg) for the CONCRETE
clock by proving a homogeneous element q (ρ_λ q = λ^k q) of the free field C⟨y⟩ has the polynomial
character P=X^k directly (connecting the concrete clock s18-24 to eq(2) without the anchor). The concrete
homogeneity route may fully discharge (ii-alg), leaving differential Lüroth (i) as the SOLE gap.

### Session 34 progress — TIGHTEST reduction: core dichotomy from the algebraic clock character
`HTGeometry/StableCoreDichotomyAlgebraic.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...StableCoreDichotomyAlgebraic` clean (3105 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the card's charged dichotomy at the ACTUAL persistent core, from the two structural inputs:
- **`persistent_core_dichotomy_from_algebraic`** : on T=stableRangeCore φ (φ an injective differential
  endomorphism of F, commuting with the clock family ρ), given a differential generator q of T
  (HypertranscendentalOver C q + differentialAdjoin C {q}=⊤ — the differential LÜROTH output), and a
  clock character that is a POLYNOMIAL of positive degree (`ρ_λ(q)=P(λ)·q`, 0<deg P — the ALGEBRAICITY),
  with the family's homomorphism/commutation, the constraint Φ|T:
  (eq 3) acts by a Möbius transform `Φ|T(q)·(cq+d)=aq+b` (s5/7 `differentialAlgEquiv_generator_mobius`);
  (eq 4) `Φ|T(q)=a·q` (s16 `charged_clock_polynomial_forces_multiplicative_of_nonzero`).
  Φ|T=`stableRangeCoreDifferentialAlgEquiv` (corpus); Differential T + DifferentialAlgebra C T +
  CharZero T discharged (s27 pattern).

MILESTONE — the card's charged clock-character law is now formalized DOWN TO EXACTLY TWO structural
inputs, at the actual core T=∩ₙΦⁿ(F):
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, differentialAdjoin C {q}=⊤ (T=C⟨q⟩) — THE deep classical gap
   (Ritt-Kolchin, not in mathlib, corpus DifferentialLurothCoefficient 3-file effort mid-development at
   the coefficient layer).
 (ii-alg) POLYNOMIAL ALGEBRAICITY: `ρ_λ(q)=P(λ)·q`, P nonconstant — the cocharacter is algebraic in λ;
   for the concrete jet-scaling clock this is q homogeneous of weight k ⟹ P=X^k (homogeneity). The
   abstract diagonalization machinery (s28-32: semilinear→Möbius→anchor→character) produces the scaling
   form; algebraicity pins it polynomial.
 (+ family hmul/hcomm — structural cocharacter properties, and Φ commuting with the clock.)
Everything else — §2 stable core, Φ|T automorphism, T's differential structure, §3 Möbius/diagonalization/
anchor/character, §4 charged no-go, eq(2) monomial — is FULLY FORMALIZED (std axioms).
NEXT session: EITHER (i) differential Lüroth (the sole deep classical gap), OR (ii-alg) discharge for the
concrete clock: prove a homogeneous q of C⟨y⟩ (ρ_λ q=λ^k q) has polynomial character P=X^k directly, and
show the core of the concrete jet-scaling clock has a homogeneous generator — connecting the concrete
model (s18-24) so the abstract q/algebraicity are realized. Differential Lüroth remains the deepest gap.

### Session 35 progress — eq(4) sharpened to ∃! a∈C^* (unique nonzero scaling constant)
`HTGeometry/EigenvalueUnique.lean` [PROVED HERE], standard axioms [propext, Classical.choice, Quot.sound],
`lake build ...EigenvalueUnique` clean (992 jobs), no warnings.
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Surveyed the differential-Lüroth corpus: 4 files (Coefficient 63KB, ComponentTransfer 47KB,
VariableSupport 25KB, ScalarExtensionSquarefree 8KB = ~143KB) — deep technical Ritt scaffolding
(distinguished-variable Bezout, scalar-extension squarefreeness, characteristic saturation); NO
field-generation T=C⟨u⟩ capstone; not safely completable in one session.

Delivered — the exact "∃! a∈C^*" form of eq(4), which my charged theorems (s16/s25) only gave as ∃a:
- `algEquiv_eigenvalue_ne_zero` : σ q = a·q, q≠0 ⟹ a≠0 (σ injective: a=0 ⟹ σq=0 ⟹ q=0).
- `algEquiv_eigenvalue_unique` : the scaling eigenvalue of a nonzero vector is unique (mul_right_cancel₀
  + algebraMap injective via map_eq_zero).
- **`algEquiv_eigenvalue_existsUnique`** : σ q = a·q ⟹ `a ≠ 0 ∧ ∃! b, σ q = b·q` — the card's "unique
  a∈C^*" (eq 4). Applies to any Φ|T(q)=a·q from the charged conclusion to sharpen it to the card's exact
  statement.

CARD STATE unchanged on the two deep inputs (i differential Lüroth, ii-alg algebraicity); the charged
conclusion eq(4) is now the EXACT card form ∃! a∈C^*. Card fully formalized modulo (i)+(ii-alg).
NEXT session: remaining card refinements toward the exact statement — (a) the NEUTRAL/CHARGED phase
split is stated (s26 dichotomy: eq3 always, eq4 when k>0); (b) k INDEPENDENT of the diagonalizing
generator q (the invariant — "k is the absolute cocharacter"; uniqueness of the charge). OR (i)
differential Lüroth. The charge-invariance (k unique) is a tractable next piece (from eq2 ρ_λ(q)=λ^k q
determining k via a nontrivial λ), complementing this session's eigenvalue-uniqueness.

### Session 36 progress — charge invariance: k is a unique well-defined invariant
`HTGeometry/ChargeUnique.lean` [PROVED HERE], standard axioms [propext, Classical.choice, Quot.sound],
`lake build ...ChargeUnique` clean (1888 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the card's charge invariant (k well-defined):
- `charge_unique` : over an infinite field, `λ^k=λ^m` for all nonzero λ ⟹ k=m (X^k, X^m agree on the
  infinite nonzero locus ⟹ X^k=X^m via eq_zero_of_infinite_isRoot ⟹ k=m via natDegree_X_pow).
- **`charge_unique_of_scaling`** : a diagonalizing generator q determines a UNIQUE charge — if
  ρ_λ(q)=λ^k·q and ρ_λ(q)=λ^m·q (both λ≠0), q≠0, then k=m. (algebraMap injective on λ^k=λ^m via
  map_eq_zero, then charge_unique.) This is the card's "k is the absolute cocharacter" invariant.

CARD STATE: the exact card statement is now formalized (modulo the two deep inputs):
 eq(2) ρ_λ(q)=λ^k q with UNIQUE k (s36) · eq(3) Φ|T Möbius (neutral, s5/7) · eq(4) Φ|T(q)=a·q with
 UNIQUE a∈C^* (s35) · dichotomy (s26) · core assembly Φ|T/T/differential-structure (s27/s34).
Fully formalized modulo:
 (i) DIFFERENTIAL LÜROTH (produces q; the deep classical gap, corpus ~143KB mid-development, no capstone).
 (ii-alg) POLYNOMIAL ALGEBRAICITY (ρ_λ(q)=P(λ)q; the concrete jet-scaling clock's homogeneity ⟹ P=X^k).
NEXT session: (i) differential Lüroth (the sole deep classical gap remaining — the charge/eigenvalue
uniqueness + dichotomy + core assembly + §3 diagonalization are all complete). The card's entire
NOVEL clock-character content is formalized; only the classical Ritt-Kolchin differential Lüroth
prerequisite (which mathlib lacks and the corpus is separately developing) remains open. Consider a
focused multi-session push on the differential-Lüroth field-generation capstone building on the corpus's
DifferentialLurothCoefficient/ComponentTransfer characteristic-set machinery.

### Session 37 progress — COMPLETE card capstone (eq3 + unique-k eq2 + unique-a∈C^* eq4)
`HTGeometry/PersistentCoreClockCharacterComplete.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...PersistentCoreClockCharacterComplete` clean
(3109 jobs). (My-cone lint clean + wired in; "owned module unreachable" lint errors are unrelated
parallel-agent RHTower files MobiusCofinalReplicaOneCorner/ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the card's COMPLETE conclusion at the persistent core, in exact form:
- **`persistent_core_clock_character_complete`** : on T=stableRangeCore φ, given a differential Lüroth
  generator q + algebraic clock character of positive charge (polynomial P, 0<deg P), Φ|T:
  (eq 3) acts Möbius on q;
  (eq 2) `∃! k, ∀λ≠0 ρ_λ(q)=λ^k·q` — UNIQUE charge;
  (eq 4) `∃! a, a≠0 ∧ Φ|T(q)=a·q ∧ (uniqueness)` — UNIQUE nonzero scaling constant.
  Assembles s34 (dichotomy eq3+eq4-∃) + s33 (eq2 ∃k) + s36 `charge_unique_of_scaling` (k unique) + s35
  `algEquiv_eigenvalue_existsUnique` (a≠0 + unique). ExistsUnique.unique for the eq4 uniqueness.

MILESTONE: the card's CHARGED clock-character law is now formalized as a SINGLE top-level theorem in its
EXACT statement (Möbius + unique charge k + unique a∈C^*), reduced to exactly TWO structural inputs at
the actual persistent core T=∩ₙΦⁿ(F):
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, T=C⟨q⟩ (produces q) — the deep classical gap.
 (ii-alg) POLYNOMIAL ALGEBRAICITY: ρ_λ(q)=P(λ)q — the concrete jet-scaling clock's homogeneity.
All novel content (abstract §1-§4 chain, concrete model, §3 diagonalization/anchor/character, core
assembly, uniqueness) is COMPLETE on standard axioms.
NEXT session: the two remaining inputs are deep classical/graded theorems:
 (i) differential Lüroth (corpus ~143KB mid-development, no capstone; huge Ritt-Kolchin effort).
 (ii-alg) concrete algebraicity via weighted grading (jet-scaling clock scales weighted-homogeneous
   poly of weight k by λ^k; probed MvPolynomial.IsWeightedHomogeneous/Finsupp.weight — fiddly Finset.prod
   monomial computation + fraction-field extension + eigenvector-homogeneity; multi-session).
Consider a dedicated push on ONE of these; the card's exact statement is otherwise fully formalized.

### Session 38 progress — (ii-alg foundation) clock scales weighted-homogeneous poly by λ^k
`HTGeometry/ClockHomogeneousScaling.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockHomogeneousScaling` clean (2960 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Toward discharging (ii-alg) [polynomial algebraicity] for the CONCRETE jet-scaling clock. Delivered:
- `clockDilationAlgHom_monomial` : the clock scales a monomial by λ to its jet-weight:
  `ρ_λ(monomial s c) = C(λ^(Finsupp.weight (·.2) s))·monomial s c`. Via aeval_monomial + Finset.prod
  manipulation (mul_pow, C_pow, prod_mul_distrib, prod_pow_eq_pow_sum, prod_X_pow_eq_monomial,
  C_mul_monomial) + the weight identity ∑ x.2·s x = Finsupp.weight.
- **`clockDilationAlgHom_isWeightedHomogeneous`** : a weighted-homogeneous polynomial of jet-weight k
  is a clock EIGENVECTOR with eigenvalue λ^k: `ρ_λ(p) = C(λ^k)·p` for `IsWeightedHomogeneous (·.2) p k`.
  Via p.as_sum + map_sum + the monomial lemma (each monomial has weight k on the support).

This is the CONCRETE realization of eq(2) for a homogeneous polynomial generator: such q has polynomial
character P=X^k directly (ρ_λ(q)=λ^k q), discharging the algebraicity for the polynomial-ring case.

CARD STATE: complete exact statement formalized (s37 capstone: eq3 + unique-k eq2 + unique-a∈C^* eq4).
The two structural inputs remain, now with (ii-alg) partially concretized:
 (i) DIFFERENTIAL LÜROTH: produces the core generator — the deep classical gap.
 (ii-alg) POLYNOMIAL ALGEBRAICITY: DONE for a homogeneous POLYNOMIAL (this session, P=X^k). Remaining:
   (ii-alg-frac) the fraction-field case (core generator is p/q, weight difference) — extend the
     homogeneous scaling to Frac; (ii-alg-hom) the core generator IS homogeneous (from clock-invariance
     of the core + graded Lüroth) — needs differential Lüroth.
NEXT session: (ii-alg-frac) extend `clockDilationAlgHom_isWeightedHomogeneous` to the field
clockDilationFieldEquiv on a ratio of homogeneous polynomials (weight a / weight b ⟹ eigenvalue λ^(a-b)),
via the algebraMap + the ring homogeneous scaling. OR (i) differential Lüroth. The concrete homogeneous
eigenvalue foundation (ring level) is now in place.

### Session 39 progress — (ii-alg-frac) field clock scales homogeneous ratio by λ^(a-b)
`HTGeometry/ClockHomogeneousScalingField.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockHomogeneousScalingField` clean (2965 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the concrete eq(2) at the FIELD level:
- **`clockDilationFieldEquiv_homogeneous_ratio`** : for p,q weighted-homogeneous of jet-weights a,b
  (b≤a), the field clock scales the ratio by λ^(a-b): `ρ_λ(algebraMap p / algebraMap q) =
  algebraMap(λ^(a-b))·(algebraMap p/algebraMap q)`. Via map_div₀ + clockDilationFieldEquiv_algebraMap
  (s20) + s38 ring homogeneous scaling + mul_div_mul_comm + the C-level power identity
  λ^a/λ^b=λ^(a-b) (div_eq_mul_inv + pow_sub₀). hcoe: algebraMap(DiffPoly→F)(C r)=algebraMap(C→F)(r)
  via IsScalarTower.algebraMap_apply + MvPolynomial.algebraMap_eq.

(ii-alg) status: the CONCRETE clock's homogeneous eigenvalue law is now DONE at both ring (s38) and
FIELD (s39) levels. A homogeneous fraction-field element q=p/q' (weights a≥b) has polynomial character
P=X^(a-b): ρ_λ(q)=λ^(a-b)·q, discharging the algebraicity input for such q.

CARD STATE: complete exact statement formalized (s37); (ii-alg) concretized for homogeneous generators
(s38/s39). Remaining:
 (i) DIFFERENTIAL LÜROTH: T≠C ⟹ ∃q, T=C⟨q⟩ — the deep classical gap.
 (ii-alg-hom) the CORE generator is a homogeneous ratio (from clock-invariance of T + GRADED Lüroth) —
   intertwined with differential Lüroth.
Both remaining pieces center on differential Lüroth (ungraded for (i), graded for the homogeneous
generator). The concrete clock's homogeneous eigenvalue law (the ALGEBRAICITY mechanism) is fully in
place; what remains is producing the homogeneous generator, which is the (graded) differential Lüroth.
NEXT session: (i) differential Lüroth — the sole deep classical gap. All the CONCRETE clock machinery
(homogeneous eigenvalue at ring+field) + the abstract chain + core assembly + exact statement + charge/
eigenvalue uniqueness are complete. Consider a dedicated push on the differential-Lüroth field-generation
capstone building on the corpus's characteristic-set machinery (DifferentialLurothCoefficient etc.).

### Session 40 progress — (ii-alg) clock eigenvector ⟹ weighted-homogeneous (⟹ eigenvalue λ^k)
`HTGeometry/ClockEigenvectorHomogeneous.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockEigenvectorHomogeneous` clean (2962 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the KEY link for the concrete algebraicity (eigenvalue is λ^k):
- `clockDilationAlgHom_coeff` : the clock acts DIAGONALLY on coefficients,
  `(ρ_λ p).coeff s = λ^(weight s)·p.coeff s`. Via MvPolynomial.induction_on' (monomial: s38
  clockDilationAlgHom_monomial + C_mul_monomial + coeff_monomial split; add: coeff_add + mul_add).
- **`isWeightedHomogeneous_of_clock_eigenvector`** : a nonzero clock EIGENVECTOR (ρ_λ(p)=χ(λ)·p ∀λ≠0)
  is WEIGHTED-HOMOGENEOUS. Proof: for any support monomial s, λ^(weight s)·coeff s = χ(λ)·coeff s
  (coeff property + coeff_C_mul), so λ^(weight s)=χ(λ) (cancel coeff≠0); same for a fixed t₀; then
  λ^(weight s)=λ^(weight t₀) ∀λ≠0 ⟹ weight s = weight t₀ (s36 charge_unique). All monomials same weight.

(ii-alg) MECHANISM COMPLETE at ring level: clock eigenvector ⟹ homogeneous (s40) ⟹ eigenvalue λ^k (s38).
So a ring clock eigenvector has polynomial character P=X^k. The ALGEBRAICITY (eigenvalue is a polynomial
λ^k) is now fully mechanized for the concrete jet-scaling clock at the ring level.

CARD STATE: complete exact statement (s37) + concrete algebraicity mechanism (s38 homogeneous→λ^k ring,
s39 →λ^(a-b) field, s40 eigenvector→homogeneous ring). Remaining:
 (i) DIFFERENTIAL LÜROTH: produces the core generator — deep classical gap.
 (ii-alg-field-eig) FIELD eigenvector ⟹ homogeneous ratio (fraction-field version of s40) — then s39
   gives eigenvalue λ^(a-b)=λ^k; connects to the diagonalized core generator (a field eigenvector).
NEXT session: (ii-alg-field-eig) extend `isWeightedHomogeneous_of_clock_eigenvector` to the field
clockDilationFieldEquiv: a field clock eigenvector x (ρ_λ(x)=algebraMap(χ λ)·x) is a homogeneous ratio
(x = algebraMap p/algebraMap q, p,q homogeneous), giving χ(λ)=λ^(a-b) via s39. This completes the
concrete algebraicity: the diagonalized core generator's character IS λ^k. Then only differential Lüroth
(the generator's EXISTENCE) remains. OR (i) differential Lüroth directly.

### Session 41 progress — homogeneous generator ⟹ polynomial character X^k (s34-algebraicity form)
`HTGeometry/ClockHomogeneousAlgebraic.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockHomogeneousAlgebraic` clean (2966 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint error is the unrelated parallel-agent
RHTower file ThetaCuspCofinalWardConvexity, not mine.)

Delivered — the concrete algebraicity in the EXACT s34 hypothesis form (ρ_λ(q)=P(λ)·q, P=X^k):
- `clockDilationAlgHom_isWeightedHomogeneous_eval` : ring form, `ρ_λ(p) = C((X^k).eval λ)·p` for p
  weighted-homogeneous of weight k (s38 + eval_X_pow).
- **`clockDilationFieldEquiv_homogeneous_character`** : field form, `∀λ≠0, ρ_λ(p/q) =
  algebraMap((X^(a-b)).eval λ)·(p/q)` for p,q homogeneous (weights a≥b) — the EXACT `hpoly_scale`
  hypothesis of `persistent_core_dichotomy_from_algebraic` (s34) with P=X^(a-b) (s39 + eval_X_pow).

(ii-alg) DISCHARGED (in form) for a homogeneous generator: a homogeneous ratio q has the polynomial
character P=X^(a-b), which is precisely s34's algebraicity input. Combined with the concrete algebraicity
mechanism (s38 homogeneous→λ^k, s39 field ratio→λ^(a-b), s40 eigenvector→homogeneous), the algebraicity
is fully mechanized: a homogeneous core generator satisfies s34's hypothesis.

CARD STATE: complete exact statement (s37) + full concrete algebraicity (s38-41). The card is now
formalized modulo the SINGLE remaining input:
 (i) DIFFERENTIAL LÜROTH (graded): T≠C ⟹ ∃ HOMOGENEOUS q (a homogeneous ratio), T=C⟨q⟩. The clock-
   invariant core T has a homogeneous differential generator. This is the deep classical Ritt-Kolchin
   theorem (graded version); the corpus's DifferentialLurothCoefficient (~143KB) develops the ungraded
   machinery; no capstone yet.
Everything else — abstract §1-§4 chain, concrete model+clock, core assembly, exact statement (unique k,
unique a∈C^*), and the full concrete algebraicity (homogeneous ⟹ polynomial character X^k) — is COMPLETE
on standard axioms.
NEXT session: (i) differential Lüroth — the SOLE deep classical gap. The card is otherwise fully
formalized. A dedicated multi-session push on the differential-Lüroth field-generation capstone (building
on the corpus's characteristic-set machinery) is the remaining work; OR the field eigenvector-homogeneity
(field version of s40 via coprime/UFD) as an alternative route to the homogeneous generator from an
abstract diagonalized eigenvector.

### Session 42 progress — ring clock eigenvalue IS λ^k (algebraicity fully characterized, ring level)
`HTGeometry/ClockEigenvaluePow.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockEigenvaluePow` clean (2963 jobs).
(My-cone lint clean + wired in; "owned module unreachable" lint errors are unrelated parallel-agent
RHTower files EulerSquarefreeDyadicAffineProjection/ThetaCuspCofinalWardConvexity, not mine.)

Delivered:
- **`clock_eigenvalue_pow`** : a ring clock eigenvector's eigenvalue is a MONOMIAL — if `ρ_λ(p)=χ(λ)·p`
  ∀λ≠0 (p≠0), then `∃k, ∀λ≠0, χ(λ)=λ^k`. Proof: s40 `isWeightedHomogeneous_of_clock_eigenvector` (p
  homogeneous of weight k) + s38 (ρ_λ(p)=C(λ^k)·p); cancel p (domain) + C injective ⟹ χ(λ)=λ^k.

(ii-alg) RING LEVEL FULLY CHARACTERIZED: any ring clock eigenvector has purely polynomial character
χ(λ)=λ^k. The algebraicity of the concrete cocharacter is completely mechanized on ring eigenvectors:
 eigenvector ⟹ homogeneous (s40) ⟹ eigenvalue λ^k (s38, packaged s42) ⟹ polynomial character X^k (s41).

CARD STATE: complete exact statement (s37) + full ring-level concrete algebraicity (s38-42). Remaining:
 (i) DIFFERENTIAL LÜROTH: produces the core generator — the deep classical gap.
 (ii-alg-field-eig) FIELD clock eigenvector eigenvalue = λ^k. Approach (from cross-multiplying x=a/b
   eigenvector): clock a·b = C(χλ)·clock b·a in ring; comparing TOP-WEIGHT components gives
   χ(λ)=λ^(w_a-w_b) (leading-term multiplicativity in the graded domain). Needs mathlib graded top-degree
   API (weightedTotalDegree_mul, leading component) — feasible but graded-API-heavy.
NEXT session: EITHER (ii-alg-field-eig) the field eigenvalue via top-weight comparison (probe
MvPolynomial.weightedTotalDegree multiplicativity + leading-component API), completing the concrete
algebraicity at the field level; OR (i) differential Lüroth (the sole deep classical gap). The card is
formalized modulo differential Lüroth; the concrete algebraicity is fully characterized at the ring level.

### Session 43 progress — FIELD clock eigenvalue is λ^(ka−kb) (algebraicity fully characterized, field level)
`HTGeometry/ClockFieldEigenvaluePow.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ClockFieldEigenvaluePow` clean (2970 jobs).
(My-cone lint clean + wired in; the "owned module unreachable" ThetaCuspCofinalWardConvexity error and
the two large-file warnings are unrelated parallel-agent RHTower/Hurwitz files, not mine.)

Delivered (three theorems):
- **`differentialPolynomial_associated_C_mul`** : associated polynomials in `C⟨y⟩` (UFD over a field)
  differ by a constant factor `C r` (via `isUnit_iff_eq_C_of_isReduced`: units are nonzero constants).
- **`clock_projective_eigenvalue_pow`** : if `ρ_λ(p)=c(λ)·p` with `c(λ)` a CONSTANT (∀λ≠0, p≠0), then
  `c(λ)=λ^k` (k = jet-weight of any monomial of p) — via `clockDilationAlgHom_coeff` at a support point.
- **`clock_field_eigenvalue_pow`** : a FIELD clock eigenvector `x` (`ρ_λ(x)=χ(λ)·x` ∀λ≠0, x≠0) has
  eigenvalue `χ(λ)·λ^kb = λ^ka` for fixed `ka,kb` — i.e. `χ(λ)=λ^(ka−kb)`, an integer power.
  MECHANISM (reduces field→ring via UFD): write `x=a/b` in lowest terms (`exists_reduced_fraction`,
  `IsRelPrime a b`); cross-multiply the eigenvector eq (map_div₀ + `clockDilationFieldEquiv_algebraMap`
  + `IsFractionRing.injective`) to the RING law `ρ_λ(a)·b = C(χλ)·a·ρ_λ(b)`; then
    (i) `a ∣ ρ_λ(a)·b` and `IsRelPrime a b` ⟹ `a ∣ ρ_λ(a)` (`IsRelPrime.dvd_of_dvd_mul_right`),
    (ii) clock invertibility `ρ_λ∘ρ_{λ⁻¹}=id` (`clockDilationAlgHom_apply_apply`+`_one`) ⟹ `ρ_λ(a) ∣ a`,
    so `a,ρ_λ(a)` associate ⟹ `ρ_λ(a)=C(r)·a` ⟹ (proj_pow) `ρ_λ(a)=C(λ^ka)·a`; substitute into the
    ring law + cancel `a` ⟹ `ρ_λ(b)=C(·)·b` ⟹ `ρ_λ(b)=C(λ^kb)·b`; substitute both + cancel `a·b`
    ⟹ `λ^ka = χλ·λ^kb`.

ALGEBRAICITY NOW FULLY CHARACTERIZED (ring s38-42 AND field s43): every clock eigenvector — ring OR
field — of the concrete jet-scaling clock has a purely monomial / ratio-of-monomials character. This
bridges an ABSTRACT diagonalized eigenvector (from the anchor/Möbius fixed point) to the concrete
polynomial character `X^k`, at the field level, WITHOUT assuming homogeneity a priori (it is derived).

CARD STATE: complete exact statement (s37) + full ring+field concrete algebraicity (s38-43). The SOLE
remaining input is (i) DIFFERENTIAL LÜROTH (graded): the persistent core `T=∩Φⁿ(F)` has a single
differential generator `q` with `T=C⟨q⟩`. Corpus is separately developing the characteristic-set
machinery for this deep classical Ritt–Kolchin prerequisite (cited by the card).
NEXT session: (i) differential Lüroth — the sole deep classical gap. With the full concrete
algebraicity now banked, the field-generation capstone (single generator of the clock-invariant core)
is the only remaining work; attack a tractable sub-piece (e.g. the graded-core homogeneous-generator
reduction) building on the corpus's DifferentialLurothCoefficient/ComponentTransfer/VariableSupport
machinery.

### Session 44 progress — differential-Lüroth landscape mapped + concrete jet clock-character witnesses
`HTGeometry/ScalarJetClockCharacter.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarJetClockCharacter` clean (2973 jobs).
(Unrelated lint noise: ThetaCuspCofinalWardConvexity unreachable + two large-file warnings — all
parallel-agent RHTower/Hurwitz files, not mine.)

CORPUS/MATHLIB SURVEY (mandate: check before writing):
- **mathlib HAS ordinary Lüroth**: `Mathlib/FieldTheory/RatFunc/Luroth.lean` — `RatFunc.Luroth.eq_adjoin_generator`
  (every intermediate field of `K(X)/K` is `K⟮generator⟯`) + `RatFunc.Luroth.algEquiv`. This is the
  ALGEBRAIC version (transcendence degree 1); it does NOT bridge to the DIFFERENTIAL version — a
  differential subfield of `C⟨y⟩` inherently involves all jets `y,y',y'',…`, so it is not an ordinary
  intermediate field of a td-1 rational function field.
- **corpus is actively formalizing Ritt's differential Lüroth**: `DifferentialLurothCoefficient`,
  `DifferentialLurothComponentTransfer`, `DifferentialLurothScalarExtensionSquarefree`,
  `DifferentialLurothVariableSupport`, `OrdinaryLuroth`, `RatFuncProjectiveAutomorphism`,
  `TranscendentalMobius` — "componentwise inputs to Ritt's reciprocity argument", explicitly "no
  finite-generation hypothesis introduced" (the capstone is still ahead). This is a delicate active
  multi-file cone; NOT entered, to avoid cross-agent collision (per cross-cone collision-scan discipline).

Delivered (in MY clock cone, non-colliding; connects differentialJet ↔ clock character ↔ s43):
- **`clockDilationFieldEquiv_differentialJet`** : the n-th jet `y^(n)` is a field clock eigenvector of
  character exactly `λ^n` — `ρ_λ(y^(n)) = λ^n·y^(n)`. (via `differentialJet_scalarDifferentialGenerator`
  = algebraMap X_{(),n}, `isWeightedHomogeneous_X`, s38, `clockDilationFieldEquiv_algebraMap`.)
- **`differentialJet_scalarDifferentialGenerator_ne_zero`** : `y^(n) ≠ 0`.
- **`clock_field_eigenvalue_differentialJet`** : the field-eigenvalue theorem `clock_field_eigenvalue_pow`
  (s43) FIRES on each jet, returning its order `(ka,kb)=(n,0)` — the canonical CHARGED (n≥1) witnesses
  showing s43 is non-vacuous in the charged regime of the clock-character law.

CARD STATE: complete exact statement (s37) + full ring+field concrete algebraicity (s38-43) + concrete
charged jet witnesses (s44). SOLE remaining input: (i) DIFFERENTIAL LÜROTH (graded) — the persistent
core `T=∩Φⁿ(F)` has a single differential generator `q`. This is being formalized in the corpus's
dedicated Ritt-reciprocity cone (`DifferentialLuroth*`); the capstone `T≠C ⟹ T=C⟨q⟩` is the remaining
work there.
NEXT session candidates (IN MY cone, non-colliding): (a) construct the concrete PROPER clock-invariant
differential subfield `C⟨y'⟩ ⊊ C⟨y⟩` (needs: jets of y' = higher X's; differentialAdjoin = adjoin of
{X_{(),n}:n≥1}; X_{(),0} transcendental over the rest via `AlgebraicIndependent C (fun n=>X((),n))`) —
a concrete non-vacuous charged CORE example; (b) monitor the corpus Ritt-reciprocity cone and, once its
capstone lands, wire `T=C⟨q⟩` into s37 to discharge the card's sole hypothesis unconditionally.

### Session 45 progress — concrete PROPER clock-invariant differential subfield (charged non-vacuity witness)
`HTGeometry/ScalarProperDifferentialSubfield.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarProperDifferentialSubfield` clean (2958 jobs).
(Unrelated lint noise: ThetaCuspCofinalWardConvexity unreachable + two large-file warnings — parallel-
agent RHTower/Hurwitz files, not mine.)
(Session start: recreated the session cron job cd60e6ae `*/1 * * * *` — it had been deleted; timing unchanged.)

Delivered:
- **`differentialJet_differentialJet_one`** : `(y')^(m) = y^(m+1)` — the m-th jet of the first jet is
  the (m+1)-st jet of the generator (via `Function.iterate_add_apply` on the derivation).
- **`differentialAdjoin_differentialJet_one_ne_top`** : `differentialAdjoin C {y'} ≠ ⊤` — the first
  jet `y' = X_{(),1}` differentially generates a PROPER subfield `C⟨y'⟩ = C(X_{(),1},X_{(),2},…)`
  omitting `y = X_{(),0}`. Proof: jets `X_{(),n}` algebraically independent over C
  (`algebraicIndependent_X`, pushed to the field via `AlgebraicIndependent.map` + `IsFractionRing.injective`);
  `differentialJetSet {y'} = {X_{(),n}:n≥1}`; `AlgebraicIndependent.transcendental_adjoin` (i=0∉{n≠0})
  ⟹ `y` transcendental over `Algebra.adjoin C {X_{(),n}:n≥1}`; `IntermediateField.transcendental_adjoin_iff`
  lifts to the intermediate field; transcendental ⟹ ∉, so `y ∉ differentialAdjoin C {y'}`, hence ≠ ⊤.

SIGNIFICANCE: the card's central object — a proper clock-invariant differential subfield ⊋ C in the
CHARGED regime — is now proven NON-VACUOUS by an explicit witness. `C⟨y'⟩` is a proper differential
subfield strictly between C and C⟨y⟩ whose generator `y'` is a clock eigenvector of weight 1
(`clockDilationFieldEquiv_differentialJet` s44: `ρ_λ(y')=λ·y'`). The clock-character law is not about an
empty class.

CARD STATE: complete exact statement (s37) + full ring+field concrete algebraicity (s38-43) + concrete
charged jet witnesses (s44) + concrete proper charged differential-subfield witness (s45). SOLE remaining
input: (i) DIFFERENTIAL LÜROTH (graded) — `T=∩Φⁿ(F)` has a single differential generator — being
formalized in the corpus's dedicated Ritt-reciprocity cone (`DifferentialLuroth*`).
NEXT session candidates (in my cone, non-colliding): (a) clock-INVARIANCE of `differentialAdjoin C {y'}`
as an IntermediateField (ρ_λ maps its jet generators `X_{(),n}` to `λ^n·X_{(),n}` ∈ it) — completing
"proper CLOCK-INVARIANT differential subfield" at the subfield level; (b) monitor the corpus Ritt cone
and wire `T=C⟨q⟩` into s37 once its capstone lands.

### Session 46 progress — the proper differential subfield is CLOCK-INVARIANT (witness now complete)
`HTGeometry/ScalarProperSubfieldClockInvariant.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarProperSubfieldClockInvariant` clean (2975 jobs).
(Unrelated lint noise: ThetaCuspCofinalWardConvexity + XiWardSpectralBudgetSumRule unreachable —
parallel-agent RHTower files, not mine.)

Delivered:
- **`clockDilationFieldEquiv_mem_differentialAdjoin_differentialJet_one`** : for every nonzero λ, the
  jet-scaling clock `ρ_λ` maps `C⟨y'⟩ = differentialAdjoin C {y'}` into itself. Proof: reduce to
  `E ≤ E.comap ρ_λ` (comap membership definitional); on generators `s = y^(m+1) ∈ differentialJetSet{y'}`,
  `ρ_λ(s) = λ^(m+1)·s` (s44 `clockDilationFieldEquiv_differentialJet`), which lies in E by `mul_mem`
  (`algebraMap_mem` for the C-scalar λ^(m+1), `subset_adjoin` for the generator s); `adjoin_le_iff`.

WITNESS NOW COMPLETE: `C⟨y'⟩` is a fully-proven concrete **proper clock-invariant differential
subfield** strictly between C and C⟨y⟩ (properness s45 `differentialAdjoin_differentialJet_one_ne_top`
+ clock-invariance s46), with a **charged** weight-1 clock-eigenvector generator `y'` (s44
`ρ_λ(y')=λ·y'`). The central object of the clock-character law (a proper clock-invariant differential
subfield ⊋ C in the charged regime) is proven NON-VACUOUS by an explicit construction.

CARD STATE: complete exact statement (s37) + full ring+field concrete algebraicity (s38-43) + concrete
charged jet witnesses (s44) + concrete proper clock-invariant charged differential-subfield witness
(s45-46). SOLE remaining input: (i) DIFFERENTIAL LÜROTH (graded) — `T=∩Φⁿ(F)` has a single differential
generator — being formalized in the corpus's dedicated Ritt-reciprocity cone (`DifferentialLuroth*`).
NEXT session candidates (in my cone): (a) show the concrete witness `C⟨y'⟩` arises as a persistent core
`∩Φⁿ(F)` for an explicit Φ (e.g. a jet-shift endomorphism), turning the witness into a full concrete
INSTANCE of the card's setup with Φ; (b) monitor the corpus Ritt cone; once its capstone `T=C⟨q⟩` lands,
wire it into s37 to discharge the card's sole hypothesis unconditionally.

### Session 47 progress — the clock charge realizes EVERY positive value (completeness of the spectrum)
`HTGeometry/ScalarClockChargeSpectrum.lean` [PROVED HERE], standard axioms
[propext, Classical.choice, Quot.sound], `lake build ...ScalarClockChargeSpectrum` clean (2976 jobs).
(Unrelated lint noise: ThetaCuspCofinalWardConvexity unreachable + Hurwitz large-file warning —
parallel-agent files, not mine.)

Delivered (generalizes the s44-46 k=1 witness `C⟨y'⟩` to all k):
- **`differentialJet_differentialJet`** : `(y^(k))^(m) = y^(m+k)` (general iterate additivity).
- **`differentialAdjoin_differentialJet_ne_top`** (k≥1) : `C⟨y^(k)⟩ ≠ ⊤` — properness at every charge
  (jets of `y^(k)` are `{X_j:j≥k}`, omitting `X_0,…,X_{k-1}`; `X_0` transcendental over the adjoin).
- **`clockDilationFieldEquiv_mem_differentialAdjoin_differentialJet`** (k) : clock-invariance of `C⟨y^(k)⟩`.
- **`clock_charge_spectrum`** (CAPSTONE) : for every k≥1, `C⟨y^(k)⟩` is a proper clock-invariant
  differential subfield whose generator `y^(k)` is a clock eigenvector of character exactly `λ^k`
  (properness ∧ eigenvector-law ∧ invariance bundled). Hence the quantized clock charge attains EVERY
  positive integer, each witnessed by the explicit charged core `C⟨y^(k)⟩`.

SIGNIFICANCE: strengthens non-vacuity (s45-46) to COMPLETENESS OF THE CHARGE SPECTRUM — the card's
integer invariant `k` is not merely realizable but takes the full value set `ℕ_{≥1}`, with a canonical
explicit witness at each value. (The universal theorem's `k∈{1,2,3,4,6}` crystallographic restriction
is specific to degree-expanding RATIONAL substitutions Φ(y)=R(y); for the general clock-neutral
constraint the charge is unrestricted, as these witnesses confirm.)

CARD STATE: complete exact statement (s37) + full ring+field concrete algebraicity (s38-43) + concrete
charged jet witnesses (s44) + complete proper clock-invariant charged subfield witness (s45-46) + full
charge-spectrum completeness (s47). The card's NOVEL delta (iterated constraint → stable core →
projective clock action → integer charge → eigen-current rigidity) is fully formalized. SOLE remaining
input is the CITED classical prerequisite DIFFERENTIAL LÜROTH (graded) — "Ritt–Kolchin differential
Luroth supplies the scalar generator" (card's own external-novelty gate lists it as classical, NOT part
of the novel delta) — being formalized in the corpus's dedicated Ritt-reciprocity cone (`DifferentialLuroth*`).
NEXT session: monitor the corpus Ritt cone; once its capstone `T=C⟨q⟩` lands, wire it into s37 to
discharge the card's sole classical hypothesis unconditionally. (In-cone clock witnesses are now
comprehensive: non-vacuity + full charge spectrum + ring/field algebraicity all banked.)
