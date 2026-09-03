# Canonical defect-slope normal form for a stage-two counterexample

- **ID:** schanuel-stage-two-defect-slope-normal-form
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** algebraic-coefficient defect theorem + Kirby exponential algebraicity
- **Statement:** Any stage-two Schanuel counterexample is a one-variable algebraic-function system with a canonical transcendental, exponentially algebraic defect slope and fixed algebraic-endpoint regulator values.

## Goal

Replace an amorphous four-number algebraic-dependence failure by one canonical one-variable object.
This is the strongest non-circular normal form obtained after the Ax-lift and constant-coefficient
descent attacks.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3  formalized: depends on formal algebraic-coefficient defect theorem
- [ ] 3 -> 4  publication-ready: external novelty and independent proof audit pending

## Statement

Assume `x_1,x_2` are `Q`-linearly independent and

\[
 K=\overline{\mathbb Q}(x_1,x_2,e^{x_1},e^{x_2})
\]

has transcendence degree less than two.  Put `y_i=e^{x_i}` and
`epsilon_i=dy_i/y_i-dx_i` in `Omega_{K/Qbar}`.  Then:

1. `trdeg_Qbar K=1`;
2. there is a unique `rho in K` with `epsilon_2=rho epsilon_1`;
3. `rho` is transcendental over `Qbar`, so `K/Qbar(rho)` is finite;
4. the tuple is an essential counterexample, and `rho` lies in the countable
   exponential-algebraic closure `ecl^C(emptyset)`;
5. on the normalized projective curve `V/Qbar` with function field `K`, for every algebraic smooth
   base point `q` avoiding coordinate poles and zeroes, and every smooth path from `q` to the
   complex point `p=(x,y)` that stays in the complement of the coordinate divisors, suitable
   logarithm branches give

\[
 \int_q^p\epsilon_i=X_i(q)-\log Y_i(q)+2\pi i k_i,\qquad k_i\in\mathbb Z. \tag{R}
\]

Thus a first counterexample is controlled by a transcendental exponentially algebraic slope and a
pair of length-one exponential-period regulator values at algebraic endpoints.

## Proof

Hermite--Lindemann rules out `trdeg K=0`, so a counterexample has `trdeg K=1`.  Therefore
`Omega_{K/Qbar}` is one-dimensional over `K`.  The defect-lattice theorem makes each `epsilon_i`
nonzero, giving a unique quotient `rho=epsilon_2/epsilon_1`.

Algebraic-coefficient independence of the defects rules out `rho in Qbar`.  Hence `rho` is
transcendental and is a transcendence basis of the one-variable function field, so `K` is finite
over `Qbar(rho)`.

For stage two, every proper nonzero rational subspace has dimension one and satisfies Schanuel by
Hermite--Lindemann; every rank-two tuple in the same rational span has transcendence degree at least
one. Hence the counterexample is essential in Kirby's sense. Kirby's theorem places it in
`ecl^C(emptyset)`.  Exponential algebraic closure is an algebraically closed exponential subfield;
it contains `K` and therefore `rho`.

Finally, write the coordinate functions on `V` as `X_i,Y_i`.  Direct integration gives

\[
 \int_q^p(d\log Y_i-dX_i)
 =\log\!\frac{Y_i(p)}{Y_i(q)}-(X_i(p)-X_i(q)).
\]

Using `Y_i(p)=exp(X_i(p))` cancels the transcendental endpoint coordinate and yields (R), with the
integer recording the logarithm branch. **[PROVED HERE]**

## Hostile audit

- The ratio `rho` exists only because the hypothetical value field is a curve; no coordinate choice
  is used.
- Transcendence of `rho` uses the proved algebraic-coefficient floor, not a dimension count over the
  wrong scalar field.
- Kirby supplies countability/exponential algebraicity, not nonexistence; no generic-power theorem
  applies to an exponentially algebraic slope.
- Regulator identity (R) is exact but does not make `p` algebraic. Existing period theorems do not
  control Abelian integrals with a transcendental endpoint.

## Failed continuations

1. **Trace/norm descent.** Applying the finite-field trace to
   `epsilon_2=rho epsilon_1` gives a rational-function differential identity over `Qbar(rho)`, but
   field conjugates do not preserve `Y_i=exp(X_i)`. The value identity is lost exactly where the
   trace would amplify it.
2. **Ax-compatible arc.** A curve through `p` satisfying the exponential differential equation is
   forbidden by the pole-order lemma unless constant.
3. **Generic powers.** The canonical slope lies in exponential algebraic closure, precisely the
   exceptional set excluded by generic-power Schanuel theorems.

## New open core

Prove that no one-variable algebraic-function system over `Qbar(rho)`, with `rho` transcendental and
exponentially algebraic, can realize both regulator specializations (R) at one generic complex point.
Any valid attack must retain the chosen exponential branch under specialization; traces, Galois
conjugation, and function-field Ax theorems erase it.

## Log

- 2026-08-14 -- dependency-closed normal form proved; trace/norm and generic-slope continuations killed.

## Lean progress -- clauses 2 and 5

`formal/GaloisForLFunctions/HTGeometry/DefectSlopeNormalForm.lean` (new, umbrella-wired,
axiom-clean) proves the two clauses of the statement that are pure algebra.

| Card item | Declaration |
|---|---|
| **clause 2**: on a one-dimensional module a nonzero `ε₁` determines a unique `ρ` with `ε₂ = ρ ε₁` | `existsUnique_defectSlope` |
| normalization: the slope of a defect against itself is `1` | `defectSlope_self` |
| **clause 5, `(R)`**: with `Y(p) = exp X(p)`, `(L(p)-L(q)) - (X(p)-X(q)) = X(q) - L(q) + 2πik` | `regulator_eq_base_add_branch` |
| the branch integer is the only freedom in `(R)` | `regulator_branch_difference` |

`existsUnique_defectSlope` is the exact content of "there is a unique `ρ ∈ K` with `ε₂ = ρ ε₁`":
one-dimensionality makes `ε₁` a basis, and nonvanishing of `ε₁` -- the defect-lattice input -- makes
the coefficient unique.  `regulator_eq_base_add_branch` is the card's cancellation computation with
the branch recorded as an integer, exactly as `(R)` states it.

## Lean progress -- clause 1

`formal/GaloisForLFunctions/HTGeometry/TranscendenceDegreeOneVariable.lean` and
`formal/GaloisForLFunctions/RHTower/SchanuelStageTwoDegree.lean` (both new, umbrella-wired,
axiom-clean) close clause 1.

| Card item | Declaration | Module |
|---|---|---|
| `x_i != 0` from rational linear independence | `ne_zero_of_linearIndependent` | `SchanuelStageTwoDegree` |
| Hermite--Lindemann: one of `z`, `exp z` is transcendental | `transcendental_or_transcendental_exp` | `SchanuelStageTwoDegree` (over the corpus `schanuelExtractionAt_one`) |
| transcendence over `Q` is transcendence over an algebraic base | `transcendental_base_of_transcendental_rat` | `SchanuelStageTwoDegree` |
| a one-variable extension has degree one | `trdeg_eq_one_of_transcendental` | `TranscendenceDegreeOneVariable` |
| **clause 1**: a transcendental element and degree below two force degree exactly one | `trdeg_eq_one_of_transcendental_of_lt_two` | `SchanuelStageTwoDegree` |
| adjoining a transcendental raises the degree by one | `trdeg_eq_add_one_of_transcendental` | `TranscendenceDegreeOneVariable` |
| an algebraic extension preserves the degree | `trdeg_eq_of_isAlgebraic` | `TranscendenceDegreeOneVariable` |

So `trdeg K = 1` is no longer an open Lean item: Hermite--Lindemann is in the corpus, and the
cardinal squeeze `1 <= trdeg < 2` is proved against `Algebra.trdeg`.

### What remains

Everything analytic or transcendence-theoretic beyond clause 1:

- the instantiation bookkeeping that identifies the abstract base/value-field pair with
  `Qbar` and `Qbar(x_1,x_2,y_1,y_2)` inside `C`;
- one-dimensionality of `Ω_{K/Q̄}` for a transcendence-degree-one extension, the geometric input
  fed to `existsUnique_defectSlope`;
- clause 3, transcendence of `ρ`, which needs the algebraic-coefficient defect theorem of
  `schanuel-defects-algebraic-coefficient-independent`;
- clause 4, Kirby's exponential-algebraicity theorem;
- the identification of `(L(p)-L(q)) - (X(p)-X(q))` with the path integral `∫_q^p ε_i`, which needs
  a contour-integration layer for `d log Y - dX` on the normalized projective curve.

## Two of the four remaining items are closed (2026-08-23)

**Stale item.** "One-dimensionality of `Ω_{K/Q̄}` for a transcendence-degree-one extension" was
already corpus-owned when that list was written:

```text
RHTower.finrank_kaehlerDifferential_eq_one_of_trdeg_eq_one
    {A : Type u} {K : Type v} [Field A] [Field K] [Algebra A K] [CharZero A]
    (htrdeg : Algebra.trdeg A K = 1) : Module.finrank K Ω[K⁄A] = 1
```

in `formal/GaloisForLFunctions/RHTower/SchanuelKaehlerDimension.lean`, together with the separable
base change and the simple-transcendental case it is built from.

**New, and general.**  `formal/GaloisForLFunctions/HTGeometry/KaehlerRankTranscendenceDegree.lean`
(axiom-clean, umbrella-wired) proves the identity at *every* transcendence degree — a genuine
mathlib gap, not only the degree-one case:

```text
rank_kaehlerDifferential_eq_trdeg (k K : Type u) [Field k] [Field K] [Algebra k K] [CharZero k] :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K
```

A transcendence basis splits the extension: over the purely transcendental part the differentials
are free on the basis (a rational function field is a localization of a polynomial ring, and
localization is formally étale, via `AlgebraicIndependent.aevalEquivField`), and the remaining part
is algebraic hence separable hence formally étale, so it only extends scalars.

Together with

```text
exists_unique_smul_of_trdeg_eq_one : trdeg k K = 1 → e ≠ 0 → ∀ f, ∃! c : K, f = c • e
```

the geometric input `existsUnique_defectSlope` consumes is now unconditional: in a
transcendence-degree-one extension every nonzero differential is a basis and every other
differential is a unique multiple of it.

### What remains, restated

- the instantiation bookkeeping identifying the abstract base/value-field pair with `Q̄` and
  `Q̄(x₁,x₂,y₁,y₂)` inside `ℂ`;
- clause 3, transcendence of `ρ`, still through
  `schanuel-defects-algebraic-coefficient-independent` — whose own Baker gate is **closed**
  (`RHTower.baker_linearForm_transcendental`), leaving only its algebraic-group/character-lattice
  step;
- clause 4, Kirby's exponential-algebraicity theorem;
- the contour-integration layer for `d log Y − dX` on the normalized projective curve.

## Rational slope exclusion (2026-08-25)

`RHTower.schanuelDefect_slope_not_rational` now proves unconditionally that any complex slope
`rho` satisfying

```text
schanuelDefect (x 1) = rho • schanuelDefect (x 0)
```

for a `ℚ`-linearly independent pair cannot equal the complex image of any `q : ℚ`.  It is a
direct consequence of the newly packaged theorem
`schanuelDefect_linearIndependent_rational`, obtained from the existing integral defect theorem by
simultaneous denominator clearing.  Targeted leaf build and axiom audit pass; no umbrella build was
run.

This closes the rational part of clause 3.  The card's exact claim that `rho` is transcendental
still requires exclusion of every algebraic irrational coefficient, i.e. the mixed Hopf-ideal and
character-lattice step of `schanuel-defects-algebraic-coefficient-independent`.

## Clauses 1–3 closed in the concrete value field (2026-08-26)

The algebraic-coefficient dependency is now closed by
`RHTower.schanuelDefect_linearIndependent_algebraic`.  Fresh corpus searches recovered the existing
concrete value field, Kähler-rank theorem, generic slope theorem, and internal-generation lemma
before new code was written.

`RHTower/SchanuelDefectAlgebraicSlope.lean` proves the missing coefficient consequence:

```text
schanuelDefect_slope_transcendental_algebraicClosure
```

Any complex scalar relating the two numerical defects is transcendental over
`algebraicClosure ℚ ℂ`; the proof applies the exact algebraic-coefficient independence theorem to
the coefficient vector `(-rho,1)`.

`RHTower/SchanuelStageTwoDefectSlopeCore.lean` then instantiates the whole algebraic core in the
literal field

```text
stageTwoValueField (x 0) (x 1)
```

and introduces its intrinsic defects in `Ω[K⁄AlgNum]`.  The main declarations are:

```text
map_stageTwoDefect
stageTwoDefect_ne_zero
existsUnique_stageTwoDefectSlope
stageTwoDefectSlope_transcendental
finiteDimensional_stageTwoValueField_adjoin_slope
exists_stageTwoDefectSlopeCore
```

Thus clauses 1–3 now hold together without an abstract-field bookkeeping premise: `trdeg K = 1`,
there is a unique `rho : K` with `epsilon_2 = rho • epsilon_1`, `rho` is transcendental over the
algebraic numbers, and `K` is finite-dimensional over its internal simple field `AlgNum⟨rho⟩`.
The finite-extension proof uses the actual four generators, proves they internally adjoin to `⊤`,
and applies finite-dimensionality of a finite algebraic adjunction; it does not weaken "finite" to
mere algebraicity.

Both new leaves pass direct checks and targeted builds, are wired into `RHTower`, and were not
umbrella-built.  Every new theorem declaration audits to only
`[propext, Classical.choice, Quot.sound]`.  Exact remaining clauses are now only clause 4
(Kirby's essential-counterexample/exponential-algebraic-closure theorem) and clause 5's geometric
identification of the already-formal regulator identity with the contour integral on the normalized
projective curve.  Card remains Stage 2 until both are formalized.

## Literal path-integral bridge (2026-08-26)

Fresh corpus search recovered the existing closed-loop FTC, logarithmic-derivative contour, and
endpoint-regulator layers before new code was written.  The missing open-path bridge is now
formalized in `HTGeometry/LogarithmicDifferentialPathIntegral.lean`:

```text
logarithmLift_deriv_eq_div
intervalIntegral_logarithmicDifferential_sub_eq
intervalIntegral_logarithmicDifferential_eq_base_add_branch
```

For differentiable pullbacks `X`, `Y` and an actual logarithm lift `exp L = Y`, the second theorem
integrates the literal differential `Y'/Y - X'` and proves

```text
∫ (Y'/Y - X') = (L(b) - L(a)) - (X(b) - X(a)).
```

The capstone combines this with `Y(b) = exp(X(b))` and proves the card's exact regulator value
`X(a) - L(a) + 2πik`.  It is not an endpoint-only restatement: the integrand and FTC identification
are part of the theorem.  Direct check, targeted leaf build, and new-declaration axiom audits pass;
the module is umbrella-wired without building the umbrella.  Clause 5 now lacks only the concrete
normalization/coordinate/path packaging that instantiates this general analytic theorem on `V`.
Clause 4 and that geometric packaging still keep the card at Stage 2.

## Clause 4 closed: exact essentiality and countable ecl membership (2026-08-26)

Fresh `formal_tools.py research` searches found the existing stage-two value field, Hermite--
Lindemann selector, Kähler-kernel machinery, matrix-minor transfer, and algebraic-coefficient
defect theorem.  `RHTower/SchanuelStageTwoExponentialAlgebraicity.lean` supplies only the missing
bridges.  It constructs three pair-supported polynomial relations, proves their gradient rows span
the three-dimensional coordinate-differential kernel, restricts them to the two-dimensional
exponential tangent, and uses nonvanishing of the intrinsic defect to prove injectivity.  A
nonsingular two-row minor therefore gives an actual Khovanskii system over `complexEclStage 1`.

The resulting declarations prove:

```text
stageTwoExponent_mem_complexEclStage_two_of_trdeg_one
stageTwoGenerator_mem_complexExponentialAlgebraicClosure_of_trdeg_one
stageTwoValueField_le_complexEclAsIntermediateField_of_trdeg_one
IsEssentialSchanuelCounterexample
isEssentialSchanuelCounterexample_stageTwo_of_trdeg_one
exists_stageTwoDefectSlopeCore_essential_ecl
```

`IsEssentialSchanuelCounterexample` is Kirby's exact condition, not a proper-subtuple proxy: its
cancellation-free inequality is `delta(x) <= delta(c)` for every rationally independent basis `c`
of every rational subspace of the span of `x`.  The capstone packages the already-proved unique
transcendental slope with exact essentiality and proves that the actual `rho : K`, hence its complex
value, belongs to the countable exponential-algebraic closure.

Direct check, targeted leaf build, and new-capstone axiom audit pass; only
`[propext, Classical.choice, Quot.sound]` occur.  New leaves are umbrella-wired, and no umbrella
build was run.  Clause 4 is closed.  Clause 5's normalized-projective-curve packaging remains.

Formalization also exposes a required reading of clause 5: the path must lie in the complement of
the zeros and poles of each `Y_i`.  Without this, an arbitrary path can cross the divisor, where
`dY_i / Y_i` and a logarithm lift are undefined.  The existing literal path-integral theorem already
has exactly this nonvanishing/log-lift domain; remaining work is the normal projective model and its
divisor-avoiding analytic path realization.

## Divisor-avoiding paths automatically supply logarithm lifts (2026-08-26)

Fresh corpus search found the pre-existing theorem
`RHTower.exists_continuousOn_log_of_hasDerivAt` in `HTGeometry/SegmentPolarForm.lean`.  No second
continuous-logarithm construction was added.  The new capstone
`exists_logarithmLift_intervalIntegral_eq_base_add_branch` in
`HTGeometry/LogarithmicDifferentialPathIntegral.lean` reuses it to prove that every differentiable
interval path on which `Y` is nowhere zero automatically admits a continuous differentiable
logarithm lift and satisfies the exact regulator identity

```text
∫ (Y'/Y - X') = X(a) - L(a) + 2πik.
```

Thus clause 5 no longer needs a separately supplied logarithm branch.  Direct file check and the
targeted leaf build pass.  The new declaration's axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.  Remaining clause-5 obligations are the normalized
projective model, coordinate pullbacks, and construction of a divisor-avoiding analytic path to
which this theorem applies.  Card remains Stage 2.

## Lean progress — canonical affine normalization and literal regulator paths (2026-09-02)

`RHTower/SchanuelStageTwoDefectSlopeNormalForm.lean` now packages clauses 1–4 through the exact
stage-two core and essentiality/ecl theorems.  For clause 5 it constructs the integral-closure
normalization ring, its affine spectrum, an exact function-field equivalence with the concrete
stage-two value field, and the transported additive and exponential rational coordinates.  It also
constructs genuine coordinate pullbacks along supplied differentiable divisor-avoiding paths,
obtains simultaneous logarithm lifts automatically, and identifies both regulator integrals.

Literal clause 5 still requires a projective compactification/normalization of the finite extension
with function field identified as the concrete value field, plus a scheme-analytification and
complex-point evaluation layer producing the required path on that model.  Neither interface exists
in the current corpus or imported mathlib.  An all-five-clauses capstone would therefore be false as
a description of the formal state; the card remains at Stage 2.

## Lean progress — the affine chart is a genuine normal Noetherian curve chart (2026-09-02)

`RHTower/SchanuelStageTwoDefectSlopeAffineNormality.lean` now proves the exact commutative-algebra
properties of the canonical affine normalization.  Transcendence of `core.rho` makes evaluation

```text
AlgNum[X] → AlgNum[core.rho]
```

bijective.  The resulting `stageTwoSlopePolynomialAlgEquiv` transfers the principal-ideal and
Dedekind-domain structure to the slope coordinate ring.  The already-proved finite-dimensionality
of the concrete value field over `AlgNum⟨core.rho⟩`, together with characteristic-zero
separability, then gives

```text
stageTwoSlopeAffineNormalizationRing_isDedekindDomain
```

for the actual integral closure.  Consequently its affine spectrum is locally Noetherian, every
stalk is integrally closed, and every codimension-one stalk is a discrete valuation ring:

```text
stageTwoSlopeAffineNormalizationScheme_isLocallyNoetherian
stageTwoSlopeAffineNormalization_stalk_isIntegrallyClosed
stageTwoSlopeAffineNormalization_stalk_isDiscreteValuationRing
```

This is the literal normal affine curve chart attached to the finite extension, not a proxy model
or an added normality hypothesis.  Direct Lean check and targeted leaf build pass; all ten public
declarations audit to exactly `[propext, Classical.choice, Quot.sound]`.  The leaf is wired into the
`RHTower` umbrella without building that umbrella.

The missing clause remains unchanged in kind: construct the normal **projective** completion with
this function field and connect its complex points/rational-coordinate evaluation to an analytic
divisor-avoiding path.  Affine normality does not supply either absent interface, so the card stays
at Stage 2.

## Lean progress — genuine global projective relative normalization (2026-09-02)

`RHTower/SchanuelStageTwoDefectSlopeProjectiveNormalization.lean` now constructs the literal
projective line over the algebraic numbers as the `Proj` of the standard grading on
`AlgNum[U₀, U₁]`.  Its degree-zero graded ring is proved canonically equivalent to `AlgNum`, and
the projective line is proper over that base.  Homogeneous evaluation

```text
U₀ ↦ 1,   U₁ ↦ core.rho
```

sends the irrelevant ideal to the top ideal, so `Proj.fromOfGlobalSections` supplies the actual
generic-point map `[1 : core.rho] : Spec K → ℙ¹`.  Taking mathlib's relative normalization along
this map gives a globally glued scheme, not an affine proxy.  Lean proves that the normalization
scheme is integral, its map to the projective line is integral, its generic inclusion is dominant,
and the normalization factorization is exact.  The composite to the degree-zero base is also
universally closed, separated, and quasi-compact.

Direct Lean check, targeted leaf build, and all-new-declaration axiom audit pass; every declaration
uses only `[propext, Classical.choice, Quot.sound]`.  The leaf is wired into the `RHTower` umbrella,
which was not built.

This does not yet prove that the relative normalization morphism is finite or locally of finite
type, so Lean cannot yet upgrade the composite to a proper normal projective curve over `AlgNum`.
It also lacks a proof that this global model's function field is the concrete field `K`, and the
scheme-analytification/complex-point interface needed to evaluate rational coordinates along a
divisor-avoiding analytic path.  Those are literal clause-5 obligations; the card remains at
Stage 2.

## Lean progress — finite and proper projective normalization (2026-09-03)

The finite/proper qualification above is now closed without an added finiteness premise.
`RHTower/SchanuelStageTwoDefectSlopeAffineChartCompatibility.lean` and
`RHTower/SchanuelStageTwoDefectSlopeInfinityChartCompatibility.lean` compute the actual pullback
maps on the two standard projective charts.  After the canonical section-ring identifications,
the first is literal inclusion of the slope coordinate ring in the concrete stage-two value field;
the second is literal inclusion of the inverse-slope coordinate ring and sends its affine
coordinate to `core.rho⁻¹`.  These are compatibilities for the genuine
`Proj.fromOfGlobalSections` generic map, not independently chosen abstract equivalences.

The reusable infrastructure
`HTGeometry/IntegralClosureRingEquiv.lean` transports integrality, integral closures, and
module-finiteness across compatible base/ambient ring-equivalence squares.  Applying it to both
computed charts proves that the relative normalization is finite on the standard two-chart cover.
`HTGeometry/FiniteMorphismAffineRestriction.lean` then globalizes that finite affine-cover result:

```text
stageTwoSlopeProjectiveNormalizationToLine_isFinite
stageTwoSlopeProjectiveNormalizationToGradeZero_isProper
```

Hence the global relative normalization is finite over the projective line, and its composite to
`Spec AlgNum` is proper.  Direct checks and targeted leaf builds pass.  Every new public
declaration audits to no axioms beyond `[propext, Classical.choice, Quot.sound]`; all leaves are
umbrella-wired, and no umbrella build was run.

Two literal clause-5 obligations remain: identify this relative normalization's function field
with the concrete stage-two value field `K`, and construct the scheme-analytification/complex-point
evaluation interface that realizes a divisor-avoiding differentiable path on this model.  Existing
path and regulator theorems consume such a path once available, but do not manufacture it from a
scheme point.  Card therefore remains at Stage 2.

## Lean progress — projective function field identified with the concrete value field (2026-09-03)

`HTGeometry/FunctionFieldPullback.lean` now proves the reusable fact that a dominant open
immersion induces an isomorphism on function fields.  The proof identifies the two generic points,
uses the stalk isomorphism of an open immersion, and contains no birationality premise hidden in
the statement.

`RHTower/SchanuelStageTwoDefectSlopeProjectiveFunctionField.lean` applies that result to the actual
relative normalization.  Its normalized standard chart is affine and dense because it contains
the dense image of `Spec K`.  The chart-section equivalence is transported through the already
computed projective generic-map square, so its section ring is exactly the concrete integral
closure inside `K`.  Passing to fraction fields on that chart and then through the dominant open
immersion gives

```text
stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv :
  stageTwoValueField (x 0) (x 1) ≃+*
    (stageTwoSlopeProjectiveNormalization x core).functionField
```

Thus the global proper integral projective model now has the literal function field required by
the card.  Direct checking, the targeted leaf build, and axiom audits of every new declaration
pass with exactly `[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired without an
umbrella build.

The sole remaining clause-5 obligation is analytic realization: connect scheme complex points and
rational-coordinate evaluation on this model to a differentiable divisor-avoiding complex path.
Mathlib and the current corpus still have no scheme analytification or equivalent complex-point
path interface.  The regulator theorem is already unconditional for every such realized path, but
the missing interface prevents an honest all-clauses capstone.  Card remains at Stage 2.

## Lean progress — scheme-valued projective regulator paths (2026-09-03)

`HTGeometry/ComplexPointRationalFunctionEvaluation.lean` adds the missing algebraic half of that
interface.  A complex-valued scheme point over `AlgNum` is an actual morphism `Spec ℂ ⟶ V`
commuting with the fixed structural maps; a rational function
regular there is represented by a germ in the local ring whose specialization is the function-field
element.  Evaluation is the point's stalk map followed by the canonical equivalence between the
unique stalk of `Spec ℂ` and `ℂ`.

`RHTower/SchanuelStageTwoDefectSlopeProjectiveRegulator.lean` transports the four literal elements
`x₁,x₂,e^{x₁},e^{x₂}` of the concrete value field through
`stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv`, making them rational functions on the
actual proper projective normalization.  `StageTwoProjectiveDivisorAvoidingPath` is a path of
complex-valued scheme points at which all four functions have local germs; its derivative,
nonvanishing, algebraic-source, scheme-theoretic smooth-base, and `(x,exp x)` target fields are
exactly the conditions used in clause 5.  The capstone

```text
exists_stageTwoProjectivePathRegulatorWitness
```

proves simultaneous logarithm lifts and both exact regulator integrals for every such path.
`exists_stageTwoDefectSlopeProjectiveNormalizationPackage` now bundles clauses 1–4, properness,
the concrete global function field, and this scheme-valued regulator law using only the card's
original linear-independence and low-transcendence assumptions.

Direct checks, targeted leaf builds, and all-new-declaration axiom audits pass with exactly
`[propext, Classical.choice, Quot.sound]`; both leaves are umbrella-wired without umbrella builds.

This still does not identify `StageTwoProjectiveDivisorAvoidingPath` with ordinary smooth paths in
the complex analytification: the corpus has no topology on `Hom(Spec ℂ,V)`, analytification functor,
or theorem equating analytic smoothness with differentiability of these evaluated coordinate
pullbacks.  Therefore the scheme-valued coordinate theorem is closed, but the paper's literal
smooth-path wording is not yet fully represented.  Card remains at Stage 2.

A final hostile audit also separates coordinate algebraicity from point algebraicity.  The present
`algebraicBase` field records that the four evaluated coordinates lie in `AlgNum`; it does not prove
that the source morphism `Spec ℂ ⟶ V` factors through an `AlgNum`-valued point of `V`.  That
scheme-theoretic factorization, together with analytification and ordinary smooth-path comparison,
remains necessary before clause 5 can trigger Stage-3 promotion.

## Lean progress — actual algebraic source-point factorization (2026-09-03)

`HTGeometry/BaseFieldPointComplexification.lean` now defines a base-field-valued point as an actual
section `Spec k ⟶ X` of the structural map and proves that its associated complex point is
literally the composite

```text
Spec ℂ ⟶ Spec k ⟶ X.
```

`RHTower/SchanuelStageTwoDefectSlopeAlgebraicBasePoint.lean` applies this to `k = AlgNum` and the
actual proper projective normalization.  The structure
`StageTwoProjectiveDivisorAvoidingPathWithAlgebraicBase` carries an `AlgNum`-valued source point,
the exact factorization of the path's source complex point through it, and formal smoothness at its
algebraic stalk.  The theorem
`exists_stageTwoProjectivePathRegulatorWitness_of_algebraicBase` supplies both regulator identities
for every divisor-avoiding coordinate-smooth path with this literal algebraic source.

Direct checks, targeted leaf builds, and all-new-declaration axiom audits pass with exactly
`[propext, Classical.choice, Quot.sound]`; both leaves are umbrella-wired without umbrella builds.
The coordinate-algebraicity/point-algebraicity mismatch is therefore closed.  Sole remaining
clause-5 mismatch is analytic: construct the complex analytification (or an equivalent established
analytic-space interface) and identify its ordinary smooth paths with the evaluated differentiable
coordinate paths consumed by the regulator theorem.  Card remains Stage 2.

## Lean progress — canonical algebraic target complex point (2026-09-03)

`HTGeometry/ComplexPointRationalFunctionEvaluation.lean` now proves the exact generic-center
regularity and evaluation dictionary.  Every rational function is regular at a complex point whose
center is the generic point, using the transported generic stalk germ; evaluation of that germ is
identified with dominant function-field pullback followed by the canonical
`functionField (Spec ℂ) ≃ ℂ` map.  It also records the affine-spectrum adjunction identity needed
to compute structural composites.

`RHTower/SchanuelStageTwoDefectSlopeGenericTargetPoint.lean` applies this dictionary to the literal
inclusion

```text
stageTwoValueField (x 0) (x 1) ↪ ℂ.
```

Composing its spectrum map with the normalized generic inclusion constructs an actual dominant
complex point of the proper projective normalization.  Lean proves that its center is the generic
point, that it lies over the standard embedding `AlgNum ↪ ℂ`, and that all four projective
coordinate rational functions are regular there.  The resulting
`stageTwoProjectiveGenericCoordinatePoint` is therefore a canonical algebraic target point, not an
assumed endpoint or proxy scheme.

Direct Lean checks and targeted leaf builds pass.  Every new declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`; the new leaf is wired into the `RHTower` umbrella, which
was not built.

The function-field comparison layer is now closed.  New exact naturality lemmas in
`HTGeometry/FunctionFieldPullback.lean` identify dominant pullback with the generic-stalk germ map,
and `stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_eq` proves that the chart equivalence
used in the normalization construction is the canonical global-sections equivalence.  Their
projective specialization is

```text
stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv_pullback
```

which proves that pullback along the normalized generic inclusion, after the chosen projective
function-field equivalence, is literally the canonical embedding of the concrete stage-two value
field into the function field of `Spec K`.  Consequently

```text
stageTwoProjectiveGenericCoordinatePoint_exponentValue
stageTwoProjectiveGenericCoordinatePoint_exponentialValue
```

evaluate the four target germs to `x₁,x₂,e^{x₁},e^{x₂}` with no comparison premise.  Direct checks,
targeted leaf builds, and axiom audits pass; every new public declaration uses only
`[propext, Classical.choice, Quot.sound]`.

Only the analytic comparison remains: construct the ordinary complex analytification of the
projective normalization and identify its smooth paths with the scheme-valued paths and evaluated
coordinate derivatives consumed by the regulator theorem.  Corpus search finds pointwise
topologies for complex spectra of affine `ℂ`-algebras and several special path-connectedness
theorems, but no global scheme analytification, smooth structure, or comparison theorem for this
normal projective curve.  Those special affine results do not establish the card's literal
ordinary-smooth-path quantifier.  Card remains Stage 2.

`HTGeometry/AlgebraSpectrumBaseChange.lean` closes the first exact affine comparison needed for
that construction.  For every commutative `k`-algebra `B` with `k → ℂ`, it equips
`B →ₐ[k] ℂ` with pointwise-convergence topology and proves the canonical homeomorphism

```text
RelativeAlgSpec.baseChangeHomeomorph :
  RelativeAlgSpec k B ≃ₜ AlgSpec (ℂ ⊗[k] B).
```

Thus base-field-valued complex points and complex points of the scalar-extended affine chart are
now identified topologically, not merely bijectively.  Direct check, targeted leaf build, and all
eight new-declaration axiom audits pass with exactly
`[propext, Classical.choice, Quot.sound]`.  The leaf is umbrella-wired without an umbrella build.
This still does not glue affine spectra into the projective analytification or furnish its smooth
path structure, so it does not by itself justify promotion.

## Lean progress — intrinsic smooth paths on an actual projective open (2026-09-03)

`HTGeometry/AlgebraSpectrumSmoothPath.lean` defines a smooth path in an affine complex-point space
intrinsically: evaluation of every regular function is `C∞`.  This condition is independent of a
chosen generating presentation, implies continuity for the pointwise topology, and is preserved
and reflected by the scalar-extension homeomorphism.

`RHTower/SchanuelStageTwoDefectSlopeCoordinatePrincipalOpen.lean` chooses one nonzero common
denominator for the four literal elements `x₁,x₂,exp x₁,exp x₂` in the concrete affine
normalization ring.  Its localization is therefore one actual affine domain on which all four are
regular functions.  The canonical map from that localization to the concrete value field sends
the four localized elements to their literal field values.

`RHTower/SchanuelStageTwoDefectSlopePrincipalOpenComplexPoints.lean` constructs the canonical
target point of this relative complex spectrum and proves that the four regular functions evaluate
there to exactly `x₁,x₂,exp x₁,exp x₂`.  Smoothness of every coordinate pullback is derived from
intrinsic affine smoothness, not supplied separately.  Consequently

```text
exists_stageTwoCoordinatePrincipalOpenPathRegulatorWitness
```

proves both exact regulator identities for every intrinsically smooth divisor-avoiding path in
this common coordinate domain from the complexification of an actual `AlgNum`-valued point to the
canonical target.  All derivative fields, continuous-derivative fields, algebraic source values,
and target values are derived.

Finally,
`RHTower/SchanuelStageTwoDefectSlopePrincipalOpenProjectivization.lean` proves that this coordinate
domain is not an affine stand-in: its spectrum maps into the actual proper projective normalization
by an open immersion

```text
stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization
```

obtained from the genuine principal-localization map, the computed normalized affine-chart
equivalence, and chart inclusion.  Every intrinsic affine smooth path thereby becomes a literal
scheme-valued path on the projective model.  Its source is proved to factor through an actual
`Spec AlgNum` point, and its endpoint is the image of the canonical exponential target.

Direct checks and targeted leaf builds pass.  Every new declaration audits to exactly
`[propext, Classical.choice, Quot.sound]`; all leaves are umbrella-wired, with no umbrella build.

This closes the affine-to-projective gluing and removes the previously supplied coordinate
derivatives from this path class.  It does not yet cover every ordinary smooth path in the full
projective complement of all coordinate poles and multiplicative zeroes: that locus need not lie
inside the chosen normalized standard chart, and the corpus still lacks global complex
analytification plus holomorphic regular-function evaluation on a finite affine cover.  That exact
global comparison remains necessary, so the card stays at Stage 2.
