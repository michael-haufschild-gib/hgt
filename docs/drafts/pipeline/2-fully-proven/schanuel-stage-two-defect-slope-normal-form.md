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
