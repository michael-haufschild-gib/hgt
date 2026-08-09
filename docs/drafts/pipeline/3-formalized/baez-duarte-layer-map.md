# The Báez-Duarte layer: map

Status: formalized (Lean, unconditional throughout)
Date: 2026-08-09

Thirty-four modules built in one session, `formal/GaloisForLFunctions/RHTower/`, ~250 declarations, ~4700
lines. Every declaration is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`). This card is
the index; the detail cards are listed at the end and several are partly superseded — read this first.

## The chain, end to end

**RH follows from a concrete approximation statement about rational sequences.**

1. `BaezDuarteL2Carrier` — the carrier is `L²((1,∞), du)`. The Mellin detector at `s` is the explicit vector
   `conj(u^{s−1})`, in `L²` exactly when `Re s < ½`, with `‖·‖² = 1/(1−2Re s)`. **No Hardy space is needed**:
   bounded point evaluation is Cauchy–Schwarz. This dissolved a wall `HTGeometry/HardyClosureZeroFree`
   had declared (docstring corrected there).
2. `NymanBeurlingCriterion`, `BaezDuarteDistance` — closed-span membership of the target forces RH, for any
   subfamily of dilations; in metric form, **`d_N → 0 ⟹ RH`** (`riemannHypothesis_of_tendsto_bdDistDiscrete`),
   with the converse floor `√(2Re ρ − 1)/|ρ|` if RH fails.
3. `StepFunctionCarrier` — the generators and target are step functions `s(⌊v⌋)/v`, and the inner product is
   `∑_{n≥1} s₁(n)s₂(n)/(n(n+1))`. So the criterion **is a discrete weighted-ℓ² problem**: RH holds if the
   constant sequence lies in the closed span of `n ↦ (n mod m)/m` in `ℓ²(ℕ≥1, 1/(n(n+1)))`.
4. `BaezDuarteGramDiscrete`, `BaezDuartePairingSeries` — both data are explicit rational series:
   `bdGram (1/m₁) (1/m₂) = ∑ (n mod m₁)(n mod m₂)/(m₁m₂n(n+1))` and `∑ (n mod m)/(m·n(n+1)) = (log m)/m`.
   By-product: `∑_{n≥1}(n mod m)/(n(n+1)) = log m`.
5. `LeastSquaresProjection`, `BaezDuarteLeastSquares` — the distance from the data: at the normal-equation
   solution `d² = 1 + ∑ᵢcᵢθᵢlogθᵢ`; at an arbitrary `c`, `d² ≤ 1 + 2∑cᵢθᵢlogθᵢ + ∑cᵢcⱼ·bdGram`.
6. `BaezDuarteHalfBound` — worked end to end: `bdGram (1/2)(1/2) = (log 2)/4` and `d² ≤ 1 − log 2`.

## Quantitative results (added after the first draft of this map)

* `BaezDuarteHalfBound`, `QuarterGramEntry`, `HalfQuarterGram` — closed-form Gram entries
  `(log 2)/4`, `(3log 2)/8 − π/32`, `(5log 2)/16 − π/32`, and the bounds `d² ≤ 1 − log 2`,
  `d² ≤ 1 − (log 2)²/(4·gram₄)`.  The reachable moduli are exactly `m ∈ {1,2,4}`: duplication and reflection
  close `q = 4` but leave `ψ(1/8)` free and bring in new unknowns for odd `q`.
* `DigammaDifferenceSeries`, `ResidueClassRecipSeries`, `DigammaThreeQuarter` — `ψ(b) − ψ(a) = ∑ₙ(1/(a+n) −
  1/(b+n))`, the progression sums `(ψ((j+1)/q) − ψ(j/q))/q`, and `ψ(3/4)`.  `∑_{k}1/((2k+1)(2k+2)) = log 2` is
  re-derived here independently of the Mellin route, so two unrelated computations agree.
* `GramResidueDecomposition` — via mathlib's `Nat.sumByResidueClasses`, for **every** modulus
  `bdGram (1/q)(1/q) = (1/q³)∑_{j=1}^{q-1} j²(ψ((j+1)/q) − ψ(j/q))`.  Vasyunin's structure, unrestricted in `q`.
* `SingleGeneratorUseless`, `GramDiagonalSandwich` — `(m−1)/(2m²) ≤ bdGram (1/m)(1/m) ≤ (log m)/m`, hence the
  single-generator gain is between `(log m)/m` and `2(log m)²/(m−1)`: every modulus helps a little, **none helps
  much**, and the gain tends to `0`.
* `UniformDistanceBound`, `DistancePositivity` — `d_N² ≤ 1 − (log 2)²/(4·gram₄)` for all `N ≥ 4`, and
  `√(1/(N!(N!+1))) ≤ d_N`, so every `d_N` is strictly positive.
* `TwoGeneratorImprovement` — `d² ≤ 1 − (3/8)log 2 − (5/32)π` for `{1/2,1/4}`, **strictly below** the
  single-generator value.  The collective effect is real at the smallest scale.
* `ZetaZerosBridge` — interoperability with mathlib's `riemannZetaZeros`.

## Obstructions (all unconditional, all with the same shape)

A bounded functional annihilating the family but not the target.

* **analytic** — the Mellin detector at a hypothetical zero (`BaezDuarteL2Carrier`), generalised to a template
  in `MellinVanishingCriterion`: any family with `MellinAnnihilated` inherits criterion, metric form and floor;
* **arithmetic** — evaluation at a highly divisible integer (`ArithmeticEvaluationObstruction`): every
  *finite*-section distance is strictly positive, so the approximation is never exact;
* pointwise version, free: `ModularCoefficientDesign.no_exact_modular_representation` — no finitely supported
  coefficient vector represents the target exactly (at `n₀ = N!` every combination vanishes).

## Structural results

* `BaezDuarteDetectorGram`, `BaezDuarteDetectorIndependence` — the detector Gram **is** the corpus's
  `rightHalfPlaneHardyCauchyGram`; its PSD theorem (proved there by a boundary integral) is
  `Matrix.posSemidef_gram`. New: the Cauchy kernel at **distinct** points is positive *definite* and
  nonsingular — the Cauchy determinant's nonvanishing without any determinant formula.
* `FractDilateBalance` — within the fractional-part dilates the Báez-Duarte family is **maximal**: a
  combination is annihilated iff `∑cₖθₖ = 0`, and one zero already forces it. Do not try to enlarge it.
* `MoebiusApproximantResidual`, `TruncatedMoebiusResidual`, `MoebiusResidualTailForm`,
  `ModularCoefficientDesign` — the constructive side. For any `c`,
  `1 − ∑c_d g_d(n) = 1 + D_c(n) − n·C₁(c)`; for `c = −μ` this is `∑_{N<d≤n}μ(d)⌊n/d⌋ + n·M₁(N)`, reusing the
  corpus's `moebius_floor_summatory`.

## What is open

One estimate, in two equivalent shapes:

* balance `∑_{N<d≤n}μ(d)⌊n/d⌋` against `n·M₁(N)` — enlarging `N` shrinks `M₁(N)` (PNT, which the corpus proves
  twice) but the tail starts at `N`, and `n log(n/N)` is far too lossy. Vasyunin-type damping is the classical
  remedy; the machinery to *test* any damping choice is complete.
* or evaluate more Gram entries. `m = 2` collapsed because `x² = x` on `{0,1}`. Beyond that, entries are
  digamma differences over residue classes — **and those are now reachable for denominators 2 and 4**: see
  `digamma-difference-series.md` (`ψ(b) − ψ(a) = ∑ₙ(1/(a+n) − 1/(b+n))`, mathlib's `digamma_one_half`, the
  corpus's `digamma_quarter`). The predicted `bdGram (1/4)(1/4) = (3log 2)/8 − π/32` would beat the `m = 2`
  bound. Denominator `3` still needs Gauss's general theorem (a mathlib TODO).

Neither is a formalisation gap. Both are equivalent to RH in aggregate, so no amount of this machinery
substitutes for the estimate.

**Why no unconditional theorem can close it from either side.** An upper bound on the collective gain staying
away from `1` for all `N` would *refute* RH; a bound reaching `1` *is* RH. And soft spectral bounds are far too
weak: Gershgorin on the Gram matrix gives `λ_max ≲ N`, hence gain `≳ 1/N → 0`, because the row of a small
modulus already has row sum `≍ N`. So the accumulation of the two-generator improvement across many moduli
cannot be obtained by any of the methods used here.

## Detail cards

`nyman-beurling-carrier-no-hardy-space.md` (7 addenda) · `nyman-beurling-is-a-discrete-l2-problem.md`
(6 addenda) · `discrete-baez-duarte-gram-evaluated.md` (2 addenda) · `cauchy-kernel-posdef-via-gram.md` ·
`baez-duarte-family-is-maximal-among-dilates.md` · `primitive-ratio-decomposition-and-third-cap.md` ·
`coefficient-free-cap-law.md` · `digamma-difference-series.md` · `quarter-gram-entry.md` ·
`single-generator-is-useless.md` · `uniform-distance-bound.md` · `two-generators-beat-one.md` ·
`gram-residue-decomposition.md` · `mathlib-reuse-sweep.md`. **Partly superseded:** `gram-diagonal-reduces-to-two-scalars.md` — its
"two scalars" boundary applies to the isolated pieces, not to the Gram entries, which are evaluated in (4).
