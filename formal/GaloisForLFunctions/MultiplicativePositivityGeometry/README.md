# Multiplicative Positivity Geometry

Multiplicative Positivity Geometry studies the positivity that an Euler product carries in its
*logarithmic coefficients*, and asks what that positivity forces on the divisor of the
function. The quadratic positivities of the corpus (Weil, Hodge, trace) live in the space of test
functions. Multiplicative positivity lives in the dual variable: the heights `u` of the vertical
line, read on the discrete group `(ℝ, +)`.

The programme's first theorem is a dictionary.

> **For a Dirichlet series with nonnegative log-coefficients, the boundary divisor
> `D(u) = (pole order) − (zero order)` at `1 + iu` is an even positive-definite function on the
> discrete group `ℝ`.**

Every harmonic forcing argument on the line `Re s = 1` (de la Vallée Poussin, Mertens, Fejér) is a
Gram inequality of this one function. Questions about forcing therefore become questions about
integer-valued positive-definite functions. Those are completely answerable.

## 1. Motivation

The [route review](../../../docs/reports/review-2510/hard-obstacles-summary.md) records two exhaustion
facts.

- **Single-channel quadratic positivity can only certify blindness.** Every sharp-stable positive
  convolution ideal of the Meyer source lies inside the off-line-blind ideal
  (`isGreatest_meyerSharpPositiveIdeal`, [ACS](../ArithmeticCastelnuovoSeveri/README.md)).
- **Coefficient positivity forces, but only on `Re s = 1`.** Λ ≥ 0, a simple pole, no poles at the
  harmonics and integer zero orders force `ζ(1+it) ≠ 0` (`harmonic_quantized_zero_vanishing`).
  With growth input the same positivity reaches the de la Vallée Poussin, Littlewood and
  Vinogradov–Korobov regions, and its next rung is a fixed zero-free strip.

So the only forcing mechanism in the corpus is multiplicative. This programme turns it into a
geometry:

- identify the object on which the positivity lives (the boundary divisor as a function on the Bohr
  dual);
- classify what that positivity permits;
- realize every permitted configuration;
- measure exactly what finite coupling and growth input can certify.

The aim is to know the complete content of multiplicative positivity before asking it to do more.

## 2. Objects

| Object | Definition | Lean |
|---|---|---|
| Positive-definite function | `φ : G → ℝ` on an additive group with `Σᵢⱼ cᵢcⱼ φ(xᵢ − xⱼ) ≥ 0` for real `c`; even when `φ(−u) = φ(u)` | `IsPosDef`, `IsEvenPosDef` |
| Weighted frequency family | weights `wᵢ ≥ 0`, frequencies `λᵢ ∈ ℝ` | — |
| Cosine trace | `u ↦ Σᵢ wᵢ cos(λᵢ u)`: the real part of `Σ wᵢ e^{−iλᵢu}` on a vertical line | `cosineTrace` |
| Boundary datum | damped weights `w(x)`, `x > 0`, with `x · trace(w(x))(u) → D(u)` as `x ↓ 0` | `IsBoundaryDivisor` |
| Boundary divisor | the limit `D`; for an Euler product, pole order minus zero order at `1 + iu` | `zetaBoundaryDivisor` for ζ |
| Nonvanishing subgroup | `{u : D(u) ≠ 0}` for integer-valued `D` with `D(0) = 1` | `nonvanishingSubgroup` |
| Progression | `h, 2h, 3h, …` in the height group | `progression_gram` |
| Profile | the restriction of `D` to a progression through `0`; a positive-definite sequence on `ℤ` | — |

The ζ boundary datum has weights `Λ(n) n^{−1−x}` on frequencies `log n`
(`zetaBoundaryWeight`, `logFrequency`); its cosine trace is `Re(−ζ'/ζ)(1 + x + iu)`
(`zetaRealLogDeriv_eq_cosineTrace`).

## 3. Language

The programme keeps these distinctions explicit.

- **Test-space positivity vs height-space positivity.** Weil and Hodge positivity are quadratic
  forms on tests. Multiplicative positivity is a Gram condition on heights. The maximality theorem
  constrains the first; it says nothing about the second.
- **Gram inequality vs harmonic inequality.** A nonnegative cosine polynomial against the Euler
  measure gives a harmonic inequality. It is one Gram form of the boundary divisor. Positive
  definiteness is the conjunction of all of them, in every number of frequencies.
- **Boundary vs interior.** On `Re s = 1` the divisor is a limit and positivity is exact. In the
  strip there is no limit, and positivity at `σ > 1` must be combined with growth input.
- **Pole order `k = D(0)` vs simple pole.** `k = 1` is rigid (classification); `k ≥ 2` admits zeros.
- **Forced vs imported.** A region is forced if it follows from the positivity of this programme. It
  is imported if a zero-free region is used as input.

## 4. Mechanisms

1. **Two-point Gram.** `(a² + b²)φ(0) + 2ab φ(h) ≥ 0` gives `|φ(h)| ≤ φ(0)`: a boundary zero has order at
   most the pole order at `1`, plus the local pole order (`boundary_zero_order_le`).
2. **Three-point Gram and translation.** The vectors `(s, ∓s, t)` at `0, h, −u` show that
   `φ(h) = ±φ(0)` forces `φ(h + u) = ±φ(u)` (`apply_add_of_eq`, `apply_add_of_eq_neg`).
3. **Quantization.** With `φ(0) = 1` and integer values, `|φ| ≤ 1` leaves `{−1, 0, 1}`. The
   translation law makes `{φ ≠ 0}` a subgroup and `φ` a `±1` character on it
   (`intValued_mul`, `nonvanishingSubgroup`).
4. **Fejér progression vector.** The constant vector on `0, h, …, (N−1)h` gives
   `0 ≤ Nφ(0) + 2Σ_{r<N}(N − r − 1)φ((r+1)h)` (`progression_gram`), via the double-sum identity
   `sum_range_sum_range_sub`.
5. **Closure.** Positive multiples and pointwise limits of positive-definite functions are positive
   definite (`isEvenPosDef_of_tendsto`). This passes positivity from `σ > 1` to the boundary.
6. **Discreteness.** A locally finite divisor has a non-dense nonvanishing subgroup, hence a cyclic
   one (`nonvanishingSubgroup_cyclic`, via `AddSubgroup.dense_or_cyclic`).

## 5. Foundational pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **P1 Boundary positivity** | The boundary divisor of any nonnegative weighted family is even positive definite on `ℝ`. | `isEvenPosDef_cosineTrace`, `IsBoundaryDivisor.isEvenPosDef` |
| **P2 Simple-pole rigidity** | If `D(0) = 1` and `D` is integer valued, then `D ∈ {−1, 0, 1}`, and a zero at `u` forces a pole at `2u`. With no off-origin poles, `D = 1_{0}`. | `boundary_values`, `boundary_zero_forces_double_pole`, `boundary_eq_delta_of_no_pole` |
| **P3 Boundary trichotomy** | A locally finite simple-pole boundary divisor is `1_{0}`, `1_{cℤ}`, or `k c ↦ (−1)^k` on `cℤ`. | `boundary_trichotomy` |
| **P4 Progression law** | If `D ≤ 0` along `h, 2h, …`, the total zero mass on that progression is at most `D(0)/2`. | `boundary_progression_zero_mass_le` |
| **P5 ζ on the boundary** | `D_ζ = 1_{0}`; hence `ζ(1+iu) ≠ 0` from positive definiteness alone. Prime phases at distinct heights are asymptotically orthonormal. | `zetaBoundaryDivisor_eq`, `riemannZeta_boundary_ne_zero_of_posDef`, `zeta_boundary_gram_tendsto` |
| **P6 Arithmetic realization** | Twisting the von Mangoldt weights by a nonnegative cosine polynomial `P(t₀ log n)` realizes the coefficient profile of `P` as a boundary divisor. Positive-definite finite profiles are exactly nonnegative cosine polynomials. | `ArithmeticRealization` (in development) |
| **P7 Exact Fejér barrier** | A nonnegative cosine polynomial of degree `K` has `a₁ ≤ 2cos(π/(K+2))·a₀`, with equality attained. | planned |
| **P8 Growth-to-forcing law** | Harmonic ratio `κ` and growth input `M` certify exactly the zero-free width `(√κ − 1)²/M`. | planned |

Consequences already proved:

- **Pole simplicity is the decisive invariant on `Re s = 1`.** It turns positive definiteness into
  quantization.
- **Pole isolation is the second invariant.** A boundary zero can exist only if a pole sits at twice
  its height.
- **A pole of order `k` allows at most `k/2` units of zero mass** on any pole-free progression
  through the origin.

## 6. Traps

- **Reading a harmonic inequality as the whole positivity.** One cosine polynomial is one Gram form;
  conclusions must use the positive-definite function itself.
- **Real coefficients see only the even part.** The boundary divisor is even, so nothing is lost,
  but complex statements need separate justification.
- **Imported regions.** The ACS harmonic module's interior collars come from a classical region, not
  from the forcing law. Interior statements here must name their growth input.
- **Abstract limits vs meromorphic divisors.** Dense nonvanishing subgroups are not excluded by
  positive definiteness alone; the trichotomy needs local finiteness of the divisor.
- **Twisted products are not Beurling systems.** `ζ(s)²/(ζ(s+it₀)ζ(s−it₀))` has nonnegative
  log-coefficients but non-integral prime weights; it calibrates positivity, not integrality.

## 7. Questions the programme aims to answer

| Question (review §4.4) | Status |
|---|---|
| What replaces the Fejér barrier? | On the boundary, the full constraint is positive definiteness of the divisor (P1). It is completely solved for simple poles (P2–P3) and sharply bounded for higher poles (P4). The exact finite-degree constant is P7. |
| How can quantization force vanishing? | On the boundary: integer values plus `|D| ≤ D(0) = 1` make `D` a character on a subgroup (P2). In the interior: open (§9). |
| What separates ζ from systems sharing its invariants? | On `Re s = 1`: positivity, pole simplicity and pole isolation determine the boundary divisor (P5). Each invariant is necessary, by realized models (P6, P3). Off the boundary: open (review Q2). |
| What can finite coupling with growth input certify? | P8: an exact two-sided law, with a barrier strictly below any fixed strip. |

## 8. Tools

- Real positive-definite calculus on additive groups: bounds, translation laws, subgroup and
  character extraction, progression Gram identities, closure under limits.
- Boundary data: a uniform interface for Euler products, Beurling systems and twisted products.
- Realization by twisting: nonnegative cosine polynomials in `t₀ log n` multiply the von Mangoldt
  weights and shift the divisor by `±k t₀`.
- Exact quadrature certificates for nonnegative cosine polynomials (P7).

## 9. Open research topics

- **Interior multiplicative positivity.** For `σ > 1`, `u ↦ Re(−ζ'/ζ)(σ + iu)` is positive definite.
  Which positive-definite constraints survive analytic continuation into `1/2 < σ < 1`, and which
  combination with growth input goes beyond the Vinogradov–Korobov region?
- **Multi-frequency profiles.** Joint positive definiteness on subgroups of rank `≥ 2` (several
  incommensurable heights). On the boundary it adds nothing for ζ, which has `D_ζ = 1_{0}`. Its
  interior analogue is open.
- **Integrality.** Beurling systems (integer prime weights) versus nonnegative Euler products: which
  boundary profiles are realized by genuine generalized-prime systems?
- **Functional-equation rigidity** (review Q2). Do Riemann's functional equation, a nonnegative
  Beurling Euler product and a simple pole determine ζ?

## 10. Place in the corpus

- **ACS.** The maximality theorem fixes what single-channel quadratic positivity can do. The
  harmonic module supplies the boundary limit `tendsto_zetaRealLogDeriv_boundary` and the Fejér
  autocorrelations reused here. This programme replaces the single cosine polynomial of that module
  by the whole positive-definite function.
- **HTGeometry.** Complex positive definiteness of atomic Fourier series
  (`PositiveDefiniteOnReal`) and the purchase-ratio cap (`CosinePolynomialPurchaseCap`) are the
  nearest existing tools.
- **RHTower.** The classical zero-free regions (dlVP, Littlewood, VK) are the interior calibration
  for P8.
- **AOG, ACCE, BVI, PM.** Their receivers are width statements; P8 identifies which width
  multiplicative positivity can reach and so where those routes must find their missing input.

## 11. Success criteria and contribution standard

The programme succeeds when the complete content of multiplicative positivity is known:

- every boundary configuration it permits is classified and realized;
- every interior statement it can certify is stated with its exact constant and its barrier;
- every gap to RH is named as an input outside multiplicative positivity.

A contribution must:

1. be an unconditional Lean theorem, with ζ inputs limited to Λ ≥ 0, residues, factorization and
   explicitly named growth bounds;
2. state a classification, realization, exact constant or sharp barrier, not a new equivalent of RH;
3. be selective: it either distinguishes ζ from a realized countermodel or proves that no
   multiplicative positivity statement can;
4. keep boundary and interior, forced and imported, separate.

## 12. Module map

| Module | Content |
|---|---|
| `PositiveDefiniteFunctions` | Even positive-definite functions on additive groups; integer-valued classification; progression law; closure. |
| `BoundaryPositivity` | Cosine traces; boundary data; the boundary positivity theorem. |
| `SimplePoleClassification` | Values, zero-forces-pole, no-pole ⇒ `δ₀`, cyclic support, trichotomy, zero-order and progression bounds. |
| `ZetaBoundaryDivisor` | The ζ boundary datum; `D_ζ = 1_{0}`; boundary nonvanishing; asymptotic orthonormality of prime phases. |
