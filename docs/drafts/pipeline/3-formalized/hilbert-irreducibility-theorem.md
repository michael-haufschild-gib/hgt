# Hilbert's irreducibility theorem (ℚ is Hilbertian)

- **ID:** hilbert-irreducibility-theorem
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — unconditional, axiom-clean
- **Statement:** For `F ∈ ℚ[X][Y]` irreducible with `deg_Y F ≥ 1`, the set of `b ∈ ℚ` with
  `F(b, Y) ∈ ℚ[Y]` irreducible is infinite.

## Lean capstone

```
GaloisForLFunctions.HTGeometry.HilbertIrreducibility.hilbert_irreducibility :
  ∀ {F : Polynomial (Polynomial ℚ)},
    Irreducible F → 1 ≤ F.natDegree →
    {b : ℚ | Irreducible (Polynomial.map (Polynomial.evalRingHom b) F)}.Infinite
```

`#print axioms hilbert_irreducibility` → `[propext, Classical.choice, Quot.sound]`.

Non-vacuity is witnessed inside the corpus: `irreducible_X_sq_sub_C_X` proves `Y² − X` irreducible
in `ℚ[X][Y]` (Eisenstein at the prime `(X)`), and `infinite_irreducible_X_sq_sub_C` instantiates the
theorem there — infinitely many rationals `b` make `Y² − b` irreducible.  Both are axiom-clean.
The integral form `hilbert_irreducibility_int` (input `f ∈ ℤ[X][Y]`, hypothesis stated over
`FractionRing ℚ[X]`) is equally axiom-clean.  All fourteen modules are wired into
`GaloisForLFunctions.HTGeometry`.

**Mathlib does not have this theorem** and has no notion of Hilbertian field: `grep -ril "hilbertian"`
over the 8264 mathlib files is empty, and `Mathlib/FieldTheory/` contains no `Hilbert` occurrence.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: `lake build` green, axiom-clean, umbrella-wired
- [ ] 3 → 4  publication-ready

## Route

**Not** the p-adic ramification route recorded in `memory/hilbert-irreducibility-programme.md`.
That route is *provably insufficient*: one prime only kills roots on ramified branches; several
primes only force the specialised Galois group to *meet* the inertia classes (conjugacy ambiguity —
Jordan's theorem is not enough); and `X⁴+1`, reducible over every `ℚ_p`, shows that no purely local
criterion can ever certify irreducibility.  HIT needs a global argument.  The local half already
built (`HTGeometry/PadicRamifiedSpecialisation.lean`) stays as an independent asset.

The route taken is the elementary analytic proof of **Coleman–Zwald**, *Hilbertian fields and
Hilbert's irreducibility theorem*, arXiv:1809.10977, Theorem 7.

Let `n = deg_Y f ≥ 1` and pick an **integer** `s₀` with `a_n(s₀) ≠ 0` and `f(s₀,·)` separable.

1. **Analytic branches.**  On a disc around `s₀` there are analytic `u₁,…,u_n` whose values are
   exactly the (distinct) roots of `f(s,·)`.  Engine: the corpus' `U0.HolomorphicIFT.holo_implicit`.
2. **Step 1** (`exists_not_ratGerm`).  For each `∅ ≠ S ⊊ Fin n`, some coefficient of
   `β_S(s) = ∏_{i∈S}(Y − uᵢ(s))` is **not** a rational function of `s`.  Otherwise clearing
   denominators gives `Bhat ∈ ℚ[X][Y]` of degree `|S|` with `Bhat(s,·) = D(s)·β_S(s,·)`, so
   `resultant (toQ f) Bhat` vanishes on a whole neighbourhood of `s₀`, hence is `0`, hence `f` and
   `Bhat` are not coprime over `ℚ(X)`, hence `f ∣ Bhat` — impossible by degree.
3. **Step 2** (`irreducible_fibre_of_not_rational`).  If for each `S` the chosen coefficient is
   irrational at `b`, then `f(b,Y)` is irreducible: a rational factor would have root set
   `{uᵢ(b)}_{i∈S}` and hence rational subset coefficients.
4. **Algebraic layer.**  With `s₀ ∈ ℤ` and base ring `ℤ[X]`, `a_n·uᵢ` is integral over `ℤ[X]`
   (`monicScale`), so every scaled subset coefficient `w = a_n^{|S|}·β_S.coeff k` is integral in the
   germ ring (`GermIntegral`, `IntegralCoefficients`).  The substitution `X ↦ s₀ + 1/T`
   (`Polynomial.taylor` ∘ `Polynomial.reflect`, `ReflectSubstitution`) stays inside `ℤ[T]`, so
   `z(t) = t^D·w(s₀+1/t)` satisfies a **monic integral** relation and is an integer whenever it is
   rational (`IntegerRoot`).  *This choice of base point and base ring removes all denominator
   clearing.*
5. **Analytic core** (`TaylorTail.thin_or_eventually_poly`, `Core.thin_of_not_isRatGerm`).
   Taylor-split `z(t) = Poly(t) + A₀(1/t)` with `deg Poly ≤ L`; the recursion
   `A_{j+1}(x) = −x²·A_j'(x)` transports `d/dt` through `t ↦ 1/t`, so `z^{(L+1)}(t) = A_{L+1}(1/t)`
   with `analyticOrderAt A_{L+1} 0 = k+L+2`.  Three cases:
   * imaginary part not identically zero near `0` ⇒ `z(t) ∉ ℤ` far out;
   * `z` eventually a polynomial ⇒ either `w` is a rational germ (excluded by step 1) or a
     coefficient is irrational and Lagrange interpolation bounds the integer points;
   * otherwise the divided-difference mean value theorem (`DividedDifference`, iterated Rolle) makes
     the normalised divided difference a *nonzero integer*, forcing the gap
     `α·t₀^q < (t_m − t₀)^E` — the predicate `Thin`.
6. **Assembly** (`ThinSets.infinite_compl_of_thin`, `Main`).  Finitely many gap-thin sets cannot
   cover the integers (window of `r·M+1` consecutive integers far out), so infinitely many `t`
   survive; `b = s₀ + 1/t` are infinitely many distinct rationals with `F(b,Y)` irreducible.
   The `ℚ[X][Y] → ℤ[X][Y]` denominator clearing is `exists_int_clear`.

## Lean modules (`HTGeometry/HilbertIrreducibility/`)
| module | content |
|---|---|
| `ThinSets` | `Thin`, window packing, `infinite_compl_of_thin` |
| `DividedDifference` | iterated Rolle, `exists_dividedDiff_eq`, `dividedDiff_mul_nodeProd` |
| `RationalInterpolation` | interpolation descent `exists_map_eq_of_eval_mem_range` |
| `TaylorTail` | `tailSeq`, `analyticOrderAt_tailSeq`, `thin_or_eventually_poly` |
| `GermIntegral` | germ-ring `R[X]`-algebra, `exists_monic_bivariate_of_isIntegral` |
| `ReflectSubstitution` | `shiftReflect`, `shiftedPoly`, `bivEval_shiftedPoly` |
| `IntegerRoot` | `exists_int_of_bivEval` |
| `Core` | `exists_int_value`, `thin_of_not_isRatGerm` |
| `AnalyticBranches` | `exists_analytic_branches` |
| `IntegralCoefficients` | `coeff_prod_map`, `prod_scaled_eq`, `isIntegral_coeff_prod` |
| `AnalyticCoefficients` | `analyticAt_coeff_prod` |
| `MonicScaling` | `monicScale`, `bivEval_monicScale` |
| `SubsetCoefficients` | `irreducible_fibre_of_not_rational`, `exists_not_ratGerm` |
| `Main` | `exists_regular_int`, `exists_int_clear`, `hilbert_irreducibility`, worked instance `Y² − X` |

## Log
- 2026-08-21 — **CLOSED at stage 3.**  `hilbert_irreducibility` and `hilbert_irreducibility_int`
  proved unconditionally and axiom-clean; fourteen modules wired into `HTGeometry`.
- 2026-08-21 — created; mathlib absence verified; p-adic route retired with reason; Coleman–Zwald
  route frozen; corpus analytic engine (`U0.HolomorphicIFT`) located.
