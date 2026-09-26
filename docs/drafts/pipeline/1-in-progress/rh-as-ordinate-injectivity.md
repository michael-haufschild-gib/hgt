# RH is the injectivity of the ordinate map

**Status:** Lean-closed (axiom-clean). Reformulation complete; producer open.
**Module:** `RHTower/OrdinateInjectivity.lean` (on `ReflectionTateParity.lean`).
**Ledger:** MUST-401, CANNOT-402.

## The chain

1. RH ⟺ the Hermitian reflection `σ : ρ ↦ 1 − ρ̄` acts trivially on `Div(ξ)` (`ReflectionTateParity`).
2. **`σ` preserves the imaginary part** (`lagPartner_im`) — so the `ℤ/2`-action is *fibred over the
   height*. Every orbit lies in one horizontal slice.
3. A free orbit is therefore **two distinct zeros at exactly the same ordinate**.

```
riemannHypothesis_iff_ordinate_injective :
  RiemannHypothesis ↔ ∀ q r : XiZeroCopy, (q.1:ℂ).im = (r.1:ℂ).im → (q.1:ℂ) = (r.1:ℂ)
```

Corollaries, all axiom-clean:

```
re_eq_half_of_slice_subsingleton :
  (∀ r, (r.1:ℂ).im = (q.1:ℂ).im → (r.1:ℂ) = (q.1:ℂ)) → (q.1:ℂ).re = 1/2
exists_ordinate_collision_of_not_riemannHypothesis :
  ¬RH → ∃ q r, (q.1:ℂ).im = (r.1:ℂ).im ∧ (q.1:ℂ) ≠ (r.1:ℂ)
```

**Any height carrying a single divisor point is automatically critical — unconditionally, with no
estimate.** The whole hypothesis lives on heights carrying two or more points, of which there are at
most `O(log t)` per unit window (MUST-246).

## Why this is a different target

Everything in the ledger that almost reaches RH is **resolution-limited**:

| family | resolution wall | ledger |
|---|---|---|
| pair correlation, bandwidth ≤ 1 | real parts only at (window)·(distance to line) | CANNOT-334/335 |
| mollified Littlewood | density exponent `2θ`, `θ < 4/7`; no profile helps | CANNOT-300/304/305 |
| Gaussian widths | certifiable widths are the trivial ones | CANNOT-333 |
| lag sampling | exponent `½` provable, `0` is RH, nothing between | MUST-242 |

All of them try to **resolve a small displacement**. But the thing to exclude is an **exact
coincidence of two ordinates** — a codimension condition, not a magnitude. The two statements are
equivalent; the two *targets* are not. Excluding a collision admits scale-insensitive arguments
(argument-principle counting on a horizontal slice, non-vanishing of a derivative along the slice,
genericity of a projection) that no resolution bound governs.

## Open core

Prove, for every real `t`, that the slice `{ρ : ξ(ρ) = 0, Im ρ = t}` has at most one point.
Equivalently: the projection `Div(ξ) → ℝ`, `ρ ↦ Im ρ`, is injective.

Two directions the law itself suggests:
- **Slice-local argument principle.** The slice is the common zero set of `Re ξ(β+it)` and
  `Im ξ(β+it)` in `β ∈ (0,1)` — two real conditions in one real variable. A collision is the
  statement that this overdetermined system has two solutions; the symmetry forces solutions to come
  in pairs, so the question is whether the pair can be non-degenerate.
- **Transversality of the ordinate map.** RH ⟺ the ordinate map is injective ⟺ its "fibre dimension"
  is zero everywhere. This is the shape of a Sard/genericity statement, not an inequality.

## Falsifiers

- If the slice argument needs a lower bound on `|ξ'|` along the slice, it has become an estimate and
  the resolution walls apply again.
- Multiplicity: a zero of order `m` gives `m` divisor *copies* at one point; the criterion is about
  distinct **points**, so it is insensitive to multiplicity — check any proposed argument does not
  silently assume simplicity.
- If a proposed transversality argument works for a general entire function with the same functional
  equation, it proves too much (CANNOT-01): the FE alone admits off-line zeros, hence admits
  collisions, so any valid argument must use the Dirichlet series as well.

## Reduction of the open core (2026-09-26)
- **Slice-local argument principle = the Laguerre hierarchy at height `t`.** Put
  `G_t(u) = ξ(½+√u+it) ξ(½−√u+it)`. It is entire, and `G_t(x²) = |ξ(½+x+it)|²` for real `x`. Its roots
  are `u = (β−½ + i(γ−t))²`. Critical zeros give `u ≤ 0`, and a collision at `t` gives the positive root
  `u = (β−½)²`. The Taylor coefficients of `G_t` are the higher Laguerre expressions of `Ξ` at `t`
  (`c₀ = Ξ²`, `c₁ = Ξ'² − ΞΞ''`, …). A collision at `t` ⟺ a positive root ⟹ a sign change in
  `(L_k(t))`, which is Csordas–Varga's hierarchy localised at one height. The open core coincides with
  route LA's (see `new-route-conjecture-loop.md`, C9).
- **Transversality** is void: collisions are codimension 0 and Hurwitz-stable under the FE (EOC-F6).
- **Lean [L], axiom-clean:** `RHTower/XiHorizontalSliceTaylorPositivity.lean`.
  - `xiSliceProduct t x = ξ(½+x+it)ξ(½−x+it)` and `xiSliceCoeff t n` (Taylor coefficients at `0`).
  - `re_eq_half_of_xiSliceCoeff_nonneg`: nonnegative coefficients at `t` ⇒ every zero with ordinate `t`
    is critical.
  - `slice_collision_free_of_xiSliceCoeff_nonneg`: nonnegative coefficients at `t` ⇒ the height is
    collision-free.
  - `exists_not_nonneg_xiSliceCoeff_of_offLine`: an off-line zero breaks the sign at its own ordinate.
  - `riemannHypothesis_of_xiSliceCoeff_nonneg`: nonnegativity at every height ⇒ RH.
  - Open producer: the sign of `xiSliceCoeff t n` for all `t` and all `n ≲ ½ log t` (detection-index
    law, loop card C10).
- **Equivalence [L], axiom-clean:** `RHTower/XiHorizontalSliceTaylorPositivityConverse.lean`,
  `riemannHypothesis_iff_xiSliceCoeff_nonneg : RH ↔ ∀ t n, 0 ≤ xiSliceCoeff t n`.
  - The converse uses the corpus's unconditional Hadamard product (`XiC_eq_constant_mul_canonicalProduct`).
    Under RH the paired factor is `E₁((t−ix)/γ)E₁((t+ix)/γ) = e^{2t/γ}((γ−t)²+x²)/γ²`.
  - It also uses the closure of `NonnegTaylorAtZero` under sums and products (Leibniz) and under
    locally uniform limits (`tendstoLocallyUniformlyOn_iteratedDeriv`).
  - **Producer shape made exact:** RH ⟺ for every `t` the slice product is a locally uniform limit of
    entire functions with nonnegative Taylor coefficients at `0`. A producer must supply such
    approximants from source data (not from the zeros). The deformation law says the approximation
    scheme must use the functional equation, the Euler product and additive structure together.
- **Per-zero cone criterion [L], axiom-clean:** `RHTower/XiHorizontalSliceConeCriterion.lean`.
  - `xiSliceCoeff_nonneg_of_cone`: if every zero copy satisfies `|Re ρ − ½| ≤ |Im ρ − t|`, all slice
    coefficients at `t` are nonnegative. The Hadamard product is grouped into Hermitian-reflection
    orbits (`lagPartner_lagPartner`, `xiSpectralPoint_lagPartner`). Each pair contributes the positive
    multiple of `x⁴ + 2((Im ρ − t)² − (Re ρ − ½)²)x² + ((Im ρ − t)² + (Re ρ − ½)²)²`, whose `x²`
    coefficient is `≥ 0` exactly outside the cone.
  - `xiSliceCoeff_nonneg_of_abs_le`: for `|t| ≤ 233/20`, every higher Laguerre expression of `Ξ` at `t`
    is nonnegative, unconditionally. This uses the corpus's computer-free critical band below
    `Im² = 2365/16`, and extends the first-order margin `|t| ≤ 58/5` to all orders.
  - The slice test at `t` is broken only by zeros inside the cone `|Im ρ − t| < |Re ρ − ½|`. A collision
    (`t = Im ρ`, `Re ρ ≠ ½`) is its apex.
- **Density consumer [L], axiom-clean:** `RHTower/XiHorizontalSliceDensityFromMeanSquare.lean`,
  `exists_volume_sliceFailure_le_of_line_meanSquare`.
  - Given the mean square of `ζΨ` on the critical line (explicit hypothesis, the corpus's MC terminus),
    the heights in `[T₁+½, T₂−½]` where some slice coefficient fails to be `≥ 0` have measure at most
    `(1/π)((T₂−T₁)/2·log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb))`.
  - Route 3's density shadow now plugs into the same missing input as Levinson and MC. Any Lean proof
    of a mollified mean square `Msq ≤ c(T₂−T₁)` makes "all-order Laguerre positivity on at least
    `1 − log c/(2π)` of every window" unconditional.
