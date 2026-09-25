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
