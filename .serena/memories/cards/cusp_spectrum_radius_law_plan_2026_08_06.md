# cusp-spectrum-radius-law — state and plan

Card: docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md

## For ζ (degree 1, conductor 1) the card is CLOSED at the boundary

`RHTower/HurwitzZetaRightAsymptotics.lean` → `ZetaTwistShiftDecomposition.lean`
→ `ZetaTwistCuspRadius.lean` → `ZetaTwistGapGeometry.lean`.

Capstone: `hadamardLimsup_zetaTwistShift_eq_infDist` —
`limsup_k |F(s₀-k,α)/k!|^{1/k} = 1/(2π · infDist α (Sing \ {α}))`
for EVERY real shift α, unconditionally. Sides use disjoint data.

**The Mellin–Barnes step the card asked for is NOT needed.** Route:
1. mathlib `expZeta_one_sub` (Hurwitz formula) gives
   `F(s₀-k,α) = (2π)^{-(1-s₀+k)} Γ(1-s₀+k)(E_k ζ(w_k,α) + E'_k ζ(w_k,-α))`,
   `w_k = 1-s₀+k`, and `|E_k|,|E'_k|` are CONSTANT in k (k is real).
2. `a^w ζ(w,a) → 1` as Re w → ∞ (`tendsto_normalizedHurwitz`): normalize by the
   first term, tail ≤ `a^{Re w}·∑(n+1)^{-2}`. So `ζ(w_k,α) ~ A^{-k}`,
   `ζ(w_k,-α) ~ B^{-k}` with A,B = the two Hurwitz first exponents.
3. A ≠ B: faster term dominates, no cancellation. A = B ⟺ α ≡ -α on the circle
   ⟹ the two Hurwitz values are EQUAL and the bracket is a period-4 factor times
   one of them (`twistWave`), invisible to the root.
4. `min(A,B) = dist(α, ℤ)` = Δ(α); at integer α, Δ = 1.

## Also closed (interior, general families)

`HTGeometry/NonnegThetaCuspGrowth.lean` + `CuspGapUnconditionalInstances.lean`:
boxed law for any non-negative coefficient family, any degree d>0, any real σ
below the abscissa. `hadamardLimsup_divisorCoeff_cusp` = degree-2 instance.
CAVEAT: interior shadow — the base height is *chosen* to be Δ.

`RHTower/ZetaStandardTwistDichotomy.lean`: `differentiable_expZeta_iff` is K–P's
continuation theorem for ζ, straight from mathlib.

## What is left

- General Selberg class `S^♯` and K–P for `d > 1`: needs the class member's own
  Hurwitz-type formula. Corpus has NO Selberg-class layer.
- Step 3 at degree 2 (independent constant for ζ²) hits a parity obstruction:
  `‖c_{2m+1}‖^{1/(2m+1)}` does not reduce to a `1/m` root. Would need a
  "limsup under exponent perturbation" lemma; `Nat.centralBinom` bounds and
  `limsup_sup_filter` are the tools.
