# cusp-spectrum-radius-law — state and plan

Card: docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md

## Degree 1 is CLOSED at the boundary, any conductor

Two independent routes, both unconditional, both via a functional equation whose
RIGHT side is a convergent series dominated by its first exponent:

1. **ζ, any real shift α** (`HurwitzZetaRightAsymptotics` →
   `ZetaTwistShiftDecomposition` → `ZetaTwistCuspRadius` → `ZetaTwistGapGeometry`).
   Capstone `hadamardLimsup_zetaTwistShift_eq_infDist`:
   `limsup_k |F(s₀-k,α)/k!|^{1/k} = 1/(2π · infDist α (Sing \ {α}))`.
   Input: mathlib `expZeta_one_sub` (Hurwitz formula) + `a^w ζ(w,a) → 1`.
2. **Any periodic Φ : ZMod N → ℂ, Φ ≠ 0** (`PeriodicLSeriesRightAsymptotics` →
   `ZModLFunctionCuspRadius`). Capstone `hadamardLimsup_zmodShift`:
   `= N/(2π n₀)`, n₀ = least n ≥ 1 with `𝓕Φ(n) ≠ 0 ∨ 𝓕Φ(-n) ≠ 0`.
   Input: mathlib `ZMod.LFunction_one_sub` + `n₀^w L(Θ,w) → Θ(n₀)`.
   `hadamardLimsup_zmodShift_of_dft_one` gives the card's Dirichlet row: N/(2π).

**Common mechanism — reusable.** Write the shifted value via the functional
equation as `(geometric)^k · Γ-ratio · bracket`; the bracket is
`E_k A_k + E'_k B_k` with `|E_k|,|E'_k|` CONSTANT in k (k real) and `E_k = e·i^k`.
Extract the dual geometric rate; the bracket then converges to the period-four
shape `e i^k a + e' (-i)^k b`, whose four values vanish together iff a = b = 0.
Minimality of the first exponent forbids that ⇒ frequent lower bound ⇒
`limsup_rpow_inv_eq_one`. NO Mellin–Barnes anywhere.

## Also closed (interior, general families)

`HTGeometry/NonnegThetaCuspGrowth.lean` + `CuspGapUnconditionalInstances.lean`:
any non-negative coefficient family, any degree d>0, any real σ below the
abscissa. CAVEAT: interior shadow — base height is *chosen* to be Δ.
`RHTower/ZetaStandardTwistDichotomy.lean`: `differentiable_expZeta_iff` = K–P for ζ.

## What is left

- Degree `d > 1`: needs the class member's own Hurwitz-type formula
  (general Selberg class `S^♯` + K–P). Corpus has NO Selberg-class layer.
- Step 3 at degree 2 (ζ²) parity obstruction: `‖c_{2m+1}‖^{1/(2m+1)}` does not
  reduce to a `1/m` root; needs a limsup-under-exponent-perturbation lemma.
  Tools if attempted: `Nat.centralBinom` bounds, `limsup_sup_filter`.
