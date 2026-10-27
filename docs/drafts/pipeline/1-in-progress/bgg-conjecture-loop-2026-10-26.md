# BGG conjecture loop

- **ID:** bgg-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card)
- **Source:** `formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/README.md` §9
- **Statement:** successive conjectures for Biarithmetic Gauge Geometry; each entry is proved and
  formalized, or closed with its positive survivor.

## C1 — Rational deformations of `ζ_γ` are classified by the horizontal zero line at height `γ`

**Conjecture.** Let `F = ζ_γ · ∏ᵢ (s − zᵢ)^{mᵢ}` (finite, `mᵢ ∈ ℤ`) lie in
`HeightCoupledSystem 2 1 1 γ` with completion `Λ`, net multiplicities `M(w) = Σ_{zᵢ = w} mᵢ` not all
zero. Let `σ* = max{Re w : M(w) ≠ 0}`. Then `σ*` is a real pole of the multiplier
(`M(σ*) < 0`), `|M(σ* + ib)| ≤ −M(σ*)` for all `b`, and `ξ(σ* + iγ) = 0`.

**Paper proof.**
1. *Lattice sieve.* `−F'/F = A + G`, `A(s) = Σ Λ(n)|1 + n^{iγ}|² n^{−s}` (nonnegative lattice
   coefficients), `G = Σ_w c(w)/(s − w)`, `c = −M`. Positive-definite vertical sections make
   `x ↦ A + G` completely monotone on a real ray. Post–Widder at scale `t`:
   `PW_k(A + G)(t) ≥ 0`, `PW_k(G)(t) → w_G(t) = Σ c(w) e^{t Re w} cos(t Im w)`, and for
   `t ∉ log ℕ` each atom `log n` contributes `≤ (k/t)(r e^{1−r})^k`, `r = log n / t ≠ 1`, with a
   uniform `(k/t)(2e^{−2})^k e^{4σ₀t} n^{−σ₀}` tail bound for `r ≥ 4`. So `PW_k(A)(t) → 0` and
   `w_G ≥ 0` off `log ℕ`, hence on `(0, ∞)` by continuity.
2. *Landau anchor.* `w_G ≥ 0` gives `G(s) = ∫₀^∞ w_G(t) e^{−st} dt` for `Re s > σ*` and
   `|G(x + ib)| ≤ G(x)`. Multiplying by `x − σ*` and letting `x ↓ σ*`: `|c(σ* + ib)| ≤ c(σ*)`.
   A top-level point with `c ≠ 0` forces `c(σ*) > 0`.
3. *Pole forcing.* `Λ = Λ_γ · R` off the finite pole set (identity theorem); `R` has a pole at
   `σ*`, `Λ` is entire, so `Λ_γ(σ*) = 0`; `ξ` has no real zeros, so `ξ(σ* ± iγ) = 0`.

**Consequences.** (a) Rational rigidity at every height `γ` carrying no zero of `ξ`;
(b) without off-critical zeros at ordinate `γ`: `σ* = 1/2`, central order strictly drops
(chiral law, exact); (c) with one, quartet contraction raises it by `4`; hence
rational `CentralVanishingCeiling γ` ⟺ no off-critical zero at ordinate `γ`, and
`∀ γ ≠ 0` rational ceiling ⟺ RH.

**Status:** formalized — card `3-formalized/bgg-rational-deformation-classification.md`.

## Log
- 2026-10-26 — created; C1 opened.
- 2026-10-27 — C1 formalized.
- 2026-10-27 — C2–C14 formalized (see `logs/bgg-250-contributions-2026-10-26.md` and the `3-formalized/bgg-*` cards).
