# Boundary radius law for the standard twist

- **ID:** standard-twist-boundary-radius-conjecture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** `../../../3-formalized/cusp-spectrum-radius-law.md` §Correction (2026-09-27)
- **Statement:** for `F ∈ S^♯` of degree `d`, every real `α₀` and `s` off an exceptional set,
  `limsup_k |F_{α₀}(s−k/d)/k!|^{1/k} = 1/(2π dist(α₀, Sing(F) \ {α₀}))`, where
  `Sing(F) = {α ∈ ℝ : F_α is not entire} ⊇ Spec(F) ∪ (−Spec(F)) ∪ {0 : F has a pole}`.

## Goal

The corrected form of the refuted boxed law of the cusp–spectrum card.  Proven: the cusp `α₀ = 0`
for every class member (Lean), and every `α₀` for `ζ` (Lean, singular set `ℤ`).  Open: `α₀ ≠ 0`
in degree `≥ 2`, and `α₀ ∉ ℤ` for general degree-one members.

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach

Two inputs are missing, both genuine:

1. **Kaczorowski–Perelli continuation.**  `F_α` entire for `α ∉ Sing(F)`, simple poles at
   `s*_ℓ = (d+1)/(2d) − ℓ/d − iθ_F/d` with `ρ₀(α) ≠ 0` for `α ∈ Spec(F)`.  Not yet in the corpus (the
   `SelbergClass/MultipleStandardTwist*` layer stops before continuation).
2. **No nearer nonreal singularity.**  The radius at `−α₀` is the distance to the nearest singularity
   of the continuation of `Φ_F(s,·)` anywhere in `ℂ`.  A real-boundary analysis does not see nonreal
   singular points.  For `ζ²` the Voronoi kernel `K₀` produces singular points `z = −2i√n` — farther
   than the real ones, but nothing excludes nearer ones in general.  A transformation formula for
   `Φ_F` (Fox `H`-function kernel from the functional equation) should locate all singular points
   `z = −ω β`, `β ∈ Spec(F)`, `|ω| = 1`; if so `|ωβ − α₀| ≥ |β − α₀|` makes the real points nearest.

The cusp proof in Lean (Mellin–Barnes, contour shift, far-left root estimate) is the template: at
`α₀ ≠ 0` the left-line estimate needs the far-left growth of `F_{α₀}` itself, which is exactly the
open content.

## Log
- 2026-09-27 — created in 0-backlog from the refutation of the general boxed law.
