# Theta rank-three direct parabolic determinant

- **ID:** S6G-DPD
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `theta-rank-three-projective-drift.md` · direct-determinant survivor
- **Statement:** Native rank-three D1 is positive on the Lean-proved refined parabolic theta cone, closing the finite S6F/TCD physical-orbit gate without proving projective-drift positivity.

## Goal

Prove unconditionally

```text
0 < thetaCuspFullReflectionEighthHankelCurvature x
```

for `0 < x < 137/2000`, using the actual source orbit and the refined cone

```text
(13/32+z²/32)z < v < (33/80+z²/16)z,
191/10+(37/5)z² < X,
0<z<3/10.
```

Together with existing seam and large-weight theorems, this discharges the remaining finite native
rank-three D1 gate. Cofinal/all-order landing remains separate.

## Gates

- [x] 0 → 1 in-progress: exact source-pure claim, hostile computation, and formal cone localization
- [ ] 1 → 2 fully-proven: computation-free direct determinant proof
- [ ] 2 → 3 formalized: exact D1 theorem and finite-interval assembly
- [ ] 3 → 4 publication-ready: integrate with full S6F/TCD landing

## Frontier

- `[CORPUS]` `thetaCuspModularProjectiveClocks_mem_refinedParabolicThinCone` proves the displayed
  cone unconditionally in Lean.
- `[CORPUS]` Native D1 is strictly positive at the modular seam and for `x≥137/2000`.
- `[LOCAL-RESEARCH]` Exact RunPod diagnostics on the larger old cone find D1 itself strictly
  positive, scale-increasing/scale-convex, and strictly concave in `w=z²`. Clock concavity reduces
  the diagnostic minimum to endpoint faces; the outer face is strictly decreasing in wall
  interpolation and minimizes at its upper corner. No output is admissible in the proof. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-parabolic-d1-contact/REPORT.md`.
- `[LOCAL-RESEARCH]` Exact principal-minor reconstruction on the refined cone finds complete
  scale-velocity Hankel matrix `H_X` strictly positive definite: all diagonal, rank-two, and
  rank-three half-prism certificates are positive. This opens a Loewner/Jacobi proof of scale
  increase. Report:
  `../2-fully-proven/computations/2026-08-29-s6f-jacobi-variation/REPORT.md`.
- `[PROVED HERE][FORMALIZED]` The source-positive vector field belongs to an exact polynomial
  `sl₂` triple. In adapted coordinates `r=U+3B`, `b=B`,
  `k=Q+3/8-3B²/8`, its companion lowering field is exactly `∂b`, the scale field has
  weights `(1/2,1/2,1)`, and the source dynamics have a three-equation normal form. Formal module:
  `PolynomialODEJetRankThreeSourcePositiveSl2`.
- `[FALSIFIED — diagnostic]` Raw coefficientwise matrix-Bernstein positivity cannot explain
  `H_X`: every scale-square coefficient matrix has negative leading rank-two/rank-three pivots and
  every scale-cube coefficient matrix has negative determinant. Cross-scale cancellation is
  essential. Report: `../2-fully-proven/computations/2026-08-29-s6f-sl2-scale-structure/REPORT.md`.
- `[FALSIFIED — diagnostic]` Global reflected-fibre positive definiteness and its all-order Bochner
  completion fail at a six-point Toeplitz section. Finite-order-five positive definiteness survives
  21.12 million arbitrary-packet attacks and remains a stronger alternate route to D1. Report:
  `../2-fully-proven/computations/2026-08-29-reflected-fibre-positive-definite/REPORT.md`.
- `[FALSIFIED]` Naive factorization in source-positive or reconstructed-gap coordinates: D1 and
  its leading rank-two minor are irreducible over `QQ` there.
- `[FALSIFIED]` A higher alternating clock hierarchy: sign-corrected order four is already mixed.
- `[LITERATURE]` Planat--Solé (arXiv:2608.19160) proves a rank-two theta-kernel concavity theorem by
  autonomous phase space and polynomial shear, but not this rank-three D1 cone theorem. Salazar
  (arXiv:2606.31647) gives positive moment-representation mechanisms that do not apply to the
  reflected theta source.

## Active conjecture and hostile verdict

`[CONJECTURE]` On the refined parabolic cone, normalized D1 is increasing in scale slack and
strictly concave in `w`; its two `w` endpoint faces are positive, with the outer face decreasing
toward the upper ratio wall.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

`[OPEN CORE]` Construct the exact contravariant/Shapovalov form on the finite reflected-jet
`sl₂` module and try to make its rank-three restriction indefinite at a rational interior state.
If it survives, prove positivity on the refined cone and use Loewner/Jacobi monotonicity for scale
reduction. A viable alternate is a nontrivial congruence mixing scale layers; raw coefficientwise
Gram/SOS is dead. Then derive clock second variation and prove the outer upper-wall polynomial
positive.

## Representation lesson

Projective drift asked for global monotonicity of D1, which is stronger than positivity. Correct
primitive is the determinant chamber itself. Its source dynamics are one-sided in scale and
second-order in clock square; complete monotonicity and source-coordinate factorization are false.
The next proof should use determinant second variation or Schur-complement geometry, not another
coefficient hierarchy.

## Log

- 2026-08-29 — Direct-cone diagnostic survives on the larger formal cone; exact boundary geometry
  and factorization/hierarchy kills independently verified.
- 2026-08-29 — Dangerous upper-clock and scale faces tightened by a computation-free paper proof
  and exact Lean theorem; active core moved from drift positivity to direct D1 positivity.
- 2026-08-29 — Exact hostile tests killed all-order reflected-fibre Bochner completion at six
  points and opened strict Loewner scale velocity as conceptual D1 scale mechanism.
- 2026-08-29 — Exact `sl₂` source structure formalized; raw matrix-Bernstein Gram killed.
