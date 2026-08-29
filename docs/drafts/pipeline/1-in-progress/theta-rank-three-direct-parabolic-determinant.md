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

`[OPEN CORE]` Derive the scale first-variation and clock second-variation signs from the determinant
and modular ODE without expanding a Bernstein table, then prove the single outer upper-wall
polynomial positive by a short source inequality or determinant identity.

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
