# Mass-shifted arcsine-vacuum source renormalization (2026-08-13)

## Formalized results

1. `XiShiftedChristoffelSourceWallTraceRenormalizationNoGo.lean`
   - Every positive degree-n raw wall satisfies `W_n>(n+1)/16`.
   - Fully positive infinite tower forces raw walls to +∞ and non-summability; no finite positive trace.
   - Canonical one-edge renormalization is exact adaptive Gauss-visible source:
     `W_n-(n+1)/16 = Q_n^G/(16 h_(n+1)) = B_n^G/(32 h_(n+1))`.
   - Literal source partition uses completed adaptive mixed P-sharp rational–Gamma/von-Mangoldt source before reflection.
   - Subtraction preserves all finite-contact residues.

2. `XiShiftedArcsineVacuumRenormalizedSourceLaw.lean`
   - Exact arcsine Jacobi energy: `E_n^arc=n+3/8`.
   - Exact two-account vacuum:
     `n+3/8=(n+1)/16+(15n+5)/16`.
     First term is invisible newborn edge; second is visible adaptive Gauss bulk.
   - Minimal positive renormalization still diverges linearly even in fully positive arcsine tower.
   - Define signed full-vacuum deviation
     `D_n(w)=scaleCompletedRelativeArithmeticSource(w,n)-(n+3/8)`.
   - It is identically zero on every nonzero coordinate-dilated arcsine admission and tends to zero for every fixed Xi degree.
   - Full counterterm subtraction preserves exact all-contact strict-frontier residue.

Both modules wired into `RHTower.lean`. Direct Lean and targeted builds pass. Axiom audits: only `propext`, `Classical.choice`, `Quot.sound`. Global lint sees both modules; unrelated concurrent modules remain unreachable.

## Scientific consequence

Raw walls and minimally-renormalized positive Gauss walls cannot be common finite actions. Correct surviving category is signed arcsine-vacuum deviation formed after adaptive source admission/Christoffel completion and before degree/reflection reporting. Exact remaining §9.3 core: prove a degree-uniform cross-degree action/admission law for `D_n` along parabolic first-contact schedules. Fixed-degree `D_n→0` is insufficient. RH remains unproved.

## Documentation

- Report §9.3 equations (9.3.720)–(9.3.724).
- Stage3 cards:
  - `mass-shifted-source-wall-trace-renormalization-no-go.md`
  - `mass-shifted-arcsine-vacuum-renormalized-source-law.md`
- Novelty remains unverified; Killip–Simon Jacobi sum rules, generalized-Jacobi asymptotics, and Romik Xi orthogonal expansions do not state route-specific adaptive prime–Gamma source law.