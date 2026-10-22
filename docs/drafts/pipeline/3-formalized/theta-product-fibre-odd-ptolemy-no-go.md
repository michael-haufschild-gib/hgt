# Theta product-fibre odd Ptolemy no-go

- **ID:** CLG-TTF-FIBRE-ODD-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` routes CLG/TTF; frontier map remains read-only
- **Statement:** The first completed theta product fibre has a strictly negative equispaced reflection-odd Ptolemy wall at some positive separation.

## Goal
Kill the strongest fibrewise-positive route to the global completed-source odd wall. Prove a source-pure obstruction: seam rise, strict half-line log-concavity, and tail decay force one negative odd wall in the first completed shell product. The surviving RH route must therefore use nontrivial cancellation between completed product fibres before applying Ptolemy transport.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module and theorem family below; targeted build green; axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
First prove a general secant obstruction. For a positive continuous profile `f` on the nonnegative ray, assume `log f` is strictly concave, `f` rises immediately from the endpoint, and `f` eventually lies below its endpoint value. An intermediate-value crossing `T > 0` with `f(T)=f(0)`, strict concavity at `T/2`, and the strict post-chord inequality at `3T/2` give
`f(T/2)^2 > f(0)^2 > f(3T/2)^2`.
The odd wall is then strictly negative because its first drop and full drop have opposite signs. Apply this to `f x = thetaCuspSourceTerm x 1`; the first completed product fibre at center zero is `f(|t|)^2`.

## Paper proof

**[PROVED HERE]** Put `g(x) = log(thetaCuspSourceTerm x 1) - log pi` for `x >= 0`. The exact Born--Witten factorization gives `thetaCuspSourceTerm x 1 = pi * exp(g(x))`, while its curvature identity gives `g''(x) = -thetaCuspBornWittenLogCurvature 1 x < 0`. Hence `g` is strictly concave on `[0,infinity)`.

The exact seam derivative is positive, so there is `a > 0` with `f(a) > f(0)`. Since the first atom tends to zero, there is `b > a` with `f(b) < f(0)`. Continuity supplies `T in (a,b)` with `f(T)=f(0)`, equivalently `g(T)=g(0)`. Strict concavity at the midpoint gives

`g(T/2) > (g(0)+g(T))/2 = g(0)`.

Writing `T = (1/3)*0 + (2/3)*(3*T/2)` gives the exterior secant inequality

`g(T)=g(0) > (1/3)*g(0) + (2/3)*g(3*T/2)`,

so `g(3*T/2) < g(0)`. With `t=T/2` and `p(s)=f(s)^2`, therefore `p(t)>p(0)>p(3t)`. Thus

`(p(0)-p(3t))*(p(0)-p(t)) - (p(t)-p(2t))^2 < 0`,

which is the reflection-odd four-point wall of product fibre `k=1` at center zero. The fibre wall depends continuously on center, so this strict failure persists on a nonempty right-neighborhood of physical centers `u>0`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:**
  `exists_thetaCuspCompletedProductFiberAmplitude_one_oddParityWall_neg` proves a negative seam wall;
  `exists_thetaCuspFirstCompletedProductFiberOddParityWall_neg_germ` proves persistence on a right germ;
  `exists_pos_thetaCuspCompletedProductFiberAmplitude_one_oddParityWall_neg` extracts a positive-center witness.
- **Strongest positive survivor:** Aggregate cancellation between product fibres is necessary; individual-fibre Ptolemy positivity cannot prove the completed-source wall.
- **New insight:** The modular seam derivative cancellation is not cosmetic. Higher shells must repair a rank-four defect created by the seam-rising first shell before any global odd-wall argument can close.
- **Status:** Paper proof dependency-closed and formalized in
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedProductFiberOddPtolemyNoGo`.
  Axiom audit reports only Lean/mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`;
  no project axiom or hypothesis is introduced.

## Log
- 2026-08-28 — created directly in 1-in-progress after corpus audit exposed the first-shell seam-rise mechanism.
- 2026-08-28 — `[PROVED HERE]` paper proof closed, formal Lean module built, umbrella import wired,
  and positive-center germ obstruction audited.
