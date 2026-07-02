# Doc-14 certificate computation — results (2026-07-02, c = 1/5, t₀ = 3/64)

Scripts: `probe_descent.py` (profile + descent spectrum + zooms),
`probe_structure.py` (bad-set structure), inline runs (N-comparison, φ-profile,
chirality). Machine: local, numpy float64. Self-tests: γ(1/4) = i√(β+c) to 1e−12;
r(t₀)/r(t₀/2) = λ to 5e−8.

## 1. Numerical-methods finding: the Koenigs telescope is float-unstable

r(t) = lim λⁿ|γ(t/2ⁿ) − β| has an error floor ≈ 1e−16·λᴺ (+ truncation ≈ 0.1·λ⁻ᴺ):
rounding at late steps is amplified by λⁿ (absolute ulp errors near β are huge
relative to D_n). Optimal N ≈ 46 gives floor ≈ 3e−9; N = 40 gives ≈ 5e−8 — exactly
the scale of the first observed "micro-descents" (artifacts); N = 80 is garbage
(predicted 7e−4; observed max|r₄₀−r₈₀| = 7.8e−4 ✓). All fine-scale analysis was
therefore redone on the EUCLIDEAN profile φ(t) = |γ(t) − β| (no telescope; the
K-step chain has no amplification; floor ≈ 1e−14).

## 2. The micro-descents are REAL: the 1D sublevel target is empirically FALSE

φ-profile on the edge annulus [3/128, 3/64] (range [0.2521, 0.3971]):

- global max descent depth saturates at 2.597e−5 (K = 18→26: 2.07, 2.48, 2.57,
  2.593, 2.597 ×1e−5) — a finite, fully resolved feature;
- bad-level measure grows (3.0e−4 → 2.4e−3, K = 18→26), widest clean gap shrinks
  (0.078 → 0.0023);
- deep zooms (to K = 44, 33M points, floor 1e−14): every probed crossing carries a
  POSITIVE saturated dip (5.0e−9, 5.6e−9, 9.7e−8 — stable under further refinement).

If every up-crossing carries a positive dip (3/3 probed, plus the global dip), then
EVERY level is straddled by a descent at its own crossing ⟹ the angle-space sublevel
{t : φ < ρ} is disconnected for essentially every ρ ⟹ **the 1D statement of
problem 14 (clean band, and even clean single levels, for the sublevel sets) is
false at c = 1/5.** The (E)/(O) certificate route and the Koenigs-window reduction
are dead as vehicles: the reduction from the planar problem to angle-space sublevels
is lossy, and its target fails.

## 3. Chirality: 1D-dirty ≠ planar-dirty — and both dip types occur, locale-coherently

A radial dip always disconnects the angle-space sublevel, but creates a PLANAR
pocket (disconnects B(β,ρ)∖K) only if the lens between the dip and the sphere lies
on the Ω-side of the arm. Escape-testing lens points (|z|>3 ⟹ Ω; entering
|z|<β ⟹ K, using the certified trap closedBall(0,β) ⊆ K):

- crossing at φ ≈ 0.2884: 8/8 dips K-side (harmless);
- crossing at φ ≈ 0.3246: 7/8 dips Ω-side (GENUINE planar pockets, depth ~5e−9);
- crossing at φ ≈ 0.3372–0.3971 zone (global dip 2.6e−5): 3/3 Ω-side;
- crossing at φ ≈ 0.3608: 8/8 K-side.

**Chirality is coherent per decoration site** (all dips at one crossing share
orientation), and both site types occur along the arm.

## 4. Consequences

1. The strong all-ρ planar form is false at these scales too (Ω-side pockets at
   radii near 0.3246 and 0.3951, recurring at all λ-rescaled scales by
   self-similarity of the germ) — consistent with the earlier c = −0.9 finding.
2. The planar bad-set is PROPER: levels whose crossings sit at K-side sites (e.g.
   ≈ 0.2884, ≈ 0.3608) show no planar pockets to depth 1e−14-resolution — planar
   cofinal cleanness at β (what the Lean chain consumes) remains plausible, but its
   truth is decided by the chirality pattern, not by any monotonicity.
3. NEW ROUTE suggested by the data: decorations are dynamical pullbacks of a
   fundamental decoration, so site chirality should be a symbolically computable
   invariant propagated conformally. A theorem "chirality is locale-coherent and
   determined by the digit history of the site" would make clean radii = levels
   whose crossings hit only K-side sites — a provable + certifiable criterion
   (K-side lens verdicts by interval escape ARE rigorously certifiable; the
   remaining tail question becomes the coherence theorem, not per-dip checking).
4. Certification-impossibility note (proved conceptually before running): value
   enclosures alone can never certify band-cleanness of a continuous profile
   (levels are attained; cleanness is about monotone attainment) — consistent with
   what the data then showed (there is nothing monotone to certify).

## Caveats

Floats (not intervals) — but all reported effects are 5+ orders above the 1e−14
floor, saturate under refinement, and the chirality verdicts use decisive escape
events. The "every crossing dips" inference rests on 4 probed sites; the chirality
statistics on 27 dips at 4 sites.
