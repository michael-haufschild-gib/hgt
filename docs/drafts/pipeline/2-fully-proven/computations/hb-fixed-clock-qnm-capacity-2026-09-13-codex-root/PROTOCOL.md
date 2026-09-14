# Protocol: fixed-clock/QNM cancellation capacity

Frozen before numerical output.

## Exact target

Current corpus reduces two proposed escape mechanisms to explicit necessary conditions.

1. Literal fixed onset: every physical branch/side/overtone factor is `F(L*z)` with `F(z)=integral_0^1 chi'(u) exp(z*u) du`, literal mathlib `smoothTransition`, real duration `L`, and
   `z = a*q+b+2*n`, where `(a,b)` is `(5/2,-3)`, `(3/2,-2)`, `(-3/2,-1)`, or `(-5/2,0)`.
2. QNM completion: after scaling the exact nonzero fundamental metric AIME numerator to one, cancellation needs a causal spectral remainder to persist near `-1`.  On an Xi fibre, the complete BM Jost divisor consists only of the two towers
   `omega_n^+ = gamma/2 - i*(2*n+1+beta/2)` and
   `omega_n^- = -gamma/2 - i*(2*n+2-beta/2)`.

Question: can one source-independent real clock duration create simultaneous physical onset extinction, or can bounded-variation Jost-mode data imitate the persistent counterterm for long delays?  Either success would expose a live loophole in existing asymptotic no-go results; failure quantifies what any complete temporal/metric/QNM matching must import from outside the declared causal pole sector.

## Hypotheses and falsifiers

- H1: one real duration produces a robust common near-zero across all four physical channels and the first nine overtones at actual zeta heights, but not midpoint controls.
- H2: increasingly many exact BM QNMs approximate a persistent counterterm on growing delay windows without explosive coefficient variation.
- H3: actual zeta heights have a cancellation-capacity signature absent from controls and synthetic off-line tilts.
- Falsify H1 by a large best worst-channel coherence, moving single-channel near-hits, or equal control behavior.
- Falsify H2 by exponential variation growth, endpoint lower-bound saturation, instability under denser validation, or inability to beat fixed error.
- Whole-class impossibility criterion: independently prove the complete source-retaining action contributes only passive stationary mass plus a finite-variation measure supported on the full BM Jost divisor.  Under that identification, existing exact no-go theorems turn H2 failure into a route kill, not merely numerical evidence.

## Mechanical application of all 24 scientific methods

1. Decompose literal onset, four affine channels, overtone index, plus/minus Jost towers, coefficient variation, and passive mass.
2. Attack with midpoint-height and synthetic off-line controls, not only known critical-line zeros.
3. Reverse-search single-channel duration near-hits, then demand simultaneous cross-channel persistence and high-precision survival.
4. View same cancellation as entire-transform coherence, a finite minimax problem, causal spectral synthesis, and a residue counterterm.
5. Map duration, height, branch, side, overtone, delay horizon, tower size, tilt, and SVD regularization.
6. Use literal mathlib pulse and exact BM Jost formulas; no fitted receiver replaces dynamics.
7. Normalize only the nonzero AIME amplitude; preserve phase, damping, onset shape, and physical affine maps.
8. Cross-check pulse by centered direct integral and integration by parts; cross-check spectral fits on a denser held-out time grid and against the exact endpoint bound.
9. Include unit duration, zero-duration limit, lowest/large overtone, both branches, both sides, first zeta height, and near-boundary tilts.
10. Vary quadrature order, duration grid, validation density, SVD cutoff/ridge, tower size, and delay window.
11. Parallelize independent height and spectral configurations across 16 CPU workers per pod; force library threads to one.
12. Test conjugate/reflection channel symmetry and beta-to-`1-beta` tower exchange.
13. Track near-hits under height controls, duration perturbations, overtone enlargement, and precision increase.
14. Bridge output to exact total-period QNM residues and full-Jost finite-variation no-go; do not call factor zeros complete action zeros.
15. Freeze formulas, grids, tolerances, controls, and acceptance rules here.
16. Preserve strongest common near-extinction, strongest single-channel near-hit, smallest long-window coefficient cost, and worst validation failure.
17. Require independent formulas/precisions for discoveries and analytic lower-bound consistency for every spectral fit.
18. Ground every map in current named Lean definitions/theorems inspected before coding.
19. Fake-proof audit: finite truncation failure does not exclude peripheral spectrum, growing modes, infinite variation, or uncomputed boundary defects.
20. Missing lemma: complete temporal/metric/action correction has finite variation and support on the classified full BM Jost divisor, with passive stationary terms separated.
21. Dependency chain: literal source -> metric AIME numerator -> total angular cokernel -> BM Jost divisor -> causal time response -> fixed-clock extinction.
22. Nearby false worlds: midpoint ordinates, synthetic beta tilts, one tower only, duration tuning, finite truncations, ridge regularization, and omitted passive mass (most favorable cancellation).
23. Boundary cases: `L=0`, `L=1`, beta near `0/1`, overtone zero/high, delay zero/large, and rank-deficient fits.
24. Positive residue target: quantitative variation-vs-delay law, robust affine channel separation, or a precise escape classification naming required peripheral/infinite-variation support.

## Numerical design and acceptance

Clock atlas: first ten mpmath zeta ordinates plus consecutive midpoints; four physical affine channels; overtones `0..8`; real durations `0.05..3`; 320-node Gauss-Legendre half-interval formula.  Coherence is `|centered F(z)|/centered F(Re z)`, hence scale-free.  Refine global minima with a denser duration search, 640 nodes, and 80/120-digit direct/integration-by-parts evaluations.  Common extinction requires every channel coherence below `1e-6`; a single near-hit is not accepted.

QNM capacity: beta `.2,.5,.8`; selected actual ordinates; two towers with `2,4,8,16` modes each; delay windows `.5,1,2,4,6`; SVD/ridge frontier fit on 401 nodes and validate on 2001 nodes.  Report coefficient `L1`, held-out maximum/RMS errors, condition spectrum, and the exact endpoint bound `L1 >= (1-error_at_T)*exp(a*T)`, where `a` is the slowest damping.  No finite-grid result is called a proof of the arbitrary-measure theorem.

Runtime family cap: ten minutes per script, no detached jobs, no Lean build.
