# Actual LI current: small-mass reciprocal-frequency scaling

- **ID:** LI-CURRENT-SINC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (global arithmetic producer); local current window and real-clock limit Lean-closed
- **Objective:** test the actual transfer-combined currents after constituent-jet positivity failed, preserving source cancellation rather than imposing a positive input cone.
- **Parent:** `li-complex-orientation-conjecture-loop-2026-09-29.md`

## Verified starting source

`LiEvenCrossCompletedAbelInteriorFirstZero.lean` defines actual current `C_n(v)` as the shifted reciprocal-moment functional of the unit flux polynomial. Its exact odd-Chebyshev form is

`Q_n(X)=−(n+1)(1−X) U_(2n+1)(2X−1)`.

For each fixed natural `n`, `C_n(0)=2(n+1)²M_0>0` and `C_n(v)` tends to this value. These fixed-order statements are already in the corpus and are not new conjectures. No uniformity in growing `n` follows from that theorem.

The exact first-current Euler jets oscillate cofinally at every positive mass, with the source small-mass first-sign boundary now Lean-closed. That refutes an all-positive constituent-jet cone; it does not determine signs of transfer-combined `C_n`.

## Joint scaling — Lean closed

Let `v→0+`, `n→∞`, `(n+1)√v→u≥0`. Proved limit is

`C_n(v)/(2(n+1)²) → H(u)`,

where the source-faithful entire series is

`H(u)=Σ_{j≥0}(−1)^j (4u)^(2j) M_j/(2j+1)!`.

Independent audit verified factor four and full source normalization. [The formal clock card](../3-formalized/li-actual-current-entire-clock-limit.md) closes the stronger arbitrary-filter limit from `v→0+` and `(n+1)²v→w`, with no separate mode-growth hypothesis. Its real series `S(w)` gives `H(u)=S(u²)`; no complex square-root branch is chosen. Complex atom notation `b^(−1)sinc(4u/√b)` remains explanatory paper notation, not the Lean definition.

Formal proof uses exact endpoint coefficient products, complete weighted shifted source moments and one uniform factorial envelope over every natural degree. It retains all multiplicity copies and reuses existing fixed-degree source continuity. No growing-order differentiation interchange is assumed.

## Arithmetic burden and hostile checks

- Determine whether the complete-source limit is already present under different names. Initial broad transfer search was partial, coverage pending, and recovered only fixed-order/current/two-scale source laws; it supplies no absence claim. Narrow reciprocal/sinc search is underway.
- Generic Chebyshev endpoint scaling is classical. Do not count its specialization alone as significant original mathematics.
- NIST DLMF confirms the exact second-kind trigonometric identity [18.5.2](https://dlmf.nist.gov/18.5#E2) and classical endpoint/Bessel limit mechanism [18.11(ii)](https://dlmf.nist.gov/18.11#ii). These support the generic mechanism, not the complete-source interchange or arithmetic positivity.
- If actual `H(u_0)<0`, the limit would force negative transfer-combined currents at arbitrarily small masses and produce accumulating interior-current zeros. This rejects the stronger zero-exclusion producer; it is not by itself an RH falsification.
- If `H≥0`, compact-offset convergence alone does not prove every finite current positive. A uniform sign margin and control outside the scaling window remain separate burdens.
- A positive real-node packet can have negative sinc sum, so real zero support alone does not give pointwise `H≥0`. Actual source distribution must enter any positivity argument.
- No numerical experiments or added RH/source-sign premises. Only dependency-closed paper theorems enter Lean.

## Next proof/audit steps

1. Audit exact atom and scaling constant; search corpus and primary literature for collisions.
2. Close complete-source domination or reject its uniform premise.
3. Examine actual-source arithmetic identity for `H`; do not rename its positivity as a producer.
4. Extract strongest nontrivial positive survivor if the proposed sign mechanism fails; formalize only after paper and significance audits.

## Positive finite-window survivor — Lean closed

Independent audit closed the constant-one candidate and sharpened it: `C_n(v)/(2(n+1)²)≥(787/6552)A>0` whenever `v>0` and `(n+1)²v≤25`. Exact source proof and final build/direct/axiom evidence are recorded in [the formal uniform-window card](../3-formalized/li-actual-current-uniform-positive-window.md).

For `N=n+1`, normalized Chebyshev factor is `U_(2N−1)(1−2x)/(2N)`. Exact endpoint recurrence gives coefficients `a_j=(-1)^j4^j∏_{i=1}^j(4N²−i²)/(2j+1)!`; all higher coefficients vanish. The original conservative bound `(8N²)^j/(j!)²` is valid. At a source node, `|x|=|v/(b+v)|≤v/|b|<v/150`. Geometric domination bounds the whole normalized-current error from `M_0` by

`A·[2v/150+(v/150)²+(8N²v/150)/(1−8N²v/150)]`.

Under `N²v≤1`, this is below the existing source sector lower bound `M_0≥(167/168)A`. The stronger factorial bound `(16N²)^j/(2j+1)!` certifies the constant-25 window. It still leaves growing-mode zero-exclusion outside the window and cannot swap `∀n∃v` into `∃v∀n`.

Equivalent clock `w=N²v` and series `S(w)=Σ_j(-1)^j(16w)^jM_j/(2j+1)!` are now formal. The direct-series source bound is sharper: `S(w)≥(1051/2184)A>0` for `0≤w≤25`. This controls compact clocks and supplies no sign beyond that window.

## Beyond the compact clock window — arithmetic producer under audit

Proposed source interface uses no zero locations. With raw theta moments `R_j` and `R_0>0`, set

`B(t)=Σ_j [R_j/R_0] t^(2j)/[(2j)!]²`,
`F(t)=t S(t²/16)`.

The existing central identity `XiC'+z G XiC=0` gives, after the even factorial transform, the exact formalized Volterra identity

`∫_0^t F(s) B(t−s) ds = t B'(t)`.

Coefficient audit: write `f_j=(−1)^jR_j/[R_0(2j)!]`; then `Σ_(j+m=n)M_j f_m=−2(n+1)f_(n+1)`. Beta integration supplies the common `(2n+2)!` denominator, matching `t B'(t)` with no extra factor. Compact convergence closes from the all-order scalar score recurrence and factorial source bounds. [Final Volterra card](../3-formalized/li-actual-clock-volterra-positive-mass.md) records complete-source identity, divergent clock positive mass and cofinal actual positive-current corridors. All seven leaves passed final checks and axiom audits.

[Unbounded-support growth](../3-formalized/li-clock-unbounded-support-response-growth.md) is now formal: every fixed real R satisfies `B(t)/exp(R√t)→∞`, and every tail contains `F(t)>M` for every M. Three additional exact leaves and all 12 public axiom audits passed. [Reciprocal sine identity](../3-formalized/li-actual-clock-reciprocal-sine-source.md) is literal and multiplicity-faithful; RH-conditional `S→0` and non-RH top-rate isolation are also formalized. Signed packet asymptotics and RVM mean remain paper-only.

Raw source positivity gives `B>0`, `B'≥0` for `t≥0`; it does not prove sign preservation of inverse convolution. Differentiation gives `F+F⋆B'=(tB')'`, whose resolvent has alternating signs generically. [The calibrated paper obstruction](../2-fully-proven/li-mass-calibrated-score-floor-obstruction.md) now matches even literal actual `R_0` and fixed first-atom polynomial floor while retaining a negative cumulant determinant. A proposed producer must retain full theta source membership or another independent invariant. The exact identity is a transformed existing recurrence; its positive-part mass consequence supplies cofinal signs, not pointwise positivity or RH.

Prior deep search `theta reciprocal cumulant Borel Volterra convolution positive kernel` returned partial retrieval at cached generation 1143614, mostly pending/stale compiler metadata. Relevant hits include `PrimeArchThetaAllOrderCumulant`'s directly inspected exact recurrence, existing `ThetaRenewalLogKernel` renewal laws, generic Volterra theory and LI reciprocal coefficient-sign no-go. No absence or ready producer claim follows. Positive-mass survivor is now exactly formalized. Arithmetic pointwise-sign burden remains open.

## Log

- 2026-09-29 — Candidate recorded before hard proof work. Exact current and fixed-order positive limit read; joint growing-order limit remains conjectural.
- 2026-09-29 — Narrow lexical reciprocal/sinc search recovered five unrelated prime/Gamma hits and no exact candidate; semantic coverage is unmeasured. Primary DLMF audit confirms classical endpoint overlap. A potentially stronger uniform positive-prefix survivor was conjectured from the actual transfer polynomial and source gap; coefficient audit pending.
- 2026-09-29 — Independent complete-source audit closed constant-25 positivity, with exact positive margin. Moved this survivor's paper theorem to its own stage-two card and assigned Lean implementation. Joint entire scaling limit remains pending; arithmetic control beyond bounded clocks remains open.
- 2026-09-30 — Uniform positive window and complete-source clock limit are final and stage-three. Two audits closed the exact Volterra law and divergent positive-mass survivor on paper; disjoint formal implementation started. Calibrated all-clock source sign remains open.

- 2026-09-30 — Complete Volterra, positive-mass and stronger cofinal unbounded response-height survivors are final. Exact dark-divisor packets retain every strict prescribed polynomial floor on one common interval; actual critical strip/Euler membership remains absent. Continued prime–Gamma germ reconstructs all clock coefficients, but convergent prime-source identity stops before central circle; [central contour transport](../3-formalized/li-clock-central-prime-gamma-contour.md) is exactly formalized with both source formulas and one radius for every real clock. Paired eta central source and quantitative clock approximation are independently paper-audited; signed orientation remains open.
