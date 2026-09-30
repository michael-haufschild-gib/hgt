# Actual LI current: complete-source entire clock limit

- **ID:** LI-CURRENT-CLOCK
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, real-clock limit); independent audit passed; no novelty claim
- **Parent:** `../1-in-progress/li-actual-current-small-mass-sinc-scaling.md`
- **Objective:** identify the complete-source growing-order limit with an entire reciprocal-moment transform, retaining multiplicity and every source atom.

## Exact statement

Let `M_j=normalizedPrimeArchMoment j` and define

`S(w)=Σ_(j≥0)(−1)^j(16w)^j M_j/(2j+1)!`.

This series converges absolutely for every real `w`. For any filter, real mass path `v→0+` and natural mode path `n`, if `(n+1)²v→w`, then

`liEvenCrossSquareMassAdjacentCurrent v n/[2(n+1)²] → S(w)`.

No separate `n→∞` hypothesis is required. At nonzero clock it follows from the two path limits; at zero clock the theorem includes bounded modes. In the original notation `(n+1)√v→u≥0`, it gives `S(u²)=Σ(−1)^j(4u)^(2j)M_j/(2j+1)!`. No complex square-root branch is used.

The constant-25 uniform window implies `S(w)≥(787/6552)A` for `0≤w≤25`, where `A=xiShiftAbsoluteMass 0`. At the boundary `w=25`, choose the exact paths `v=w/(n+1)²` rather than assuming an arbitrary convergent clock stays below 25. At `w=0`, `S(0)=M_0` directly. Independent audit also closed the sharper direct-series margin `S(w)≥(1051/2184)A>0` on the same window: no finite-mass prefactor error remains in the limit. These are local clock statements, not signs at every clock or an RH theorem.

## Dependency-closed paper proof

1. The audited normalized endpoint polynomial has exact coefficients
   `a_j(n)=(−1)^j4^j∏_(i=1)^j[4(n+1)²−i²]/(2j+1)!`.
   The formula is valid for all natural `j`, since the product vanishes as soon as `j≥2(n+1)`. Before that index each factor is nonnegative and at most `4(n+1)²`. Hence `|a_j(n)|≤[16(n+1)²]^j/(2j+1)!`.
2. Exact normalized source atoms expand as
   `λ/(1+vλ)² Σ_j a_j(n)[vλ/(1+vλ)]^j`,
   where the sum is finite and actual `Re λ>0`, `|λ|<1/150`. Consequently normalized complete current is
   `Σ_j a_j(n)v^j T_j(v)`,
   `T_j(v)=Re Σ_q λ_q^(j+1)/(1+vλ_q)^(j+2)`.
   For each fixed `n`, finite polynomial expansion and absolute reciprocal summability justify this equality; no differentiation of growing-order expressions occurs.
   Its equivalent finite moment-functional identity uses `T_j(v)=Re[xiShiftedReciprocalMoment v j−v xiShiftedReciprocalMoment v (j+1)]` and holds algebraically for every real `v`: the current is defined by the scaled unit-flux polynomial, and `2(n+1)²` never vanishes. Root audited this stronger totalized identity before implementation. Complete-node estimates and boundary limits still use nonnegative/positive mass.
3. For `v>0`, `|1+vλ_q|≥1`, so the entire source satisfies `|T_j(v)|≤A/150^j`. For each fixed `j`, the individual denominators tend to one as `v→0+`, and their absolute majorant is `|λ_q|/150^j`. Dominated convergence over every multiplicity copy gives `T_j(v)→M_j`.
4. For fixed `j`, rewrite `a_j(n)v^j` as
   `(−1)^j4^j∏_(i=1)^j[4(n+1)²v−i²v]/(2j+1)!`.
   The two assumed path limits make this tend to `(−1)^j(16w)^j/(2j+1)!`, even when modes remain bounded at zero clock.
5. A convergent real clock is eventually bounded above by a positive constant `R`. For these positive masses, every summand is bounded by `A(16R/150)^j/(2j+1)!`. This sequence is summable, being a factorial subsequence of an exponential series. Dominated convergence for the natural-index sum gives the displayed limit. The same factorial envelope with `R=|w|` proves absolute convergence of `S` at every real clock.
6. For any fixed `0<w≤25`, take natural `n→∞` and `v=w/(n+1)²`. Exact clock equals `w`, positive masses tend to zero, and every path value lies in the audited window. Closedness of the inequality passes its fixed positive margin to `S(w)`. At zero clock use the existing sector lower bound for `M_0`.
7. Direct series estimate gives `|S(w)−M_0|≤A Σ_(j≥1)ρ^j/(2j+1)!`, `ρ=16|w|/150`. For `0≤w≤25`, `ρ≤8/3`; successive tail ratios are at most `ρ/20≤2/15`, starting with `ρ/6`. Thus the tail is at most `20/39`, and the source sector lower bound yields `S(w)≥(167/168−20/39)A=(1051/2184)A`. This stronger survivor was separately paper-audited before assignment to Lean.

## Prior research and significance

- Classical endpoint sine/Bessel mechanism is documented in [DLMF 18.5.2](https://dlmf.nist.gov/18.5#E2) and [18.11(ii)](https://dlmf.nist.gov/18.11#ii). The complete-source interchange is the additional burden here; no global novelty claim.
- Direct source inspection of `LiEvenCrossAllModeLaguerreClock.lean` and its formalized card found an exact Fourier/Laguerre clock at fixed critical mass, not this complete small-mass entire limit. `XiShiftedHardEdgeMehlerHeine.lean` supplies a real-node atom phase limit; source-faithful domination over complex nodes remains necessary.
- Cached deep search `reciprocal zero sine entire Borel theta convolution bounded inverse spectrum`, generation 1143344, returned `partial=false` and complete inventory but predominantly pending/stale compiler coverage. Candidate lemmas and source arguments inspected; none supplies this exact limit. No absence or fresh-build claim follows.
- `S≥0` at every clock, boundedness at every clock, and a source-pure arithmetic producer remain unproved. Generic positive real-node packets can have negative sine sums. A negative actual `S(w)` would defeat the stronger all-interior-current zero-exclusion producer, not by itself falsify RH.

## Formal closure and scope

1. Independent hostile audit of coefficient scaling, complete-source domination, arbitrary-filter quantifiers and endpoint margin transfer passed. Both denominator powers and zero-clock bounded modes were checked.
2. Reused exact endpoint coefficients from `LiEvenCrossActualCurrentEndpointCoefficients.lean`; no duplicate Chebyshev infrastructure.
3. `LiEvenCrossActualCurrentClockSource.lean`, `LiEvenCrossActualCurrentClockSeries.lean` and `LiEvenCrossActualCurrentClockLimit.lean` close the actual weighted source tower, real-clock absolute convergence/error/positive margin and literal arbitrary-filter current limit. All named `--old` builds, final exact source checks and foundation-only scratch capstone axiom audits passed. The main theorem is `tendsto_liEvenCrossSquareMassAdjacentCurrent_clock` at line 197; no separate mode growth or filter nontriviality premise.
4. Root spot-checked exact source moment bounds, real-series definition/margin and actual-current limit/DCT quantifiers, and read the source and limit axiom logs. All leaves wired. Complex holomorphy is a paper consequence, explicitly outside this real-clock formal capstone. No all-clock sign or RH producer is claimed.

## Log

- 2026-09-29 — Complete-source paper proof recorded before hard implementation. Fixed clock replaces redundant separate growing-order premise. Independent audit and Lean remain pending.
- 2026-09-29 — Independent audit passed and supplied the sharper direct-series positive margin `1051/2184`. Source-only entire series/positive clock window assigned to a separate leaf; root will formalize the weighted shifted source tower, then reuse the endpoint coefficient leaf for the actual-current limit.
- 2026-09-29 — `LiEvenCrossActualCurrentClockSeries.lean` passed named build, all ten foundation-only axiom audits and final exact check with no diagnostics. Real-clock absolute convergence, exact zero, error envelope and stronger positive margin are closed; complex holomorphy remains paper-only. Root `LiEvenCrossActualCurrentClockSource.lean` also passed named build (52 seconds), eight foundation-only capstone axiom audits and final exact direct check with empty output. It retains every shifted source denominator, proves literal consecutive-moment difference, sharp all-degree bound and fixed-degree boundary limit. Both leaves wired; main actual-current limit remains in implementation, so card stays paper stage.
- 2026-09-29 — `LiEvenCrossActualCurrentClockLimit.lean` closes all-real-mass finite coefficient/source-tsum expansion, fixed-degree scaled coefficient limit, uniform complete-source factorial envelope and arbitrary-filter actual-current capstone. Named build passed (12565 jobs, leaf 11 seconds); final exact leaf check exited zero with empty output. All eight exported theorem axiom audits returned only standard foundations. Evidence in `/tmp/hgt-li-current-clock-limit.ZqGFPV/{build,direct,axioms}.log`. Shared endpoint coefficient leaf also passed its final direct and axiom audits. Promoted only after every real-clock capstone and dependency was final-audited; RH remains open.
