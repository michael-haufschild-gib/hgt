# Actual LI even Euler jets oscillate cofinally

- **ID:** LI-EJ-OSC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route LI; exact Cassini Euler response, completed-Abel initial current, squared-node gap and Vivanti–Pringsheim corpus theorems.
- **Statement:** At every squared mass `v>0`, the even shifted Euler derivatives of the actual zeroth LI adjacent current take both signs cofinally. On `0<v≤1/4`, the even logarithmic-mass germ retains two disjoint cubic-pole lattices encoding the exact source multiplicities; at every positive mass, sufficiently large nodes retain cubic poles.

## Goal and exact significance

The source current tower is already a two-scale transform of one Cassini Euler response. Its universal transfer polynomials have nonnegative coefficients in the squared shifted Euler operator. One possible source producer would make every constituent even Euler jet nonnegative. This theorem excludes that stronger producer on the actual infinite source, without any RH or off-line-zero premise. Any successful use of the transfer polynomials must retain cancellation between jets of opposite signs.

This is not an RH proof or falsification. Generic Pringsheim, logarithmic-residue calculus, finite-packet inertia and Mittag–Leffler transfer polynomials are existing knowledge, not novelty claims. Proposed new content is the actual-source cofinal oscillation and the exact noncancelling pole lattices underlying it. Worldwide novelty remains unverified pending bounded corpus and primary-source audits.

## Precise objects

Let `C(u)=xiSquaredSeamCassiniSource u`, `L=C′/C`, and use the meromorphic continuations

`D(z)=2z[zL′(1−z)−L(1−z)]`,

`Γ(z)=2zD′(z)=−4z³L″(1−z)+12z²L′(1−z)−4zL(1−z)`.

For `v>0`, define

`R_v(t)=Γ(v exp t)+Γ(v exp(−t))`.

On the positive real mass axis the existing shifted-moment bridge gives

`Γ(v)=v C₀(v)`,

where `C₀(v)=liEvenCrossSquareMassAdjacentCurrent v 0`. Put

`g(x)=exp(x) C₀(exp(x))`.

Then `R_v(t)=g(log v+t)+g(log v−t)` for real `t`. In particular odd Taylor coefficients vanish, while

`[t^(2k)] R_v(t)=2g^(2k)(log v)/(2k)!`.

The closed sign statement is: for every `v>0` and every natural `K`, there are `k₋,k₊≥K` with

`g^(2k₋)(log v)<0<g^(2k₊)(log v)`.

Equivalently, `(E+1)^(2k) C₀(v)` takes both signs cofinally, where `E=v∂v`.

## Dependency-closed paper proof [PROVED HERE]

1. **Genuine pole and exact multiplicity.** An actual Xi squared node `b=α²` is nonzero, and `C` has a zero of exact positive multiplicity `m` at `1+b`. Locally,

   `L(u)=m/(u−1−b)+analytic`.

   Substituting into the exact Euler expression gives

   `D(z)=−2mb²/(z+b)²+2mb/(z+b)+analytic`,

   hence `Γ(z)` has cubic leading coefficient `−8mb³` at `z=−b`.

2. **Logarithmic pullback.** Choose `t₀` with `v exp t₀=−b`. The map `t↦v exp t` has derivative `−b≠0` there. Therefore `Γ(v exp t)` has a genuine cubic pole at `t₀` with coefficient

   `(−8mb³)/(−b)³=8m`.

   The same holds on every translated point `t₀+2πiℓ`, `ℓ∈ℤ`.

3. **No reflection cancellation.** At the same `t₀`, the reflected mass is `−v²/b`. The unconditional corpus bound `‖b⁻¹‖<1/150` gives `‖b‖>150`. For `v≤1/4`, reflected mass has norm `<1/2400`, whereas every actual squared Xi node has norm `>150`. Thus the reflected branch is analytic at `t₀` and cannot cancel the cubic pole. More generally direct and reflected pole lattices cannot meet: an intersection would give `b₁b₂=v²`, contradicting their norms. Reflected poles have cubic coefficient `−8m`.

4. **Every positive mass has a retained pole.** At arbitrary mass, individual poles can cancel when reciprocal multiplicities balance. Hardy nevertheless supplies positive real Xi zeros `t` beyond every bound, hence actual squared nodes `b=t²` with `|b|>v²`. At the direct logarithmic pole the reflected mass has norm `v²/|b|<1`. The unconditional squared-node lower bound `|b'|>81/4` for every actual node excludes a reflected source zero there. The direct order `−3` survives. No simplicity or RH hypothesis enters; universal survival of individual nodes at arbitrary mass is not claimed.

5. **Entire real-axis continuation and finite Taylor radius.** On every real `t`, both masses are positive. The Cassini source is nonzero at their corresponding centers, so `R_v` is analytic near every real point and real-valued on the real axis. It is meromorphic globally and analytic at `0`. Its Taylor radius is positive and finite: an infinite radius would produce an entire analytic function agreeing with the actual meromorphic source near `0`, hence throughout the connected complex plane by meromorphic uniqueness, contradicting the retained cubic pole.

6. **Both signs cofinally.** Suppose Taylor coefficients were eventually nonnegative. Subtract the finite initial Taylor polynomial. The resulting real-coefficient series has the same finite positive radius and is nonnegative coefficientwise. Vivanti–Pringsheim forces a singularity at the positive real boundary of that radius. The actual meromorphic continuation is analytic there; germ uniqueness along the real segment identifies it with the disk sum and contradicts Pringsheim. Eventual nonpositive coefficients are excluded by negating before removing the finite prefix. Hence both signs occur cofinally. Evenness leaves only even coefficients, giving the asserted derivative signs.

No estimates on unknown zero locations, numerical evidence or presumed current positivity enter this proof.

## No-go closure and positive survivor

- **Exact failed mechanism:** source orientation through all nonnegative even shifted Euler jets, including eventual one-sign variants, is impossible on the actual source at every positive mass.
- **Strongest positive survivor:** evenization preserves two disjoint multiplicity-faithful periodic cubic-pole lattices; the signed cubic coefficient is `±8m`. Actual divisor information is retained through a nonlocal logarithmic germ even while the constituent even jets oscillate.
- **New insight:** coefficientwise-positive transfer operators do not reduce LI to coefficientwise-positive input jets. Actual all-mode current orientation must use structured cancellation, with genuine cubic source poles still present.
- **Status:** complete paper proof and exact Lean capstone `RHTower.liEvenCrossRealLogMassFirstCurrent_even_deriv_cofinal_both_signs`, for every `LiEvenCrossPositiveMass`. Route LI remains open; only the stronger differential cone is excluded.

## Corpus and novelty audit

- Existing exact source bridge: `LiEvenCrossCassiniRadialEulerBridge.lean:39`.
- Existing current definition and polynomial flux: `LiEvenCrossCompletedAbelInteriorFirstZero.lean:57,118`.
- Exact multiplicity and zero exhaustion: `XiSquaredSeamCassiniSource.lean:174,209`.
- Squared-node gap: `XiReciprocalSquareSecondMomentRadius.lean:30,53`.
- Existing Pringsheim theorem: `HTGeometry/VivantiPringsheim.lean:321`.
- Real-segment continuation: `HTGeometry/SegmentAnalyticContinuation.lean:86`.
- Meromorphic germ uniqueness: `SuzukiCarlemanJumpEulerDefectWeld.lean:103`.
- Narrow LI source/text searches found finite-packet sign oscillation, but no actual-source even Euler-jet oscillation theorem. Index results are partial/source-only and do not replace exact source inspection.
- Bounded primary audit found no exact matching source theorem. Closest checked sources are [Zhang, *Complete Monotonicity of Special Functions*, §3.4](https://arxiv.org/pdf/1506.07012), [Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, §§8–9](https://arxiv.org/pdf/2206.03682), and [*Uniform Beta Smoothing of Widder Sums…*, Appendix C (September 2026)](https://www.preprints.org/manuscript/202609.1018). These contain related ordinary derivative or Li/moment hierarchies, not the claimed cofinal logarithmic Euler-jet fluctuation. Generic Pringsheim/pole calculus remains classical. This audit does not certify universal absence from public literature or model training data.

## Formalization and validation

Verified leaves:

- `LiEvenCrossCassiniLogMassPole.lean`: exact complex source continuation, real-axis analyticity, evenness and retained cubic pole.
- `LiEvenCrossCassiniAllMassPole.lean`: Hardy source nodes beyond every scale and retained cubic pole at every positive mass.
- `LiEvenCrossEulerJetOscillation.lean`: canonical Taylor radius and cofinal both-sign coefficients.
- `LiEvenCrossEulerCurrentBridge.lean`: exact moment normalization, actual first-current identification and cofinal Euler-jet signs.
- `LiEvenCrossRealEulerJetBridge.lean`: all-order real/complex derivative identification and literal real-current capstone.

All five leaves are wired into `RHTower.lean`. Targeted foreground `lake build --old <named leaves>` checks passed. Final exact `lake env lean <leaf>` audits passed for every leaf, without warnings. Scratch-only `#print axioms` audits of source poles, lattice coefficients, canonical/current oscillation and real-current capstones report only `propext`, `Classical.choice`, `Quot.sound`; no added source axiom or RH premise. No heartbeat override or numerical experiment used. Generated indexes regenerated.

Both `scripts/formal_tools.py lint` and `lint --check-generated` ran. Whole-tree lint remains red on unrelated unwired modules; the latter also reports generated gap/overview files becoming stale during concurrent work. No local leaf appears in the errors. This is a targeted theorem certificate, not a green whole-tree gate or an RH solution. No full umbrella build run.

## Log

- 2026-09-29 — All-positive-mass extension and real derivative interface proved and audited; all five leaves wired. Exact final source checks and foundation-only axiom audits passed. Promoted to stage 3 with unrelated whole-tree lint failures explicitly retained.

- 2026-09-29 — Conjectured from actual source formulas after rejecting scalar sign, generic finite inertia and classical Euler-clock recurrences as new contributions.
- 2026-09-29 — Dependency-closed paper proof found; strengthened mere cone failure to cofinal both-sign oscillation and multiplicity-faithful periodic pole-lattice survivor.
- 2026-09-29 — Started Lean formalization with disjoint local-pole and global-Pringsheim modules. Goal remains active; RH remains open.
- 2026-09-29 — Bounded primary audit found no exact collision for the combined actual-source cofinal-sign and disjoint-pole-lattice result; novelty remains unverified.
