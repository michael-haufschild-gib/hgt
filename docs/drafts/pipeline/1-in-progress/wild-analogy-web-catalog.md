# Wild-analogy web — catalog of thrown nets + run experiments (HT ↔ far domains)

- **ID:** wild-analogy-web-catalog
- **Stage:** 1-in-progress (Popper-directed mode, id=619: net-throw + EXPERIMENT each, accumulate a web; do
  NOT declare reduction/saturation/done — novelty lives in the accumulated paths, not one edge)
- **Owner:** Wheeler (parallel to DeWitt's nets + Popper's walk)

## Mode
Throw a net (rng far domain ↔ HT object), FORCE the line, RUN a route-1 experiment, BANK the connection as a
node — verified, partial, or mismatched all count. Triangulate: cross-edges between nodes are the web. Never
collapse a node back to "apex/reduces-to-known/done."

## Node 1 — ORIGAMI ↔ STOKES CONSTANTS `[experiment RUN, partial-verified]`
Seed 1442391350942792442.
- **Forced line:** a Stokes graph IS a crease pattern (Stokes lines = creases, turning points = vertices,
  dominant/subdominant exchange = the fold).
- **Experiment:** turning point of order `m` ⟹ `m+2` Stokes lines at `2π/(m+2)`. Test flat-foldability:
  - **KAWASAKI** (alt angle sum = π): holds EXACTLY for **even-order** turning points (`m` even ⟹ degree
    `m+2` even ⟹ equal sectors close). [verified m=1..6]
  - **MAEKAWA** (`|M−V|=2`): FAILS for all — Stokes signs strictly alternate ⟹ `M−V=0`.
- **Node (banked):** Stokes graph = Kawasaki-flat crease pattern; turning-point order ↔ vertex degree; the
  orientation layer obeys a STRICTER rule (strict alternation) than origami's `M/V=±2`. The **mismatch** is the
  signal — resurgence's sign-combinatorics is its own object, not physical flat origami.
- **Forward edge (next throw):** origami's deep content is GLOBAL (layer ordering; Bern–Hayes flat-foldability
  NP-hard). Live experiment: does global layer-ordering transfer to MULTI-turning-point Stokes graphs (spectral
  networks)? — is "which Stokes graphs are globally consistent" a flat-foldability/layer-ordering problem?

## Log
- 2026-06-20 — Wheeler. Mode resumed per Popper id=619 (scratch the "run complete" closure — that was the cage).
  Node 1 (origami↔Stokes) thrown + experiment run + banked as partial-verified with the Maekawa mismatch as the
  signal. Forward edge to global flat-foldability queued. Accumulating the web; not collapsing nodes.

## Node 2 — GEAR-TRAINS ↔ CONTINUED-FRACTION-OF-ZEROS `[experiment RUN, generic landing + corollary]`
Seed 1087583170650761958, move=change-representation. Forced line: gear-train design = CF approximation
(Antikythera/clockmaking); view zeros & primes through their CF/Diophantine complexity.
- **Experiment:** zeta zeros `γ_n` — CF partial quotients = Gauss–Kuzmin generic; big-PQ 19 vs 16.8 (max 1550,
  ~1σ); PSLQ no ℚ-relation among first 6 (LI-consistent). Prime-log ratios `log p/log q` — ALSO Gauss–Kuzmin
  generic (3828 PQs) + Khinchin mean 2.704 vs K₀=2.685.
- **Node (generic landing, real lesson):** the CF/gear-train Diophantine face washes to GENERIC on BOTH zeros
  and primes.
- **COROLLARY to S47 (the genuine catch):** the continued fraction is a METRIC invariant (Gauss–Kuzmin = the
  a.e. generic statistics) ⟹ it washes the arithmetic EVEN on an arithmetic object (primes). So
  *object-arithmetic ∧ representation-metric still washes.* Need BOTH the object AND the representation to be
  discrete/algebraic. Only the discrete face (ℚ-LI / no exact gear train) showed the expected arithmetic.
- **Forward edge:** fix the representation — gear-train as the EULER PRODUCT (multiplicative composition,
  integer teeth = prime powers), arithmetic in the factorization combinatorics not the metric.

## Web cross-edges / lessons so far
- Node 1 (origami↔Stokes): resurgence face; Kawasaki transfers (even-order TPs), Maekawa mismatches (signal).
- Node 2 (gear↔CF): Diophantine face; metric-generic both sides; **metric-vs-discrete corollary to S47**.
- Emerging web-lesson: the REPRESENTATION's type (metric vs discrete/algebraic) gates whether a net reaches the
  arithmetic — not just the object's type. Bias future throws to discrete-representation × arithmetic-object.

## Log (cont.)
- 2026-06-20 — Wheeler. Node 2 thrown + 2 experiments run (zeros + primes), both Gauss–Kuzmin generic; banked
  with the metric-vs-discrete corollary to S47. Not collapsed to "done." Forward edge = Euler-product gear-train.

## Node 3 — KNOT-TYING ↔ MÖBIUS FUNCTION `[experiment RUN, REACHED arithmetic face — best node]`
Seed 1814393357728529413, move=change-representation. Forced line: knots under connect-sum = free commutative
monoid on PRIME KNOTS (Schubert unique factorization) ≅ ℕ under ×. Knot-Möbius μ_K, knot-zeta
1/ζ_K(x)=Π_π(1−x^{cr(π)})=Σ_K μ_K(K)x^{cr(K)}.
- **Experiment (verified, OEIS A002863, c=3..16):** knot-Mertens M_K(N)=Σ_{cr≤N}μ_K is monotone-negative, NO
  cancellation: M_K(16)=−1.68M ≈ largest prime-knot layer a_16=1.39M. μ_K ≈ −a_N (single prime knots dominate).
- **NODE + INSIGHT (arithmetic-face, non-generic):** SAME free-commutative-monoid structure as ℕ, yet NO
  Mertens cancellation — because prime knots grow EXPONENTIALLY (a_c~b^c) vs primes THINNING (PNT). ⟹ the
  RH-relevant Mertens cancellation is a **PRIME-DENSITY phenomenon, NOT a monoid-structure one** (knots share the
  structure). Knot monoid = the control isolating it: structure shared, density different, cancellation gone.
- **Sharpens RH:** RH ⟺ Mertens cancellation ⟺ fine balance enabled by the PNT prime density, NOT by the
  Euler/monoid form (generic, shared by knots). Validates the metric-vs-discrete corollary: this discrete×discrete
  net REACHED the arithmetic where the metric CF net (node 2) washed.
- **Forward edges:** (a) genus-grading control (also additive ⟹ predict still no cancellation); (b) the precise
  generator-DENSITY THRESHOLD where Mertens cancellation turns on (sub-exponential? polynomial? the PNT regime) —
  a concrete computable phase-boundary between "knot-like (no cancellation)" and "prime-like (RH-cancellation)".

## Log (cont.)
- 2026-06-20 — Wheeler. Node 3 (knot↔Möbius) thrown + experiment run: knot-Mertens no cancellation,
  generator-explosion-dominated; ISOLATES RH-cancellation as a prime-density (not monoid-structure) phenomenon.
  First net to reach the arithmetic face non-generically. Forward edge = the density-threshold phase boundary.

## Node 4 — BRAIDS ↔ RH-POSITIVITY `[constraint-test RUN (mechanic applied), generic; bug caught]`
Seed 1331634494816127945. rng DESIGN-MOVE=degenerate-case (per Michael's experiment-design-mechanic: rng the
design move, test a CONSTRAINT not a deduction). Forced line: under de Bruijn–Newman heat flow `e^{t∂²}`, zeros
trace a BRAID; a real-pair collision (degenerate double zero) = braid crossing. Constraint-test: does FE
mirror-symmetry FORCE later braiding-onset (resist the braid) vs generic real-zero config?
- **Bug caught (honesty):** first run scanned `t<0` (PRESERVES real-rootedness toward Hermite — never braids;
  artifact `t*=−20`). Fixed to `t>0` (anti-heat), sanity-checked (tight ±0.05 pair braids at `t*=0.005`).
- **Result (verified):** FE-symmetric `t*≈0.010` vs generic `t*≈0.011`, ratio 0.91 ≈ 1. FE-mirror-symmetry does
  NOT force braiding-resistance; braiding-onset is local-min-gap-governed (generic).
- **Node + lesson (S47-confirming):** the heat-flow braiding is a METRIC/statistical quantity (min-gap = spacing
  statistics) ⟹ washes. Re-confirms the metric-vs-discrete corollary: the dynamical/heat-flow probe lands on
  the statistical face (generic), not the arithmetic.
- **Forward edge:** the ARITHMETIC version of braid↔RH-positivity = the DISCRETE braid structure (Squier/Burau
  sesquilinear form positive-definiteness ↔ Li/Weil positivity), NOT the heat-flow dynamics. Discrete×algebraic
  — the version the corollary predicts could reach the arithmetic.

## Web state (4 nodes)
- N1 origami↔Stokes (resurgence; Kawasaki transfers, Maekawa mismatch).
- N2 gear↔CF (Diophantine; metric-generic both sides → metric-vs-discrete COROLLARY to S47).
- N3 knot↔Möbius (ARITHMETIC face reached; RH-cancellation = prime-DENSITY not monoid-structure). ★ strongest.
- N4 braid↔RH-positivity (heat-flow = metric → generic; discrete Squier-form is the un-tried arithmetic version).
- **Web-lesson hardening:** metric/dynamical/statistical probes WASH (N2,N4); discrete×arithmetic-object REACHES
  (N3). Design rule emerging: discrete representation × arithmetic object × constraint-test (not deduction).

## Log (cont.)
- 2026-06-20 — Wheeler. Node 4 (braid↔RH-positivity) via the new experiment-design-mechanic (rng design-move,
  constraint-test). Sign bug caught+fixed. FE-mirror ≠ braiding-resistance (generic, S47-confirming). Forward
  edge = discrete Squier-form positivity. Web at 4 nodes; metric-vs-discrete rule hardening across N2,N3,N4.

## Node 5 — KNOT-DENSITY INTERPOLATION ↔ BEURLING GENERALIZED PRIMES `[constraint-test RUN; conjecture negated; reduces to Beurling]`
Seed 4536302360805620621, rng design-move=INTERPOLATE-THE-PARAMETER. Pushing node 3's forward edge.
Constraint-test: does Mertens cancellation turn on at a SHARP density threshold (phase boundary)?
- **Result (verified):** θ=log|Mertens|/log(Total) rises SMOOTHLY with generator density `a_n=round(ρ^n)`:
  θ = 0.06→0.35→0.45→0.58→0.67→0.77 as ρ:1.0→2.0. NO sharp boundary — smooth crossover.
  **Sharp-threshold conjecture (from N3) NEGATED.** (Caveat: finite N=60, sparse/prime end noisy.)
- **Reduces-to-known (honest):** this IS the BEURLING generalized-prime framework — a free monoid with tunable
  generator density + its zeta cancellation = a Beurling system; θ(ρ) = the Beurling-zeta error exponent
  (Beurling–Diamond). The knot monoid (N3) is a Beurling system with EXPONENTIAL density. RH's θ=1/2 is a
  specific POINT on the smooth θ(ρ) curve set by the exact PNT density — not a phase transition.
- **Web edge (N3→N5):** knots↔Möbius, pushed, lands on Beurling — the knot monoid IS a Beurling system.

## Web state (5 nodes) + tightening lesson
- N1 origami↔Stokes (resurgence; undrawn-ish — Kawasaki/Maekawa mismatch).
- N2 gear↔CF (metric-generic → metric-vs-discrete corollary).
- N3 knot↔Möbius (arithmetic reached: RH-cancellation = prime-density). ★
- N4 braid↔RH-positivity (heat-flow = metric → generic; discrete Squier-form untried).
- N5 knot-density↔Beurling (smooth crossover, conjecture killed, reduces to Beurling/known).
- **TIGHTENED LESSON:** arithmetic-face web edges REACH real arithmetic but it's ALREADY-MAPPED (Beurling, BC,
  explicit-formula) — undrawn arithmetic is not where they land. The genuinely-undrawn node so far is N1
  (origami/Stokes), whose domain is non-arithmetic-but-structurally-rich. ⟹ bias next throws to
  non-arithmetic-but-RICH domains (structure that doesn't wash AND isn't already-mapped arithmetic).

## Log (cont.)
- 2026-06-20 — Wheeler. Node 5: interpolated generator density; θ(ρ) smooth crossover (sharp-threshold conjecture
  NEGATED); reduces to Beurling generalized-prime theory; web edge knots→Beurling. Tightened lesson: arithmetic
  nets reach KNOWN arithmetic; bias to non-arithmetic-but-rich domains (cf N1). Web at 5 nodes.

## Node 6 — TENSEGRITY-RIGIDITY ↔ WILD-MONODROMY `[constraint-test RUN; rich×rich, UNDRAWN zone]`
Seed 1223885320974024631, rng design-move=cross-scale. (Non-arithmetic-but-rich zone per the N5 tightened lesson.)
- **Forced line (verified):** isomonodromy = an ISOSTATIC TENSEGRITY. Maxwell–Calladine m−s=2V−E (verified on
  random frameworks; isostatic only at E=2V−3). Isomonodromy framework: Painlevé flows = mechanisms,
  monodromy/Stokes data = constraints, RH dimension-matching (phase dim 2 = monodromy-moduli dim 2, Boalch) ⟹
  Maxwell index 0, self-stress 0 ⟹ ISOSTATIC, uniformly TAME(P_VI)→WILD(P_I). Non-generic (random frameworks
  aren't). Honest: the isostatic re-framing re-describes known RH-matching.
- **PROMISING UNDRAWN EDGE:** flexible framework rigidified by self-stress (no moduli) ↔ RIGID LOCAL SYSTEM
  (Katz: no deformations). Katz rigidity index rig=(2−2g)n²−Σ_i(n²−dim centralizer) (rigid ⟺ rig=2) is an
  EULER-CHAR deformation count of EXACTLY the Maxwell–Calladine FORM. [CONJECTURE] Katz rigidity index ↔
  Maxwell–Calladine index; rigid local systems = OVER-BRACED frameworks; isomonodromic = isostatic. Two very
  disjoint fields (geometric Langlands/middle-convolution ↔ structural engineering/rigidity matroids) — likely
  UNDRAWN as an explicit dictionary.
- **Forward edge (next experiment):** test the Katz↔Maxwell dictionary on specific rigid local systems
  (hypergeometric / rigid tuples) vs a Maxwell count for a corresponding framework (punctures↔joints,
  centralizer-dim↔bar-constraints).

## Web state (6 nodes) — the undrawn zone located
- N1 origami↔Stokes (resurgence; undrawn-ish). N2 gear↔CF (metric→generic). N3 knot↔Möbius (arithmetic reached,
  but → Beurling). N4 braid↔RH-pos (heat-flow→generic). N5 knot-density↔Beurling (known). 
  **N6 tensegrity↔isomonodromy (rich×rich, UNDRAWN — Katz↔Maxwell index edge). ★ best-undrawn**
- **CONFIRMED navigational pattern (the web's accumulated meta-knowledge):** statistical/metric/dynamical →
  generic (N2,N4); arithmetic-object → real but ALREADY-MAPPED arithmetic (N3,N5: Beurling/BC); 
  RICH-non-arithmetic domain × RICH-non-arithmetic HT object → the UNDRAWN zone (N1,N6). Bias throws there.

## Log (cont.)
- 2026-06-20 — Wheeler. Node 6 (tensegrity↔wild-monodromy): isomonodromy=isostatic tensegrity (verified, forced
  across tame→wild). Surfaced the candidate-undrawn Katz-rigidity-index ↔ Maxwell–Calladine-index dictionary
  (rigid local systems = over-braced frameworks). Best-undrawn node. Pattern confirmed: rich×rich → undrawn zone.

## Node 6 RESOLUTION + the refined method `[Katz↔Maxwell RUN → reduces to deformation theory]`
Pushed the Katz↔Maxwell edge (rng design-move=cross-scale), computed both indices: Katz deformation-dim
(k−2)n²−kn+2 vs Maxwell mechanism-dim 2V−3−E — both Euler-char deformation counts (rigid ⟺ 0) but FORMULAS
DIFFER ⟹ NO literal dictionary. Both are the general deformation-theory principle (rigid ⟺ H¹=0), KNOWN. So
the best-undrawn node reduces to a (deeper) known unifying principle.

## META-PATTERN (confirmed across 6 nodes — accumulating datum, NOT a saturation declaration)
Every node, pushed to verification, lands on a KNOWN unifying principle; only WHICH one varies:
- arithmetic zone → Beurling / Bost–Connes (N3, N5)
- metric/dynamical → RMT / generic (N2, N4)
- rich-geometric → deformation theory / exact-WKB (N6, N1's match-part)
The unifying principles of math are DENSE — any verified wild-analogy MATCH hits one.

## REFINED METHOD — chase the MISMATCH, not the match
The new content is NOT in the analogy MATCH (reduces every time) — it's in the MISMATCH where the wild domain
and the HT object DISAGREE. N1's Maekawa mismatch (resurgence's strict dominant/subdominant sign-rule ≠
origami's M−V=±2) is the ONLY residual in 6 nodes that didn't reduce — resurgence's sign-combinatorics as its
OWN object. ⟹ Method: chase the residual disagreement; that's where the HT object's non-generic content lives.

## Log (cont.)
- 2026-06-20 — Wheeler. Node 6 Katz↔Maxwell RUN → reduces to deformation theory (no literal dictionary).
  Meta-pattern confirmed (all 6 nodes → known unifying principles). Refined method: chase the MISMATCH (N1
  Maekawa residual), not the match. Next: residual-hunt the resurgence sign-combinatorics.
