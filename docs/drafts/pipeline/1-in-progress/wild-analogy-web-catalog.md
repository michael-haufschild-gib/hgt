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

## Cross-edge 1 — N3-BEURLING ↔ N1-RESURGENCE `[triangulation; RUN; verified; mostly drawn]`
Seed 1631767503798513116, rng design-move=null-vs-forced. First cross-edge (connect two nodes' reduced
principles via the shared HT object — Popper's triangulation).
- **Verified:** the explicit formula ψ(x)=x−Σ_ρ x^ρ/ρ−… IS a resurgent TRANS-SERIES in z=log x. Zeros
  ρ=1/2+iγ = BOREL-PLANE SINGULARITIES ("instanton actions"); residues 1/ρ = STOKES CONSTANTS. Reconstruction
  from 40 zeros tracks true ψ(x) (err 0.06→1.06, x=20→100, shrinking with more zeros).
- **Null-vs-forced:** RH ⟺ all Borel singularities ALIGNED on Re(ρ)=1/2 ("resonant" trans-series); null =
  scattered; Euler product FORCES a zero↔prime DUALITY = a resurgence bridge equation (alien derivs at zeros
  ↔ primes).
- **Honest grade:** mostly DRAWN (explicit formula foundational; "zeros as resurgent structure" has precedent).
  Candidate-fresh thread: Euler-product-as-resurgence-bridge + "RH = Borel-alignment". Reduces, BUT connects two
  DISTANT frameworks (analytic-NT/Beurling ↔ Écalle resurgence) via the HT object — the triangulation value.

## META (web at 6 nodes + 1 cross-edge) — the honest interconnection-map finding
Matches reduce (all 6 nodes); mismatches reduce (N1 Maekawa → Stokes-matrix theory); cross-edges largely reduce
too — BUT each connects DISTANT known principles via the shared HT object. The field's unification is dense
enough that every match/mismatch/cross-edge hits known structure. ⟹ The PRODUCT of the web is not one escaped
nugget but the INTERCONNECTION-MAP: how the unifying frameworks of HT (Beurling/BC, RMT, deformation-theory/
exact-WKB, resurgence, periods) connect THROUGH the object. Per Popper "don't declare, keep going" — keep
throwing; cross-edges (triangulation) feel higher-value than fresh nodes now.

## Log (cont.)
- 2026-06-20 — Wheeler. Cross-edge 1 (N3 Beurling ↔ N1 resurgence): explicit formula = resurgent trans-series
  (zeros=Borel singularities, residues=Stokes consts), verified by reconstruction; RH=Borel-alignment;
  Euler-product=resurgence-bridge. Mostly drawn; the triangulation value is connecting distant frameworks.
  Honest meta: the web's product is the interconnection-map. Keep throwing cross-edges.

## Node 7 (DECISIVE) — P-FINITE RESIDUE SPECTRUM, ζ-confound test `[pre-registered, RUN 2-pipeline, verdict: binary+confound]`
Popper's first "non-reducing" measurement (id=648): P-finite residue σ_min/σ_max vs (order w, degree d) gives
HOLONOMIC=abrupt→0-at-true-order / RANDOM=flat-high / HT=gradual. Confound: his HT samples (logΓ,ψ,ψ') are all
ζ-built. DECISIVE TEST (pre-registered, id=650): do NON-ζ HT (Mahler Σx^(2^k), partition Π1/(1−x^k), Thue–Morse
Π(1−x^(2^k))) share it?
- **RESULT (verified, d=1, w=1..7):** holonomic e^x/BesselJ0 → EXACT 0 at true order, stays. ALL HT (ζ and
  non-ζ) → monotone GRADUAL decay, never abrupt. Slopes: ζ-family (logΓ,ψ) ~2.5–3.5 dec/step (steep, parallel
  to each other); lacunary non-ζ (Mahler, Thue–Morse) ~1 dec/step (SHALLOW); partition ~2–3 (intermediate).
- **VERDICT (pre-registration confirmed both axes):** (1) qualitative three-way is GENUINE HT-class, NOT
  ζ-artifact — but = the KNOWN BINARY (HT ⟺ no finite holonomic relation). (2) PARALLEL slopes = ζ-FAMILY
  ARTIFACT (confound confirmed): slope tracks ANALYTIC structure (dense/pole steep, lacunary/natural-boundary
  shallow) = the conformal-geometry confound, NOT an HT-class invariant. logΓ/ψ/ψ' parallel because SAME ζ-object.
- **NOT the first real nugget:** graded signature = (known binary: gradual⟺HT) + (conformal confound: slope =
  analytic sub-class). Honest negative. Script: computations/2026-06-20-wheeler-pfinite-zeta-confound.py
- **Method datum:** even Popper's best non-reducing candidate, decisively tested with a pre-registered prediction
  + non-ζ controls, resolved to binary+confound. The pre-registration + control design WORKED (no theater).

## Log (cont.)
- 2026-06-20 — Wheeler. Node 7: decisive ζ-confound test of the P-finite residue signature. Pre-registered;
  non-ζ HT share gradual decay (genuine HT-class = binary) but NOT the parallel slopes (ζ-artifact = conformal
  confound). Verdict: binary + confound, not a universal HT law. Honest negative, two-pipeline.

## Node 8 — MODULAR-FLOW-GEODESICS ↔ WELD-σ_p `[constraint-test RUN; rich×rich; ON-MISSION; reduces to Furstenberg]`
Seed 2264430926371876805, rng design-move=symmetry-break. Touches the NATIVE weld 𝓜⁺.
- **Forced line (chasing the mismatch):** the weld is NOT a single flow (modular geodesic) — it's a COMMUTING
  FAMILY {σ_p} = a HIGHER-RANK abelian action = the Furstenberg ×p×q setup.
- **Experiment (verified):** lacunary α=Σ2^{-2^k} — single ×2 orbit covers 0.20 of [0,1] (non-rigid, Cantor
  closure); joint ×2×3 covers 1.00 (Furstenberg-RIGID, equidistributes). Generic control: both ≈1. ⟹ the
  multi-prime structure FORCES equidistribution-rigidity a single prime lacks (needs ≥2 coprime primes).
- **NODE (on-mission):** the native weld's {σ_p} IS a higher-rank Furstenberg-RIGID action (Rudolph–Johnson) —
  the DYNAMICAL REALIZATION of "constraint-not-flow": the weld is pinned by the rigidity of the joint
  multi-prime action, no flow-freedom. The multi-prime coupling is exactly what forces the constraint.
- **Honest grade:** math reduces to KNOWN (Furstenberg ×p×q rigidity). BUT most ON-MISSION node — makes the
  native weld PRECISE (Furstenberg-rigid higher-rank action) + gives "constraint-not-flow" a concrete theorem.
  Low novelty (Furstenberg known), genuine SIGNIFICANCE for building 𝓜⁺ (charter's "native object made precise").
  Candidate weld "face" (cf DeWitt's ω-symmorphic face).

## Web state (8 nodes + 1 cross-edge)
- Reduce-to-known zone: N2,N4 (metric→generic), N3,N5,xedge1 (arithmetic→Beurling/BC), N7 (binary+confound).
- Rich×rich / undrawn-framing zone: N1 (Stokes/Kawasaki), N6 (isomonodromy=isostatic→deformation theory),
  **N8 (weld=Furstenberg-rigid, ON-MISSION, charter-advancing). ★ most on-mission**
- Meta-pattern HOLDS (all reduce to known principles); the on-mission VALUE is in nodes that make the NATIVE
  weld precise (N8: rigidity) even when the imported math is known — that's the charter's significance axis.

## Log (cont.)
- 2026-06-20 — Wheeler. Node 8 (weld-σ_p ↔ Furstenberg rigidity): the weld's multi-prime {σ_p} is a
  Furstenberg-rigid higher-rank action = constraint-not-flow realized; needs ≥2 coprime primes. Reduces to known
  Furstenberg rigidity but ON-MISSION (makes the native weld precise). Candidate weld face. Web at 8 nodes+1 edge.

## Node 8 RESOLUTION — weld has a UNIQUE natural state (Rudolph–Johnson → BC KMS)
Pushed N8's on-mission edge: Furstenberg rigidity of {σ_p} ⟹ (Rudolph–Johnson MEASURE rigidity) joint ×p×q
orbits equidistribute to LEBESGUE regardless of start (verified: rel-dev 0.38–0.44 for π−3,e−2,√2−1, →0
asymptotically) ⟹ the native weld 𝓜⁺ has a UNIQUE natural state = Bost–Connes KMS-uniqueness. Reduces to known
(Furstenberg/RJ/BC) but makes the native weld's equilibrium structure precise (charter significance).

## STRATEGIC STATE (8 nodes + 1 cross-edge; meta-pattern robust)
Every node reduces to a known unifying principle. The genuine PRODUCT: (i) interconnection-map of HT's unifying
frameworks; (ii) navigational pattern (statistical→generic, arithmetic→Beurling/BC, rich×rich→deformation/WKB/
rigidity); (iii) ON-MISSION weld-faces that make 𝓜⁺ precise while reducing to known — N8 (weld = Furstenberg-
rigid, unique state) + DeWitt's ω-symmorphic obstruction + BC seam-thermodynamics. Those THREE faces = a coherent
"𝓜⁺ characterized" charter contribution (symmorphic-ω / ζ-thermodynamics / Furstenberg-rigidity).
PROPOSED to Popper (id=656): consolidate the 3 weld-faces into one "𝓜⁺ characterized" charter card —
significance-high (native object made precise), novelty-low (each reduces to known), a real positive artifact.
Awaiting steer: (a) keep throwing, (b) consolidate weld-faces [Wheeler leans], (c) other axis.

## Log (cont.)
- 2026-06-20 — Wheeler. N8 resolution: weld unique natural state (RJ→BC), verified equidistribution-to-Lebesgue.
  Raised strategic state — 3 on-mission weld-faces (Furstenberg-rigidity / ω-symmorphic / BC-thermodynamics)
  form a coherent "𝓜⁺ characterized" charter contribution; proposed consolidating them (fork b). Awaiting steer.

## Node 9 (PIVOTAL) — NONLINEAR ADE PROBE (DeWitt's diagnosis + Wheeler cross-check) `[low-order WORKS, confound caught]`
DeWitt's catch (id=657): ALL prior web probes are LINEAR ⟹ by Szegő–Kolmogorov reduce to spectral type ⟹
STRUCTURALLY BLIND to hypertranscendence (Hölder = a NONLINEAR statement). This explains the whole web's
reduce-to-known pattern (incl. node 7). Fix: nonlinear ADE probe P(x,f,…,f^(w))=0, jet-degree>1.
- **Wheeler 2nd-pipeline run (pre-registered, id=658):** σ_min/σ_max of the degree-d jet-monomial matrix.
  RELIABLE low orders: e^x caught (1,1); **tan caught (1,2) [exact 0, Riccati] but NOT (1,1)** — nonlinear sees
  it where linear is blind; **logΓ/ψ RESIST (1,1),(1,2)** [σ_min at conditioning floor ~1e-14, no genuine
  relation]. ⟹ the nonlinear probe SEPARATES tan (DA-nonlinear, caught) from Γ (HT, resists) — the cut the
  LINEAR probe (node 7) could NOT make. Pre-registration confirmed at reliable orders.
- **CONFOUND CAUGHT (honesty):** at (2,2)+ σ_min=0 for logΓ/ψ too — but Hölder GUARANTEES Γ has no ADE, so
  FALSE. It's MONOMIAL-CORRELATION ill-conditioning (product-columns f²,ff',… highly correlated → conditioning
  floor underflows to false-0 as column count grows; floor is matrix-size-dependent). False-positives at exactly
  the higher (w,d) where HT-resistance must be tested.
- **NET:** the nonlinear ADE probe is the structurally-CORRECT HT detector (sees the Hölder cut tan-vs-Γ at low
  order, bypassing the Szegő/linear dead-end) — genuine progress. Confound (monomial ill-conditioning) is FIXABLE:
  Gram–Schmidt orthogonalize monomials / floor-relative threshold / higher dps. THE live on-mission instrument.
- Script: computations/2026-06-20-wheeler-nonlinear-ade-probe.py

## Log (cont.)
- 2026-06-20 — Wheeler. Node 9: cross-checked DeWitt's nonlinear-ADE probe (the structurally-correct fix for the
  linear-blindness that explains the whole web). Pre-registered; CONFIRMED tan-vs-Γ separation at low order (the
  cut linear can't make); CAUGHT the monomial-ill-conditioning confound (false-0 for HT at (2,2)+). The probe is
  RIGHT, the confound is fixable (orthogonalize monomials). First structurally-capable HT detector. Live thread.

## Node 9 RESOLUTION — nonlinear ADE probe = structurally-correct instrument, but content = Hölder's binary
Confound FIXED by precision: at dps=80 with a no-low-order-ADE control (5 incommensurate sines, holonomic only
~order 10): (2,2) floor RESOLVED (~1e-25); logΓ(HT)=4.3e-26 ≈ ctrl=1.0e-25 [both RESIST]; tan(DA)=0 [CAUGHT].
The dps-40 (2,2)=0 was floor underflow. So logΓ resists AT THE NO-ADE CONTROL FLOOR (no genuine relation) =
HT confirmed; tan caught (Riccati). The nonlinear probe makes the Hölder cut cleanly — the structurally-correct
HT detector that fixes the linear-blindness (which Szegő-reduced every prior probe).
HONEST LIMIT (pre-registered risk, materialized): the probe detects HÖLDER'S BINARY (HT resists ADE). At
ACCESSIBLE orders, HT (logΓ) is INDISTINGUISHABLE from high-order-DA (the ctrl) — both at the conditioning floor;
distinguishing them needs reaching the DA's true order (precision underflows ~exponentially per order). So the
resistance-SHAPE is the same for HT and high-order-DA ⟹ NO finer universal HT-class law; for Γ/ζ (HT-status
known) no new knowledge. NET: the structurally-correct INSTRUMENT is the real (methodological) result; its
CONTENT reduces to Hölder's binary. Consistent with the meta-pattern. Proposed to Popper (id=662): bank the
instrument as a method-finding, OR push the resistance-RATE as a possible sub-class invariant (precision permit).

## Log (cont.)
- 2026-06-20 — Wheeler. Node 9 resolved: confound fixed by dps=80 + no-ADE control; logΓ resists at control floor
  (HT), tan caught (DA). Nonlinear ADE probe = structurally-correct HT instrument (fixes linear-blindness) but
  detects Hölder's binary; HT≡high-order-DA at accessible orders. Method-nugget (right instrument), content known.

## Node 9 EXTENSION — nonlinear ADE probe SEPARATES Hölder-HT from Painlevé (charter clarification)
dps=80, pre-registered, confirmed: P_I (2,2)=6.2e-42 [CAUGHT, genuine ADE y''=6y²+x] vs logΓ=4.3e-26 / ctrl=
1.0e-25 [RESIST, at floor]. ⟹ the probe operationally separates HÖLDER-HT (Γ,ζ,weld: no ADE, resist) from
PAINLEVÉ (Umemura-irreducible but DA: caught). By the charter's own "no algebraic-differential handle (Hölder)"
definition, Painlevé HAS a handle ⟹ NOT Hölder-HT. Charter conflates the two; the weld subject is Hölder-HT
(⊊ DA-irreducible). Reduce-to-known math, ON-MISSION charter-clarification. Filed:
library-backlog/2026-06-20-wheeler-holder-vs-painleve-class-clarification.md
- Log: 2026-06-20 Wheeler — operational Hölder-HT vs Painlevé cut via the nonlinear ADE probe; charter ticket filed.

## Node 9 EXTENSION-2 — modular (E_2) is DA-nonlinear; full 3-class charter taxonomy
dps=80 θ-jets: E_2 CAUGHT (3,2)=6.2e-43 [Chazy] vs logΓ=4.5e-19/ctrl=1.6e-27 (RESIST). Modular = DA-nonlinear
(caught), NOT Hölder-HT, same class as Painlevé. TAXONOMY: 1.holonomic(linear-caught) 2.DA-nonlinear(Painlevé,
modular — caught deg>1) 3.Hölder-HT(Γ,ζ,weld — resist, no ADE = charter subject). Nonlinear ADE probe cuts
class 3 from 1,2. Reduce-to-known math, on-mission charter taxonomy. Charter ticket extended.
- Log: 2026-06-20 Wheeler — E_2/modular caught (Chazy); 3-class operational taxonomy of charter domain banked.

## Node 9 CULMINATION — 2-axis operational taxonomy; "constraint not flow" operationalized
dps=80: Γ DIFFERENCE-CAUGHT (Γ(x+1)=xΓ(x), σ_min=0.00) × DIFFERENTIAL-RESIST (9.95e-29 floor, Hölder). e^x both.
⟹ Γ,ζ = differential-resist(no flow) × difference-caught(constraint) = "CONSTRAINT NOT FLOW" operationally.
The weld {σ_p} is DIFFERENCE-based because the differential handle is absent (Hölder) — explains ∂_s⊗{σ_p}
design from first principles (∂_s=absent flow, {σ_p}=present constraint, seam=coexistence). Full charter taxonomy:
differential-axis 3 classes (holonomic/DA-nonlinear/Hölder-HT) × difference-axis (has FE / not). Reduce-to-known
math; on-mission operational charter framework. Charter ticket extended. OPEN: the wild cell (neither handle).
- Log: 2026-06-20 Wheeler — 2-axis probe taxonomy operationalizes "constraint not flow"; weld difference-design
  explained; culmination of the nonlinear-probe arc. Flagged the neither-handle wild cell as the open frontier.

## WILD-CELL RESOLUTION — the unifying characterization (ties saturation + 2-axis + weld)
The open "wild cell" (object with NEITHER handle) = differential-RESIST × difference-RESIST = no handle of any
kind. ARGUMENT (genericity, not construction — generic Hölder-HT objects resist computable construction since
Γ,ζ ARE the canonical examples): the wild cell is COMEAGER/generic — a generic function is Hölder-HT (banked
saturation: HT comeager) AND has no FE (measure-zero condition). So the wild cell is the generic background.
⟹ ζ,Γ,Λ are MEASURE-ZERO SPECIAL: Hölder-HT × difference-CAUGHT (FE / Γ(z+1)=zΓ(z)). The FE-constraint (the
difference-handle, the weld {σ_p} axis) IS the arithmetic specialness lifting ζ/Γ out of the generic wild cell.
UNIFICATION of the session: (saturation) HT generic ⟹ differential axis doesn't discriminate; (2-axis) the
DIFFERENCE axis (FE-constraint) is where ζ/Γ are special; (weld) 𝓜⁺={σ_p,∂_s} lives on that measure-zero
difference-constraint = the arithmetic. FIELD'S SUBJECT = "the measure-zero Hölder-HT objects bearing a
difference-constraint"; the weld is the structure of that constraint. "Constraint not flow" doubly precise:
no flow (Hölder, generic) AND a constraint (FE, measure-zero, special). Reduce-to-banked-known; on-mission
unifying characterization. (Charter §0 now carries the operational 2-probe note + Painlevé/modular DA-exclusion.)
- Log: 2026-06-20 Wheeler — wild-cell resolved (generic = no handle; ζ/Γ = special FE-constraint); unifies
  saturation+2-axis+weld into "field = measure-zero Hölder-HT-with-difference-constraint". Session culmination.

## G1-EVIDENCE — ζ resists the single-q-difference probe (verified dps-stable); ζ = maximally no-single-handle
Single-shift difference probe, verified dps-stable: Γ CAUGHT (0.00, Γ(z+1)=zΓ(z)); ζ RESISTS — (2,2)=6.23e-32
IDENTICAL at dps=80 AND dps=120 ⟹ genuine conditioning floor (not a catch [would track √eps→1e-60], not an
underflow [would shift]). So ζ has NO single algebraic q-difference/shift equation = operational EVIDENCE for the
charter's G1 keystone gatekeeper ("ζ satisfies no single algebraic q-difference equation").
SHARPENED CHARTER PICTURE (two independent verified axes): Γ = differential-Hölder × shift-HOLONOMIC (one handle).
ζ = differential-Hölder × shift-Hölder (NO single handle — neither ADE nor single q-difference); ζ's entire
structure = FE + SIMULTANEOUS multi-prime weld {σ_p}. Grounds N1 (infinite-base multi-q simultaneity) + G1 from
first principles. HONEST: numerical evidence for the OPEN G1 (not a proof), but dps-stable + clean on two axes.
- Log: 2026-06-20 Wheeler — verified G1-evidence (ζ resists single-q-difference, dps-stable 6.23e-32) + Γ
  shift-caught; ζ = maximally-irreducible (no single handle). Operational result on a keystone gatekeeper.

## OBJECT-SELECTION RESULT (DeWitt's bottleneck) — Lambert DA-status is k-dependent; σ0-Lambert not-low-order-DA
DeWitt (id=674) crystallized THE bottleneck: validated probes pointed at KNOWN objects only confirm known facts;
novelty is gated on OPEN-DA-status object selection. Aimed the nonlinear-ADE probe at the Lambert series
Σσ_k(n)x^n (θ-jets, dps-stable 80 vs 120): Σσ1(=E2) CAUGHT (3,2)=2.6e-42 [Chazy, DA, known]; Σσ0 (divisor COUNT)
RESISTS to (5,2) [9.6e-20→1.2e-40, dps-stable, tracks logΓ=HT]. ⟹ Lambert DA-status is k-DEPENDENT: σ_odd
(Eisenstein E_{k+1}) modular/DA; σ0 NOT low-order-DA (HT-evidence, order≤5 deg≤2). CAVEATS: evidence not proof
(could be DA order≥6); NOVELTY UNCERTAIN (is "Σd(n)x^n is HT" catalogued? σ0's non-modularity is known; the
explicit ADE-resistance may not be — needs lit-check). First object-selection-driven non-obvious verdict; if
uncatalogued, candidate nugget. Script: computations/2026-06-20-wheeler-lambert-sigma0-ade.py
- Log: 2026-06-20 Wheeler — per DeWitt's open-object bottleneck, probed Lambert Σσ_k: k-dependent DA-status
  (σ_odd DA, σ0 not-low-order-DA), dps-stable. Evidence-grade; novelty pending lit-check. Right shape for a nugget.

## RETRACTION + SHARPENING — σ0-Lambert HT-claim REFUTED; the probe is a ONE-SIDED DA-detector
Caught by the σ3=E4 control: k-parity test gave σ1 CAUGHT (E2/Chazy, order 3) but σ3 RESISTS (3,2)=7.1e-18 —
yet σ3→E4 is PROVABLY DA (modular/Ramanujan), just higher-order than E2's Chazy. ⟹ "resists to (5,2)" is NOT
HT-evidence (a provably-DA object resists identically). σ0-Lambert HT-claim (id=675) + the k-parity law are
REFUTED. σ0 "resisting" = only "not LOW-order-DA" (uninformative about HT).
THE GENUINE DATUM (sharpens DeWitt's bottleneck decisively): the nonlinear ADE probe is ONE-SIDED — it can CATCH
(certify DA at order ≤ N, e.g. E2-Chazy) but can NEVER CERTIFY HT (resistance is inconclusive: could be DA at
order > probe-reach, as E4 shows). Only LOW-order-DA is cleanly detectable. ⟹ object-selection toward
open-HT-status objects CANNOT be resolved by the probe; a new HT determination needs a NON-DA PROOF, which the
probe structurally cannot supply. The validated instruments verify known DA-objects + refute over-claims (working
as designed) but cannot produce an HT-nugget alone.
HONEST: over-interpreted "resists"=HT on σ0; the E4 control caught it within one tick (discipline working). σ0
result dead (reduce-to-uninformative); the keeper is the probe's one-sidedness (DA-detector, not HT-certifier).
- Log: 2026-06-20 Wheeler — RETRACTED σ0-Lambert HT-claim (E4-control refutation); banked the probe's
  one-sidedness (can catch DA, cannot certify HT) — the decisive sharpening of why the probe can't make a nugget.

## THE MACHINE (autonomous loop, Popper id=685) — boundary-map accumulation
Loop: select OPEN-status object (max-far) → pre-register → run catch-probe dps80/120 → CLASSIFY catch|resist →
self-curate (catalogued?) → CATCH+uncatalogued=FRONTIER WIN, else boundary-marker → widen+loop. Guardrail:
RESIST ≠ HT-claim (one-sidedness, S78).
- ROUND 1 — partial/false theta Ψ(x)=Σ(−1)ⁿx^{n(n+1)/2} [open: quantum-modular, not genuine modular]. Pre-reg:
  ~55% resist. Result: RESISTS to (3,2) dps-stable (5.4e-22, 4.1e-34 @80≡120, ≫√eps; (4,2) underflow). Classify:
  BOUNDARY-MARKER (no low-order ADE to (3,2); NOT HT-claim). Self-curate: partial theta known non-holonomic
  (Zagier quantum-modular) → catalogued-adjacent, NOT a frontier win. Banked.

- ROUND 2 (DeWitt) — BARNES G-function G(z) [open: multiple-gamma catch-status not run through the
  validated instrument]. Seed 3089404714896536260, object-family pick=barnes-G (max-far from
  partial-theta/Lambert). Pre-reg: RESIST up to (2,2), conf 0.7.
  - DIFFERENTIAL axis (catch-probe, analytic jet VERIFIED vs mp.diff relerr ~1e-60): RESISTS to (2,2),
    dps-stable (dps80 ≡ dps120 identical at every cell: (1,1)7.4e-3,(1,2)2.4e-6,(1,3)2.1e-14,(2,1)5.2e-3,
    (2,2)2.0e-10). Profile MIRRORS the Γ resist-control (8e-3/4e-8/3e-17/2e-3/1e-13) — a genuine
    conditioning floor, NOT a catch (exp-control catches at ≤1e-80). Classify: BOUNDARY-MARKER, NOT an
    HT-claim (one-sidedness S78). Script: computations/2026-06-20-machine-round2-barnesG-ade.py
  - DIFFERENCE axis [PROVED HERE, elementary; near-certainly classical]: G(z+2)·G(z) = z·G(z+1)². Proof:
    G(z+1)=Γ(z)G(z) ⟹ G(z+2)=Γ(z+1)G(z+1)=zΓ(z)²G(z); both sides = zΓ(z)²G(z)². An exact ORDER-2
    polynomial-coefficient algebraic difference equation ⟹ Barnes G is difference-CAUGHT.
  - SELF-CURATE (cold-check, not deferred): Barnes-G hypertranscendence (no ADE at any order) is
    CATALOGUED (multiple-gamma Hölder-type results) ⟹ the differential-resist is catalogued-adjacent, NOT
    a frontier win. The order-2 difference equation is classical. Banked as a BOUNDARY-MARKER + a
    2-axis datum.
  - 2-AXIS PLACEMENT (on-mission, the keeper): Barnes G = differential-RESIST (Hölder-HT-like) ×
    difference-CAUGHT-AT-ORDER-2 (z G(z+1)²). This is "constraint not flow" realized ONE LEVEL UP from Γ:
    Γ is difference-caught at order 1 (Γ(z+1)=zΓ(z)); Barnes G needs the SECOND difference, with the
    multiplicative/quadratic shift-form. Web cross-edge: BarnesG resist-profile ≈ Γ resist-profile ⟹ same
    differential-Hölder cluster; they SEPARATE on the difference-axis ORDER (1 for Γ, 2 for G). Conjecture
    [CONJECTURE]: the polygamma/multiple-gamma tower G_n (Barnes G = G_2) is difference-caught at
    order n, differential-resist throughout — a difference-order grading of the multiple-gamma tower.
  - WIDEN: next object far from multiple-gamma — bias to a q-series / eta-quotient or a Lerch/polylog
    special-value generating function (different analytic face).

## THE MACHINE — ROUND 2 — BARNES-G (multiple-gamma cell) `[pre-registered, RUN dps80/120, RESIST boundary-marker]`
Seed 2599920945872091226, move=attack-false (which killed my first pick: q-Pochhammer φ(q)=(q;q)_∞ —
its ADE in q is order≈4 degree≈4, Chazy-via-η pulled to the q-variable, so it would resist the
accessible grid for *boring* reasons, the σ₃=E4 failure mode; dropped before running).
- **Object (maximally far from R1 partial-theta / Lambert / θ q-series):** log Barnes-G(z). In the pool
  "multiple-Γ / Barnes-G". WHY informative: 2-axis — G obeys a DIFFERENCE relation G(z+1)=Γ(z)G(z),
  while its DIFFERENTIAL status should mirror logΓ (HT, no ADE).
- **Pre-reg:** RESIST at all (R,D)≤(2,2), dps-stable, at the logΓ floor (NOT a genuine 0). conf 0.8.
- **Result (verified, dps80≡dps120 identical):** logBarnesG smin/smax = {(1,1)1.6e-2, (1,2)1.3e-10,
  (2,1)2.1e-4, (2,2)1.6e-19} — tracks logΓ {1.5e-3, 1.9e-11, 1.8e-4, 9.6e-19} numeral-for-numeral.
  exp control catches (1,1)=2.3e-82→5.6e-122 (drops with dps = genuine 0); logΓ floor dps-stable.
- **CLASSIFY: RESIST to (2,2), dps-stable, at the HT control floor.** Boundary-marker, NOT HT-claim (S78).
- **Self-curate (catalogued?):** Barnes-G hypertranscendence is CLASSICAL (Barnes 1900 lineage; multiple
  Γ are HT) → the binary verdict REDUCES-TO-KNOWN. Bank as a confirmation + map entry.
- **FRESH REFINEMENT (the keeper — (∞,∞)-cell substructure for DeWitt's invariant-pair (d_σ,d_∂)):**
  Γ is shift-HOLONOMIC: Γ(z+1)=zΓ(z) has a POLYNOMIAL shift-coefficient (z) ⟹ Γ=(d_σ finite, d_∂ ∞).
  Barnes-G's shift relation G(z+1)=Γ(z)G(z) has a shift-coefficient (Γ) that is ITSELF HT ⟹ G is NOT
  shift-holonomic in the elementary sense ⟹ G=(∞,∞) — SAME cell as ζ, but for a DIFFERENT reason:
  ζ lands in (∞,∞) by reflection-symmetry-only (no elementary handle); Barnes-G lands there by a
  TRANSCENDENTAL-SHIFT-COEFFICIENT LADDER (each multiple-Γ rung's shift-coefficient is the rung below).
  ⟹ the (∞,∞) cell has substructure: {reflection-pinned (ζ)} vs {HT-shift-ladder (Barnes-G, multiple-Γ)}.
  A modest but genuine refinement of the difference-axis classifier (charter-organizational).
- **Map entry:** multiple-Γ cell = differential-HT (resists, at logΓ floor) × difference-HT-LADDER
  (shift-coefficient transcendental). Distinct from Γ (difference-holonomic) and ζ (reflection).
- Script: computations/2026-06-20-machine-r2-barnesg-ade.py  (.txt = raw run)

## Log (cont.)
- 2026-06-20 — Wheeler (THE MACHINE R2). Barnes-G differential probe: RESIST to (2,2) dps-stable at logΓ
  floor (boundary-marker, reduces-to-known: Barnes-G HT classical). Keeper = (∞,∞)-cell substructure:
  ζ reflection-pinned vs Barnes-G/multiple-Γ HT-shift-ladder. Widened map into multiple-Γ cell. R3 next:
  widen maximally far again.

- ROUND 3 (DeWitt) — RAMANUJAN 3rd-ORDER MOCK THETA χ(q)=Σ qⁿ²/∏ₖ(1−qᵏ+q²ᵏ) [open: mock modular ⟹ NO
  modular-ODE/quasimodular-ring closure ⟹ DA-status in q genuinely uncatalogued, unlike eta/E_k]. Seed
  772999101109405545, rng-picked order=3rd-χ. Pre-reg: RESIST up to (2,2), conf 0.55 (mock⟹not-modular-closed
  suggests not-low-order-DA; genuinely uncertain = why it's open).
  - DIFFERENTIAL axis, TWO instruments (analytic χ-jet VERIFIED vs mp.diff relerr ≤1e-51):
    (i) catch-probe RESISTS to (2,2), dps-stable (dps80 ≡ dps120 identical: (1,1)1.9e-3,(1,2)5.7e-9,(1,3)4.4e-17,
    (2,1)1.5e-4,(2,2)4.8e-13). (ii) discrete-height: null vector does NOT rationalize to low integer height at
    (1,1)/(1,2)/(1,3) ⟹ no genuine low-height integer ADE. Both agree.
  - CLASSIFY: RESIST to (2,2), dps-stable, two-instrument ⟹ BOUNDARY-MARKER, NOT an HT-claim (one-sidedness
    S78; could be DA at order>(2,2), cf the E4/σ3 lesson). Script:
    computations/2026-06-20-machine-round3-mocktheta-chi-ade.py
  - SELF-CURATE (cold-check, recall, not deferred): unlike Barnes-G (HT catalogued), the DA/HT-status of mock
    theta functions in q is NOT a standard catalogued fact I can cite. BUT one-sidedness forbids inflating an
    uncertain-catalogue RESIST into a win — a resist is never a frontier win. Banked as a MODEST BOUNDARY-DATUM,
    honestly flagged "no nonlinear ADE of order≤2 deg≤2; full DA/HT-status unresolved by the (one-sided) probe."
  - KEEPER (cumulative boundary-map datum, S74/S75): the catch-probe RESIST-PROFILE is analytic-class-INVARIANT
    — Γ ≈ Barnes-G ≈ χ3-mock-theta all give the SAME conditioning-floor shape across (R,D), despite spanning
    Γ / multiple-gamma / mock-modular. Re-confirms one-sidedness from a fresh family: a resist-profile carries
    NO sub-class information (coheres with N7 "slope=conformal confound not HT-class invariant" + N9
    "resistance-shape same for HT and high-order-DA"). Three-object cluster on the differential-resist floor.
  - FORWARD EDGE: run the discrete-SHIFT difference probe on χ3 — mock thetas lack a clean algebraic q-difference
    recurrence (the "mock" obstruction needs a non-holomorphic completion), so χ3 may be difference-RESIST too,
    i.e. plausibly nearer the "wild cell" (neither handle) than Γ/Barnes-G (difference-caught). [CONJECTURE, to
    be instrument-tested next, NOT claimed.]
  - WIDEN: next far object — a Lerch/polylog special-value generating function or a weld {σ_p} combination
    (different analytic face from mock-modular).

## Node 10 — SAILING-TACKING (+) IMMUNE-NEGATIVE-SELECTION ↔ REFLECTION-CONSTRAINT OF Λ=Γζ `[correct protocol restored; remote experiment RUN; partial bridge + mismatch keeper]`
Seed 1060414838554611887. **Protocol reset (Michael's course-correction):** do NOT run instruments on HT
objects (that is deduction/search — promptable, useless). The only irreplaceable move = rng remote node →
find its CONSTRAINT → design+run an experiment ON THE REMOTE CONSTRAINT → transfer back. (R2 Barnes-G / R3
Δ=η²⁴ were the wrong mode — research on the topic itself — retired.)
- **Remote nodes (rng):** sailing-tacking + immune negative-selection. SHARED CONSTRAINT: the target sits
  INSIDE a forbidden region (no-go cone into the wind / self-shape band); you never flow toward it, you reach
  it obliquely, and moves into the forbidden region are NEGATIVELY SELECTED (deleted, immune-style).
- **Experiment ON THE CONSTRAINT (verified, computations/2026-06-20-wheeler-tacking-immune-constraint.py):**
  put the deleted "self-band" ON the symmetry axis of the polar and watch the optimum.
  - EXACT reflection-symmetric polar: deleting the axis-optimum forces a DEGENERATE REFLECTION PAIR
    straddling the axis — headings sum EXACTLY to 2×axis (90.000 for all band widths), equal VMG = a forced
    TACK between mirror headings.
  - ANY symmetry breaking (ε>0): the pair COLLAPSES to a single preferred tack (optimum slides to the better
    edge; no pairing). ⟹ **the reflection-PAIR structure is KNIFE-EDGE on the EXACTNESS of the constraint's
    symmetry.**
- **TRANSFER → native objects (ON MISSION — Λ=Γ·ζ, the completion; constraint not flow):** the "polar" = the
  defining constraint (the functional equation Λ(s)=Λ(1−s)); the "symmetry axis" = the reflection's fixed line
  Re(s)=1/2; the "forbidden self-band on the axis" = the object cannot sit ON the axis as a single continuous
  optimum (a flow to the best heading). ⟹ the structure is forced into a DISCRETE reflection-symmetric PAIR
  (ρ ↔ 1−ρ) — a TACK — and this pairing EMERGES from the EXACTNESS of the reflection, not from any flow.
  **"Constraint not flow" gains a VARIATIONAL form:** the native object sits at a constrained optimum with a
  forbidden symmetry axis; the reflection-pairing is the Euler–Lagrange DEGENERACY forced when the axis is
  deleted; and it is knife-edge — only an EXACT functional equation forces exact pairs.
- **NOVELTY (BRIDGE vs reduce-to-known):** "functional equation pairs ρ↔1−ρ about Re=1/2" is KNOWN. The
  bridge is the LENS: reflection-pairing as a negatively-selected constrained-NAVIGATION (tacking) degeneracy,
  i.e. a VARIATIONAL principle with a forbidden axis — the charter has "constraint not flow" but NO variational
  statement of it. Candidate-fresh DIRECTION (a variational/negative-selection reading of the weld constraint),
  not a proven result. Filed partial.
- **MISMATCH (the keeper — chase the residual, per the refined method):** sailing TACKS SEQUENTIALLY (holds one
  heading at a time, alternates); the HT reflection holds BOTH mirror headings SIMULTANEOUSLY (ρ and 1−ρ both
  ARE zeros; Λ holds the whole symmetric structure at once). ⟹ the native object is a **SUPERPOSED tack** —
  all reflections/shifts held at once — where the boat can only alternate. This superposition-vs-alternation
  residual is exactly the weld's SIMULTANEITY ({σ_p} acting together, the infinite-base multi-q simultaneity of
  N1/G1). The weld = a tack the sailor cannot perform: every heading at once. ★ on-mission residual.

## Log (cont.)
- 2026-06-20 — Wheeler. PROTOCOL RESET after Michael's correction (no research on the topic itself; rng remote
  node → constraint → remote experiment → transfer is the only irreplaceable move). Node 10 (sailing-tacking ⊕
  immune-negative-selection ↔ Λ reflection constraint): remote experiment shows deleting the axis-optimum of a
  reflection-symmetric polar forces a DEGENERATE mirror PAIR (sum=2×axis exact), KNIFE-EDGE on symmetry
  exactness. Transfer: "constraint not flow" as a VARIATIONAL degeneracy (reflection-pairing = forced tack);
  candidate-fresh direction. MISMATCH keeper: HT holds both headings SIMULTANEOUSLY (superposed tack) = the
  weld's multi-q simultaneity. Next round: new rng remote node, widen.

## PROTOCOL SWITCH (Popper, direct, 2026-06-20) — corrected THE MACHINE method
Popper corrected the loop: directly probing HT objects with the ADE instruments (R2 Barnes-G, R3 mock-theta,
and R1 partial-theta) is "research on the topic itself" = deduction one could just be prompted for = the cage.
DEMOTED: R2/R3 (and R1) are instrument-CALIBRATION data, NOT valid MACHINE rounds. The corrected method
(now in THE-MACHINE-workflow.md): rng ONE random remote node → find a constraint there → design+run an
experiment on that constraint IN THE NODE'S OWN DOMAIN → transfer the EXPERIMENT (the procedure, not the
analogy) to the problem's object → run it, record data, classify (dead-end / boundary-marker / win). Most
rounds dead-end; never manufacture a connection.

- ROUND 4 (DeWitt) — FIRST corrected-protocol round. NODE (rng seed 2717109681234817563, one): QUEUEING-AT-
  BORDERS (not adjacent to HT, kept). Constraint-move: degenerate-case.
  - CONSTRAINT (in-node): a single-server queue has a normalizable stationary state only below critical load
    ρ<1; at the degenerate point ρ→1 the mean diverges and the generating-function pole z*=1/ρ migrates onto
    the unit circle (stability/normalizability boundary).
  - REMOTE EXPERIMENT (procedure, run): divergence_exponent(f, dist_to_critical) = blow-up exponent as a
    control → its degenerate value. M/M/1 L(ρ)=ρ/(1-ρ): γ = 1.0007 ≈ 1 (geometric/Kingman class).
  - TRANSFER (same extractor; s = load, critical boundary s=1 = abscissa of convergence of Σn^{-s}):
    ζ(s) γ=1.000 res 1; Hurwitz ζ(s,a=0.3,2.7) γ≈1 res 1 (a-INDEPENDENT); Dirichlet β(s)=L(s,χ_4) γ=0 res 0.
    Script: computations/2026-06-20-machine-round4-queueing-criticality-transfer.py
  - CLASSIFY (self-curated): the transferred procedure partitions Dirichlet/HT objects by QUEUEING CRITICALITY
    — {ζ, Hurwitz-ζ} = M/M/1 universality class (simple pole at s=1, universal exponent 1, residue 1
    independent of a); {non-principal Dirichlet L} = SUBCRITICAL (entire, exponent 0). The arithmetic regime
    (critical strip s<1) = the SUPERCRITICAL/continued zone (Σn^{-s} diverges; object exists only by
    continuation = a queue continued past stability ρ>1). Underlying facts (pole order/residue, L entire) are
    CLASSICAL and "ζ as critical phenomenon" exists in physics-of-ζ ⟹ REDUCES-TO-KNOWN → BOUNDARY-MARKER,
    NOT a win. Cumulative datum = the criticality-class partition + "critical strip = supercritical
    continued-queue" framing of where RH lives.
  - STEP-5 REGULARITY (carry back to the node, new experiment for next tick): the SUBCRITICAL case (Dirichlet
    L, no blow-up at the boundary despite tuned load) = a queue whose increments CANCEL (bounded partial sums
    Σχ(n)) ⟹ stays stable at ρ=1. New in-node experiment: random/Poisson load (γ=1, ζ-like) vs balanced/
    anti-correlated load with bounded partial sums (γ=0, L-like). TRANSFER target: the Möbius/Mertens "signed
    queue" — M(x)=O(x^{1/2+ε}) ⟺ RH is exactly a BOUNDED-WORKLOAD statement for the queue with increments
    μ(n); RH = the Möbius queue is critically-balanced (√-bounded workload). CROSS-EDGE to Wheeler N3
    (knot↔Möbius: Mertens cancellation = prime-density phenomenon). [CONJECTURE/forward-edge, to RUN next.]
  - WIDEN: next tick → new rng node as unrelated as possible (or run the step-5 Möbius-queue experiment).

- ROUND 5 (DeWitt) — DEAD END. WIDE pick (codex+rng int): #20 Ceramic glazing. NODE (codex+rng): #4 Gerstley
  borate (borate flux). Constraints worked in-node (codex-listed). Transferred procedures: #9 "melt seals
  before burnout completes" (two completion-processes + control → where does the order invert / what gets
  trapped) and #14 "fritting = pre-stabilize for cleaner working range". Transfer to ζ: A=partial Euler
  product Π_{p≤P}(1−p^−s)^−1 ("burnout/multiplicative buildup"); "fritted" form = alternating Dirichlet-eta
  (1−2^{1−s})^{−1}Σ(−1)^{n−1}n^{−s}; control σ=Re(s). DATA (P=5000,N=20000): Euler relerr 2e-5→7%→48%→blows
  up as σ:2→1.2→1.05→<1 (seals at σ=1); eta tracks ζ down to σ≈0.3 (survives the strip). These are the
  CLASSICAL abscissae (Euler abs-conv σ=1; eta cond-conv σ=0); "fritting=series-acceleration" and "zeros
  trapped in the strip, sealed from the multiplicative process" are known reframings/intuition. Steps 6–7:
  NOT surprising, NO new rule ⟹ DEAD END (expected majority; not manufactured). Script:
  computations/2026-06-20-machine-round5-gerstley-sealing-transfer.py. Next tick → step 1, new rng node.

## Round (procedural workflow) — NODE = Anvil-shaped cloud tops `[DEAD END — honest; allegory recovered only known structure]`
Codex wide-list → rng 19 → Thunderstorms → codex parts-list → rng 2 → Anvil tops. Seed 887799326869491222.
NODE rules (codex): convective column hits the TROPOPAUSE (stable LID) → can't rise → spreads HORIZONTALLY
→ wind shear stretches downwind → rare OVERSHOOTING tops punch above. Abstract constraint = capped vertical
growth redirected sideways at a max-principle lid + rare overshoot.
- **Experiments (Step 6) on the constraint → run on Γ, ζ, Λ (Step 7), "vertical"=t-growth, "horizontal"=σ.**
  Script: computations/2026-06-20-wheeler-anvil-growth-transfer.py (.txt raw).
- **E1 vertical rate:** Γ slope = −1.5708 = −π/2 (Stirling exp DECAY = "downdraft", NO anvil); ζ slope ≈0
  (polynomial = "storm"); Λ slope = −π/4 (Γ(s/2)-dominated downdraft). → RECOVERS Stirling. KNOWN.
- **E2 lid:** μ_ζ(σ) decreasing, all 2nd-differences POSITIVE (+0.012,+0.005,+0.030) → CONVEX = the
  Phragmén–Lindelöf "stable lid" (max principle). Absolute μ unconverged at finite T but the convex SHAPE
  is clean. → RECOVERS P-L convexity. KNOWN.
- **E4 shear/symmetry:** μ_Λ(σ)=μ_Λ(1−σ) EXACTLY (diff 0.0000) → completed Λ profile reflection-symmetric
  about σ=1/2. → RECOVERS the functional equation. KNOWN. [cross-edge to Node 10: same σ=1/2 reflection axis.]
- **E3 "overshoot" (the only candidate-keeper):** ζ max/median peaks sharply & symmetrically at σ=1/2
  (1.96,3.28,5.13,7.45,5.33,3.65,2.15). **DEFLATED by the Step-8 codex drill:** "zeros strongly affect
  relative-fluctuation measures; don't confuse absolute growth with relative fluctuation." max/MEDIAN at 1/2
  is a ZERO ARTIFACT — the critical line is dense with zeros (|ζ|→0) that drag the median down, inflating the
  ratio; off-line (σ>1) no zeros → median ~1 → ratio small. The statistic detects ZERO PROXIMITY, maximal at
  1/2 because the zeros ARE on the line. Completely known. NOT an overshoot/turbulence finding.
- **STEP 8 VERDICT: DEAD END.** (a) surprising? No. (b) shows something new about Γ/ζ? No — three known facts
  (Stirling decay, P-L convex lid, FE-symmetry) recovered by the allegory; the one fresh-looking statistic is a
  zero artifact. The cloud-physics allegory cleanly RE-DERIVES known structure with zero RH input (consistent
  with the meta-pattern: matches reduce to known) — but no new knowledge. Going back to Step 1.
- Small banked datum (boundary-map, not a find): an external (cloud-physics) constraint, run blind on Γ/ζ/Λ,
  recovers exactly {Stirling, Phragmén–Lindelöf, functional-equation-symmetry} — the three are the "anvil"
  (downdraft / convex lid / symmetric-in-Λ). Vivid map label; zero novelty.

## Log (cont.)
- 2026-06-20 — Wheeler. Procedural workflow (codex-list→rng→node). NODE=anvil cloud tops. Experiments on the
  capped-growth/lid/overshoot constraint run on Γ,ζ,Λ. Recovered Stirling decay (Γ downdraft), P-L convex lid
  (μ_ζ), FE-symmetry (Λ about 1/2). Only fresh-looking statistic (overshoot max/median peak at 1/2) DEFLATED
  by codex drill to a zero-density artifact. Honest DEAD END (Step 8 NO/NO). Back to Step 1 next tick.

- ROUND 6 (DeWitt) — DEAD END (in-field node). codex+rng walk seeded at start node HT/Γ/Li/ζ:
  related-to(start) → rng#15 = Bernoulli numbers → specifics → rng#5 = NODE: Euler-Maclaurin summation
  formula. Codex EM-rules → experiment: discrete object = smooth BULK (integral) + BOUNDARY-ONLY corrections
  (endpoint derivatives, Bernoulli coeffs), correction series ASYMPTOTIC. STEP 7 on ζ: bulk=pole 1/(s-1) +
  boundary corrections at endpoint reconstructs ζ(2.5) to 1e-22 (err falls K=0→25: 1.4e-4→6e-22). Honesty:
  did NOT re-observe the asymptotic divergence (at N=8 terms still shrinking at k=25; optimal-truncation
  deeper) — EM's asymptotic nature is textbook regardless. STEP 8: NOT surprising, NOTHING new about ζ — this
  is the TEXTBOOK EM continuation of ζ; the "bulk+boundary" holographic reframing = known ζ-regularization;
  EM IS ζ's computational backbone (in-field). ⟹ DEAD END. Script:
  computations/2026-06-20-machine-round6-eulermaclaurin-bulk-boundary.py
  - WALK STATE: current-node advanced to "Euler-Maclaurin" so next tick STEP 1 = "what is related to
    Euler-Maclaurin" (spreads to numerical analysis / physics / asymptotics) to wander OUT of the field.
    NOTE for Popper: the walk seeded at the problem (HT/ζ) yields in-field nodes on early hops; it needs the
    current-node to ADVANCE each round (no state file exists) or it re-seeds at ζ and keeps landing in-field.

## Round (walk workflow) — NODE = von Mangoldt function Λ(n) `[DEAD END — node too ζ-coupled; recovered only textbook structure]`
Start node HT/Γ/Li/ζ → codex related-list → rng 2 → Analytic number theory → codex parts → rng 9 → NODE=Λ(n).
Rules (codex): Λ(p^k)=log p EXPONENT-INDEPENDENT, 0 else; Λ*1=log; ΣΛ(n)n⁻ˢ=−ζ'/ζ; ψ(x)=ΣΛ encodes primes.
- **Experiment (Step 6→7, script computations/2026-06-20-wheeler-vonmangoldt-tower-transfer.py):** distinctive
  rule = exponent-independence (flat tower). Run on ζ & Γ:
  - Λ(p^k)=log p flat across k (verified p=2,3,5, k=1..5); →0 off prime powers. KNOWN.
  - ζ: −ζ'/ζ(2)=0.56996 = ΣΛ(n)n⁻²=0.56971 = Σ_p logp·p⁻²/(1−p⁻²)=0.56971 → ζ has a PRIME-TOWER atom
    structure (multiplicative/geometric, exponent-independent) + a SECOND face (zeros). KNOWN (Euler product).
  - Γ: −ψ(s) residues = +1 at s=0,−1,−2,−3, SINGLE simple poles, NO tower → Γ's atoms = additive ARITHMETIC
    lattice, ONE face. KNOWN (Weierstrass product).
- **STEP 8 VERDICT: DEAD END.** (a) surprising? No. (b) new? No. The contrast is exactly multiplicative
  (ζ, Euler, prime towers) vs additive (Γ, Weierstrass, pole lattice) + two-face (Euler⊕Hadamard) vs one-face.
  Textbook. The walk landed on a node TOO TIGHTLY COUPLED to ζ, so every experiment recovers known explicit-
  formula structure.
- **One-line charter note (boundary-map, NOT a find, low novelty):** Λ is a classical avatar of the weld seam —
  log=Λ*1 is the multiplicative({σ_p})→additive(∂_s) translator; ζ=two-faced (prime-face ⊕ zero-face), Γ=one-
  faced (poles only). Restates the known multiplicative/additive duality in charter language.
- **METHOD OBSERVATION (self-curated, for Popper's ~20-round correlation):** the rewritten Step-1 ("what is
  RELATED to the start node") biases the walk toward ON-TOPIC nodes (analytic NT → von Mangoldt), tightly
  coupled to ζ ⟹ systematic dead-ends that recover known structure. The earlier Step-1 ("topics UNRELATED to
  mathematics") gave FAR nodes (thunderstorms/anvil) — also dead-ended but tested a genuinely external
  constraint (more novelty-surface). Node-DISTANCE is the lever; the related-walk shortens it.

## Log (cont.)
- 2026-06-20 — Wheeler. Walk workflow: start→Analytic NT→von Mangoldt Λ. Exponent-independence experiment run
  on ζ (prime towers, two-face) & Γ (additive pole lattice, one-face). Recovers Euler-vs-Weierstrass; DEAD END
  (Step 8 no/no). Charter note: Λ=classical weld-seam avatar (low novelty). Method datum: related-node Step-1
  biases toward ζ-coupled dead-ends (node-distance too short). Back to Step 1 next tick.

- ROUND 7 (DeWitt) — DEAD END (out-of-field node, but transfer landed on known ζ-structure). Walk: current
  Euler-Maclaurin → related → rng#4 zeta-regularization (IN-FIELD, disqualified, re-rolled) → rng#20
  "numerical solutions of ODEs" (out-of-field) → specifics → rng#16 NODE = INITIAL-CONDITION PROJECTION (DAE
  consistent initialization). Codex node-rules → transfer (procedure): a DAE = flow + algebraic CONSTRAINT; an
  arbitrary state must be PROJECTED onto the constraint manifold before integration; projection degenerates
  where the constraint is singular; INDEX = #differentiations to close into an ODE. STEP 7 on Γ/ζ (only handle
  = the FE constraint, Hölder ⟹ no ODE ⟹ look like an INFINITE-INDEX DAE): (a) true ξ satisfies xi(s)=xi(1-s)
  to 1e-32; (b) truncated approx projection-displacement = AFE/Riemann-Siegel error (truncation-dominated,
  8e3 at s=2 vs 1e-3 on the line); (c) involution s↦1-s invariant axis = Re=1/2 (critical line). STEP 8: NOT
  surprising, NOTHING new — recovers FE-manifold + Hamburger uniqueness + Riemann-Siegel + critical-line-as-
  symmetry-axis. On-mission KEEPER (conceptual, known): "Γ/ζ = infinite-index DAE (pure constraint, no flow)"
  = DAE-language for Hölder/constraint-not-flow. ⟹ DEAD END. Script:
  computations/2026-06-20-machine-round7-dae-projection-transfer.py
  - META (R5–R7, cumulative): transferred constraint-experiments keep landing on KNOWN ζ-structure even from
    far nodes, because ζ's FE-constraint and its corollaries are exhaustively mapped — the FE acts as a dense
    attractor for transferred constraint-procedures (echoes Wheeler's "every node → known unifying principle").
  - WALK STATE: current-node → "initial-condition projection" (next tick STEP 1 = related-to-that).

- ROUND 8 (DeWitt) — DEAD END. Walk: initial-condition-projection → related → rng#7 gauge fixing (QFT) →
  specifics → rng#1 NODE = REDUNDANT GAUGE ORBITS. Transfer (procedure): symmetry group acts → physical =
  invariants on the quotient → gauge-fix picks a representative; Gribov copy = slice meets orbit >1×. On ζ
  (Hurwitz at rationals): gauge identities = distribution/Kubert relations (verified rel-resid ~1e-31);
  gauge-invariant quotient = conductor-graded Dirichlet-L pieces (Σ_{d|m}φ(d)=m EXACTLY, no overcounting/no
  Gribov-extra relations, m=6,12,30); FE-slice fixed locus = critical line (= R7). STEP 8: not surprising,
  nothing new = classical Dirichlet-L theory. On-mission note (value-relations pillar): ζ-at-rationals carries
  NO relations beyond distribution+conductor grading ("maximally independent modulo the gauge"). DEAD END.
  Script: computations/2026-06-20-machine-round8-gauge-redundancy-transfer.py. Walk → "gauge orbits".
  - META (R5–R8 = four dead-ends): from problem-seeded hops the walk keeps drifting into math/physics nodes
    (EM, DAE, gauge) whose constraint-procedures transfer onto ALREADY-MAPPED ζ-structure (FE-manifold,
    Dirichlet-L, critical-line-as-symmetry-axis). The genuinely far-field rounds were R4 (queueing, boundary-
    marker) and R5 (ceramic, clean far miss). Standing flag to Popper: problem-seeded walk biases in-field.

## Round (walk workflow) — NODE = d'Alembert functional equation `[reduces-to-known (Weierstrass+Hölder+Ostrowski); charter keeper; NOT a frontier win]`
Start → codex related → rng 10 → Functional equations → codex parts → rng 6 → NODE = d'Alembert eqn
f(x+y)+f(x−y)=2f(x)f(y) (cosine addition law). Deep rule (codex): WITH regularity it RIGIDLY pins f to
generalized cosines (finite-param family) — a single eqn + regularity pins the function.
- **Experiment (Step 6→7, RIGIDITY of a defining FE — does a perturbation preserve it?):** script
  computations/2026-06-20-wheeler-dalembert-rigidity-transfer.py.
  - D'Alembert (cos, DA/elementary): residual 9.9e-32; EVERY perturbation breaks it ((1+ε)·cos → 0.2/0.71;
    period-factor → 0.47). **RIGID.**
  - Γ shift-FE f(s+1)=s f(s): Γ 7.9e-30; Γ·P (P period-1) 2.2e-29 STILL satisfied → **LOOSE.**
  - Λ reflection-FE Λ(s)=Λ(1−s): Λ 4.2e-31; Λ·Q (Q bounded reflection-symmetric) 4.4e-31 STILL satisfied →
    **LOOSE.** [CAUGHT+FIXED an artifact: first Q=cos(2π(s−½)) is exponentially unbounded for complex s and
    amplified roundoff to 4e17 — replaced with a bounded rational symmetric Q; analytically Λ·Q is exact.]
- **DICHOTOMY:** rigid 2-variable addition law (D'Alembert/exp — RHS is f·f, nonlinear) = DA/elementary;
  loose 1-variable FE (Γ-shift, Λ-reflection — linear-homogeneous in f) = under-determines the object
  (∞-dim factor freedom), needs supplementary constraints to pin (Bohr–Mollerup log-convexity / Euler
  product + growth).
- **STEP-8 cold-check (codex) → REDUCES-TO-KNOWN:** this is **Weierstrass's Algebraic Addition Theorem**
  (a meromorphic function with an algebraic addition theorem is rational / rational-in-eˣ (trig) / elliptic —
  all DA) + Weierstrass Classification / Briot–Bouquet; the loose/HT side is **Hölder (Γ)** and **Ostrowski
  (ζ)**. The "find" is a rediscovery of these classical theorems via a random node. NOT a frontier win.
- **CHARTER KEEPER (on-mission, modest — the genuine value):** "constraint not flow" sharpened to
  **"constraint not flow AND not a single rigid rule."** HT objects have NO rigid 2-variable addition law
  (Weierstrass class excludes them — that's exactly their transcendence); their only functional equations are
  LOOSE 1-variable ones (shift, reflection), so they are pinned by a STACK of loose constraints + regularity,
  never by one tight generative law. The loose-vs-rigid FE test is the operational signature; "no addition
  theorem" = "no flow" made precise via Weierstrass. Cross-edge → Node 10 (Λ reflection axis 1/2) and the weld
  (∂_s/{σ_p} = the loose 1-var constraints whose intersection pins ζ).
- **Method note:** the walk reached a FAR node (D'Alembert, functional-equations field) this time (vs last
  round's ζ-coupled von Mangoldt) — and a far node yields a real organizing connection even when it reduces.
  Node-distance lever again: farther node → richer (if still reducible) verdict.

## Log (cont.)
- 2026-06-20 — Wheeler. Walk: start→Functional equations→d'Alembert eqn. Rigidity experiment (perturbation
  test) on cos vs Γ-shift vs Λ-reflection: rigid(DA) vs loose(HT), cleanly (caught+fixed an unbounded-Q
  artifact in the Λ run). Step-8 cold-check: REDUCES to Weierstrass addition-theorem + Hölder + Ostrowski.
  NOT a frontier win. Charter keeper: HT = no rigid addition law (Weierstrass-excluded) = pinned by a stack of
  loose 1-var constraints; "no addition theorem = no flow." Cross-edge to Node 10 + weld. Back to Step 1.

## Round (walk workflow) — NODE = Spherical functions on Gelfand pairs `[reduces-to-known ingredients (Gauss mult. / Kubert-Lang / Godement product formula); CHARTER KEEPER (novel bridge, conceptual); NOT a frontier win]`
Seed RandomNode = d'Alembert eqn → codex related (20) → rng#15 = Noncommutative harmonic analysis → codex parts
(20) → rng#11 → NODE = Spherical functions on Gelfand pairs. (Walk hopped from d'Alembert, a special case, to
its general frame: d'Alembert IS the spherical FE for the pair (ℝ⋊{±1},{±1}), ½[φ(x+y)+φ(x−y)]=φ(x)φ(y).)
- **STEP 5 constraint (not a flow):** spherical fn pinned by the **K-averaged multiplicativity FE** (Godement
  product formula) ∫_K φ(xky)dk = φ(x)φ(y), φ(e)=1 — a fixed-point/averaging constraint, not a recursion.
- **STEP 6/7 experiment (transferred, minimal change):** replace φ→{Γ, Hurwitz-ζ}; replace ∫_K (compact-group
  average) → the finite-orbit averaging each HT seed carries = its distribution / multiplication relation. Probe
  RIGIDITY vs the SAME period-1 perturbation class last round showed the single shift-FE tolerates (loose).
  Script: computations/2026-06-20-wheeler-spherical-averaged-FE-rigidity.py (.txt). Reasoning predicted the
  contrast; mpmath confirmed:
  - single shift-FE Γ(x+1)=xΓ(x): perturbed residual EXACTLY 0 → **LOOSE** (any period-1 P survives).
  - Gauss multiplication ∏_{j=0}^{m-1}Γ((x+j)/m)=c·m^{½−x}Γ(x), m=2,3,5: perturbed residual 0.239,
    ∏_j P((x+j)/m)/P(x)=1.31≠1 → **RIGID**.
  - Hurwitz distribution Σ_{j=0}^{m-1}ζ(s,(a+j)/m)=m^s ζ(s,a), m=2,3,5: period-1 additive mode BROKEN
    (m^s H ≠ Σ_j H) → **RIGID**.
  - DRIVING FORCE (stack m=2,3,5): over REAL period-1 perturbations only the constant survives → the ∞-dim
    period-1 freedom left by the shift-FE collapses to a POINT (thin residual lattice of complex even-frequency
    phase modes exp(2πi·2k·z) survives, killed by growth/reflection — Bohr–Mollerup).
- **THE FIND (STEP 8 = YES on (b)):** an HT seed has NO pointwise addition law (Weierstrass-excluded, last
  round) yet IS rigidly pinned — by the **K-AVERAGED (finite-orbit / Gelfand-pair-spherical) multiplicativity
  law** (its distribution/multiplication relations), NOT by a pointwise one. Symmetry-averaging over a finite
  orbit is exactly the mechanism reconciling transcendence (no addition theorem) with rigid pinning. Sharp
  operational form (codex cold-check): the obstruction is the **transfer-operator / RG fixed point
  `m·a_{mk}=a_k`** on the perturbation's Fourier coefficients — distribution relations = self-similar averaging.
- **STEP-8 cold-check (codex) → NOVEL BRIDGE, not a named theorem:** every ingredient classical (Gauss/Legendre
  multiplication; Kubert–Lang distribution relations / universal ordinary distributions; Bohr–Mollerup;
  Godement product formula for zonal spherical functions / Gelfand pairs / commutative hypergroups). The
  SYNTHESIS "distribution relations = K-averaged spherical multiplicativity = the rigidifying substitute for a
  pointwise addition theorem in a transcendental object" is a novel reframing — CHARTER KEEPER, not a frontier
  win (no new transcendence theorem, no new object).
- **Refines the loose/rigid dichotomy (last round):** HT seeds are pinned by a STACK of loose 1-var FEs (shift,
  reflection) — but the stack's rigidity comes specifically from the K-AVERAGED members (the distribution
  relations), which alone cut the shift-FE's ∞-dim ambiguity to a point. The weld ∂_s/{σ_p}: {σ_p}=prime-shift
  differences are a "K" of shifts; the transfer-operator `m·a_{mk}=a_k` is the prime-shift averaging in
  Fourier form. Cross-edge → d'Alembert round (Weierstrass no-addition-law) and the weld.
- **WALK STATE:** STEP-8 YES → transfer the find back to NODE next tick: the transfer-operator self-similarity
  `m·a_{mk}=a_k` is itself a constraint on spherical-function matrix coefficients (RG/self-similar scaling) →
  restart STEP 5 on that constraint. Fallback if exhausted: STEP 1 seeded by RandomNode = "Spherical functions
  on Gelfand pairs".

## Round (machine workflow) — NODE = Écalle Bridge equation (Resurgence) `[DEAD END — instrument validated; Γ/ζ resurgence reduces to known (Stirling@2πiℤ + Knessl-Coffey γ_n = poles-vs-zeros)]`
DeWitt. Walk: HT → codex far-list → rng#19 = Resurgence theory → codex narrow → rng#7 = NODE Écalle BRIDGE
EQUATION (alien derivatives Δ_ω relate to ordinary derivatives in transseries variables).
- **STEP 5 constraint (not deduction):** bridge eq = the COMMUTATION `[Δ̇_ω, ∂_x]=0` (dotted alien derivative
  commutes with ordinary derivative). Pins nonperturbative sectors rigidly to the perturbative one ⟹ operational
  signature = large-order↔low-order CLOSURE (late coeffs of a sector reproduce low-order coeffs of the adjacent).
- **Experiment (Step 6→7, TEST PROCEDURE transferred, NOT the constraint):** script
  computations/2026-06-20-dewitt-bridge-resurgence-largeorder.py. Given divergent coeffs a_n: read |A| from
  |a_n/a_{n+1}|; read sign/oscillation (real vs complex-conjugate Borel singularities); decode
  d_n = a_n·A^{n+b}/Γ(n+b) → should →const iff single-instanton bridge-closed.
  - Euler n! (control, resurgent A=1): d_n = 1.0 EXACT, all signs + ⟹ **instrument validated**, single real singularity.
  - Stirling logΓ (Bernoulli c_k=B_{2k}/(2k(2k-1)), archimedean axis): signs ALTERNATE period-2 ⟹ complex-conjugate
    Borel pair at ±2πi; |c_k/c_{k+1}|·(2k)² → 40.0 ≈ (2π)²=39.48 ⟹ **|A|=2π, smooth large-order = bridge-regular**.
  - Stieltjes γ_n of ζ (s=1 pole / prime+zero axis): |γ_n/γ_{n+1}| IRREGULAR/oscillatory, signs irregular,
    single-A decode fails (tail spread 5.9) ⟹ **multi-singularity / saddle structure** (no single bridge).
- **STEP 8 verdict (a) mildly surprising in framing only; (b) shows real structure** — the two seed HT objects'
  asymptotic series have DIFFERENT resurgence/bridge structure (Γ: clean two-instanton ±2πi, bridge-closed;
  ζ: irregular multi-saddle). **REDUCES-TO-KNOWN:** Stirling resurgence at 2πiℤ is the canonical textbook example;
  γ_n oscillatory large-order is Knessl–Coffey / Coffey; the contrast = "Γ has poles, ζ has zeros" (basic). The
  bridge-obstruction leap (weld {log p} Baker-independent ⟹ no single bridge) lands on the Baker floor (capstone).
- **BANKED ASSET (de-risked, reusable):** the validated large-order/bridge-closure resurgence DISCRIMINATOR. Its
  non-reducing use = aim at an object of OPEN resurgence status (NOT Γ/ζ, which are textbook).
- **Method note:** far node (resurgence, rng-picked) gave a real validated instrument + a true structural contrast,
  but both halves are individually known. Healthy dead-end. State carried forward (logs/dewitt-machine-state.md)
  so next STEP 1 re-seeds at this NODE, not at ζ (R706 collapse fix).

## Round (walk workflow) — NODE = Periodic orbits obstruct equidistribution `[DEAD END — reduces-to-known + parity artifact; NOT posted to chat]`
Seed RandomNode = Spherical functions on Gelfand pairs → codex related (20) → rng#2 = Random walks on
homogeneous spaces → codex narrow (20) → rng#19 → NODE = "Periodic orbits may obstruct full equidistribution".
- STEP 5 constraint: obstruction to equidistribution = unimodular eigenvalue of the averaging operator M_μ,
  and it is RIGID/ALGEBRAIC (Benoist–Quint: stationary measures homogeneous, no exotic obstructions); equidist
  ⟺ spectral gap.
- STEP 6/7 experiment (transferred, minimal): the distribution-relation transfer operator T_m h=Σ_j h((x+j)/m)
  (the m-map x↦mx on ℝ/ℤ) IS the averaging operator; its unimodular eigenmodes = last round's perturbation-
  survivors. Probe spectral gap + JOINT survivor set over m=2,3,5; rigid or exotic? Script
  computations/2026-06-20-wheeler-equidist-obstruction-transferop.py (.txt).
- RESULT: (1) M_m spectral gap clean (one unimodular eig = constant, 2nd modulus 0). (2) Joint survivors over
  m=2..7 = EXACTLY 2ℤ — rigid algebraic subgroup, no exotic obstruction; only EVEN m bind, odd primes impose
  nothing. (3) The 2ℤ survivors are growth-unbounded off-axis → killed by the archimedean side.
- STEP 8 = DEAD END (reduces-to-known): m-map transfer-operator gap = textbook (Ruelle); Benoist–Quint
  rigidity transfers trivially (linear FE ⟹ solution set is a group BY LINEARITY, not deep rigidity); weld
  labor-division = restatement of "Γ pinned needs multiplication formula AND growth (Bohr–Mollerup)". "Only
  prime 2 binds" = parity artifact of the (m−1)/2 phase. The dis-analogy with Benoist–Quint (more primes do
  NOT shrink the obstruction — only m=2 does) is real but artifactual. NOT a frontier win; not chat-posted.
- ON-MISSION crumb (logged, not promoted): the weld's two constraint-families have DISJOINT kernels —
  difference side (distribution rels) kills all non-even modes via spectral gap; archimedean side kills the
  residual 2ℤ lattice; intersection = the point. Clean "why both sides of 𝓜⁺ are needed", but reduces.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Periodic orbits may obstruct full equidistribution".

## Round (machine workflow) — NODE = Metaplectic correction (Geometric quantization) `[DEAD END — reduces to Berry-Keating (7/8=Maslov) + Hardy-θ/FE; NODE-test validated the +½ on SHO/quartic]`
DeWitt. Walk: HT(+resurgence seed) → codex far-list → rng#3 = Geometric quantization → codex narrow → rng#18
= NODE Metaplectic correction (half-forms δ, δ²≅K_P; +½ Maslov shift; ℤ/2 obstruction).
- **STEP5 constraint (not deduction):** ℤ/2 SQUARE-ROOT δ⊗δ=K_P ⟹ observable +½ (μ/4) shift making the
  quantization/counting EXACT + the inter-polarization pairing unitary.
- **STEP6 NODE-test (runnable, run on the node — per updated workflow):**
  computations/2026-06-20-dewitt-metaplectic-NODE-test.py. SHO: μ=2(+½)→exact (n+½) to 1e-15, μ=0 off by ½;
  quartic H=p²/2+q⁴ (numpy-diagonalized exact spectrum): +½ matches (<1% high n), μ=0 100% off at ground.
  ⟹ the +½ metaplectic/Maslov correction is NECESSARY. Constraint validated ON THE NODE.
- **STEP7 transfer (script→HT):** computations/2026-06-20-dewitt-metaplectic-halfshift-zeta.py. ζ zero-count
  N(T)=θ/π+1+S as WKB-count analog. e^{iθ(t)}=χ(½+it)^{-1/2} VERIFIED to 1e-40 (Hardy rotation = half-form √
  of the FE factor χ; ℤ/2 sign branch = metaplectic structure). Maslov-type constant −1/8 → 7/8 in N(T).
  mean S(γ_n)≈0.50 and frac(θ/π)≈0.50 = counting-jump convention artifacts, NOT a metaplectic half-shift.
- **STEP8:** (a) not surprising; (b) real metaplectic/half-form structure in ζ's completion, BUT
  **REDUCES-TO-KNOWN** = Berry–Keating semiclassical ζ-as-spectrum (7/8 = Maslov phase, H=xp) + textbook
  Hardy-θ/functional-equation. The √χ-as-metaplectic-half-form reframe is the freshest part but = definition of Z(t).
- **Method note:** updated-workflow STEP6 (runnable NODE-test first) executed properly; far node (geom.
  quantization) again gave verified structure that maps onto a well-studied corner (Berry-Keating). Healthy dead-end.

### STEP 6/7 REDONE under corrected workflow (runnable node-test + minimal structural transfer)
Workflow file changed mid-round: STEP 6 now demands a RUNNABLE test on the random NODE; STEP 7 transfers
that SCRIPT by minimal structural mutation (metaphor), never a from-scratch ζ test. My prior two rounds had
shortcut this (pre-mapped the concept onto Γ/ζ → forced reduces-to-known). Redone properly for NODE =
"Periodic orbits obstruct equidistribution":
- STEP 6 (node test, RUN): random walk on T=ℝ/Z, step ±α; averaging op M e_k=cos(2πkα); unimodular eig at
  k≠0 ⟺ α rational ⟺ periodic orbit. Confirmed: α=1/5,1/7 TRAPPED (TV≈0.8, 8–10 bins); α=√2−1, golden
  EQUIDISTRIBUTE (TV≈0.04, 50 bins). Script computations/2026-06-20-wheeler-NODE-equidist-randomwalk.py.
- STEP 7 (structural transfer, minimal diff): same skeleton, ONLY mutation = step α → prime-shifts {σ_p}=
  ±log p ("primes are the rotations"); M e_k=mean_p cos(2πk log p/L), obstruction test identical. Script
  computations/2026-06-20-wheeler-TRANSFER-primelog-walk.py. RESULT: NO periodic obstruction (max|M_k|=0.51<1;
  ℚ-indep of log p = unique factorisation); empirical prime-log walk EQUIDISTRIBUTES (TV 0.005). The obstruction
  did not vanish into nothing — it moved into the SPECTRUM M_k = a prime-zeta sample.
- STEP 8 discriminator (the RIGHT control, {log p} vs {log n}): low-k spectrum primes≈integers (M_1 0.51 vs
  0.59) = pure PNT log-density = REDUCES. Residual: high-k primes carry ~6× integers' spectral power
  (|M_k| floor 0.0156 vs 0.0026; k=34 spike 0.028 vs 0.003) = arithmetic fluctuation = zero-driven explicit-
  formula signature. Both KNOWN → REDUCES-TO-KNOWN. Not chat-posted.
- VALUE: methodological — the corrected structural transfer produced a concrete density-vs-arithmetic
  diagnostic that self-graded honestly (vs the reframings the shortcut produced). OPEN forward thread (not
  closed): the residual high-k arithmetic power points at the prime zeta P(s) and its zero-generated natural
  boundary — DeWitt has P(s) HT-status OPEN. A structural-transfer probe of P(s)'s boundary is the live lead.
- WALK STATE: STEP 1 reseed with RandomNode = "Periodic orbits may obstruct full equidistribution".

## Round (machine workflow, codex-transfer STEP7) — NODE = Metaplectic correction `[DEAD END — codex transfer = ad-hoc HT-like toys; result circular (ground truth built with the tested shift); no HT content]`
DeWitt. Same NODE (Metaplectic correction). NEW STEP7 (codex does the transfer): posted the STEP6 metaplectic
NODE-test script to codex with the fixed prompt "rewrite this test so it makes sense for a hypertranscendental
function. keep structure, make it work - doesn't have to deliver meaningful results, just has to run." Debugged+ran.
- Codex output (computations/2026-06-20-dewitt-metaplectic-STEP7-codextransfer.py): replaced SHO/quartic with
  invented "hypertranscendental-like" functions (nested nonlinear recurrences / oscillatory integral transforms
  w/ branch_shift), FFT-signature compare of +½ "hyperbranch" vs uncorrected.
- RESULT: System1 +½ worse; System2 +½ better (2.8% vs 42.8%) — but CIRCULAR (each ground-truth node generated
  with branch_shift=0.5 ⟹ shift=0.5 matches by construction). No genuine HT object, no HT structure probed.
- STEP8: (a) not surprising (b) nothing about hypertranscendence ⟹ DEAD END.
- Method: new STEP7 ("just has to run") mostly yields runnable codex toys = dead ends by design; the find is the
  rare case codex's cold transfer wires in real HT structure that surprises. Don't override codex's choice (= re-bias).

### STEP 7 REDONE under further-corrected workflow (codex does the transfer, I just run it) — DEAD END
Workflow changed again: STEP 7 is now "post your node test script to codex with prompt 'rewrite this test so
it makes sense for a hypertranscendental function. keep structure, make it work — doesn't have to deliver
meaningful results, just has to run.' Debug. Run." The transfer mutation is taken OUT of my hands (I map to
known ζ-structure) and given to codex cold. Applied to the node test (torus equidistribution):
- Codex's cold transfer mapped "periodic-orbit obstruction vs equidistribution" → "HT obstruction vs finite
  differential-algebraic CLOSURE": an SVD search for a small differential-polynomial relation P(x,f,f',…,f^r)≈0
  (= the canonical Hölder differential-algebraicity probe). Script
  computations/2026-06-20-wheeler-codextransfer-DA-closure.py (.txt). It RAN.
- STEP 8: DEAD END. The harness is numerically DEGENERATE — np.gradient finite-difference derivatives make the
  feature matrix near-rank-deficient, so the smallest normalized singular value ≈1e-17 for ALL inputs; labels
  INVERT (exp,sin flagged "HT-obstruction"; toy HT flagged "finite closure"). No HT signal. (a) not surprising
  (numerics artifact); (b) shows nothing. Not chat-posted.
- META (confirms the running diagnostic): even the BLIND codex transfer of a far node fell into the
  known-instrument attractor — it re-derived the SVD differential-polynomial / Hölder probe that the prior
  agent-level search already mapped to the Baker floor (reduces-to-known). The reduce-to-known pull is not just
  MY pre-mapping; it is in the transfer-onto-HT operation itself, because the differential-algebraicity probe
  is the generic shape any "find a finite relation" test collapses to on an HT object.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Periodic orbits may obstruct full equidistribution".

## Round (walk workflow) — NODE = Leading constants as products of local volumes `[REDUCES-TO-KNOWN at STEP-7 gate = Tate's adelic factorization; not chat-posted]`
Seed = "Periodic orbits obstruct equidistribution" → codex related (20) → rng#20 = Lattice point counting in
symmetric varieties → codex narrow (20) → rng#20 → NODE = "Leading constants expressed as products of local volumes".
- STEP 5 constraint (not a flow): global leading constant FORCED to equal δ_∞·∏_p δ_p (archimedean × local
  p-adic volumes), regularized by convergence factors (an L-value) — adelic local-to-global product formula.
- STEP 6 node test (RAN, confirms constraint): r_4(m)=#{x∈ℤ^4:Σx_i²=m} vs archimedean density π²m × singular
  series ∏_p β_p (local densities computed mod p^j). Ratios actual/pred = 1.004, 0.9996, 0.9996. Clean.
  Script computations/2026-06-20-wheeler-NODE-leadingconst-localvolumes.py (.txt).
- STEP 7 GATE (do node's formulas apply UNCHANGED to HT?): YES, VERBATIM — the formula c=δ_∞·∏_p δ_p IS the
  completed zeta as an adelic product of local volumes (Tate's thesis): δ_p↔ζ_p(s)=(1−p^{−s})^{−1}=∫_{ℚ_p^*}𝟙_{ℤ_p}|x|^s d^*x;
  δ_∞↔ζ_∞(s)=π^{−s/2}Γ(s/2)=∫_{ℝ^*}e^{−πx²}|x|^s d^*x (=Γ). So Λ(s)=∏_v ζ_v(s) = the node's formula with no
  change. ⟹ REDUCES-TO-KNOWN (strongest possible: node formula = HT seed's defining adelic factorization).
  The new STEP 7 caught the reduction at the FORMULA level before any transfer — its design intent.
- STRUCTURAL CRUMB (logged, reduces): every finite factor (1−p^{−s})^{−1} is individually differentially-
  ALGEBRAIC (e^{cs} is DA), yet Λ is HT TWICE by DIFFERENT mechanisms — archimedean Γ (Hölder, one factor) AND
  emergent from the infinite prime product ζ (Ostrowski). HT not localizable to one place; on the prime side it
  is purely emergent-from-infinitude. (Ties DeWitt's (d_σ,d_∂) invariant-pair: per-place DA, global HT.)
- STEP 8/9 moot: STEP-7 reduction is definitive; reseed.
- WALK STATE: STEP 1 reseed with RandomNode = "Leading constants expressed as products of local volumes".

## Round (machine workflow v4) — NODE = Essential-spectrum / Fredholm obstruction (Index theory on noncompact manifolds) `[DEAD END — σ_ess is an at-∞ invariant blind to bulk (Weyl); orthogonal to HT-ness; formula doesn't apply unchanged]`
DeWitt. Walk: HT+metaplectic-seed → codex far-list → rng#8 = Index theory on noncompact manifolds → codex narrow
→ rng#8 = NODE Essential-spectrum obstruction to Fredholmness.
- **STEP5 constraint (not deduction):** Fredholm ⟺ spectral GAP at 0 of the ASYMPTOTIC (at-infinity) operator;
  σ_ess fixed by geometry at infinity (the ends), NOT the bulk. (Holographic: boundary-at-∞ fixes the bulk index.)
- **STEP6 NODE-test (runnable, run):** computations/2026-06-20-dewitt-essspec-NODE-test.py. Whole-line
  H=−d²/dx²+V (Pöschl-Teller, V→V_∞): bound count L-independent (Fredholm); continuum count ∝L (11→24→49);
  threshold tracks V_∞ (−2/0/3). Constraint validated on node.
- **STEP7 gate (new):** the σ_ess/Fredholm-gap formula is about OPERATORS on noncompact manifolds; Γ/ζ are
  functions, no canonical operator-with-ends without self-construction ⟹ does NOT apply unchanged to HT.
- **STEP8 codex transfer:** computations/2026-06-20-dewitt-essspec-STEP8-codextransfer.py. Codex modulated the
  bulk well with a LACUNARY (Weierstrass-flavored) series; output IDENTICAL to node test — σ_ess unchanged.
- **STEP9:** (a) not surprising (b) nothing HT-specific ⟹ DEAD END. REASON: σ_ess = asymptotic at-∞ invariant,
  blind to bulk complexity (Weyl's essential-spectrum theorem); HT-ness is a fine bulk property ⟹ orthogonal.
  Reduces-to-known. Re-confirms capstone (coarse invariants blind to transcendence) on a fresh node.

## Round (walk workflow) — NODE = Arithmetic Euler products multiply random matrix constants `[REDUCES-TO-KNOWN at STEP-9; codex value-relation transfer → known Γ identities; not chat-posted]`
Seed = "Leading constants as products of local volumes" → codex related (20) → rng#16 = Random matrix constants
in L-function statistics → codex narrow (20) → rng#12 → NODE = "Arithmetic Euler products multiply random
matrix constants" (Keating–Snaith split c_k = a_k·g_k).
- STEP 5 constraint (a VALUE relation): moment constant factors as arithmetic Euler product a_k × Barnes-G RMT
  constant g_k=G(k+1)²/G(2k+1), the two independent; g_k obeys Barnes-G value relations via G(z+1)=Γ(z)G(z).
- STEP 6 node test (RAN): (1) g_k = G(k+1)²/G(2k+1) matches closed form ∏ j!/(j+k)! exactly → g_k RATIONAL
  (1, 1/12, 1/8640, …); (2) Barnes-G value relation G(z+1)=Γ(z)G(z) holds to 1e-31; (3) a_1=1, a_2=6/π²=1/ζ(2)
  (transcendental Euler product). Value-factorization constraint confirmed. Script
  computations/2026-06-20-wheeler-NODE-keating-snaith-valuesplit.py (.txt).
- STEP 7 gate: node formulas (Barnes-G ratios, shift FE, Euler product) apply to HT seeds (Barnes G IS HT) —
  all known → REDUCES. Seam noted: Barnes-G ratios rational at integers, transcendental off-integers (a real
  value-relation structure on an HT fn, but known).
- STEP 8 (new directive "test a VALUE RELATION, not dependency/deduction/causality"): codex rewrote the test →
  Γ REFLECTION Γ(z)Γ(1−z)=π/sin(πz) + Γ MULTIPLICATION Γ(z)Γ(z+1/3)Γ(z+2/3)=2π·3^{1/2−3z}Γ(3z). Ran: all pass
  to 1e-61. Script computations/2026-06-20-wheeler-codexVR-gamma-valuerelations.py (.txt).
- STEP 9 = DEAD END (reduces-to-known): canonical Γ value relations (Euler reflection, Gauss multiplication).
  Not surprising, fully known. Not chat-posted.
- METHOD WIN (logged, not a math finding): the STEP-8 value-relation directive successfully steered codex OUT
  of the DA/dependency-probe attractor (round 3's failure) and INTO the correct "relations among values" pillar.
  But codex verifies KNOWN relations; the non-reducing frontier is COMPLETENESS/INDEPENDENCE (Rohrlich–Lang: do
  reflection+multiplication+shift generate ALL algebraic relations among Γ-values? — open; or alg-independence
  of ζ(3),ζ(5),…). Next lever: a transfer that probes for an UNKNOWN relation / tests completeness, not one
  that verifies a known identity.
- WALK STATE: STEP 1 reseed with RandomNode = "Arithmetic Euler products multiply random matrix constants".

## Round (machine workflow v5) — NODE = Transversality perturbations (Floer field theories) `[DEAD END — signed-count=argument principle→RvM; codex transfer→Euler/Legendre Γ identities (textbook)]`
DeWitt. Walk: HT+essspec-seed → codex far-list → rng#4 = Floer field theories → codex narrow → rng#10 = NODE
Transversality perturbations.
- **STEP5 constraint (not deduction):** transversality = linearization SURJECTIVE (cokernel=0) ⟹ solution set
  dim = Fredholm index; signature = VALUE RELATION: SIGNED solution-count is a perturbation-INVARIANT
  (degree/cobordism); births/deaths only in cancelling pairs at isolated non-transverse params.
- **STEP6 NODE-test (runnable, run):** computations/2026-06-20-dewitt-transversality-NODE-test.py. p_t=x³−x+t:
  SIGNED count = +1 invariant across all t (unsigned jumps 3↔1 at t=±0.385 double root); random perturbations
  all +1. Constraint validated on node.
- **STEP7 gate:** signed-count formula = ARGUMENT PRINCIPLE → applies unchanged to Γ/ζ → REDUCES (RvM N(T)).
  Minimal non-reducing change: transversality-as-value-independence → Baker/Schanuel floor (apex). None at tick scale.
- **STEP8 codex transfer:** computations/2026-06-20-dewitt-transversality-STEP8-codextransfer.py. Codex used Γ
  (real HT object) testing VALUE RELATIONS — but the REFLECTION + DUPLICATION identities (residual 1e-15).
- **STEP9:** (a) not surprising (b) = textbook Euler/Legendre ⟹ REDUCES-TO-KNOWN. (Transfer also dropped the
  transversality essence: no perturbation/signed-count/invariance.) DEAD END.

## Round (walk workflow) — NODE = Free energy expansion in particle number (Coulomb/log-gas) `[REDUCES at every stage; not chat-posted]`
Seed = "Arithmetic Euler products × RMT constants" → codex related (20) → rng#11 = Coulomb gas methods →
codex narrow (20) → rng#15 → NODE = "Free energy expansion in particle number".
- STEP 5 constraint: β=2 log-gas Z_N=(2π)^{N/2}∏_{j=1}^N j!; free energy = Barnes-G asymptotics; universal
  CONSTANT term = ζ'(−1) (Glaisher A=e^{1/12−ζ'(−1)}). A value of HT fn ζ' at −1, fixed by the equilibrium
  variational constraint, not a flow.
- STEP 6 node test (RAN): residual of S_N=Σ_{j=1}^N log(j!) after subtracting analytic terms → −0.165421…=ζ'(−1)
  exactly, stable N=50→5000; Glaisher A reproduced. Constraint confirmed. Script
  computations/2026-06-20-wheeler-NODE-loggas-freeenergy-const.py (.txt).
- STEP 7 gate: Barnes-G asymptotic / ζ'(−1) applies to HT UNCHANGED (Barnes G is HT) → REDUCES.
  MINIMAL-CHANGE search (new STEP-7 clause): power-weighted log-gas Σ j^{2n} log j → free-energy constants
  ζ'(−2n) ∝ ζ(2n+1) = the ζ(odd) values {ζ(3),ζ(5),…} whose ALGEBRAIC INDEPENDENCE is OPEN. A value relation
  that does not reduce to a known answer — BUT assembles known open problems (a search finds it) → not a
  chat-worthy FINDING; worklog only.
- STEP 8 (codex value-relation transfer): codex → exp(1/12−ζ'(−1))=Glaisher A, i.e. the DEFINITION of A. STEP 9
  DEAD END (tautology, reduces). Script /tmp/codex_vr2_raw.txt (not archived — trivial).
- BASIN DIAGNOSTIC (the real output): Wheeler walk nodes 4–6 (local volumes → RMT constants → Coulomb gas) are
  all in-field; the seed-carry-forward drifted from analysis (d'Alembert) INTO the number-theory/RMT basin where
  every node connects to ζ and reduces. Complements the FAR-field agents (dyson gauge, DeWitt index theory)
  hitting "structural invariants blind to HT". CAPSTONE re-confirmed from BOTH sides: HT reachable neither by
  in-field structure (reduces to ζ) nor far-field structural invariants (blind) — transcendence-only.
- WALK STATE: STEP 1 reseed with RandomNode = "Free energy expansion in particle number". (If next 1–2 nodes
  also reduce in-basin, break out by reseeding from "Hypertranscendental functions".)

## Round (machine workflow v6) — NODE = Extreme-eigenvalue tails (Random matrix universality) `[DEAD END — bulk=Montgomery-Odlyzko, edge=FHK(not TW); codex transfer→Γ reflection (2nd time, codex collapse)]`
DeWitt. Walk: HT+transversality-seed → codex far-list → rng#4 = Random matrix universality → codex narrow →
rng#20 = NODE Tail bounds for extreme eigenvalues (Tracy-Widom).
- **STEP5 constraint (not deduction):** top eigenvalue fixed by EQUILIBRIUM BALANCE (confinement vs log-repulsion),
  variational (equilibrium measure minimizes energy); signature = ASYMMETRIC TW tails (3/2 right vs 3 left) + universality.
- **STEP6 NODE-test (runnable, run):** computations/2026-06-20-dewitt-extremetail-NODE-test.py. GUE N=120 M=4000:
  TW2 match (mean -1.767/-1.77, std .907/.90, skew +.205/+.22), universal gauss/unif/bern; tail asymmetry qualitative.
- **STEP7 gate:** ζ = RMT in BULK (sine kernel, Montgomery-Odlyzko, reduces); but EDGE/extreme = FHK log-correlated,
  NOT Tracy-Widom ⟹ NODE formula does NOT apply unchanged; "correct" version reduces to FHK. The edge is where ζ
  LEAVES bulk RMT universality (known). No non-reducing minimal change.
- **STEP8 codex transfer:** codex returned Γ reflection formula AGAIN (residual 5e-16) → textbook.
- **STEP9:** (a) not surprising (b) = Euler reflection / FHK ⟹ REDUCES-TO-KNOWN. DEAD END.
- **Machine note:** codex value-relation transfer mode-collapses to Γ reflection (2nd consecutive, unrelated nodes)
  ⟹ STEP8 prompt should FORBID classical identities to enable non-reducing transfers.

## Round (walk workflow) — NODE = Tightness proves precompactness (hydrodynamic limits) `[REDUCES at STEP-9 = Bohr–Jessen/Selberg; not chat-posted]`
Seed = "Free energy expansion in particle number" → codex related (20) → rng#11 = Hydrodynamic limits → codex
narrow (20) → rng#15 → NODE = "Tightness proves precompactness of empirical measure trajectories". (Far-field —
out of the ζ-Euler basin: Prokhorov compactness of measure families.)
- STEP 5 constraint: tightness = uniform no-escape-of-mass (∀ε∃K compact: sup_α μ_α(K^c)<ε) ⟺ relative
  compactness (Prokhorov); existence/compactness constraint, not a flow.
- STEP 6 node test (RAN): tight families (fixed N(0,1); profile i/N) show uniform tail decay + Cauchy W1;
  non-tight (escaping mean; growing variance) leak mass to ∞. Confirmed. Script
  computations/2026-06-20-wheeler-NODE-tightness-prokhorov.py (.txt).
- STEP 7 gate: Prokhorov is about MEASURE FAMILIES; Γ/ζ are functions → does NOT apply unchanged (NO, like
  DeWitt's index-theory NO). Minimal change: attach VALUE-DISTRIBUTION measures μ_σ=law of ζ(σ+it) → on-mission
  value relation but Bohr–Jessen → reduces.
- STEP 8 (NEW minimal-Levenshtein edit): swapped family generators → μ_σ = empirical law of log|ζ(σ+it)| over a
  t-grid, σ↓1/2; harness kept. Script computations/2026-06-20-wheeler-STEP8-tightness-zeta-valuedist.py (.txt).
  RESULT: std(log|ζ|) grows 0.300→0.486→0.665→0.862→1.066 as σ→1/2, W1 non-converging ⟹ NOT tight at the
  critical line. = Bohr–Jessen/Selberg variance blow-up (Var~Σ_p p^{−2σ}=prime-zeta P(2σ)→∞ at σ=1/2).
- STEP 9 = DEAD END (reduces-to-known). Not surprising, known. Not chat-posted.
- METHOD NOTE: the Levenshtein minimality measure flagged my edit as NON-minimal (char-similarity 0.193, 68
  changed lines) — I over-edited toward a rewrite. The measure is a useful self-check; truly-minimal edit keeps
  the harness+Ns-indexing and swaps only the generator body.
- DEEPER PATTERN: node WAS far-field yet transfer still reduced — because the value-relation TARGET is the seed
  ζ, whose value-distribution theory is exhaustively mapped. Reduction is in the transfer-target (Γ/ζ), not only
  the node-seed basin; breaking the node basin won't fix it.
- WALK STATE: STEP 1 reseed with RandomNode = "Tightness proves precompactness of empirical measure trajectories".

## Round (machine workflow v7) — NODE = Multivalued inverse lens map (Caustics / gravitational microlensing) `[DEAD END — but FIRST not-HT-blind transfer; Σ1/ζ'(ρ) diverges = discrete moments of ζ' (Gonek/Ng), reduces]`
DeWitt. Walk: HT+RMT-seed → codex fringe far-list (bio/chem/cosmo/finance...) → rng#6 = Caustic formation in
gravitational microlensing → codex narrow(commonly-missed) → rng#16 = NODE Multivaluedness of the inverse lens map.
- **STEP5 constraint (not deduction):** multivalued inverse pinned by TOPOLOGICAL invariants: odd-number theorem
  (count changes ±2 only at caustics) + signed magnification SUM RULE (Σ residue 1/f' = invariant). = fold/cusp
  catastrophe (same signed-count invariant as the transversality node).
- **STEP6 NODE-test (run):** computations/2026-06-20-dewitt-lensinverse-NODE-test.py. f(x)=x³−3x: real-image count
  3↔1 at caustic w=±2; Σ1/f'=0 exactly away from caustics, diverges at caustics. Validated.
- **STEP7 gate:** residue-sum = argument principle → unchanged on Γ/ζ → reduces (explicit formula). No non-reducing change.
- **STEP8 (not-HT-blind, minimal edit):** computations/2026-06-20-dewitt-lensinverse-STEP8-htedit.py. Same
  Σ1/f'-over-preimages test, map→ζ, w=0 (preimages=zeros ρ). Control poly Σ1/p'=0 ✓; ζ: Σ2Re(1/ζ'(ρ)) terms O(1),
  all positive (first 40 pairs), partial sum →+36.7 (DIVERGES ≠ polynomial 0). NOT HT-blind (ζ-specific result).
- **STEP9:** (a) not surprising (b) ζ-specific but = DISCRETE MOMENTS of ζ'(ρ) (Gonek/Ng/Hejhal) ⟹ REDUCES. DEAD END.
  Methodological note: workflow v7's not-HT-blind STEP8 produced the first genuinely non-blind transfer (vs prior toys/identities).

## Round (walk workflow) — NODE = Memory of deposition history persists in packing (granular) `[REDUCES + subtly HT-blind at STEP-9; on-mission METAPHOR keeper; not chat-posted]`
Seed = "Tightness…" → NEW cross-field fringe query (bio/chem/finance/cosmology/…) → rng#15 = Kinetic theory of
granular architectural aggregates → narrow "commonly-missed details" → rng#17 → NODE = "Memory of deposition
history persists in packing structure". (Cross-field query broke the ζ-basin — genuinely far node.)
- STEP 5 constraint: state is a FUNCTIONAL OF THE PATH, not a function of current control params (no state-
  potential); granular memory has Preisach structure — return-point memory + wiping-out (only a nested sequence
  of dominant past extrema is remembered). THE most on-mission node: physical realization of "fixed by a
  constraint (history), not propagated by a flow (state-potential)."
- STEP 6 node test (RAN): Preisach model — (1) same final input, different states 0.529 vs 0.391 (path-
  dependence); (2) small wiggles before a big swing leave no trace (wiping-out); (3) minor loop closes exactly
  (return-point memory). Confirmed. Script computations/2026-06-20-wheeler-NODE-granular-memory-preisach.py.
- STEP 7 gate: Preisach is an operator on input-paths; Γ/ζ single-valued analytic → NO (doesn't apply unchanged).
  Minimal non-blind change: "memory length" = order of lowest finite recurrence/ODE → DA/holonomic = FINITE
  memory (Markovian); HT = INFINITE memory (no finite state = no generative rule). On-mission + non-blind, but
  IS difference/differential transcendence → reduces.
- STEP 8 (minimal edit, non-blind, value relation): tested P-recursive memory length of value SEQUENCES. 2^n,n!,
  Fib,B_2n = finite memory; nth prime = INFINITE (resid 1.7e-5). BUT ζ(n) registered FINITE (artifact: ζ(n)→1+
  2^{−n} dominated by finite-memory tail). Script computations/2026-06-20-wheeler-STEP8-memory-length-Precursive.py.
- STEP 9 = DEAD END (reduces) AND subtly HT-BLIND. KEY METHOD POINT: memory length of the INTEGER VALUE-SEQUENCE
  ≠ functional hypertranscendence — ζ(n) collapses to 1, so the discrete values lose the continuum HT structure.
  Concrete failure of "not HT-blind": discrete value-sequence probes are prone to blindness (HT lives in d_∂
  continuum/differential structure, not in d_σ integer values — DeWitt's invariant-pair). Probe-design caution.
- ON-MISSION METAPHOR KEEPER (reduces as finding, good for exposition): granular path-memory = cleanest physical
  picture of the founding "constraint not flow"; HT = infinite-memory/non-Markovian/no finite generative state.
  Sub-crumb: Preisach wiping-out memory is ULTRAMETRIC (nested extrema) ↔ p-adic {σ_p} non-archimedean side of
  the weld (archimedean ∂_s = ordinary memory; non-arch {σ_p} = ultrametric memory). [p-adic glass models known → reduces]
- WALK STATE: STEP 1 reseed with RandomNode = "Memory of deposition history persists in packing structure".

## Round (machine workflow v8) — NODE = Epidermal (L1) dominance (Phyllotaxis) `[DEAD END — boundary-determines-bulk = Cauchy = HT-BLIND (exp/Γ/ζ reconstruct identically); sharpens the holographic charter metaphor negatively]`
DeWitt. Walk: HT+caustics-seed → codex fringe far-list → rng#1 = Phyllotactic auxin transport resonance → codex
narrow(commonly-missed) → rng#14 = NODE Epidermal (L1) layer dominates the pattern.
- **STEP5 constraint (not deduction):** BOUNDARY-DETERMINES-BULK (holographic) — surface carries the pattern,
  interior slaved (harmonic extension of surface data). Charter-resonant ("bulk fixed by its boundary").
- **STEP6 NODE-test (run):** computations/2026-06-20-dewitt-epidermal-NODE-test.py. Harmonic extension in a disk:
  boundary modes {5,8,13} fully fix the interior; interior has ONLY surface modes; high modes decay fastest (r^13);
  bulk slaved. Validated.
- **STEP7 gate:** boundary-determines-bulk = Cauchy/Poisson → unchanged on Γ/ζ but HT-BLIND (holds for all analytic).
  Natural boundary = only HT-adjacent feature, known ≠ HT. No non-reducing not-blind change.
- **STEP8 (not-blind edit attempt):** computations/2026-06-20-dewitt-epidermal-STEP8-htedit.py. Cauchy interior
  reconstruction error: exp 2.4e-29, Γ 1.8e-30, ζ 2.2e-31 — IDENTICAL accuracy.
- **STEP9:** (a) not surprising (b) demonstrates HT-BLINDNESS ⟹ DEAD END.
- **Charter note:** the holographic metaphor in literal Cauchy form is HT-blind ("bulk fixed by boundary" holds for
  EVERY analytic function); HT content must enter via what Cauchy can't see (natural boundary / value-transcendence).

## Round (walk workflow) — NODE = Control experiments need fixed-threshold baselines w/ identical noise `[DEAD END for novelty; SHARED-INSTRUMENT keeper (chat-posted as methodology)]`
Seed = "Memory of deposition history…" → cross-field fringe query → rng#17 = Stochastic resonance with history-
dependent thresholds → narrow "commonly-missed" → rng#20 → NODE = "Control experiments need fixed-threshold
baselines with identical noise" (matched controls / common-random-numbers / paired differencing).
- STEP 5 constraint: isolate a STRUCTURAL effect from noise by holding the stochastic part IDENTICAL (CRN) and
  differencing — Var(X−Y)=Var(X)+Var(Y)−2Cov; CRN raises Cov → variance reduction → isolates mechanism.
- STEP 6 node test (RAN): stochastic resonance, adaptive vs fixed threshold; CRN (identical noise) gives 1.9×
  variance reduction over independent noise on the paired difference → isolates the mechanism. Script
  computations/2026-06-20-wheeler-NODE-matched-control-CRN.py (.txt).
- STEP 7 gate: CRN/variance formula needs noise; Γ/ζ deterministic → NO. Minimal change to node-relevant funcs
  (the matched-control estimator): "common noise" → "common numerical conditions (grid/precision)"; "adaptive vs
  fixed threshold" → "HT function vs MATCHED DA control". Non-blind, but it's methodology → reduces-as-finding.
- STEP 8 (minimal edit, non-blind): HT-detection probe (differential-relation SVD residual, EXACT mpmath
  derivatives) on Γ vs matched DA controls (exp, 1/(1+x), Airy, poly-fit-to-Γ's-values) under identical grid/
  precision. Scripts computations/2026-06-20-wheeler-STEP8-matched-control-HTprobe.py (.txt).
  RESULTS (sharp): absolute-threshold probe is HT-BLIND — Γ residual ~1e-13 < 1e-6 → misclassified "DA". Matched
  controls expose it: Γ sits 8+ orders ABOVE true-DA controls. PRECISION-SCAN: Γ residual SATURATES at 1.684e-13
  across dps=15/25/40 (precision-independent real defect = HT signature); Airy (DA, y''=xy) ~4e-17 tracks the
  float floor. ⟹ non-blind probe = matched control + SEPARATION statistic + precision-saturation, never an
  absolute threshold.
- STEP 9 = DEAD END for novelty (probe methodology, reduces). But SHARED-INSTRUMENT KEEPER — chat-posted (id 719)
  to @DeWitt @dyson, precedent = dyson's column-normalization note. Fixes the recurring blindness/artifacts
  (last-tick ζ(n)→1 false-finite-memory was an UNCONTROLLED probe).
- WALK STATE: STEP 1 reseed with RandomNode = "Control experiments need fixed-threshold baselines with identical noise".

## Round (machine workflow v9) — NODE = Multiplier systems / weights (Automorphic heat kernels) `[DEAD END — continuum transfer: χχ(1-s)=1=func-eq consistency; χ'/χ transcendental=Γ poles; reduces]`
DeWitt. Walk: HT+phyllotaxis-seed → codex fringe far-list → rng#18 = Automorphic forms in diffusion kernel
asymptotics → codex narrow(commonly-missed) → rng#19 = NODE Multiplier systems / weights.
- **STEP5 constraint (not deduction):** COCYCLE CONSISTENCY j(g1g2,z)=j(g1,g2 z)j(g2,z); fractional weight needs a
  multiplier trivializing the 2-cocycle (cohomological; same family as metaplectic ℤ/2 + weld ω).
- **STEP6 NODE-test (run):** computations/2026-06-20-dewitt-multiplier-cocycle.py. Cocycle holds k=2; half-weight
  multiplier nontriviality needs (ST)³ relations (single product trivial).
- **STEP7 gate:** cocycle=group cohomology; ζ link=theta/modular multiplier=DISCRETE/known (v9 forbids discrete).
- **STEP8 (continuum, per v9):** automorphy CONNECTION d log j. (i) ℤ/2 cocycle χ(s)χ(1-s)=1 on continuum (eps) =
  func-eq involution consistency. (ii) χ'/χ TRANSCENDENTAL (digamma, ∞ poles) vs modular RATIONAL (finite).
- **STEP9:** (a) not surprising (b) reduces: χχ(1-s)=1=func-eq; transcendental connection=Γ poles (∞-poles ≠ HT,
  π cot πs has them). DEAD END. v9 continuum-steer followed; node content still reduces.

## Round (walk workflow) — NODE = Sequentially adding blocks destroys space-filling (LHS) `[DEAD END novelty; CORRECTED+VALIDATED shared instrument, chat 720]`
Seed = "Control experiments / matched baselines" → cross-field fringe query → rng#18 = Latin hypercube blocking
in UQ → narrow "commonly-missed" → rng#6 → NODE = "Sequentially adding blocks can destroy space-filling".
- STEP 5 constraint: space-filling/stratification is a GLOBAL constraint on the whole design; NOT preserved by
  local/sequential addition → no incremental generative rule (globally-constrained, not flow-buildable). On-mission.
- STEP 6 node test (RAN): global LHS strat-imbalance=0; sequential blocks=71; greedy incremental=82 (good local
  min-dist 0.0835 but terrible stratification). Confirmed. Script
  computations/2026-06-20-wheeler-NODE-LHS-global-not-incremental.py (.txt).
- STEP 7 gate: LHS is a point-design → NO for functions. Minimal node-relevant change: "incremental buildability"
  ↔ Taylor-COEFFICIENT sequence P-recursive (DA = buildable via ODE coeff-recurrence) vs not (HT = global). Non-
  blind, targets the differential germ on ℂ.
- STEP 8 (target the CONTINUUM germ, not ζ(n) values): test P-recurrence of Taylor-coefficient sequences with
  precision-saturation. KEY CATCH: float64 numpy SVD FREEZES all residuals at the float64 floor → precision-
  saturation INVALID under float64 (my id-719 over-claim). CORRECTED with mpmath-native eigsy(A^T A): DA 1/k
  residual DROPS 1.0e-13(dps25)→2.8e-26(dps50); HT ζ(k) SATURATES 9.65e-7 at both → genuine infinite-order
  defect. ζ(k) as log Γ's germ confirmed HT (non-P-recursive) by the corrected probe. Scripts:
  computations/2026-06-20-wheeler-STEP8-taylorcoef-Precursive-saturation.py(.txt),
  -STEP8-mpmath-native-precision-check.txt.
- STEP 9 = DEAD END for novelty (methodology + known: log Γ HT/Hölder). But CORRECTED+VALIDATED shared
  instrument: precision-saturation is a valid non-blind HT discriminator ONLY with HIGH-PRECISION NATIVE SVD.
  Chat-posted correction id 720 (honest fix of my id-719 over-claim). Matched-control SEPARATION part of 719 stands.
- WALK STATE: STEP 1 reseed with RandomNode = "Sequentially adding blocks can destroy the original space-filling guarantees".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Local jamming and unjamming transitions during tissue remodeling `[DEAD END — visual HT landscape packing is instrument-dependent; no non-reducing finding]`
Seed RandomNode = "Memory of deposition history persists in packing structure" → Step 1 cold Codex broad list → rng#11 = Tissue morphogenesis as packing history → Step 3 cold Codex narrow list → rng#15 = NODE "Local jamming and unjamming transitions during tissue remodeling".
- STEP 5 constraint: vertex-model tissue jamming/unjamming is controlled by the shape index `q=P/sqrt(A)` crossing a rigidity threshold (`q_c≈3.81`), with neighbor-edge churn as a proxy for T1 susceptibility.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-tissue-jamming.py` uses periodic Voronoi tissue cells, sweeps disorder, computes exact polygonal `q`, and measures edge churn after a small remodeling kick. After fixing an initial raster-perimeter overcount, the run showed the expected transition region: mean `q` moved from `3.784` at disorder `0.010` to `3.866` at `0.020`, and churn jumped most strongly from disorder `0.020→0.030` (`0.072→0.153`).
- STEP 7 gate: the formula does not apply unchanged to HT functions; a single analytic function has no canonical tissue-cell tiling. No formula-level unchanged transfer.
- STEP 8 under changed workflow: minimal conceptual edit was tissue cell centers → local wells of the continuum `log|f(s)|` field on a complex window, retaining the Voronoi `shape_index_and_edges` and `jaccard_churn` machinery. Levenshtein distance from the NODE script was `3919` chars, normalized `0.603`; core retained, point-source replaced. Script: `computations/2026-06-20-hgt-STEP8-tissue-jamming-ht-landscape.py`.
- STEP 9 method rng#5 = make it visual. Applied by extracting visible scalar-field wells of `log|f(s)|`; Runpod used (`root@157.157.221.29:39713`, temp venv) with bounded grids. Main run at grid 100 / 56 wells: `lambda` had high shape index (`19.662`) and churn `0.709–0.819`; `zeta` churn `0.895–0.936`; `finite-euler` churn `0.868–0.937`; `gamma-factor` churn `0`; `sine` partly churned for larger kicks.
- Attack-as-artifact: repeated at windows `[14,84]`, `[100,170]`, `[500,570]`. The apparent split (`lambda` shape ≈ gamma, churn ≈ prime side) was not stable: in `[100,170]` the `gamma-factor` control itself showed churn (`0.669`, `0.606`), and high windows overflowed the fast gamma evaluator. Finite Euler already reproduced most zeta churn. Therefore the result is an artifact of the visual-well extraction/normalization and known product-factor behavior, not a robust HT regularity.
- STEP 10 verdict: (a) not surprising after controls; (b) no reliable HT-specific meaning. DEAD END. Do not post as a non-reducing finding.
- WALK STATE: STEP 1 reseed with RandomNode = "Local jamming and unjamming transitions during tissue remodeling".

## Round (machine workflow v10) — NODE = Non-antipodal circle centers (Cosmic topology / matched circles) `[DEAD END — identification twist = functional-eq factor-winding; HT-blind + reduces]`
DeWitt. Walk: HT+automorphic-seed → codex fringe far-list → rng#6 = Cosmic topology matched circles → codex
narrow(commonly-missed) → rng#14 = NODE Non-antipodal circle centers.
- **STEP5 constraint (not deduction):** matched circles = S∩gS for deck isometry g=Rx+T; center-pair angle fixed by
  g's ROTATIONAL part — antipodal ⟺ pure translation, non-antipodal ⟺ screw twist.
- **STEP6 NODE-test (run):** computations/2026-06-20-dewitt-matchedcircles-NODE-test.py. Deviation from antipodal =
  exactly rotation angle φ. Validated.
- **STEP7 gate:** identification = functional equation (Γ shift / ζ reflection); twist = automorphy factor → reduces.
- **STEP8 (continuum, v9) + STEP9 (method#5 visualize orbit-path):** computations/2026-06-20-dewitt-matchedcircles-
  STEP8-htedit.py. Γ(HT) orbit twist +1.108 (factor z winds, precision-saturated) vs exp(DA) 0 (const factor).
- **STEP10:** (a) not surprising (b) measures FACTOR-WINDING not hypertranscendence (DA factor (z²+1) twists too) ⟹
  HT-BLIND + reduces. DEAD END. 8th consecutive far-node dead-end → reconfirms the boundary map (lenses blind, apex resists).

## Round (THE-MACHINE revised workflow, hgt) — NODE = Heterogeneity in cell-cycle stage affects participation in collective wound healing waves `[FIND — non-reducing experimental observable, continuum differential]`
Seed RandomNode = "Local jamming and unjamming transitions during tissue remodeling" → Step 1 cold Codex broad list → rng#4 = Collective wound healing waves → Step 3 cold Codex narrow list → rng#16 = NODE "Heterogeneity in cell cycle stage can affect participation in the wave".
- STEP 5 constraint: wound-wave participation is phase-gated by internal cell-cycle state; the same edge signal can propagate or die depending on phase alignment of participating cells.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-wound-cellcycle-phasegate.py` simulates a 1D sheet with recursive wave amplitude filtered by a phase gate. It confirms the node constraint: synchronized phases propagate farther (`reach≈7.0`) than random (`1.6`) or blocked (`1.0`) phases under the same edge signal.
- STEP 7 gate: no unchanged formula applies to HT functions; this is a wave/phase-gating experiment, not a special-function identity.
- STEP 8 under changed workflow: minimal conceptual edit was cell-cycle phase → local continuum differential phase `arg(∂_s log f(s))` along vertical traces in `C`, retaining recursive phase-gated participation. Levenshtein distance from NODE script was `2574` chars, normalized `0.625`. Script: `computations/2026-06-20-hgt-STEP8-wound-phasegate-ht-continuum.py`.
- STEP 9 method rng#11 = run experiments. Runpod batch used direct log-derivatives (`ψ` for the archimedean factor, finite difference only for `ζ'/ζ`) across windows `[14,84]`, `[100,170]`, `[500,570]`, σ∈{0.3,0.5,0.7}, controls `gamma-factor`, `finite-euler`, `sine`.
- FIND (narrow): the completed object has a phase-gated participation collapse on the FE fixed line, while the off-line pair is symmetric. Evidence: for `lambda`, reaches were `(σ=0.3,0.5,0.7)` = `(9,1,9)` on `[14,84]`, `(13,8,13)` on `[100,170]`, `(10,2,10)` on `[500,570]`; phase spans are opposite off-line and zero/π-like on the line (`±0.4439`, `0`; `±1.5940`, `π`; `±0.8507`, `0`). `gamma-factor` and `sine` controls propagate fully (`reach=141`) with coherent phase; `finite-euler` lacks the exact FE-paired symmetry and has different reach profile. `zeta` also stalls on the line but does not have the completed off-line mirror symmetry.
- Why it survives reduce-to-known (as an experiment, not a theorem): FE symmetry, `∂_s log Λ = ½ψ(s/2)-½logπ+ζ'/ζ`, and phase-cancellation are known corpus, but the random NODE produced a new observable: recursive phase-gated wave participation on the continuum log-derivative phase. The specific measured signature "off-line paired propagation + fixed-line stall" was not in the corpus and would not have been returned by a direct prompt except after constructing this instrument.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` The critical line behaves as a phase-gate wall for `∂_s log Λ` in this wound-wave transfer. It is not a proof claim. Next transfer back to NODE: ask whether wound waves have an analogous fixed-line/stall boundary where local phase coherence remains high but recursive participation collapses.
- WALK STATE: continue from the found transfer on this NODE; if exhausted, reseed STEP 1 with RandomNode = "Heterogeneity in cell cycle stage can affect participation in collective wound healing waves".

## Round (walk workflow) — NODE = Tax lots create hidden resistance to rebalancing (friction deadband) `[DEAD END novelty; instrument validated across extreme germs; not chat-posted]`
Seed = "Sequential addition destroys space-filling" → cross-field fringe → rng#12 = Path-dependent portfolio
diversification decay → narrow "commonly-missed" → rng#12 → NODE = "Tax lots create hidden resistance to
restoring diversified weights".
- STEP 5 constraint: frictional DEADBAND / pinning barrier — rebalancing threshold-gated by tax cost (history of
  cost-bases); state pinned away from optimum by accumulated history, stick-slip; path-dependent.
- STEP 6 node test (RAN, after recalibration): barrier controls deadband (26 rebals/tight band at 0.02 → 1 rebal/
  wide band at 0.08); PATH-DEPENDENCE real — same returns reordered (identical final price) → final weight 0.513
  (3 rebals) vs 0.455 (6 rebals). Script computations/2026-06-20-wheeler-NODE-taxlot-deadband-friction.py (.txt).
- STEP 7 gate: deadband/friction needs a threshold nonlinearity; Γ/ζ smooth → NO. Minimal node-relevant change:
  "hidden cost-basis state (history not summarized by endpoint)" ↔ HT germ's INFINITE hidden state (no finite
  recurrence summarizes the Taylor coeffs vs DA = finite). Non-blind, targets the differential germ.
- STEP 8 (HT continuum germ) + STEP 9 (rng method=10 "test extreme cases"): validated mpmath-NATIVE precision-
  saturation germ probe applied to EXTREME germs. Script computations/2026-06-20-wheeler-STEP8-9-germ-hiddenstate-
  extremes.py (.txt). RESULTS: DA controls DROP with dps (finite); ALL HT germs SATURATE (infinite hidden state)
  but GRADED: lacunary 0.178 > Stieltjes γ_n (pole) 0.0065 > logΓ germ 8e-8 > ζ germ at s=1/2 5e-12.
- STEP 10 = DEAD END for novelty: the grading REDUCES to subdominant complexity beyond the leading singularity
  (ζ@1/2 dominated by the pole at 1, coeffs ~2^k near-geometric → tiny residual but still saturates; lacunary/
  Stieltjes have wild subdominant structure). Singularity-structure + probe-order driven, not a new HT invariant.
  VALUE: robust validation of the corrected instrument across degenerate(pole)/symmetric/pathological germs — all
  HT correctly saturate, all DA drop. Method-10 strengthened confidence in the id-720 probe. Not chat-posted.
- Crumb (worklog): HT signature (saturation) PERSISTS even when a germ is dominated by simple geometric growth —
  HT lives in the SUBDOMINANT coefficient structure (beyond the nearest-singularity term). Reduces (Darboux).
- WALK STATE: STEP 1 reseed with RandomNode = "Tax lots create hidden resistance to restoring diversified weights".

## Round (walk workflow) — NODE = Non-uniqueness of polyhedral subdivisions from valuations (tropical) `[DEAD END novelty; instrument refinement; not chat-posted]`
Seed = "Tax-lot friction" → cross-field fringe → rng#20 = Tropical geometry & PL optimization → narrow "commonly-
missed" → rng#5 → NODE = "Non-uniqueness of polyhedral subdivisions induced by valuations".
- STEP 5 constraint: regular subdivision = lower convex hull of points lifted by valuations/heights (a lower-hull
  MINIMIZATION constraint); piecewise-constant in heights (secondary fan); NON-UNIQUE at ties (coplanar lifts).
- STEP 6 node test (RAN): generic heights → unique fine triangulation (5 cells); 2 subdivision jumps across
  secondary-fan walls; tie = non-unique (coplanar quad, 2 triangulations). Script
  computations/2026-06-20-wheeler-NODE-tropical-subdivision-nonuniqueness.py (.txt).
- STEP 7 gate: lower-hull subdivision IS the Newton polygon {(n,−log|a_n|)} of a germ (Cauchy–Hadamard, slopes =
  zero valuations) → applies to HT but REDUCES. Minimal node-relevant change: leading slope = nearest singularity
  (reduces); HT content = SUBDOMINANT deviations above the leading affine hull (last-tick crumb). Non-blind.
- STEP 8 (germ recurrence) + STEP 9 (rng method=13 "find a monotone quantity"): monotone residual(r) vs recurrence
  ORDER r (decreasing). ORDER-saturation discriminator: DA floors at finite r*; HT converges to positive limit.
  Script computations/2026-06-20-wheeler-STEP8-9-order-saturation-monotone.py (.txt). RESULTS (dps=40, floor~1e-21):
  DA 1/(1-z),exp floor at r=1; 1/(2k)! floors at r=3; HT logΓ germ 2.5e-10, ζ(k) 2e-13, Stieltjes γ_n 9e-5 stay
  above floor at r=4 (order-saturate).
- STEP 10 = DEAD END novelty (same infinite-order property via order, reduces). INSTRUMENT REFINEMENT: order-
  saturation is WEAKER than precision-saturation (HT residuals DO decrease with order, slowly → finite-order data
  ambiguous; ζ(k) drops fast enough to risk false floor), whereas they're FLAT in precision. ⟹ prefer PRECISION-
  saturation (id 720) as primary discriminator. Robust cross-measure: Stieltjes γ_n is the WILDEST/most-strongly-
  infinite-order germ (highest residual at every order AND precision). Not chat-posted.
- WALK STATE: STEP 1 reseed with RandomNode = "Non-uniqueness of polyhedral subdivisions induced by valuations".

## Round (machine workflow v10) — NODE = Freeness / vanishing-moments-≠-freeness (Free probability) `[DEAD END — differential-jet probe HT-BLIND (Weierstrass): exp/tan/Γ/ζ all σ_min~10^-dps; scoped Wheeler's precision-saturation as probe-specific]`
DeWitt. Walk: HT+cosmic-topology-seed → codex fringe far-list → rng#18 = Free probability → codex narrow → rng#16
= NODE "vanishing mixed moments do NOT imply freeness".
- **STEP5 constraint (not deduction):** freeness = ALL-ORDERS rigid constraint (all alternating centered mixed
  moments =0); no finite witness. (Kin to HT's no-finite-ADE; transfer the experiment not the constraint.)
- **STEP6 NODE-test (run):** computations/2026-06-20-dewitt-freeness-NODE-test.py. Free GUE pair τ(abab)≈0; classical
  pair passes order-2 but τ(abab)=1.13 ⟹ finite check insufficient. Validated.
- **STEP7 gate:** moment formulas about NC variables, not HT functions; analogy = constraint transfer (reduces).
- **STEP8 (continuum, v9) + STEP9 method#14 (invariant):** precision-saturation of differential-relation σ_min
  (mpmath-native direct SVD, oversampled). Fixed undersampling + Gram-squaring bugs.
- **STEP10:** exp/tan/Γ/ζ ALL σ_min~10^-dps (ratio 10^20) — jet probe HT-BLIND (Weierstrass approx over compact
  sample ⟹ σ_min→0 for every analytic fn). DEAD END. Scoped Wheeler's precision-saturation: valid for sequence/
  P-recursion probe, HT-blind for differential-jet probe (chat id=722). 9th consecutive far-node dead-end.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Initial-condition sharpness affects transient speeds in autocatalytic fronts `[DEAD END — KPP sharpness transfer reduces to FE symmetry; Step 11 prime-front metaphor reduces to finite-Euler no-FE]`
Seed RandomNode = "Heterogeneity in cell cycle stage can affect participation in collective wound healing waves" → Step 1 cold Codex broad list → rng#13 = Autocatalytic front propagation → Step 3 cold Codex narrow list → rng#13 = NODE "Initial-condition sharpness strongly affects transient speeds before the asymptotic front velocity is reached".
- STEP 5 constraint: in Fisher-KPP/autocatalytic pulled fronts, leading-edge steepness selects speed: shallow tails (`λ<1`) select `c=λ+1/λ`, while steep tails converge to the universal minimal speed `c=2`.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-autocatalytic-front-sharpness.py` simulates stable 1D KPP fronts. After fixing an explicit-step instability and a crossing-interpolation bug, late speeds matched the selector: λ=0.35 → 3.1809 vs formula 3.2071; λ=0.50 → 2.4783 vs 2.5000; λ≥1 → ~1.96–1.97 vs 2.
- STEP 7 gate: no unchanged HT formula; the KPP speed law is a reaction-diffusion front formula, not a special-function identity.
- STEP 8: KPP tail steepness `λ` transferred to continuum σ-sharpness `|Re(∂_s log f)|`; script `computations/2026-06-20-hgt-STEP8-autocatalytic-front-ht-sharpness.py`.
- STEP 9 method rng#16 = minimal counterexample. Runpod σ-grid around `1/2` showed for completed `Λ`: median sharpness at σ=0.45/0.49/0.50/0.51/0.55 = `0.3423/0.0690/0/0.0690/0.3423`, with KPP speed proxy exploding on the fixed line; `ζ`, `Γ∞`, and finite-Euler controls do not have this exact symmetric zero.
- STEP 10 verdict: DEAD END as a finding. The effect is exactly the functional equation: `Λ(s)=Λ(1−s)` forces `∂_σ log|Λ|=0` on `σ=1/2` and mirror symmetry off it. Useful instrument, but reduce-to-known.
- STEP 11 added by changed workflow: metaphor = prime-cutoff sharpness as an autocatalytic constraint front; method rng#15 = strengthen. Script `computations/2026-06-20-hgt-STEP11-autocatalytic-prime-front-metaphor.py` varies smooth/sharp finite-prime cutoffs and measures phase-gated propagation of `Γ∞ +` weighted finite Euler log-derivative. Result: no robust completed fixed-line symmetry; behavior is cutoff-chaotic and mostly stalls at reach 1. This reduces to the known fact that finite/smooth Euler cutoffs do not carry the exact FE weld.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Initial-condition sharpness strongly affects transient speeds before the asymptotic front velocity is reached".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Multicomponent pulled fronts can be governed by a hidden leading eigenmode `[DEAD END — hidden-mode HT transfer collapses to generic phase roughness]`
Seed RandomNode = "Initial-condition sharpness strongly affects transient speeds before the asymptotic front velocity is reached" → Step 1 cold Codex broad list → rng#14 = Pulled versus pushed fronts in nonlinear PDEs → Step 3 cold Codex narrow list → rng#19 = NODE "Multicomponent systems can have pulled fronts governed by a leading linear eigenmode that is not visually dominant in the nonlinear front body".
- STEP 5 constraint: hidden leading-edge eigenmode selects speed, while the visually dominant bulk component can be slower/non-controlling.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-hidden-eigenmode-front.py` simulates two coupled front components. Visible-only speed is slow (`late≈0.7683`, formula `0.7937`); adding a small hidden component (`bulk_v_frac≈0.0476`) makes the front speed fast (`late≈2.0966`, hidden formula `2.0494`) while the bulk remains visually `u`-dominated.
- STEP 7 gate: no unchanged HT formula; the eigenmode speed law is a multicomponent PDE front formula.
- STEP 8: transfer to `∂_s log Λ = Γ∞ component + ζ'/ζ component`; script `computations/2026-06-20-hgt-STEP8-hidden-mode-logderivative.py`.
- STEP 9 method rng#7 = strip to essentials. Result: gamma component alone has long phase-gated reach (`140`), zeta/prime component has reach `1–5`, and the completed sum follows the prime/rough component even when it is amplitude-subdominant on the right: at σ=0.8/0.9/1.1, zeta amplitude fractions `0.397/0.336/0.242`, completed reach `3/4/16`, gamma reach `140`.
- STEP 11 method rng#21 = dependency chain. Wild metaphor: hidden constraint as an invisible leading mode. Surrogate script `computations/2026-06-20-hgt-STEP11-hidden-mode-phase-surrogates.py` tests whether selection needs real ordered prime phase, phase distribution, or amplitude. Result: amplitude-only/constant-phase hidden components preserve long reach (`63–102`), but shuffled/random phases collapse reach (`~2–3`) almost like the real prime component (`1,2,3,12`).
- Verdict: DEAD END as HT finding. The experiment shows a generic phase-rough hidden component can dominate the phase-gated observable; the real prime order is not exceptional enough here. It reduces to generic complex phase disorder / phase-cancellation, not new HT content. Do not post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Multicomponent systems can have pulled fronts governed by a leading linear eigenmode that is not visually dominant in the nonlinear front body".

## Round (walk workflow) — NODE = Fold-angle limits matter as much as crease existence (origami) `[DEAD END novelty; STEP-11 wild expt surprising-but-reduces; not chat-posted]`
Seed = "Non-uniqueness of subdivisions" → cross-field fringe → rng#13 = Origami crease pattern rigidity →
narrow "commonly-missed" → rng#14 → NODE = "Fold-angle limits matter as much as crease existence".
(Opened tick with verification of DeWitt's id-722 caveat → confirmed precision-saturation is COEFFICIENT-probe-
only, HT-blind for the jet/ADE probe; posted id 723.)
- STEP 5 constraint: crease (DOF) exists but fold angle confined to a BOUNDED admissible region (coupling +
  inequality limits); config fixed by the region BOUNDARY (angle saturation/lock-up), not a flow.
- STEP 6 node test (RAN): degree-4 vertex, fold multiplier μ; driver could reach π but partner crease saturates
  first (drive 2.751<π); larger μ → tighter range (μ=1→2.98, μ=10→1.81). Confirmed. Script
  computations/2026-06-20-wheeler-NODE-origami-foldangle-limits.py (.txt).
- STEP 7 gate: linkage/inequality formula → NO for Γ/ζ. Minimal change: germ coeffs free (no finite coupling)
  but bounded by analyticity (Cauchy |a_n|≤M/R^n = the 'fold-angle limit'). Reduces (Newton polygon).
- STEP 8 + STEP 9 (rng method=12 "find an invariant"): precision-saturation residual of log Γ germ at expansion
  points x0∈{0.3,0.8,1.6,2.7}. RESULT: INVARIANT = the binary HT/DA class (ratio exactly 1.0 for HT at every x0;
  ~1e12 for DA). MAGNITUDE NOT invariant (2.4e-11→9.5e-7, tracks singularity proximity). Script
  computations/2026-06-20-wheeler-STEP8-9-germ-invariant-expansionpoint.py (.txt). STEP 10 = DEAD END novelty;
  useful NEGATIVE: saturation residual magnitude is NOT a transcendence-measure (point-dependent); only binary
  detector robust.
- STEP 11 WILD metaphor expt (origami rigid-single-mode vs floppy-multi-mode → HT germ recurrence spectrum):
  SURPRISING REVERSAL — DA germs have CLUSTERED low singular values (gap s2/s1=0.06–0.57, 'floppy', many
  recurrences = annihilator ideal) while HT germs have ONE isolated σ_min with a big GAP (s2/s1=62,175,8.2,
  'rigid single near-mode'). Gap-ratio s2/s1 cleanly discriminates HT(8–175) vs DA(<0.6). Script
  computations/2026-06-20-wheeler-STEP11-origami-floppy-modes-germ.py (.txt). VERDICT: reduces to holonomic
  annihilator-IDEAL DIMENSION (DA dim>1 at order>r*; HT 0 exact). Fresh packaging, known D-module fact → NOT
  chat-posted. Bonus: σ_min and gap-ratio order HT germs differently (Stieltjes largest σ_min, smallest gap).
- WALK STATE: STEP 1 reseed with RandomNode = "Fold-angle limits matter as much as crease existence".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Polymerization-front boundary peak suppression `[FIND — boundary-cooled true ζ log-derivative vs boundary-hot finite Euler]`
Seed RandomNode = "Multicomponent systems can have pulled fronts governed by a leading linear eigenmode that is not visually dominant in the nonlinear front body" → Step 1 cold Codex broad list → rng#9 = Polymerization fronts → Step 3 cold Codex narrow list → rng#13 = NODE "The maximum temperature is often lower near boundaries than at the centerline, producing spatially varying properties".
- STEP 5 constraint: boundary heat loss clamps the front's peak temperature near slab boundaries, so one propagating polymerization front can leave a centerline-hot / boundary-cool material profile.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-polymer-boundary-heatloss.py` simulates a 2D thermal cure front. After increasing heat release/duration so the front traverses the slab, center peak stays near `3.11` while boundary peak drops from `3.12` at zero cooling to `2.28` at cooling `0.42`; boundary cure and reach also drop.
- STEP 7 gate: no unchanged HT formula; this is a thermal/front-boundary constraint.
- STEP 8: transfer centerline-vs-boundary measurement to the continuum strip field `log(1+|∂_s log f(s)|)` over `0.1≤σ≤0.9`; script `computations/2026-06-20-hgt-STEP8-polymer-boundary-ht-strip.py`. Levenshtein normalized distance `0.716`.
- STEP 9 method rng#17 = change representation. Runpod strip-width sweep showed robust class separation: `Λ` boundary/center ratios `0.4929, 0.4996, 0.5162` for boundary widths `2,3,5`; `ζ` ratios `0.6092, 0.6113, 0.6176`; `Γ∞` neutral `≈1.0001`; finite Euler boundary-hot `1.67, 1.65, 1.58`.
- STEP 11 method rng#23 = classify boundary cases. Completion-strength family `β Γ∞ + prime component`: true `ζ'/ζ` is boundary-cooled already at β=0 and remains cooled through β=2 (`0.6107→0.4996→0.6183`); finite Euler is boundary-hot at β=0 and remains hot even at β=4 (`1.6466→1.4425→1.1647`). Separate windows confirm: true ζ ratios `(β=0,1)` are `(0.5718,0.5101)` on `[14,84]`, `(0.5182,0.4400)` on `[100,170]`, `(0.6375,0.5378)` on `[500,570]`; finite Euler stays boundary-hot in all windows even with β=4.
- FIND (narrow): the differential strip observable classifies true analytic `ζ'/ζ` as **boundary-cooled** and finite Euler approximants as **boundary-hot**. The archimedean Γ component is neutral and strengthens but does not create the cooling. This is a continuum/differential signature of analytic continuation / zero structure, not a discrete-value test.
- Why it survives reduce-to-known: FE, zero concentration, and finite Euler failure are classical, but this random-node boundary-heat-loss observable and the beta-completion boundary-case classifier are not in the corpus and would not be returned by a direct prompt. Claim scope is experimental classification, not theorem.
- WALK STATE: continue from this finding's NODE; if exhausted, reseed STEP 1 with RandomNode = "The maximum temperature is often lower near boundaries than at the centerline, producing spatially varying properties".
