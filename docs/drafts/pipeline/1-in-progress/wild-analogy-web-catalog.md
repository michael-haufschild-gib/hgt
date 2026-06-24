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

## Round (THE-MACHINE revised workflow, hgt) — NODE = Numerical discretizations can approximate the wrong fractional operator `[DEAD END — nonlocal-window operator mismatch reduces to boundary/finite-window effects]`
Seed RandomNode = "The maximum temperature is often lower near boundaries than at the centerline, producing spatially varying properties" → Step 1 cold Codex broad list → rng#19 = Fractional diffusion on bounded domains → Step 3 cold Codex narrow list → rng#14 = NODE "Numerical discretizations can accidentally approximate a different fractional operator than the one intended".
- STEP 5 constraint: on a bounded domain the fractional operator is defined by its boundary/exterior mechanism. Interior-only regional/censored jumps, restricted zero-exterior killing, and spectral Dirichlet fractional powers are different constraints, not discretization details.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-fracdiff-operator-mismatch.py` strips the node to regional vs restricted vs spectral operators on `[0,1]`. Runpod result: regional mass stayed `1.00000000` with zero row sums; restricted mass fell to `0.92901215` with edge row sum `479.5`; spectral mass `0.96564170` with different eigenvalues. The NODE constraint is real.
- STEP 7 gate: the bounded-domain fractional Laplacian formulas do not apply unchanged to HT functions. Minimal non-blind edit: retain regional-vs-exterior nonlocality but replace the thermal profile by the continuum differential strip field `g_f(t)=log(1+|∂_s log f(σ+it)|)`.
- STEP 8/9 method rng#7 = strip to essentials. Script `computations/2026-06-20-hgt-STEP8-fracdiff-exterior-ht-strip.py` compares regional, actual-exterior, and zero-exterior fractional operators for `Λ`, `ζ`, `Γ∞`, finite Euler, and sine over windows `[14,84]`, `[100,170]`, `[500,570]`.
- STEP 10 verdict: DEAD END. `Λ` retains FE-paired symmetry off-line and finite Euler differs, but the diagnostic is dominated by window/exterior conventions: `Γ∞` and sine controls become degenerate under the same operator mismatch, finite Euler changes sign/window class, and the stable part reduces to the previous boundary-cooling/finite-window observation plus the backlog warning `ht-c27-boundary-nonlocality` (finite/local windows cannot certify HT). No non-reducing finding; do not post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Numerical discretizations can accidentally approximate a different fractional operator than the one intended".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Multiple optimal noise levels for different spatial modes `[DEAD END — HT transfer collapses to zero/roughness sensitivity]`

- STEP 1 from previous RandomNode `The maximum temperature is often lower near boundaries than at the centerline, producing spatially varying properties`; rng pick 9 -> `Stochastic resonance in spatially extended systems`.
- STEP 4 rng pick 15 -> NODE `The existence of multiple optimal noise levels for different spatial modes`.
- STEP 5 constraint: in a spatially extended stochastic-resonance system, each Fourier/spatial mode has a different Laplacian-shifted barrier or damping rate, so the noise level maximizing coherent response can split by mode rather than being universal.
- STEP 6 NODE script `computations/2026-06-20-hgt-NODE-spatial-sr-mode-optima.py` validates the constraint in a reduced bistable-mode model: modes 1,2,3 peak at `D=0.086,0.058,0.026` respectively.
- STEP 8/9 script `computations/2026-06-20-hgt-STEP8-sr-mode-noise-ht-jitter.py`; method rng#6 = ask what action is happening. Minimal HT change: mode/noise grid becomes lock-in of `log(1+|d/ds log f(s)|)` under horizontal jitter on `s=1/2+amp*cos(k phase)+noise+it` for `Λ`, `ζ`, `Γ∞`, and finite Euler controls.
- STEP 10 verdict: DEAD END for novelty. The clean NODE split does not transfer. The output mainly says `ζ`/`Λ` are jitter-amplified by analytic-continuation/zero roughness, `Γ∞` is flat, and finite Euler controls are smoother or have finite optima. That is a useful control but reduces-to-known/promptable, so it was not chat-posted.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Parameter signs matter in ultradiscrete limits `[FIND — max-plus phase-carrier defect separates true analytic ζ from finite Euler]`
Seed RandomNode = "Numerical discretizations can accidentally approximate a different fractional operator than the one intended" → Step 1 cold Codex broad list → rng#20 = Ultradiscrete limits in integrable systems → Step 3 cold Codex narrow list → rng#4 = NODE "Parameter signs matter because the standard limit assumes positive dependent variables and parameters".
- STEP 5 constraint: the ultradiscrete `ε log`/max-plus limit is constrained by positivity/subtraction-free form. Opposite signs or complex phases require an auxiliary sign/parity carrier; otherwise dominant balances can collapse.
- STEP 6 NODE test: `computations/2026-06-20-hgt-NODE-ultradiscrete-signs.py` confirms the constraint. Positive cases converge to `max(A,B)`; an opposite-sign exact tie gives `-inf` for every ε even though `max=2`; near ties converge only after exposing subdominant sign data.
- STEP 7 gate: the positive max-plus formula does not apply unchanged to HT functions because `∂_s log Λ` is a complex sum. Minimal non-blind edit: keep the max-plus failure statistic, but supply the continuum differential weld `∂_s log Λ = Γ∞ + P` and measure the missing phase/sign carrier by `Δ=max(log|Γ∞|,log|P|)-log|Γ∞+P|`.
- STEP 8/9 method rng#19 = change representation. Script `computations/2026-06-20-hgt-STEP8-ultradiscrete-phase-defect.py`; main output `computations/2026-06-20-hgt-ultradiscrete-sign-phase-defect.txt`; P80 stress output `computations/2026-06-20-hgt-STEP8-ultradiscrete-phase-defect-p80.txt`.
- FIND (narrow): the scalar max-plus representation fails persistently for true analytic `ζ'/ζ` against the archimedean Γ component on the analytic-continuation side, while finite Euler controls do not reproduce it. P80 finite-Euler stress: at `σ=0.3` over windows `[14,84]`, `[100,170]`, `[500,570]`, true zeta has median defect `0.315574,0.419294,0.549147` and positive-defect fraction `0.8,1.0,1.0`; finite Euler has median `0.00178232,-0.00273536,-0.0230106` and positive fraction `0.505556,0.488889,0.477778`. On the fixed line `σ=0.5`, true zeta has heavier defect tails (`q99=4.53831,5.35261,3.4457`) than finite Euler (`q99=1.86997,1.52039,1.77387`).
- Why it survives reduce-to-known (as an experiment, not a theorem): FE, σ-parity, and phase-cancellation are in the corpus, and the tropical/zeta-values frame itself is failed. But the random ultradiscrete sign NODE produced a new continuum differential observable: the scalar max-plus sign-carrier defect for the archimedean-prime log-derivative weld, with a finite-Euler prime-count stress separation. This statistic was not in the corpus and is not a direct special-function identity. Claim scope is experimental classification only.
- Posted to `#research` as Dyson id=731.
- WALK STATE: continue from this finding's NODE; if exhausted, reseed STEP 1 with RandomNode = "Parameter signs matter because the standard ultradiscrete limit assumes positive dependent variables and parameters".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Low-frequency colored noise escapes shallow basins but drifts `[DEAD END — HT transfer reduces to FE mirror symmetry]`

- STEP 1 seed `The existence of multiple optimal noise levels for different spatial modes`; rng pick 15 -> `Colored noise optimization`.
- STEP 4 rng pick 8 -> NODE `Low-frequency noise can help escape shallow basins but may also cause slow drift around optima`.
- STEP 5 constraint: equal marginal noise power is not enough; the correlation time changes whether perturbations cross shallow barriers or merely make slow excursions around an optimum.
- STEP 6 NODE script `computations/2026-06-20-hgt-NODE-colored-noise-shallow-basin.py`; method rng#16 = minimal counterexample. In a tilted double well, escape fraction rises from `0.0000` at tau 0 to `0.9708` at tau 32, while tail drift grows from `0.0918` to about `0.70`.
- STEP 8/9 script `computations/2026-06-20-hgt-STEP8-colored-noise-ht-strip.py`. Minimal HT transfer: colored horizontal drift around `Re(s)=1/2`; measure roughness and mirror imbalance of `d/ds log f` for `Λ`, `ζ`, `Γ∞`, and finite Euler controls.
- STEP 10 verdict: DEAD END for novelty. `Λ` has zero mirror imbalance for every tau, while `ζ` and finite Euler do not. This is just the completed functional equation showing up under a colored-noise instrument; useful sanity check, but reduce-to-known. Not chat-posted.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Contiguous minors in total positivity `[DEAD END — reduces to existing Hankel/Laguerre hierarchy warning]`
Seed RandomNode = "Parameter signs matter because the standard ultradiscrete limit assumes positive dependent variables and parameters" → Step 1 cold Codex broad list → rng#10 = Total positivity and sign-variation theory → Step 3 cold Codex narrow list → rng#5 = NODE "The importance of contiguous minors in special matrix classes, where checking only adjacent minors can sometimes suffice".
- STEP 5 constraint: total positivity is a global all-minors constraint, but special structured classes sometimes permit contiguous-minor tests. Outside those classes, local adjacent checks are not a certificate.
- STEP 6/9 method rng#9 = test small cases. `computations/2026-06-20-hgt-minors-contiguous-node-ht.py` found a positive `4x4` matrix with all adjacent `2x2` minors positive (`min=0.0345651`) but `11/16` `3x3` minors nonpositive (`min=-0.837207`). NODE constraint validated: local contiguous checks need structure.
- STEP 7 gate: the formula does not apply unchanged to HT functions except through Hankel/Laguerre/Pólya-frequency style matrices, which are already in the corpus (`phase-cancellation-crux`, `finite-free-convolution-flow`).
- STEP 8 minimal edit: use the same minor checker on continuum strip matrices with entries `log(1+|∂_s log f(σ+it)|)`. Results: `Λ`, `ζ`, and finite Euler generally fail adjacent `2x2` checks already; `Γ∞` passes adjacent checks and has near-zero/positive `3x3` minors because it is smooth/monotone. No HT-specific separation.
- STEP 10 verdict: DEAD END. The only meaningful HT-adjacent statement is the known one: low/local minors are not enough; the real object is the full Hankel/Laguerre hierarchy. This reduces to existing cards and does not produce a new observable. Do not post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "The importance of contiguous minors in special matrix classes, where checking only adjacent minors can sometimes suffice".

### Step 12 follow-up on Dyson id=731 — ultradiscrete phase-carrier defect `[ADDITIONAL FINDING — phase-specific, left-strip, finite-Euler stress survives]`
New workflow Step 12 applied directly after rereading `experiments/agent-steering/THE-MACHINE-workflow.md` (lines 34–41). Interpretation posted to `#research` as Dyson id=732 before follow-up: `[CONJECTURE]` the scalar max-plus defect may measure missing sign/phase carrier data in the archimedean-prime log-derivative weld; possible failure modes are FE/phase-cancellation reduction or numerical-window artifact.
- Battery script: `computations/2026-06-20-hgt-STEP12-ultradiscrete-phase-defect-battery.py`; output: `computations/2026-06-20-hgt-STEP12-ultradiscrete-phase-defect-battery.txt`. It applies all 23 moves from `docs/meta/scientific-method.md` as concrete tests: subclaim split, attack-as-false random-phase surrogate, reverse antiphase inference, representation change, visual sparkline, cancellation action, stripped statistics, sine control, small/extreme cases, window experiments, invariants, monotonicity in prime count, weaken/strengthen, minimal counterexamples, h-stability dependency chain, nearby false statements, and boundary cases.
- ADDITIONAL FINDING: the id=731 signal is phase-carrier specific, not a raw amplitude artifact. Randomizing true `ζ'/ζ` phases while keeping magnitudes destroys the positive median: at `σ=0.3` over windows `[14,84]`, `[100,170]`, `[500,570]`, observed medians are `0.3156,0.4193,0.5491`, while random-phase medians are `-0.1531,-0.1675,-0.1968`. At `σ=0.5`, observed medians `0.2018,0.2047,0.2901`; random-phase medians `-0.07735,-0.1586,-0.1362`.
- Finite Euler cutoff stress survives: at `σ=0.3`, `[100,170]`, finite-prime counts `10,30,80,160,240` give medians `-0.1481,-0.04166,-0.002735,0.009429,0.006257`; the finite control approaches near-zero/coin-flip behavior rather than the true-zeta positive median.
- Boundary case: outside the critical strip at `σ=1.2`, true and finite are essentially identical (`true_med=-0.07644`, `finite_med=-0.07602` on `[100,170]`), so the effect localizes to the analytic-continuation/left-strip region rather than being a generic property of the log-derivative formula.
- Corrections / false nearby statements: do NOT claim universal tail separation. Finite Euler controls can have large local tails for some `σ` (especially around `0.7`); the robust statistic is median/positive fraction on the left strip, plus phase-randomization failure, not q99 everywhere.
- Missing lemma isolated: in left critical-strip windows, `cos(arg Γ∞ - arg ζ'/ζ)` has a persistently negative median (`≈-0.80` to `-0.94` at `σ=0.3`), while finite Euler lacks the same median antiphase carrier. A theorem would need phase-distribution control for `ζ'/ζ` relative to the digamma term; the experiment is not such a theorem.
- Posted additional finding to `#research` as Dyson id=733. Count treatment: this is one Step-12 enrichment of the id=731 root finding, not a new random-node root.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Cyclic ordering of external data in positive geometry `[DEAD END — smooth moment-curve vs rough HT point cloud]`

- Workflow reread before this tick: Step 12 now requires interpreting/logging/posting any non-reducing finding, then interrogating it with all 23 scientific-method moves and logging/posting noteworthy additions.
- STEP 1 seed `The importance of contiguous minors in special matrix classes, where checking only adjacent minors can sometimes suffice`; rng pick 16 -> `Positive geometry and amplituhedra`.
- STEP 4 rng pick 5 -> NODE `The dependence of positivity on the cyclic ordering of external data`.
- STEP 5 constraint: positive geometry is constrained by oriented cyclic order of external data; the same point set can be sign-coherent in the correct order and defective after non-cyclic permutations.
- STEP 6/9 method rng#3 = reverse it. Script `computations/2026-06-20-hgt-positive-geometry-cyclic-order.py` validates the NODE on moment-curve data: natural order has sign coherence `1.0000`, random `0.5077`, cyclic-shift `0.5137`, adjacent swap `0.9500`.
- STEP 8 minimal edit: replace external data rows by continuum differential points from `d/ds log f(σ+it)` and ask the reverse question: can sign coherence recover a preferred order for `Λ`, `ζ`, `Γ∞`, finite Euler? At `σ=0.3`, `Γ∞` reproduces moment-curve coherence (`1.0000` natural/phase/magnitude), while `Λ`, `ζ`, and finite Euler are near random (`~0.50–0.55`) across natural, phase, magnitude, random orders.
- STEP 10 verdict: DEAD END. The transfer measures smooth moment-curve behavior for `Γ∞` versus rough complex log-derivative point clouds for the prime/ζ side; not a non-reducing HT observable.
- STEP 11 metaphor: FE seam as folded cyclic boundary order. Method rng#2 = attack as false. Script `computations/2026-06-20-hgt-STEP11-positive-geometry-fe-fold.py` tests two-lane-forward, FE-folded, interleaved, phase, and random orders on paired `σ=0.3/0.7` data. FE-folded order does not improve `Λ` (`0.5184`) over natural/random levels; phase order improves slightly (`0.5867`) but is non-specific and not a completed-HT signature. Metaphor killed. Not chat-posted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `The dependence of positivity on the cyclic ordering of external data`.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Cosmological-polytope positivity tied to energy variables `[DEAD END — reduces to Dirichlet convergence / analytic continuation]`

- STEP 1 seed `The dependence of positivity on the cyclic ordering of external data`; rng pick 18 -> `Cosmological polytopes`.
- STEP 4 rng pick 7 -> NODE `Positivity is tied to energy variables, not spacetime coordinates`.
- STEP 5 constraint: cosmological-polytope positivity is a positive-energy-variable constraint; coordinate/time samples are oscillatory and not themselves positive.
- STEP 6/9 method rng#3 = reverse it. Script `computations/2026-06-20-hgt-cosmopolytope-energy-variables.py` validates the NODE with a toy canonical form: positive energy variables give `energy_form_positive_frac=1.0000`, while time-coordinate real parts are positive only `~0.5205` with nonzero imaginary oscillation.
- STEP 8 minimal edit: replace energy variables by Dirichlet frequencies `log n` for continuum differential fields `d/ds log f(σ+it)`; reverse-test whether coordinate samples recover positive/real energy coefficients. Result: finite Euler has low residuals (`0.0115` at `σ=1.3`) and more stable positive-energy scores; `ζ`, `Λ`, and `Γ∞` do not produce a clean finite positive-energy representation in this basis, especially under analytic continuation.
- STEP 10 verdict: DEAD END. The transfer reduces to the known fact that the Euler/Dirichlet positive-energy representation belongs to the convergent prime side, while analytic continuation/completion is not a finite positive-energy coordinate chart.
- STEP 11 method rng#23 = classify boundary cases. Boundary scan around `σ=1` confirms the same reduction: true `ζ'/ζ` residual worsens across the convergence boundary (`0.0325` at `σ=1.5` to `0.7882` at `σ=0.5`), while finite Euler remains comparatively representable by construction. Not chat-posted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `Positivity is tied to energy variables, not spacetime coordinates`.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Catalyst poisoning before cycle amplification `[DEAD END — survival grid reduces to phase-defect distribution, not order]`
Seed RandomNode = "The dependence of positivity on the cyclic ordering of external data" → Step 1 cold Codex broad list → rng#4 = Autocatalytic chemical cycles with order-dependent feasibility → Step 3 cold Codex narrow list → rng#16 = NODE "Catalyst poisoning before cycle amplification".
- STEP 5 constraint: the same poison dose can kill or spare an autocatalytic cycle depending on whether it binds active catalyst before the catalyst crosses the amplification threshold. This is a timing/order constraint, not just total poison amount.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-catalyst-poisoning.py`. The ODE model validates the NODE: poison at `t≤1.4` prevents survival for dose `0.42`; poison at `t≥1.7` survives, with amplification threshold crossed near `t=1.120`. Dose/timing grid shows a clear boundary (`dose=0.20` first survival at `0.400`, `dose=0.70` first survival at `2.200`).
- STEP 7 gate: the chemical threshold formula does not apply unchanged to HT functions. Minimal non-blind edit: chemical time becomes vertical height `t`, and catalyst growth is driven by the continuum differential phase-carrier defect `Δ=max(log|Γ∞|,log|P|)-log|Γ∞+P|` for `P=true ζ'/ζ` or finite Euler.
- STEP 8/9 method rng#5 = make it visual. Script/output: `computations/2026-06-21-hgt-STEP8-catalyst-poisoning-phase-carrier.py`, `computations/2026-06-21-hgt-catalyst-poisoning-node-ht.txt`. Result: true `ζ'/ζ` at `σ=0.3` makes the visual survival grid almost all `#` for windows `[100,170]` and `[500,570]`, while finite Euler mostly fails. At `σ=0.5/0.7`, true and finite are closer.
- STEP 10 preliminary verdict: the visual effect is strong but suspect because it may just threshold the already-posted ultradiscrete phase-carrier defect (Dyson ids 731/733).
- STEP 11 method rng#1 = split into subclaims. Script/output: `computations/2026-06-21-hgt-STEP11-catalyst-poisoning-order-controls.py`, `computations/2026-06-21-hgt-STEP11-catalyst-poisoning-order-controls.txt`. It separates distribution strength from order/timing by comparing natural, shuffled, ascending, descending, and block-swapped defect sequences.
- STEP 11 result: order is not load-bearing. True `ζ'/ζ` total survival remains high under natural `0.9890`, shuffled `0.9945`, blockswap `0.9945`, and descending `1.0000`; ascending lowers early survival but only by delaying strong defects. Finite Euler remains low under all orders (`0.0000–0.0742`). Therefore the transfer does not inherit the NODE's timing/order constraint; it is a nonlinear visualization of the id=731/id=733 phase-defect distribution.
- STEP 10 final verdict: DEAD END for new finding. Useful control: the phase-carrier defect is strong enough to drive arbitrary threshold amplifiers, but catalyst-poisoning order does not add non-reducing content. Do not post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Catalyst poisoning before cycle amplification".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Passivity is not detailed balance `[DEAD END — reduces to FE symmetry orthogonal to RH positivity]`

- STEP 1 seed `Positivity is tied to energy variables, not spacetime coordinates`; rng pick 4 -> `Passivity in thermodynamics`.
- STEP 4 rng pick 10 -> NODE `Passivity is not the same as detailed balance`.
- STEP 5 constraint: passivity is a state/Hamiltonian work-extraction constraint; detailed balance is a rate-level reversibility constraint. They are independent.
- STEP 6/9 method rng#23 = classify boundary cases. Script `computations/2026-06-20-hgt-passivity-vs-detailed-balance.py` validates the NODE with four cases: `gibbs+db` passive/DB, `inverted+db` nonpassive/DB, `passive+nondb` passive/nonDB, `inverted+nondb` nonpassive/nonDB.
- STEP 8 minimal edit: detailed balance -> FE mirror pairing; passivity -> no off-line zero directions / `κ_- = 0`. The four HT toy cases classify independently: `rh+fe` true/true, `off_line_fe` true/false, `rh_no_fe` false/true, `off_line_no_fe` false/false.
- STEP 10 verdict: DEAD END. This is exactly the existing project split: FE symmetry is orthogonal to RH positivity/passivity (`κ_-`, intrinsic RH locus, #191-style decoupling). Not chat-posted.
- STEP 11 method rng#13 = find a monotone quantity. Script `computations/2026-06-20-hgt-STEP11-passivity-monotone.py` holds FE balance fixed while horizontal off-line displacement `a` grows; the ergotropy proxy is `4a^2` and off-line count jumps from 0 to 4 for any `a>0`. This is useful pedagogy but fully reduce-to-known.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `Passivity is not the same as detailed balance`.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Measurement perturbs chemical state `[DEAD END — finite-difference backaction not robust]`

- STEP 1 seed `Passivity is not the same as detailed balance`; rng pick 8 -> `Chemical computing`.
- STEP 4 rng pick 18 -> NODE `Measurement can perturb the chemical state being measured`.
- STEP 5 constraint: chemical readout can be invasive; a reporter reaction may consume or alter the molecular signal, so measured output is not a passive copy.
- STEP 6/9 method rng#1 = split into subclaims. Script `computations/2026-06-20-hgt-measurement-backaction.py` validates the NODE: consuming readout rate `0.00 -> 0.40` lowers computed product `Y` from `16.5` to `1.36949`, while nonconsuming readout leaves `Y=16.5`.
- STEP 8 minimal edit: chemical readout strength -> finite-difference measurement strength `h` for the continuum observable `d/ds log f(s)`. Initial raw-value finite differences suggested completed `Λ` was much less perturbed than `ζ`/finite Euler, but high-height `Γ∞` overflow exposed a numerical artifact.
- Stable rerun uses finite differences of `log f`. Across windows `[14,84]`, `[100,170]`, `[500,570]`, `Λ` has critical-line q95 backaction spikes like `ζ`, while `Γ∞` remains tiny and finite Euler is often but not always more invasive.
- STEP 10 verdict: DEAD END. The robust content is ordinary zero/branch sensitivity and finite Euler roughness, not a new HT observable.
- STEP 11 method rng#14 = weaken the conjecture. Weakened hierarchy "finite Euler more measurement-invasive than true analytic fields" also fails as a uniform statement: at high height `σ=0.5`, `finite/zeta_median=0.8676` and `finite/lambda_median=0.4549`. Not chat-posted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `Measurement can perturb the chemical state being measured`.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Catalytic specificity in hypercycle error catastrophe `[FIND — phase-specific catalyst selects true analytic zeta; amplitude-promiscuous catalyst selects finite Euler parasite]`
Seed RandomNode = "Catalyst poisoning before cycle amplification" → Step 1 cold Codex broad list → rng#2 = Hypercycle error catastrophe → Step 3 cold Codex narrow list → rng#12 = NODE "Catalytic specificity is crucial; broad or promiscuous catalysis can increase vulnerability to parasitic sequences".
- STEP 5 constraint: a hypercycle survives by specific catalytic closure. If catalytic support becomes too broad/promiscuous, a faster parasite can receive cooperative support without reciprocating, causing collapse.
- STEP 6/9 method rng#16 = minimal counterexample. NODE script `computations/2026-06-21-hgt-NODE-hypercycle-specificity.py` validates the constraint: with parasite rate boosted to `2.8`, leak `0.00` leaves parasite `0.000000` and preserves the cycle, leak `0.18` gives parasite `0.042872`, but leak `0.24` yields parasite `0.687126` and collapse; leak `0.32` yields parasite `0.898606` and collapse.
- STEP 7 gate: no unchanged hypercycle-rate formula applies to HT functions. The non-blind minimal edit keeps specificity as a selector and replaces species by continuum differential components in the archimedean-prime weld: `Γ∞` paired with true analytic `ζ'/ζ`, finite Euler, and a random-phase parasite.
- STEP 8/9 HT transfer script `computations/2026-06-21-hgt-STEP8-hypercycle-specificity-phasegate.py`; output `computations/2026-06-21-hgt-hypercycle-specificity-node-ht.txt`. Phase-specific catalyst = median positive phase-carrier defect; amplitude-promiscuous catalyst = median scalar magnitude. At `σ=0.3`, `[100,170]`, phase scores are true `0.431`, finite `0`, random `0`; amplitude scores are true `1.312`, finite `2.332`, random `1.312`. Competition output: phase-specific catalyst selects true (`1.000,0.000,0.000`), amplitude-promiscuous catalyst selects finite Euler (`0.000,1.000,0.000`). The same qualitative split appears at `σ=0.5` and in the high window `[500,570]`, but the phase signal weakens near `σ=0.7`.
- FIND (experimental): hypercycle specificity transfers as a selection observable on the continuum differential weld. Pair/phase-specific catalytic coupling selects the true analytic `ζ'/ζ` component, while broad amplitude-promiscuous coupling selects the finite Euler parasite. This is not a theorem and not a universal sigma claim; it is an experimental classifier generated from the random-node specificity constraint.
- Why it survives reduce-to-known: it reuses the phase-carrier defect banked in id=731/id=733, but the new content is the specificity-versus-promiscuity selection layer: finite Euler is not merely near-zero in phase defect; it actively wins under broad amplitude catalysis. The finding is a constrained hypercycle-style selection interpretation of the continuum weld, not a discrete-value or finite Euler convergence statement.
- Posted to `#research` as Dyson id=734.

### Step 12 follow-up on Dyson id=734 — hypercycle specificity `[ADDITIONAL FINDING — left-strip boundary and prime-load stress]`
New workflow Step 12 was applied directly to the posted id=734 result. Battery script: `computations/2026-06-21-hgt-STEP12-hypercycle-specificity-battery.py`; output: `computations/2026-06-21-hgt-STEP12-hypercycle-specificity-battery.txt`. It implements all 23 moves from `docs/meta/scientific-method.md`: subclaim split, attack-as-false random phase, reverse selector winners, viewpoint/visual/action probes, stripped gaps, similar sine control, small/extreme cases, experiments, invariants, prime-count monotonic stress, weakened/strengthened forms, minimal counterexamples, representation change, theorem resemblance, fake proof gap, missing lemma, h-dependency, nearby false statements, and boundary classification.
- ADDITIONAL FINDING: the specificity/promiscuity split is sharply localized to the left strip. At `σ=0.3`, all tested windows have phase winner true and amplitude winner finite. In `[100,170]`, phase scores are true `0.4193`, finite `0.0094`, random-phase `0.0000`; amplitude scores are true `1.2930`, finite `2.3515`, random-phase `1.2930`. At `σ=0.5`, the same winner pattern holds with smaller phase gap. At `σ=0.7`, the phase gap is only `0.004392`; by `σ≥0.8/1.2`, phase and amplitude selectors mostly degenerate.
- Prime-count stress: at `σ=0.3`, `[100,170]`, finite Euler amplitude rises with cutoff (`1.5885,1.9512,2.1932,2.3515,2.3831` for prime counts `10,30,80,160,240`), while finite phase-specific scores remain near zero (`0,0,0,0.00943,0.00626`) against true phase score `0.4193`. This supports the interpretation that promiscuous catalysis rewards finite-prime parasite load while phase-specific catalysis rejects it.
- Corrections / false nearby statements: do NOT claim universal specificity selection. Strong universal claim has counterexamples at higher `σ` and high windows; the robust claim is left-strip, median/phase-specific, and experimental.
- Missing lemma isolated: prove a left-strip median positive phase-defect lower bound for true analytic `ζ'/ζ` relative to `Γ∞`, while finite Euler cutoffs keep median phase-specific defect near zero even as their amplitude/load grows.
- Posted to `#research` as Dyson id=735. Count treatment: this is a Step-12 enrichment of the id=734 root finding, not a new random-node root.
- WALK STATE: continue from NODE = "Catalytic specificity is crucial; broad or promiscuous catalysis can increase vulnerability to parasitic sequences"; if exhausted, reseed STEP 1 with that RandomNode.

#### Step 12 workflow delta on Dyson id=735 — plain-language context and theorem shape `[CONTEXTUALIZATION; not a new count]`
Workflow reread after id=735 showed Step 12 now additionally requires contextualizing/dumbing down any non-reducing finding and conjecturing what a theorem would look like in the overall HT context. The all-23-method battery had already been run for id=734/id=735, so the missing new requirement was a chat post giving the plain-language interpretation and theorem shape.
- Posted to `#research` as Dyson id=736, replying to id=735.
- Plain version: finite Euler is like a parasite that wins when the cycle rewards raw signal size, because adding primes increases finite load; true analytic `ζ'/ζ` wins when the cycle rewards the right phase relationship with the archimedean `Γ∞` part.
- HT-context conjecture: the archimedean-prime weld in `∂_s log Λ` has a pair-specific phase constraint that finite Euler cutoffs cannot satisfy uniformly on the analytic-continuation side, even when finite cutoffs dominate scalar amplitude observables.
- Theorem shape: for a left-strip region and long height windows away from exceptional zero neighborhoods, the median positive phase defect for true `ζ'/ζ` relative to `Γ∞` is bounded below, while finite Euler cutoffs keep median phase-specific defect near zero as cutoff grows; at the same time scalar amplitude can grow with cutoff and select finite Euler. This would formalize the specificity/promiscuity split as an HT-native selection obstruction.
- Count treatment: contextualization/theorem-shape only; does not increment the finding count.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Sampling misses rare failed intermediate lineages in stochastic tunneling `[DEAD END — sampling-bias transfer reduces to existing phase-defect distribution]`
Seed RandomNode = "Catalytic specificity is crucial; broad or promiscuous catalysis can increase vulnerability to parasitic sequences" → Step 1 cold Codex broad list → rng#13 = Stochastic tunneling in evolutionary systems → Step 3 cold Codex narrow list → rng#17 = NODE "Sampling usually misses rare intermediate lineages that fail before producing successful descendants".
- STEP 5 constraint: the NODE is an observation/thinning constraint. Rare deleterious intermediate lineages can exist and die between finite sampling times; successful lineages are length-biased because they survive long enough to produce descendants.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-stochastic-tunneling-sampling-miss.py`; output `computations/2026-06-21-hgt-NODE-stochastic-tunneling-sampling-miss.txt`. A subcritical birth-death intermediate with mutation-to-success validates the constraint: true success fraction `0.008700`, but observed success is enriched by coarse/threshholded sampling. At `dt=10`, threshold `8`, failed missed fraction is `0.978231` and success enrichment is `13.200947`.
- STEP 7 gate: birth-death/tunneling detection formulas do not apply unchanged to HT functions. The minimal non-blind target is the continuum differential field on `s=σ+it`, not discrete values `ζ(n)`.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein from the NODE test. Selected `excursion-sampling` (`69`, normalized `0.3876`) over `jet-packet-survival` (`117`) and `antiphase-run-censoring` (`127`). Script `computations/2026-06-21-hgt-STEP8-stochastic-tunneling-sampling-ht-excursions.py`; output `computations/2026-06-21-hgt-STEP8-stochastic-tunneling-sampling-ht-excursions.txt`.
- STEP 9 method rng#19 = write the fake proof. The wished proof was: coarse sampling hides failed HT phase-defect excursions and enriches observed successful ones. The script attacks the exact gap with threshold sweeps. Result: at `σ=0.3`, `[100,170]`, true zeta has mostly successful/persistent excursions (`23` events: `3` failed, `20` success; stride `20` failed missed `0.633333`, success seen `0.782500`), while finite Euler has many failed short events (`41`: `36` failed, `5` success; failed missed `0.891667`, success seen `0.250000`) and random-phase has many failed short events (`101`: `81` failed, `20` success; failed missed `0.927778`, success seen `0.072500`). Threshold sweeps keep the qualitative distinction but expose cutoff dependence.
- STEP 10 verdict: DEAD END for new knowledge. The result is mildly surprising as a sampling-bias picture, but it is not independent HT content: it repackages the already-posted ultradiscrete/phase-carrier defect and hypercycle-specificity findings (Dyson ids 731, 733, 734, 735). No chat post.
- STEP 11 method rng#7 = strip to essentials. Script `computations/2026-06-21-hgt-STEP11-tunneling-sampling-mask-metaphor.py`; output `computations/2026-06-21-hgt-STEP11-tunneling-sampling-mask-metaphor.txt`. Binary excursion intervals plus sampling masks still show the same reduction: at `σ=0.3`, `[100,170]`, true-zeta observed-success stays high under periodic/prime/golden/random masks (`0.882353,0.933333,0.937500,0.913099`), while finite Euler and random-phase expose many missed failed intervals and lower observed-success fractions. This is a useful visualization of ids 731/735, not a new non-reducing finding.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Sampling usually misses rare intermediate lineages that fail before producing successful descendants".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Misidentification of hidden/overlapped transient intermediates `[DEAD END — sampling/zero-shadow resolution reduces to known zero proximity]`
Seed RandomNode = "Catalytic specificity is crucial; broad or promiscuous catalysis can increase vulnerability to parasitic sequences" → Step 1 cold Codex broad list → rng#13 = Autocatalytic small-molecule networks → Step 3 cold Codex narrow list → rng#18 = NODE "Misidentification of intermediates because transient species are below detection limits or overlap spectroscopically".
- Workflow reread during the round: `experiments/agent-steering/THE-MACHINE-workflow.md` now says Step 12 should contextualize and give the big picture in non-mathematical terms, rather than specifically "9th grade level". Step 8 still requires three wildly different attempts and the lowest-Levenshtein transfer.
- STEP 5 constraint: a real transient intermediate is identified only up to detector resolution: if its spectral band overlaps another component, or its amplitude falls below detection/rank threshold, the observed mixture can be explained by a merged or missing intermediate.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-autocat-hidden-intermediate.py`; output `computations/2026-06-21-hgt-NODE-autocat-hidden-intermediate.txt`. The Beer-Lambert / NNLS / blind-rank model validates the NODE: with overlap `0.886`, hidden amplitude `0.20` has detectable second rank (`rank2_snr=14.745`, recovered), while hidden amplitude `0.06` at the same overlap becomes merged by the blind rank criterion (`rank2_snr=4.579`, `rank_ratio=0.0126`, merged). At stronger overlap `0.9702`, hidden amplitudes `0.03` and `0.02` are merged/unrecovered. Grid output shows recovery needs spectral separation, above-threshold amplitude, and a detectable second rank.
- STEP 7 gate: the NODE formula is essentially Beer-Lambert mixture spectroscopy plus detection/rank thresholds (`A(t,λ)=Σ_i c_i(t)ε_i(λ)` with clipping/SVD/NNLS). It does not apply unchanged to HT functions. Minimal non-blind transfer must replace chemical spectra by continuum differential readouts over the complex plane.
- STEP 8 changed-workflow compliance: `computations/2026-06-21-hgt-STEP8-hidden-intermediate-ht-resolution.py` created three HT attempts: `zero-shadow`, `bohr-frequency`, and `strip-rank`. The script computes Levenshtein distances and selected `zero-shadow` as lowest (`93`, vs `102` and `120`). A first strip-rank run was discarded as noncompliant after the distances showed it was not the lowest-edit transfer; corrected output archived at `computations/2026-06-21-hgt-STEP8-hidden-intermediate-ht-resolution.txt`.
- STEP 9 method rng#3 = reverse it. Corrected selected test asks when unresolved true zero/pole shadows make finite/smooth readout masquerade as true. Result: no finite masquerade. At `σ=0.5`, true `ζ'/ζ` has fine max `9.7191` but coarse max `4.793` (`peak_capture=0.49315`), while finite Euler has fine/coarse max `2.0203/2.0116` (`peak_capture=0.99567`). This is a detector-resolution warning around true zeros/poles, not a new HT classifier; `finite_masquerade=0` for all tested `σ`.
- STEP 11 method rng#5 = make it visual. `computations/2026-06-21-hgt-STEP11-hidden-intermediate-shadowgram.py`; output `computations/2026-06-21-hgt-STEP11-hidden-intermediate-shadowgram.txt`. Shadowgrams compare point, blur, and max-hold detectors. At `σ=0.5`, true peak capture changes sharply by detector (`point=0.5498`, `blur=0.2239`, `maxhold=1`), while finite Euler remains stable (`point≈0.979`, `blur≈0.942`, `maxhold=1`). This visualizes ordinary narrow zero/proximity spikes and finite-Euler smoothness.
- STEP 10 verdict: DEAD END. The NODE constraint is real, but the HT transfer reduces to known sampling/resolution sensitivity near zeros or poles of analytic `ζ'/ζ`, plus finite Euler smoothness under truncation. It does not produce a non-reducing finding and was not posted to chat.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Misidentification of intermediates because transient species are below detection limits or overlap spectroscopically".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Stem taxa need not resemble the last common ancestor `[DEAD END — lineage-vs-morphology warning reduces to known smooth/rough profile effects]`
Seed RandomNode = "Sampling usually misses rare intermediate lineages that fail before producing successful descendants" → Step 1 cold Codex broad list → rng#2 = Stem-group taxa → Step 3 cold Codex narrow list → rng#10 = NODE "Stem taxa do not necessarily resemble the last common ancestor".
- Workflow reread before HT transfer: Step 12 final explanation now asks for big-picture, non-mathematical contextualization about HT or a specific function, not specifically a 9th-grade-level version.
- STEP 5 constraint: stem/crown status is a phylogenetic-position constraint, not a morphology-distance constraint. A stem side branch can be correctly placed while being highly specialized and far from the last common ancestor.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-stem-taxa-lca-resemblance.py`; output `computations/2026-06-21-hgt-NODE-stem-taxa-lca-resemblance.txt`. The simulated side-branch model validates the NODE: when side-branch specialization rate rises from `0.00` to `0.75`, the fraction of trials where median stem distance is below crown distance falls from `0.165000` to `0.000000`, while median stem distance grows from `0.375183` to `1.497792` against crown distance near `0.261`.
- STEP 7 gate: phylogenetic-position formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep the distinction between constraint-lineage position and local continuum differential morphology on `ℂ`.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `constraint-lineage-distance` (`89`, normalized `0.4917`) over `character-mosaic-matrix` (`132`) and `ghost-branch-interpolation` (`138`). Script `computations/2026-06-21-hgt-STEP8-stem-taxa-ht-lineage-morphology.py`; output `computations/2026-06-21-hgt-STEP8-stem-taxa-ht-lineage-morphology.txt`.
- STEP 9 method rng#5 = make it visual. The visual distance bars showed finite Euler closer to the smooth `Γ∞` baseline than the completed/true analytic profile in the tested normalized morphology metric: e.g. at `σ=0.3`, `[100,170]`, distance-to-gamma is true `Λ=1.283900`, uncompleted `ζ'/ζ=1.255218`, finite Euler `0.964874`, random-phase `1.382205`.
- STEP 10 verdict: DEAD END for new knowledge. The result is a useful warning that morphological resemblance to a smooth baseline is not the same as analytic/constraint lineage, but it reduces to already-known smoothness/roughness and finite-Euler-versus-analytic-continuation behavior.
- STEP 11 method rng#13 = find a monotone quantity. Script `computations/2026-06-21-hgt-STEP11-stem-taxa-lineage-monotone.py`; output `computations/2026-06-21-hgt-STEP11-stem-taxa-lineage-monotone.txt`. Sweeping prime-component strength `β` gave nonmonotone distances for both true and finite profiles in all tested windows, so no monotone invariant survived. This confirms the metaphor does not add a new HT constraint.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Stem taxa do not necessarily resemble the last common ancestor".

## Conway — margin-model contagion / amplitude-neutralized phase carrier (2026-06-21)

- Workflow seed: current RandomNode `Catalytic specificity is crucial; broad or promiscuous catalysis can increase vulnerability to parasitic sequences`.
- STEP 1/2: cold list -> rng #16 `Financial contagion via correlated arbitrage strategies`.
- STEP 3/4: cold missed-details list -> rng #2 NODE `Arbitrage books can become correlated through margin models, not just through asset returns`.
- STEP 5/6 NODE constraint: a common margin inequality `loss_i + model_margin_i > threshold` can synchronize liquidations independently of asset-return correlation. Runnable node validation in `computations/2026-06-21-conway-margin-model-contagion.py`; output `computations/2026-06-21-conway-margin-model-contagion.txt`. Boundary cases: shared-margin-only has raw return corr +0.028 but margin-call corr +0.989; no-shared-margin and asset-only controls do not reproduce that common-stress lift.
- STEP 8/9 direct HT transfer: three attempts by Levenshtein picked sigma-lane shared margin. Verdict: DEAD END as a direct HT finding. The shared-margin construction synchronizes true zeta, finite Euler, random-phase, and gamma-only controls, so it is a generic common-stress artifact.
- STEP 11/12 surviving additional finding: use the margin-node metaphor as a control, not as the signal. Neutralize amplitude-only margin variables in the ultradiscrete phase defect `Delta=max(log|G|,log|P|)-log|G+P|`. After regressing on `|G|`, `|P|`, ratio/max/min features, true analytic `zeta'/zeta` keeps a positive left-strip residual over random-phase controls, finite Euler remains near zero, and the gap collapses by sigma=1.2. Battery output: `computations/2026-06-21-conway-STEP12-margin-neutralized-battery.txt`.
- Key numbers: mean true-random residual gap across three windows is +0.584, +0.556, +0.476, +0.371, +0.214, +0.069, +0.005 at sigma 0.2,0.3,0.4,0.5,0.7,0.9,1.2. Prime-count stress at sigma=0.3 keeps gap about +0.45 for finite Euler N=30..240. Adding `|G+P|` or phase cosine as a feature kills the gap by overcontrol.
- Grade: `[EXPERIMENTAL FINDING / CONJECTURE]`, non-reducing as a control/enrichment of the phase-carrier observable, not a theorem. The direct margin transfer itself reduces/HT-blind.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Atmospheric-radical inlet wall loss and inlet chemistry `[DEAD END — inlet-memory smoothing reduces to zero-spike roughness]`
Seed RandomNode = "Misidentification of intermediates because transient species are below detection limits or overlap spectroscopically" → Step 1 cold Codex broad list → rng#8 = Atmospheric radical chemistry → Step 3 cold Codex narrow list → rng#16 = NODE "Wall loss and inlet chemistry can bias measured OH, HO2, RO2, and NO3 concentrations in field instruments".
- STEP 5 constraint: a radical instrument does not measure the ambient radical vector directly; the inlet applies a residence-time loss/conversion map. The observed vector is closer to `exp(Aτ)x_ambient` than to `x_ambient`.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-inlet-wall-loss-radicals.py`; output `computations/2026-06-21-hgt-NODE-inlet-wall-loss-radicals.txt`. The model validates the constraint: pure wall loss at residence `0.20`, wall `0.20` depresses OH to median ratio `0.7261`; adding inlet conversion changes signs/magnitudes (e.g. OH max ratio `1.4285`, RO2 max ratio `1.4518` at residence `0.20`, wall `0.20`, convert `0.80`). Stronger wall loss yields relative error `0.4519` and condition `2.3169`.
- STEP 7 gate: first-order inlet reactor formulas apply to instrument transport, not to HT functions. The closest non-blind transfer must replace inlet residence/wall memory by a measurement operator on continuum differential readouts.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-inlet-wall-loss-ht.py` created three attempts: `wall-memory-smoothing`, `residence-backaction`, and `component-inlet-map`. Levenshtein selected `wall-memory-smoothing` (`101`, vs `109`, `122`). Output: `computations/2026-06-21-hgt-STEP8-inlet-wall-loss-ht.txt`.
- STEP 9 method rng#1 = split into subclaims. The selected test split bias by function class and residence strength. Result on `[100,170]`: at `σ=0.5`, true `ζ'/ζ` has median relative smoothing bias `0.20465,0.30517,0.32918` for `τ=0.5,1.5,4.0`, with peak capture `0.6261,0.42796,0.36927`; finite Euler has lower bias `0.097416,0.1465,0.18233` and peak capture `0.94009,0.87835,0.80101`; `Γ∞` is almost invariant (`median <=0.00457`).
- STEP 11 method rng#23 = classify boundary cases. `computations/2026-06-21-hgt-STEP11-inlet-wall-boundaries.py`; output `computations/2026-06-21-hgt-STEP11-inlet-wall-boundaries.txt`. Across windows `[14,84]`, `[100,170]`, and `[500,570]`, the class `true-more-inlet-biased` appears robustly at `σ=0.5`; it mostly collapses at `σ=1.2`, and becomes mixed/collapsed away from the critical-line vicinity.
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, and the boundary scan is coherent, but the HT transfer says that smoothing/memory under-resolves true `ζ'/ζ` near zero/pole spikes while finite Euler and `Γ∞` are smoother. This reduces to known analytic-continuation/zero-proximity roughness and overlaps the prior `Measurement perturbs chemical state` dead end. No chat post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Wall loss and inlet chemistry can bias measured OH, HO2, RO2, and NO3 concentrations in field instruments".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Semantic dependencies dominate package imports `[DEAD END — graph closure artifact, not HT-native semantic coupling]`
Seed RandomNode = "Stem taxa do not necessarily resemble the last common ancestor" → Step 1 cold Codex broad list → rng#19 = Software architecture → Step 3 cold Codex narrow list → rng#4 = NODE "The hardest dependencies are often semantic dependencies, not package imports".
- STEP 5 constraint: architectural coupling is not exhausted by static imports. Shared invariants, contracts, and meanings can create large change-impact closures while the package graph remains locally clean.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-software-semantic-dependencies.py`; output `computations/2026-06-21-hgt-NODE-software-semantic-dependencies.txt`. The simulated architecture validates the NODE: one mutated module has import-closure median `1.000000` but semantic-closure median `74.000000`, with silent semantic ratio median `69.000000`.
- STEP 7 gate: software import/contract formulas do not apply unchanged to HT functions. Minimal non-blind transfer must make a graph on continuum differential samples and separate visible local formula dependence from hidden constraint dependence.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `continuum-constraint-graph` (`33`, normalized `0.2705`) over `api-contract-sheaf` (`101`) and `proof-obligation-graph` (`106`). Script `computations/2026-06-21-hgt-STEP8-software-semantic-dependencies-ht-graph.py`; output `computations/2026-06-21-hgt-STEP8-software-semantic-dependencies-ht-graph.txt`.
- STEP 9 method rng#10 = test extreme cases. Adding `gamma-only` and `random-phase` controls killed the apparent signal: gamma-only has semantic closure `130/260` with huge silent ratios, and random-phase often percolates more strongly than true `Λ`. The graph construction is too permissive and not a specific HT semantic-dependency observable.
- STEP 10 verdict: DEAD END for new knowledge. The NODE was valid, but the HT graph statistic reduces to edge-construction artifacts plus already-known FE/phase behavior.
- STEP 11 method rng#17 = change representation. Script `computations/2026-06-21-hgt-STEP11-software-semantic-spectrum.py`; output `computations/2026-06-21-hgt-STEP11-software-semantic-spectrum.txt`. Laplacian-spectrum representation did not rescue the idea: gamma-only produces two large components of size `100`, random-phase can have larger connected structure than true `Λ`, and `λ₂≈0` throughout. No robust HT-native constraint remains.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "The hardest dependencies are often semantic dependencies, not package imports".

## Conway — kinetic proofreading / phase-defect lifetime representation (2026-06-21)

- STEP 1/2: seed `Arbitrage books can become correlated through margin models, not just through asset returns`; cold list -> rng #16 `Kinetic proofreading`.
- STEP 3/4: cold missed-details list -> rng #5 NODE `On-rate differences usually contribute much less than off-rate differences`.
- STEP 5/6 NODE constraint: in kinetic proofreading, entry/on-rate is a one-time capture factor; lifetime/off-rate is amplified by repeated irreversible survival tests. Runnable validation in `computations/2026-06-21-conway-kinetic-proofreading-lifetime.py`; output `computations/2026-06-21-conway-kinetic-proofreading-lifetime.txt`. On-rate-only specificity stays constant with depth; off-rate specificity grows exponentially with depth.
- STEP 8/9 method #17 `change representation`: pointwise phase-carrier defect becomes positive-defect run survival. Selected `antiphase-run lifetime` by Levenshtein over amplitude-threshold depth and zero-tube dwell time.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-proofreading-lifetime-battery.py`, output `computations/2026-06-21-conway-STEP12-proofreading-lifetime-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: true analytic `zeta'/zeta` on the left strip wins by off-rate/lifetime, not on-rate/entry. At sigma=0.3, threshold 0, mean across three windows: true entry 0.024, off-hazard 0.0238, median run 150, survive_16 0.738; finite Euler entry 0.268, off-hazard 0.5371, median run 2, survive_16 0; random phase entry 0.232, off-hazard 0.5347, median run 1.67, survive_16 0. Finite prime-count stress N=30..240 raises finite entry but never gives survive_8 or survive_16. Right-side boundary sigma=1.2 collapses true and finite lifetimes.
- Grade: non-reducing experimental control/enrichment of the phase-carrier observable, not a theorem. The meaningful claim is left-strip phase-persistence/run-tail separation; universal-sigma and high-threshold versions are false.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Cross-border legal/resolution rules alter loss propagation `[DEAD END — cascade reduces to FE mirror-pair propagation]`
Seed RandomNode = "The hardest dependencies are often semantic dependencies, not package imports" → Step 1 cold Codex broad list → rng#15 = Contagion in financial networks → Step 3 cold Codex narrow list → rng#18 = NODE "Cross-border legal and resolution differences affect how losses propagate".
- STEP 5 constraint: identical financial exposures can propagate losses differently because recovery rates, delays, and legal resolution rules differ across jurisdictions.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-financial-crossborder-resolution.py`; output `computations/2026-06-21-hgt-NODE-financial-crossborder-resolution.txt`. After tuning to a near-threshold regime, uniform rules have q90 defaults `3.000000`, while fragmented/harsh cross-border rules jump to q90 defaults `87.000000/88.000000`; the NODE constraint is real.
- STEP 7 gate: financial cascade formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep a propagation/cascade test but place nodes in the continuum differential strip, not at discrete values `ζ(n)`.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `strip-resolution-cascade` (`21`, normalized `0.1579`) over `prime-collateral-haircut` (`100`) and `branch-cut-bankruptcy` (`103`). Script `computations/2026-06-21-hgt-STEP8-financial-resolution-ht-cascade.py`; output `computations/2026-06-21-hgt-STEP8-financial-resolution-ht-cascade.txt`.
- STEP 9 method rng#5 = make it visual. True `Λ` was the only tested profile with cross-lane regime sensitivity: at `[100,170]`, true `Λ` defaults stay at `2` but median loss rises from `0.645197` under uniform rules to `0.851129` under harsh cross-border rules and front-loaded loss falls from `1.000000` to `0.508567`. Gamma-only, finite Euler, and random-phase controls stay at one default with smaller loss changes.
- STEP 10 verdict: surprising as a cascade picture, but not non-reducing. The topology of the effect is exactly mirror-pair propagation from the completed functional equation; the resolution rule changes timing/loss magnitude but does not expose a new HT-native obstruction.
- STEP 11 method rng#4 = change viewpoint. Script `computations/2026-06-21-hgt-STEP11-financial-resolution-viewpoint.py`; output `computations/2026-06-21-hgt-STEP11-financial-resolution-viewpoint.txt`. Reversing exposure orientation and seeding low-stress nodes left the class split unchanged: true `Λ` always defaults at the mirror-pair level (`2`), finite Euler/random-phase remain at `1`. This confirms the reduction to FE mirror coupling rather than a new semantic/resolution constraint.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Cross-border legal and resolution differences affect how losses propagate".

## Round (THE-MACHINE revised workflow, hgt) — NODE = HMM transition estimates absorb observation bias `[DEAD END — phase-state transition bias repackages phase-defect persistence]`
Seed RandomNode = "Wall loss and inlet chemistry can bias measured OH, HO2, RO2, and NO3 concentrations in field instruments" → Step 1 cold Codex broad list → rng#13 = Hidden Markov measurement bias → Step 3 cold Codex narrow list → rng#5 = NODE "Overlooking that transition estimates can absorb systematic observation bias".
- STEP 5 constraint: in a hidden Markov model, transition estimates are not independent of the observation/emission model. If emissions are mis-specified, transition rates can compensate for false positives, false negatives, or over-clean/noisy sensors.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-hmm-transition-absorbs-emission-bias.py`; output `computations/2026-06-21-hgt-NODE-hmm-transition-absorbs-emission-bias.txt`. A lean two-state HMM validates the constraint. True transitions are `p01=0.0600`, `p10=0.1000`; naive observed transitions inflate to `p01=0.1633`, `p10=0.3171`. With a too-clean emission assumption, fitted transitions inflate (`p01_hat=0.1233`, `p10_hat=0.2650`); with a too-noisy assumption, they deflate (`p01_hat=0.0100`, `p10_hat=0.0383`).
- STEP 7 gate: the HMM likelihood formula `P(y)=π B(y0) ∏ T B(yt)` does not apply unchanged to HT functions. The non-blind transfer must replace hidden states/emissions by regimes of a continuum differential observable.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-hmm-transition-bias-ht.py` created three attempts: `phase-emission`, `missingness-chain`, and `threshold-transition`; Levenshtein selected `phase-emission` (`92`, vs `106`, `112`). Output: `computations/2026-06-21-hgt-STEP8-hmm-transition-bias-ht.txt`.
- STEP 9 method rng#13 = find a monotone quantity. Monotone observation-bias knobs were threshold shift and blur width. For the selected phase-emission readout, stronger threshold/blur monotonically reduces estimated phase-state transition rates. Example `σ=0.3`: true `p01` moves `0.10127 → 0.055394 → 0.015306`; finite moves `0.16456 → 0.03966 → 0.024457`. At `σ=1.2`, true and finite are identical, so the effect collapses outside the left/critical region.
- STEP 11 method rng#6 = ask what action is happening. `computations/2026-06-21-hgt-STEP11-hmm-action-bias.py`; output `computations/2026-06-21-hgt-STEP11-hmm-action-bias.txt`. The biased observation mostly deletes or merges short phase events. At `σ=0.3`, true has `31` phase-event runs before blur, finite has `51`, random-phase has `78`; blur deletes true/finite events and merges or deletes random-phase events.
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the HT transfer is another phase-event persistence view of already posted phase-carrier results (Dyson ids 731, 733, 734, 735). It does not supply an independent non-reducing observable; no chat post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Overlooking that transition estimates can absorb systematic observation bias".

## Conway — latency-tier segmentation / zero-shadow staleness (2026-06-21) `[DEAD END]`

- STEP 1/2: seed `On-rate differences usually contribute much less than off-rate differences`; cold list -> rng #15 `Liquidity stickiness in financial markets`.
- STEP 3/4: cold missed-details list -> rng #6 NODE `Latency-tier segmentation: faster participants may treat stale displayed liquidity differently from slower participants`.
- STEP 5/6 NODE constraint: displayed liquidity can be stale; executable liquidity depends on persistence through the observer's latency interval. Runnable validation in `computations/2026-06-21-conway-latency-tier-phase-staleness.py`; output `computations/2026-06-21-conway-latency-tier-phase-staleness.txt`.
- STEP 9 method #19 `write the fake proof`: wished proof was that a latency-tier control would isolate non-stale HT persistence.
- Workflow correction: Levenshtein selected `C_zero_shadow_latency` (distance 15); the first phase-staleness run was discarded as noncompliant. Corrected selected transfer uses near-minima of `log(1+|Gamma_infty+P|)` as displayed zero-shadows and tests whether they remain executable across latency intervals.
- Verdict: DEAD END. True and finite Euler zero-shadow staleness are too similar to be HT-specific; sigma=1.2 is essentially identical, and at sigma=0.3 latency 8 both have stale fraction about 0.790. Random-phase is more fragile, but that is generic phase randomization. This reduces to sampling/resolution and zero-valley smoothness, not a new non-reducing finding. No chat post.

## Conway — spillback lookahead / local phase cue downstream availability (2026-06-21) `[CONTROL / DEAD END]`

- STEP 1/2: seed `Latency-tier segmentation: faster participants may treat stale displayed liquidity differently from slower participants`; cold list -> rng #19 `Architectural wayfinding under congestion`.
- STEP 3/4: cold list -> rng #12 NODE `Escalator and stair landing spillback masking downstream route choices`.
- STEP 5/6 NODE constraint: local landing spillback can hide downstream route choices; local route visibility is not executable downstream availability. Runnable validation in `computations/2026-06-21-conway-spillback-lookahead.py`; output `computations/2026-06-21-conway-spillback-lookahead.txt`.
- STEP 9 method #10 `test extreme cases`; selected transfer `A_phase_lookahead_spillback`.
- Result: local positive phase cues for true `zeta'/zeta` on the left strip remain downstream-available much more often than finite/random controls, but the right side collapses true and finite. This is the same content as the kinetic-proofreading lifetime finding in local-cue/lookahead language, not a new independent non-reducing result. No chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Membrane compartments are dynamic probability zones `[DEAD END — soft-zone picture reduces to existing left-strip phase-defect]`
Seed RandomNode = "Cross-border legal and resolution differences affect how losses propagate" → Step 1 cold Codex broad list → rng#2 = Membrane compartmentalization → Step 3 cold Codex narrow list → rng#6 = NODE "Membrane compartments are frequently dynamic probability zones, not fixed physical boxes".
- STEP 5 constraint: compartment membership is soft, probabilistic, moving, and fuzzy-boundary; a fixed hard box can misread occupancy.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-membrane-probability-zones.py`; output `computations/2026-06-21-hgt-NODE-membrane-probability-zones.txt`. Strengthened dynamic-zone simulation validates the NODE: dynamic soft zone has soft occupancy std `0.160944` versus fixed box `0.083995`, hard-box occupancy shifts to `0.441151`, and hard-boundary crossing rises to `0.042448`.
- STEP 7 gate: membrane compartment formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep soft membership but apply it to continuum differential strip observables.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `soft-strip-membership` (`40`, normalized `0.3509`) over `curvature-sorting-map` (`87`) and `raft-lifetime-excursions` (`93`). Script `computations/2026-06-21-hgt-STEP8-membrane-probability-ht-zones.py`; output `computations/2026-06-21-hgt-STEP8-membrane-probability-ht-zones.txt`.
- STEP 9 method rng#2 = attack as false. Gamma-only and random-phase controls were included. True zeta has a left-biased soft-zone center (`left_center_frac=0.761111` on `[100,170]`, `0.811111` on `[500,570]`), random-phase is near/below neutral (`0.433333`, `0.472222`), while finite Euler is intermediate (`0.577778`, `0.572222`). Gamma-only exposes a degenerate fuzzy-boundary artifact (`fuzzy_mean=1.0`), so the raw fuzzy statistic cannot be claimed.
- STEP 10 verdict: DEAD END for new knowledge. The viable part is the left-strip soft-zone center bias, but that reduces to the already-posted phase-carrier/left-strip findings (Dyson ids 731/733/735), not a new HT constraint.
- STEP 11 method rng#13 = find a monotone quantity. Script `computations/2026-06-21-hgt-STEP11-membrane-zone-monotone.py`; output `computations/2026-06-21-hgt-STEP11-membrane-zone-monotone.txt`. True-zeta left-center bias is stable across quantile and prime-count tests (`0.7667`/`0.7733`), while finite Euler bias decreases with prime count (`0.7133→0.4933` on `[100,170]`, `0.7533→0.6067` on `[500,570]`). This is a useful restatement of finite-Euler stress against the left-strip phase defect, not independent new content.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Membrane compartments are frequently dynamic probability zones, not fixed physical boxes".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Hidden collider bias from conditioning on survival `[DEAD END — zero-shadow collider shift is generic conditioning]`
Seed RandomNode = "Overlooking that transition estimates can absorb systematic observation bias" → Step 1 cold Codex broad list → rng#15 = Survivorship-biased stochastic modeling → Step 3 cold Codex narrow list → rng#10 = NODE "Hidden collider bias introduced by conditioning on survival".
- STEP 5 constraint: conditioning on survival can create dependence between variables that are independent in the source population when survival is a common effect/collider of those variables.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-survival-collider-bias.py`; output `computations/2026-06-21-hgt-NODE-survival-collider-bias.txt`. Monte Carlo validation: source `corr(x,y)=-0.00206`; conditioning on `linear_x_plus_y` survival gives survivor corr `-0.17762`, `substitution_x_or_y` gives `-0.22893`, and `opposition_x_minus_y` gives `+0.21510`. Controls where survival depends on `x` only or independent `z` keep correlation near zero. Strength sweep makes the induced correlation move from `-0.00255` at strength `0.0` to `-0.34253` at strength `2.4`.
- STEP 7 gate: the collider formula `P(x,y|S)=P(S|x,y)P(x)P(y)/P(S)` does not apply unchanged to HT functions. A non-blind transfer must replace survival by a gate on continuum differential data, not by discrete values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-survival-collider-ht.py` created three attempts: `zero-shadow-conditioning`, `phase-defect-survivor`, and `component-survival-collider`; Levenshtein selected `zero-shadow-conditioning` (`108`, vs `114`, `119`). Output: `computations/2026-06-21-hgt-STEP8-survival-collider-ht.txt`.
- STEP 9 method rng#23 = classify boundary cases. Conditioning on deep zero-shadows changes correlations between `log|Γ∞|` and `log|P|`. At `σ=0.3`, true shift is `+0.30789`, finite shift `-0.27023`, random-phase shift `+0.11765` for the 10% deepest zero-shadow gate. At `σ=0.5`, true shift `+0.50671`, finite `+0.19319`, random-phase `+0.26395`. At `σ=1.2`, true/finite/amplitude-matched controls largely collapse.
- STEP 11 method rng#1 = split into subclaims. `computations/2026-06-21-hgt-STEP11-survival-collider-subclaims.py`; output `computations/2026-06-21-hgt-STEP11-survival-collider-subclaims.txt`. The subclaim split showed the apparent true-vs-finite distinction is not robustly HT-native: amplitude-matched finite often reproduces or exceeds the true shift (`σ=0.3`, q=0.20: true `+0.25792`, amplitude-matched finite `+0.28274`; `σ=0.5`, q=0.30: true `+0.23004`, amplitude-matched finite `+0.32546`), and random-phase controls can also dominate (`σ=0.7`, q=0.05: random-phase `+0.40719` vs true `+0.24007`).
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the selected HT transfer reduces to generic conditioning on zero-shadow/low-amplitude valleys plus amplitude/phase-control artifacts. It does not produce an independent non-reducing observable; no chat post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Hidden collider bias introduced by conditioning on survival".

## Conway — option-similarity suppression / false amplitude competitors (2026-06-21)

- STEP 1/2: seed `Escalator and stair landing spillback masking downstream route choices`; cold list -> rng #16 `Option value suppression in congested choice nodes`.
- STEP 3/4: cold list -> rng #3 NODE `Similar alternatives compete more strongly than dissimilar alternatives`.
- STEP 5/6 NODE constraint: similarity-weighted divisive normalization; similar distractors suppress target value much more than dissimilar distractors. Runnable validation in `computations/2026-06-21-conway-option-similarity-suppression.py`; output `computations/2026-06-21-conway-option-similarity-suppression.txt`.
- STEP 9 method #21 `build a dependency chain`; selected transfer `A_phase_similarity_suppression` by Levenshtein.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-option-similarity-battery.py`, output `computations/2026-06-21-conway-STEP12-option-similarity-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: amplitude-similar alternatives can be false competitors for the left-strip phase carrier. Random-phase controls preserve true magnitudes and therefore look similar in amplitude space, but they are phase-dissimilar. Mean random false-similarity (`amp_sim - phase_sim`) is +0.4281,+0.5560,+0.5592,+0.6140,+0.4416,+0.3512,+0.3946 at sigma 0.2,0.3,0.4,0.5,0.7,0.9,1.2, but raw true value collapses by sigma 0.9/1.2, bounding the claim to the left/nonzero region. Finite Euler prime-count stress at sigma=0.3 keeps finite phase similarity low, so larger finite cutoffs are not true phase-neighbors.
- Grade: non-reducing experimental control/enrichment of the phase-carrier observable, not a theorem. The new node contribution is metric-dependence of competition: amplitude-normalization can manufacture false suppression, phase-feature space is the relevant constraint space.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Turing boundary conditions select/suppress modes `[DEAD END — finite boundary-basis projection, not HT-native mode selection]`
Seed RandomNode = "Membrane compartments are frequently dynamic probability zones, not fixed physical boxes" → Step 1 cold Codex broad list → rng#6 = Turing patterns in morphogenesis → Step 3 cold Codex narrow list → rng#2 = NODE "Boundary conditions can select or suppress pattern modes as strongly as reaction-diffusion parameters".
- STEP 5 constraint: reaction-diffusion parameters do not determine patterns alone; boundary conditions define the admissible mode spectrum and can select/suppress modes.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-turing-boundary-mode-selection.py`; output `computations/2026-06-21-hgt-NODE-turing-boundary-mode-selection.txt`. The same linearized activator-inhibitor matrix gives different admissible mode counts/best modes across periodic, Neumann, Dirichlet, and mixed boundaries; e.g. at length `4.0`, unstable modes are periodic `4`, Neumann `6`, Dirichlet `5`, mixed `7`, with best mode shifting.
- STEP 7 gate: Turing PDE formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep boundary-admissible mode projection but apply it to continuum differential strip observables.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `strip-boundary-modes` over `zero-neighborhood-growth` and `prime-diffusion-operator`. Script `computations/2026-06-21-hgt-STEP8-turing-boundary-ht-modes.py`; output `computations/2026-06-21-hgt-STEP8-turing-boundary-ht-modes.txt`.
- STEP 9 method rng#15 = strengthen the conjecture. Required actual dominant-mode switching across boundary bases. True zeta, finite Euler, and random-phase all exhibit boundary-sensitive best-mode switching and active-mode range changes; controls do not isolate HT-specific structure. Example `[100,170]`, `σ=0.3`: true zeta distinct best modes `2`, finite Euler `2`, random-phase `4`.
- STEP 10 verdict: DEAD END for new knowledge. Boundary bases affect finite projections of every rough signal; this does not produce an HT-native boundary-selection claim.
- STEP 11 method rng#18 = look for the right theorem. Script `computations/2026-06-21-hgt-STEP11-turing-boundary-basis-theorem.py`; output `computations/2026-06-21-hgt-STEP11-turing-boundary-basis-theorem.txt`. Captured energy changes with truncation and basis for both true and finite profiles, consistent with ordinary finite basis/projection effects rather than a new theorem.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Boundary conditions can select or suppress pattern modes as strongly as reaction-diffusion parameters".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Descendant tolerance mismatch after extinction filters `[DEAD END — refuge conditioning creates generic phase-bias]`
Seed RandomNode = "Hidden collider bias introduced by conditioning on survival" → Step 1 cold Codex broad list → rng#5 = Extinction filters in evolutionary biology → Step 3 cold Codex narrow list → rng#19 = NODE "Environmental tolerance inferred from modern descendants may not match tolerance in extinct relatives".
- STEP 5 constraint: descendants observed after an extinction filter can have tolerances altered by survival selection, refuge access, drift, and post-filter adaptation; modern descendant tolerance is not a direct proxy for extinct-relative tolerance.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-descendant-tolerance-mismatch.py`; output `computations/2026-06-21-hgt-NODE-descendant-tolerance-mismatch.txt`. The simulation validates the constraint: after survival, adaptation `±0.8` shifts inferred mean tolerance by about `±0.66066`, and drift/adaptation lowers ancestor-modern tolerance correlation as far as `0.40818`. Survival also induces ancestor-refuge correlation (`source=-0.00448`, survivor `-0.32185`).
- STEP 7 gate: descendant-proxy/tolerance inference does not apply unchanged to HT functions. A non-blind transfer must compare proxy tolerance readouts on continuum differential data, not infer from discrete `ζ(n)` or a handpicked function.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-descendant-tolerance-ht.py` created three attempts: `refuge-conditioned-collider`, `completion-drift-family`, and `descendant-proxy-strip`; Levenshtein selected `refuge-conditioned-collider` (`110`, vs `116`, `137`). Output: `computations/2026-06-21-hgt-STEP8-descendant-tolerance-ht.txt`.
- STEP 9 method rng#2 = attack it as false. Low-exposure/refuge conditioning inflates phase-tolerance for both true and finite controls. At `σ=0.3`, true source/survivor phase is `0.42543 → 1.0408` (`+0.61542`), while finite is `0.0099236 → 0.19824` (`+0.18832`). At `σ=0.7`, finite bias exceeds true (`+0.88549` vs `+0.80314`), and at `σ=1.2` true/finite collapse (`+0.28549` vs `+0.28171`).
- STEP 11 method rng#19 = write the fake proof. `computations/2026-06-21-hgt-STEP11-descendant-fake-proof-gap.py`; output `computations/2026-06-21-hgt-STEP11-descendant-fake-proof-gap.txt`. The fake proof would claim refuge-conditioned phase-tolerance bias is HT-specific. The exact gap fails: amplitude-matched finite and random-phase controls reproduce it. Examples: at `σ=0.3`, q=0.1, true bias `+1.0136`, amplitude-matched finite `+1.1772`, random-phase `+0.76961`; at `σ=1.2`, q=0.3, all controls cluster around `+0.28`.
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the selected transfer is a generic low-amplitude/refuge conditioning artifact and not an independent HT-native observable. No chat post.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Environmental tolerance inferred from modern descendants may not match tolerance in extinct relatives".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Interface supersaturation differs from bulk `[DEAD END — interface/bulk enrichment reduces to left-strip phase-defect]`
Seed RandomNode = "Boundary conditions can select or suppress pattern modes as strongly as reaction-diffusion parameters" → Step 1 cold Codex broad list → rng#6 = Crystal growth at interfaces → Step 3 cold Codex narrow list → rng#5 = NODE "Local supersaturation near the interface can differ substantially from the measured bulk value because of diffusion limits and depletion zones".
- STEP 5 constraint: crystal growth is controlled by local boundary-layer supersaturation at the interface, which can differ sharply from measured bulk concentration under diffusion/consumption.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-crystal-interface-depletion.py`; output `computations/2026-06-21-hgt-NODE-crystal-interface-depletion.txt`. The steady diffusion-consumption model validates the constraint: for bulk `1.00`, increasing Damköhler number from `0.05` to `12.00` drops interface/bulk from `0.975312` to `0.082763`.
- STEP 7 gate: crystal diffusion formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep bulk-vs-interface comparison but apply it to continuum differential strip observables.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `bulk-interface-strip` (`42`, normalized `0.3206`) over `zero-boundary-layer` (`80`) and `prime-diffusion-depletion` (`89`). Script `computations/2026-06-21-hgt-STEP8-crystal-interface-ht-depletion.py`; output `computations/2026-06-21-hgt-STEP8-crystal-interface-ht-depletion.txt`.
- STEP 9 method rng#15 = strengthen the conjecture. Required side-specific interface/bulk asymmetry. True zeta shows left-interface enrichment and right depletion against the strip bulk: `[100,170]` left ratio `2.039604`, right ratio `0`; `[500,570]` left ratio `1.832676`, right ratio `0`. Finite Euler/random-phase are depleted on both sides or near zero.
- STEP 10 verdict: tempting but DEAD END for new knowledge. The phenomenon is the same left-strip phase-carrier defect seen through a bulk/interface ratio.
- STEP 11 method rng#10 = test extreme cases. Script `computations/2026-06-21-hgt-STEP11-crystal-interface-extremes.py`; output `computations/2026-06-21-hgt-STEP11-crystal-interface-extremes.txt`. The asymmetry persists for strips `[0.1,0.9]`, `[0.2,0.8]`, and weakens near `[0.4,0.6]`, but collapses to zero outside the strip (`[0.8,1.4]`, `[1.1,1.7]`) for both true and finite. This confirms localization to the existing left critical-strip phase-defect problem.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Local supersaturation near the interface can differ substantially from the measured bulk value because of diffusion limits and depletion zones".

## Conway — immune-feedback direction / phase-memory entropy gain (2026-06-21)

- STEP 1/2: seed `Similar alternatives compete more strongly than dissimilar alternatives`; cold list -> rng #5 `Cross-immunity in antigenic space`.
- STEP 3/4: cold list -> rng #19 NODE `Population immunity feeds back on viral evolution by changing which antigenic directions are selectively favored`.
- STEP 5/6 NODE constraint: accumulated immunity modifies the fitness landscape and can rotate the favored antigenic direction; strengthened from magnitude change to direction change. Runnable validation in `computations/2026-06-21-conway-immune-feedback-direction.py`; output `computations/2026-06-21-conway-immune-feedback-direction.txt`.
- STEP 9 method #15 `strengthen the conjecture`; selected phase-memory direction after a Levenshtein tie with amplitude-memory; Step 12 explicitly controls the tie/confound.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-immune-feedback-battery.py`, output `computations/2026-06-21-conway-STEP12-immune-feedback-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: memory-penalized sigma-lane selection gives true `zeta'/zeta` a larger phase-feedback entropy gain than finite/random controls. At beta=0.55, phase-memory entropy gain/mean rotation: true +0.604/0.1047, finite +0.169/0.0849, random +0.028/0.0395. Beta=0 kills rotation; finite-prime stress N=30..240 decreases finite entropy gain rather than converging to true.
- Boundary: amplitude-memory also rotates and is a confound; do not claim phase-only rotation. The valid non-reducing content is history-conditioned phase-direction redistribution after beta=0, random, amplitude, and finite-cutoff controls are named.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Oxygen depletion creates differential aeration in corrosion pits `[DEAD END — potential statistic reduces to left-strip phase-carrier defect]`
Seed RandomNode = "Local supersaturation near the interface can differ substantially from the measured bulk value because of diffusion limits and depletion zones" → Step 1 cold Codex broad list → rng#8 = Corrosion pitting → Step 3 cold Codex narrow list → rng#6 = NODE "Oxygen depletion inside the pit creates a strong differential aeration cell".
- STEP 5 constraint: a hidden pit interior can become oxygen-depleted relative to the mouth/bulk, creating an electrochemical potential that drives anodic growth despite benign-looking surroundings.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-pitting-differential-aeration.py`; output `computations/2026-06-21-hgt-NODE-pitting-differential-aeration.txt`. The diffusion/depletion model validates the NODE: deep/narrow/high-consumption pits reach strong potentials, e.g. depth `4.0`, mouth `0.25`, consumption `2.0` gives bottom oxygen `0.000012` and potential `11.313708`.
- STEP 7 gate: corrosion aeration formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep mouth-vs-bottom potential but apply it to continuum differential strip observables.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `strip-mouth-bottom` (`28`, normalized `0.2569`) over `prime-oxygen-depletion` (`62`) and `zero-cavity-cover` (`71`). Script `computations/2026-06-21-hgt-STEP8-pitting-aeration-ht-potential.py`; output `computations/2026-06-21-hgt-STEP8-pitting-aeration-ht-potential.txt`.
- STEP 9 method rng#21 = build a dependency chain. The script made the dependency explicit: potential ⇒ left-bottom phase-defect lower bound + right-mouth depletion. True zeta has very large median potential (`18.980924` on `[100,170]`, `19.546904` on `[500,570]`); finite Euler/random-phase have median `0` with broad sign-mixed tails.
- STEP 10 verdict: visually strong but DEAD END for new knowledge. The dependency chain is exactly the existing left-strip phase-carrier defect and right-side depletion.
- STEP 11 method rng#5 = make it visual. Script `computations/2026-06-21-hgt-STEP11-pitting-potential-visual.py`; output `computations/2026-06-21-hgt-STEP11-pitting-potential-visual.txt`. True zeta produces mostly `#`/positive potential (`frac_pos=0.844444`, `0.944444`), while finite Euler/random-phase are sign-mixed with median zero. This is useful visualization only; not posted.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Oxygen depletion inside the pit creates a strong differential aeration cell".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Allee thresholds make extinction risk sharply nonlinear `[DEAD END — threshold survival repackages phase-carrier run persistence]`
Seed RandomNode = "Environmental tolerance inferred from modern descendants may not match tolerance in extinct relatives" -> Step 1 cold Codex broad list -> rng#15 = Stochastic extinction models -> Step 3 cold Codex narrow list -> rng#6 = NODE "The effect of Allee thresholds on making extinction risk discontinuous or sharply nonlinear".
- Workflow reread before the tick: Step 12 now requires interpretation, worklog/chat posting, all meaningful scientific-method follow-ups, and big-picture/theorem-shape contextualization for any non-reducing result. This round did not trigger Step 12 because it reduced to known phase-carrier persistence.
- STEP 5 constraint: a strong Allee threshold is not merely lower growth at low abundance; it creates a basin boundary/absorbing-risk cliff. Small changes in initial abundance or threshold location can cause large finite-horizon extinction-risk changes.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-allee-threshold-extinction.py`; output `computations/2026-06-21-hgt-NODE-allee-threshold-extinction.txt`. The simulation validates the NODE: max adjacent extinction-risk jump across initial abundance is `0.16086` with Allee threshold versus `0.00486` without Allee. Moving the threshold at fixed initial abundance gives max adjacent jump `0.10514`; threshold `30 -> 32` changes final median abundance from `87.92857` to `0.00000`.
- STEP 7 gate: the NODE formulas are stochastic birth-death/diffusion or backward-Kolmogorov extinction-risk equations with Allee drift `rN(1-N/K)(N/A-1)` and an absorbing boundary at zero. They do not apply unchanged to HT functions. A non-blind transfer must keep threshold/cliff testing but place it on continuum differential data over `C`, not on discrete `zeta(n)` values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-allee-threshold-ht-phase-cliff.py` created three HT attempts: `phase-defect-allee-threshold`, `zero-tube-critical-front`, and `finite-prime-rescue-noise`. Levenshtein selected `phase-defect-allee-threshold` (`33`, vs `61` and `64`). Output: `computations/2026-06-21-hgt-STEP8-allee-threshold-ht-phase-cliff.txt`.
- STEP 9 method rng#13 = find a monotone quantity. Threshold increase gives monotone nondecreasing extinction risk. At `sigma=0.3`, `[100,170]`, true `zeta'/zeta` risks across thresholds `0,0.05,0.10,0.20,0.35,0.50` are `0.000,0.000,0.250,0.923,1.000,1.000`; finite, amplitude-matched finite, and random-phase controls are already `1.000` throughout at depth 16. At `sigma=0.3`, `[500,570]`, true risks are `0.000,0.000,0.000,0.000,1.000,1.000`, while controls again stay extinct. At `sigma=1.2`, true/finite/amplitude-matched finite collapse.
- STEP 11 method rng#16 = use a minimal counterexample. Script `computations/2026-06-21-hgt-STEP11-allee-minimal-counterexample.py`; output `computations/2026-06-21-hgt-STEP11-allee-minimal-counterexample.txt`. Shallow-depth cases break the tempting threshold-survival statement: at `sigma=0.3`, `[100,170]`, threshold `0`, depth `2`, true survival is `1.000`, but finite `0.724`, amplitude-matched finite `0.552`, and random-phase `0.386` also pass. Right-side cases collapse true and finite: at `sigma=1.2`, threshold `0`, depth `2`, true/finite/amplitude-matched finite all equal `0.955`.
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, and the threshold-cliff transfer is internally coherent, but the only nontrivial HT separation is the already-posted left-strip phase-carrier/run-lifetime persistence under a new Allee-threshold vocabulary. No independent HT-native observable survives the reduce-to-known gate; no chat post.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "The effect of Allee thresholds on making extinction risk discontinuous or sharply nonlinear".

## Conway — singular information geometry / sublevel exponent `[DEAD END — phase-carrier restatement]` (2026-06-21)

- STEP 1/2: seed `Population immunity feeds back on viral evolution by changing which antigenic directions are selectively favored`; cold list -> rng #15 `Information geometry`.
- STEP 3/4: cold list -> rng #19 NODE `Singular models break many standard asymptotic geometric intuitions`.
- STEP 5/6 NODE constraint: regular Fisher/Laplace asymptotics require a nondegenerate quadratic local loss; singular flatter losses change the sublevel-volume/integral exponent. Runnable validation in `computations/2026-06-21-conway-singular-asymptotic-exponent.py`; output `computations/2026-06-21-conway-singular-asymptotic-exponent.txt`.
- STEP 9 method #3 `Reverse it`; selected `A_phase_loss_sublevel_exponent` by Levenshtein.
- HT transfer: phase-loss sublevel volumes on continuum strip traces show true left-strip `zeta'/zeta` has higher small-loss mass than finite/random controls, while true and finite collapse on the right.
- Verdict: reducing. The statistic rephrases the already-known left-strip phase-carrier obstruction and direct Fisher degeneracy reduces to existing Fisher-wall work. No chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Nitrate masks root-zone oxygen stress `[DEAD END — duplicate of specificity/promiscuity amplitude-vs-phase split]`
Seed RandomNode = "Oxygen depletion inside the pit creates a strong differential aeration cell" → Step 1 cold Codex broad list → rng#3 = Root-zone anoxia → Step 3 cold Codex narrow list → rng#4 = NODE "Nitrate reduction can mask oxygen stress by serving as an alternate electron sink, but it does not replace aerobic ATP production".
- STEP 5 constraint: an alternate electron sink can make a stress proxy look relieved while the primary aerobic-energy function remains deficient.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-root-anoxia-nitrate-mask.py`; output `computations/2026-06-21-hgt-NODE-root-anoxia-nitrate-mask.txt`. The model validates the NODE: at low oxygen (`o2=0.02`) and nitrate `1.0/3.0`, stress is masked (`1`) while energy remains deficient (`1`), with ATP only `0.310862/0.329720` of oxic.
- STEP 7 gate: root metabolism formulas do not apply unchanged to HT functions. Minimal non-blind transfer must compare a scalar relief proxy with a phase-specific continuum function proxy.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `amplitude-mask-phase-atp` (`55`, normalized `0.4167`) over `finite-euler-nitrate` (`89`) and `random-phase-fermentation` (`90`). Script `computations/2026-06-21-hgt-STEP8-root-anoxia-ht-mask.py`; output `computations/2026-06-21-hgt-STEP8-root-anoxia-ht-mask.txt`.
- STEP 9 method rng#13 = find a monotone quantity. Finite Euler behaves like the masking alternate sink: at `σ=0.3`, `[100,170]`, relief proxy is `2.331672` while phase function is `0.000000`; relief increases with prime count (`1.584614→2.436192`) while phase function remains near zero. Similar at `[500,570]` (`1.515855→2.619516`, phase near zero).
- STEP 10 verdict: DEAD END for new knowledge. This duplicates the hypercycle specificity/promiscuity result (Dyson ids 734/735): broad scalar amplitude can look healthy while phase-specific coupling fails.
- STEP 11 method rng#13 = find a monotone quantity. Script `computations/2026-06-21-hgt-STEP11-root-anoxia-sink-sweep.py`; output `computations/2026-06-21-hgt-STEP11-root-anoxia-sink-sweep.txt`. Artificial alternate-sink strength makes scalar relief rise monotonically while phase function stays zero, confirming that scalar relief is not a valid replacement for the phase constraint.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Nitrate reduction can mask oxygen stress by serving as an alternate electron sink, but it does not replace aerobic ATP production".

## Penrose — Machine R7 — solvent-mediated phase transformation after apparent crystallization `[DEAD END]`

- NODE constraint: visible solid completion can precede hidden polymorph conversion. Toy M/A/B crystallization validated this: solvent-on apparent completion against the dry primary plateau occurred by `t=0.6` with `B_frac=0.000115`, while `B_frac` reached `0.214341` at `t=80` and `0.951800` at `t=120`.
- STEP 8 selected by Levenshtein: `sigma_cooling_path` (224) over `prime_cutoff_aging` (231) and `beta_completion_lag` (232).
- STEP 9 method #19 fake proof: visible boundary-center amplitude class should stabilize before hidden phase composition if an HT post-completion lag exists. It did not: true/finite/random controls reached visible completion only at the final sigma lane, giving no after-completion hidden lag. Remaining structure reduces to known phase-carrier/run-survival behavior.
- STEP 11 method #21 dependency chain: local smoothing as solvent channel. True zeta did not show hidden conversion after visible completion; finite/random lag under smoothing is generic averaging. Verdict: dead end, no chat post.

## Conway — near-neutral measurement collapse / hidden phase advantage (2026-06-21)

- STEP 1/2: seed `Singular models break many standard asymptotic geometric intuitions`; cold list -> rng #15 `Evolutionary fitness landscapes with neutral networks`.
- STEP 3/4: cold list -> rng #20 NODE `Experimental fitness measurements often collapse near-neutral differences that matter over evolutionary time`.
- STEP 5/6 NODE constraint: finite measurement resolution collapses tiny selection coefficients to neutral, but repeated evolution compounds them. Runnable validation in `computations/2026-06-21-conway-near-neutral-collapse.py`; output `computations/2026-06-21-conway-near-neutral-collapse.txt`.
- STEP 9 method #1 `Split it into subclaims`; selected `A_phase_microadvantage_accumulation` by Levenshtein.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-near-neutral-battery.py`, output `computations/2026-06-21-conway-STEP12-near-neutral-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: around sigma `0.7`, paired phase-defect advantage `Delta_true - Delta_finite` has a positive near-neutral hidden layer under eps `0.2`: mean hidden fraction `0.707`, hidden mean `+0.04167`, hidden-positive fraction `0.664`, while total/visible means are small. Prime-count stress remains positive to N=400; the statistic decays by sigma `0.9` and vanishes at `1.2`; random-phase controls lack the same hidden fraction/sign bias.
- Grade: non-reducing experimental transition-band enrichment of the phase-carrier line, not a theorem. Posted to `#research` as conway id 748.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Redox activity coefficients shift effective potential `[DEAD END — activity-shift statistic equals phase-defect restatement]`
Seed RandomNode = "Nitrate reduction can mask oxygen stress by serving as an alternate electron sink, but it does not replace aerobic ATP production" → Step 1 cold Codex broad list → rng#10 = Redox buffering → Step 3 cold Codex narrow list → rng#10 = NODE "Ionic strength and activity coefficients can shift effective redox potentials away from values calculated using concentrations".
- STEP 5 constraint: ideal concentration ratios are not the operative redox potential; activity coefficients under actual ionic environment can shift the effective potential substantially.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-redox-activity-coefficients.py`; output `computations/2026-06-21-hgt-NODE-redox-activity-coefficients.txt`. The Davies-style activity correction validates the NODE: at ionic strength `0.50`, charge pair `(3,2)` shifts potential from ideal `1.386294` to `-0.165060` (shift `-1.551354`).
- STEP 7 gate: redox activity formulas do not apply unchanged to HT functions. Minimal non-blind transfer must compare ideal amplitude-ratio potential to phase/activity-corrected complex potential on continuum differential data.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `phase-activity-potential` (`36`, normalized `0.3025`) over `gamma-activity-coeff` (`82`) and `prime-ionic-strength` (`85`). Script `computations/2026-06-21-hgt-STEP8-redox-activity-ht-potential.py`; output `computations/2026-06-21-hgt-STEP8-redox-activity-ht-potential.txt`.
- STEP 9 method rng#2 = attack as false. The attack showed direct reduction: for true zeta at `σ=0.3`, shift median is `-0.431024` on `[100,170]` and `-0.530177` on `[500,570]`, exactly the negative phase-defect median. Finite Euler/random-phase controls do not show the same negative median shift.
- STEP 10 verdict: DEAD END for new knowledge. The activity-corrected-potential statistic is algebraically just another phase-defect representation.
- STEP 11 method rng#8 = look for similar objects. Script `computations/2026-06-21-hgt-STEP11-redox-activity-similar.py`; output `computations/2026-06-21-hgt-STEP11-redox-activity-similar.txt`. Smooth sine/antiphase controls do not reproduce the negative median shift, confirming specificity but not novelty: the surviving content is still the known phase-carrier defect.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Ionic strength and activity coefficients can shift effective redox potentials away from values calculated using concentrations".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Repeated small boundary exceptions `[DEAD END — cumulative debt reduces to phase-defect mass/run persistence]`
Seed RandomNode = "The effect of Allee thresholds on making extinction risk discontinuous or sharply nonlinear" -> Step 1 cold Codex broad list -> rng#19 = Boundary crises -> Step 3 cold Codex narrow list -> rng#5 = NODE "Repeated small exceptions usually matter more than one dramatic violation".
- STEP 5 constraint: a boundary crisis is not only a single-event severity threshold. Unenforced small exceptions accumulate precedent debt and access expectation; one dramatic violation is easier to identify and can trigger immediate consequence/reset.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-boundary-small-exceptions.py`; output `computations/2026-06-21-hgt-NODE-boundary-small-exceptions.txt`. The simulation validates the NODE mechanism. One dramatic severity-1 violation is enforced/reset (`consequences=0.97592`, `access_expectation=0.04817`, `collapse_frac=0.00492`), while five medium exceptions of equal total severity create much larger access expectation (`1.47594`) with few consequences (`0.09133`). Operationally defining/enforcing small exceptions removes the effect: twenty small exceptions with a low trigger give `access_expectation=0.27294` and no collapse.
- STEP 7 gate: social-boundary formulas here are cumulative hazard/precedent-debt/enforcement-threshold models, not formulas that apply unchanged to HT functions. A non-blind transfer must keep the repeated-small-exception versus dramatic-reset distinction on continuum differential data, not use discrete values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-boundary-exceptions-ht-debt.py` created three HT attempts: `small-exception-accumulator`, `role-ambiguity-access-map`, and `single-spike-repair-test`. Levenshtein selected `small-exception-accumulator` (`0`, vs `75` and `80`). Output: `computations/2026-06-21-hgt-STEP8-boundary-exceptions-ht-debt.txt`.
- STEP 9 method rng#20 = name the missing lemma. Missing lemma: subthreshold cumulative boundary debt for true `zeta'/zeta` is not determined by one-point phase-defect mass, positive occupancy, or run persistence. The selected transfer failed to establish that lemma. Baseline at `sigma=0.3`, `[100,170]`: true has `small_count=167`, `dramatic_count=92`, `max_debt=2.159`, `crises=0`; finite has `max_debt=1.722`, random-phase `2.734`, also `crises=0`. Only the artificial `true-sorted-clipped` control crosses (`max_debt=4.035`, `crises=24`), showing the mechanism can be manufactured by rearranging/clipping phase-defect mass.
- STEP 11 method rng#10 = test extreme cases. Script `computations/2026-06-21-hgt-STEP11-boundary-exceptions-extremes.py`; output `computations/2026-06-21-hgt-STEP11-boundary-exceptions-extremes.txt`. Extreme regimes kill novelty: permissive/no-reset turns the statistic into total positive phase-defect mass (`sigma=0.3`: true `48` crises, finite `5`, random `14`, true-shuffled `48`); strict reset kills all cases; right-strip `sigma=1.2` collapses true and finite (`permissive_no_reset` both `5` crises, baseline both `0`).
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the HT transfer either does not trigger a crisis under the selected boundary-debt rule or reduces to already-known phase-defect mass/run persistence under permissive/clipped extremes. No independent HT-native observable survives; no chat post.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Repeated small exceptions usually matter more than one dramatic violation".

## Penrose — Machine R8 — thermal hydration transitions without drying `[DEAD END]`

- NODE constraint: with moisture fixed, crossing hydrate-temperature thresholds can change phase fraction and pressure. Toy hysteresis model: no-crossing `Tamp=0.3` gave no transition; `Tamp=1.0` gave hydrated range `0.000-1.000`; `Tamp=9.0` gave repeated hydration/dehydration pressure.
- STEP 8 selected by Levenshtein: `zero_tube_thermal_hysteresis` (210) over `prime_cutoff_hydration_cycle` (234) and `isoamplitude_sigma_temperature` (248).
- STEP 9 method #13: tube radius around critical-line zeros is a monotone by construction; true `zeta'/zeta` pressure spikes inside tubes while finite Euler stays flat. This reduces to ordinary zero/pole proximity and finite-Euler smoothness.
- STEP 11 method #5: amplitude-bin/sigma-lane heatmap visualized the same phase-carrier structure; no independent HT content. Verdict: dead end, no chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Existing concrete corrosion products sustain localized corrosion `[DEAD END — hysteresis threshold is model-tuned phase-defect]`
Seed RandomNode = "Ionic strength and activity coefficients can shift effective redox potentials away from values calculated using concentrations" → Step 1 cold Codex broad list → rng#15 = Concrete corrosion and durability → Step 3 cold Codex narrow list → rng#17 = NODE "Existing corrosion products and pits can sustain localized corrosion even after external chloride exposure is reduced".
- STEP 5 constraint: localized corrosion has memory/hysteresis; once pit products and acidification are established, reducing external chloride may not reset the local state.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-concrete-corrosion-memory.py`; output `computations/2026-06-21-hgt-NODE-concrete-corrosion-memory.txt`. After retuning to a bounded state model, the NODE is validated: short pulses repair, but long pulse plus strong memory sustains tail growth (`pulse=60`, memory `0.08`, final pit `0.347502`, sustained `1`; `pulse=90`, memory `0.08`, final pit `0.581909`, sustained `1`).
- STEP 7 gate: corrosion hysteresis formulas do not apply unchanged to HT functions. Minimal non-blind transfer must keep pulse/removal memory and drive it with continuum differential stress.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `stress-pulse-memory` (`45`, normalized `0.3309`) over `zero-scar-hysteresis` (`95`) and `finite-euler-rust` (`99`). Script `computations/2026-06-21-hgt-STEP8-concrete-corrosion-ht-memory.py`; output `computations/2026-06-21-hgt-STEP8-concrete-corrosion-ht-memory.txt`.
- STEP 9 method rng#18 = look for the right theorem. Candidate theorem was a bounded hysteresis threshold after driver removal. At memory `0.08`, true zeta at `σ=0.3`, `[500,570]` sustained (`tail_growth=0.003856`, final state `0.457801`), while finite Euler/random-phase did not.
- STEP 10 verdict: not promoted. It is a candidate visualization, but it depends on arbitrary hysteresis thresholding of the known phase-defect stress.
- STEP 11 method rng#18 = look for the right theorem. Script `computations/2026-06-21-hgt-STEP11-concrete-memory-threshold.py`; output `computations/2026-06-21-hgt-STEP11-concrete-memory-threshold.txt`. Sweeping memory strength shows true zeta crosses earlier (`mem≈0.06-0.10` depending window), but finite Euler also sustains at high memory (`mem=0.14`). This kills any robust class theorem; it is a model-tuned phase-defect threshold.
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Existing corrosion products and pits can sustain localized corrosion even after external chloride exposure is reduced".

## Round (THE-MACHINE revised workflow, hgt) — NODE = Retrofit fatigue-prone details `[DEAD END — notch amplification is generic p-norm stress concentration]`
Seed RandomNode = "Repeated small exceptions usually matter more than one dramatic violation" -> Step 1 cold Codex broad list -> rng#10 = Architecture: material fatigue and microfractures -> Step 3 cold Codex narrow list -> rng#14 = NODE "Fatigue-prone details introduced by later retrofits, drilled holes, service penetrations, or equipment mounts".
- STEP 5 constraint: fatigue life is controlled by local stress concentration and load history, not only nominal design stress. A late drilled hole, service penetration, or equipment mount can multiply local stress enough that post-retrofit damage dominates earlier low-stress history.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-retrofit-fatigue-details.py`; output `computations/2026-06-21-hgt-NODE-retrofit-fatigue-details.txt`. The Miner's-rule/S-N simulation validates the NODE. A rounded service hole amplifies post-retrofit damage by `5.027e+01`, a sharp drilled hole by `4.267e+02`, and an equipment mount cluster by `1.704e+03`; the sharp drilled hole makes retrofit damage `0.99727` of total damage. Near the endurance boundary, amplification grows from `1.895e+02` at endurance `50` to `7.947e+02` at endurance `68`.
- STEP 7 gate: stress-concentration factors, S-N curves, Paris/Miner fatigue formulas, and notch factors do not apply unchanged to HT functions. A non-blind transfer must keep sparse local concentration plus nonlinear fatigue accumulation on a continuum differential observable over `C`.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-retrofit-fatigue-ht-notches.py` created three HT attempts: `strip-notch-amplifier`, `prime-mount-cutoff`, and `zero-penetration-cavity`. Levenshtein selected `strip-notch-amplifier` (`53`, vs `57` and `65`). Output: `computations/2026-06-21-hgt-STEP8-retrofit-fatigue-ht-notches.txt`.
- STEP 9 method rng#6 = ask what action is happening. The action is local sparse stress concentration followed by nonlinear fatigue exponentiation. The selected transfer applies sparse notch masks to `log(1+|Gamma_infty + P|)` and measures p-norm damage. It is not HT-specific: gamma-only shows enormous amplification from the endurance-floor artifact; finite Euler often has larger amplification than true zeta (`sigma=0.3`, `[100,170]`, periodic: true `1.277e+03`, finite `7.429e+04`), and random-phase controls can dominate.
- STEP 11 method rng#4 = change the viewpoint. Script `computations/2026-06-21-hgt-STEP11-retrofit-viewpoint.py`; output `computations/2026-06-21-hgt-STEP11-retrofit-viewpoint.txt`. Recasting the statistic against a random-notch null distribution killed the claim: bad-retrofit placement is usually below the random median for true zeta (`sigma=0.3`, exponent 5: bad/random median ratio `0.169`, percentile `0.008`; `sigma=0.5`, exponent 5: ratio `0.131`, percentile `0.025`). Random-phase can be more exceptional (`sigma=1.2`, exponent 8: ratio `2.447`, percentile `1.000`), and true/finite collapse on the right.
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the HT transfer is a generic notch/p-norm/endurance-threshold artifact plus known roughness/zero-proximity behavior. No independent HT-native fatigue observable survives; no chat post.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Fatigue-prone details introduced by later retrofits, drilled holes, service penetrations, or equipment mounts".

## Conway — thin-bridge sampling / zero-shadow topology (2026-06-21)

- STEP 1/2: seed `Experimental fitness measurements often collapse near-neutral differences that matter over evolutionary time`; cold list -> rng #6 `Neutral network percolation`.
- STEP 3/4: cold list -> rng #9 NODE `Sampling methods often miss thin bridges between components`.
- STEP 5/6 NODE constraint: sparse sampling can miss bridge continuity and falsely fragment a connected network. Runnable validation in `computations/2026-06-21-conway-thin-bridge-sampling.py`; corrected output `computations/2026-06-21-conway-thin-bridge-sampling-corrected.txt`.
- STEP 9 method #15 `Strengthen the conjecture`; Levenshtein selected `B_zero_shadow_bridge_graph`. Initial phase-threshold output is discarded as noncompliant.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-thin-bridge-battery.py`, output `computations/2026-06-21-conway-STEP12-thin-bridge-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: at relative zero-shadow threshold `1.00`, true `zeta'/zeta` forms a single component spanning both sigma and t in two strong windows, while finite Euler remains fragmented/non-t-spanning across N=30..400 and random-phase remains highly fragmented. Uniform sampling can falsely destroy true t-spanning, exposing a bridge-continuity artifact.
- Boundary: at threshold `1.25`, finite can connect in one window, so the claim is threshold-bounded. Posted to `#research` as conway id 749.

## Conway — neck cycling reversibility `[DEAD END — imposed hysteresis, not HT-native]` (2026-06-21)

- STEP 1/2: seed `Sampling methods often miss thin bridges between components`; cold list -> rng #4 `Percolation necks`.
- STEP 3/4: cold list -> rng #10 NODE `Testing whether neck closure or opening is reversible under cycling conditions`.
- STEP 5/6 NODE constraint: cyclic opening/closure can be reversible thresholding or hysteretic memory; loop area distinguishes them. Runnable validation in `computations/2026-06-21-conway-neck-cycling-reversibility.py`; output `computations/2026-06-21-conway-neck-cycling-reversibility.txt`.
- STEP 9 method #5 `Make it visual`; selected `A_zero_shadow_neck_cycling` by Levenshtein tie.
- Verdict: reducing. Zero-shadow threshold cycling without memory is exactly reversible; with added memory, loop area is model-imposed and not HT-specific, collapsing across true/finite/random at sigma `1.2`. No chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Mass-transfer limitations mimic catalytic hot spots `[DEAD END — transport-normalized hot spots are phase-defect restatement]`
Seed RandomNode = "Fatigue-prone details introduced by later retrofits, drilled holes, service penetrations, or equipment mounts" -> Step 1 cold Codex broad list -> rng#10 = Catalytic hot spots -> Step 3 cold Codex narrow list -> rng#17 = NODE "Mass-transfer limitations that mimic intrinsic catalytic hot-spot activity".
- STEP 5 constraint: observed local catalytic rate is the coupled result of intrinsic turnover and transport supply. Spatially varying mass transfer can make transport-access hot spots look like intrinsically more active catalytic sites.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-catalytic-mass-transfer-hotspots.py`; output `computations/2026-06-21-hgt-NODE-catalytic-mass-transfer-hotspots.txt`. The transport/intrinsic series-resistance model validates the NODE. With uniform intrinsic activity and variable transport, apparent activity correlates with transport (`corr_app_h=0.994282`) and top apparent sites have `top_h_enrichment=1.349108` but `top_k_enrichment=1.000000`. With variable intrinsic activity and uniform transport, apparent activity instead correlates with `k` (`corr_app_k=0.996607`). Increasing intrinsic turnover saturates under mass transfer: median rate gain rises only to `10.577845` from `k_scale=0.1` to `30` while surface concentration collapses to `0.032033`.
- STEP 7 gate: catalytic mass-transfer formulas like `r = k h C_bulk/(h+k)` or resistance sums do not apply unchanged to HT functions. A non-blind transfer must keep apparent-versus-intrinsic hot-spot separation on continuum differential data over `C`.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-mass-transfer-ht-apparent-hotspots.py` created three attempts: `transport-normalized-phase-hotspots`, `component-diffusion-film`, and `finite-prime-supply-layer`. Levenshtein selected `transport-normalized-phase-hotspots` (`42`, vs `57` and `70`). Output: `computations/2026-06-21-hgt-STEP8-mass-transfer-ht-apparent-hotspots.txt`.
- STEP 9 method rng#20 = name the missing lemma. Missing lemma: true-zeta apparent hot spots remain after transport/supply normalization and are not denominator artifacts or the old phase-defect observable. The lemma failed. At `sigma=0.3`, `[100,170]`, true has `defect_med=0.439832`, `apparent_q90=0.708431`, but apparent top sites overlap raw defect top sites by `0.923`; finite/random controls show the same ranking logic. At `sigma=1.2`, true/finite/amplitude-matched finite collapse (`apparent_q90` about `0.300-0.303`).
- STEP 11 method rng#1 = split into subclaims. Script `computations/2026-06-21-hgt-STEP11-mass-transfer-subclaims.py`; output `computations/2026-06-21-hgt-STEP11-mass-transfer-subclaims.txt`. Across smoothing widths `5,13,29,57`, true-vs-finite separation is already present before normalization and top-overlap stays high (`0.846-0.962`). At `sigma=1.2`, true-vs-finite raw and apparent separations vanish or change sign (`raw_sep_vs_finite≈-0.003`, `apparent_sep_vs_finite≈0`).
- STEP 10 verdict: DEAD END for new knowledge. The NODE constraint is real, but the HT transfer is a transport-normalized restatement of the already-known phase-defect/left-strip signal, with right-strip collapse. No chat post.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Mass-transfer limitations that mimic intrinsic catalytic hot-spot activity".

## Penrose — Machine R9 — amorphous/glassy phases instead of full crystallinity `[DEAD END]`

- NODE constraint: kinetic arrest can beat nucleation, so the same final dryness can end crystalline or glassy depending on ramp rate. Toy ramp model: crystal fraction drops from `1.000` at slow ramp `0.02` to `0.403` at fast ramp `1.0`.
- STEP 8 selected by Levenshtein: `finite_window_fe_crystallization` (242). STEP 9 method #12 found the expected invariant: completed true FE residual is numerical zero across window-growth rates, while uncompleted/finite controls are not. This reduces to the known functional equation.
- STEP 11 method #15 strengthened “crystal” to FE residual plus phase-carrier run order. Initial FE-exact random fakes failed the carrier run test, but adversarial constant-phase FE fakes can force full carrier positivity on the same windows, even where true has short runs. Verdict: naive FE+phase-run crystallinity is not a non-reducing invariant; no chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Biofilm detachment is active life-history release `[DEAD END — burstiness control fails; finite/random dominate]`
Seed RandomNode = "Existing corrosion products and pits can sustain localized corrosion even after external chloride exposure is reduced" → Step 1 cold Codex broad list → rng#17 = Biofilm ecology → Step 3 cold Codex narrow list → rng#5 = NODE "Detachment is an active life-history process, not merely accidental sloughing".
- STEP 5 constraint: biofilm detachment is state-triggered dispersal with burst/timing structure, not merely passive random erosion.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-biofilm-active-detachment.py`; output `computations/2026-06-21-hgt-NODE-biofilm-active-detachment.txt`. After strengthening the trigger nonlinearity, active detachment has higher CV than passive sloughing (`0.360358` vs `0.181454`) and more total detached biomass (`2.166431` vs `1.910510`), validating the NODE.
- STEP 7 gate: biofilm detachment formulas do not apply unchanged to HT functions. Minimal non-blind transfer must compare stress-triggered event release against passive sampling on continuum differential stress.
- STEP 8 revised rule applied: three HT-transfer attempts were created and ranked by Levenshtein. Selected `stress-triggered-events` (`25`, normalized `0.2273`) over `finite-cutoff-slough` (`76`) and `zero-spore-release` (`88`). Script `computations/2026-06-21-hgt-STEP8-biofilm-detachment-ht-events.py`; output `computations/2026-06-21-hgt-STEP8-biofilm-detachment-ht-events.txt`.
- STEP 9 method rng#8 = look for similar objects. Finite Euler and random-phase controls show equal or stronger active-event burstiness than true zeta in most cases; e.g. at `σ=0.3`, `[100,170]`, active CV true `1.442351`, finite `2.587684`, random `2.358151`.
- STEP 10 verdict: DEAD END. Stress-triggered burstiness is not an HT-specific feature; it is a generic thresholding property of rough event fields.
- STEP 11 method rng#20 = name the missing lemma. Script `computations/2026-06-21-hgt-STEP11-biofilm-detachment-missing-lemma.py`; output `computations/2026-06-21-hgt-STEP11-biofilm-detachment-missing-lemma.txt`. The missing lemma would require true burstiness to dominate controls across trigger thresholds, but true never dominates (`true_dominates=0` for thresholds `0.35–0.75`).
- WALK STATE: dead end → STEP 1 reseed with RandomNode = "Detachment is an active life-history process, not merely accidental sloughing".

## Conway — transition-path dynamics / phase-edge softness (2026-06-21)

- STEP 1/2: seed `Testing whether neck closure or opening is reversible under cycling conditions`; cold list -> rng #11 `Stochastic resonance near transition barriers`.
- STEP 3/4: cold list -> rng #10 NODE `Transition-path dynamics differ from residence-time statistics`.
- STEP 5/6 NODE constraint: residence/dwell statistics do not determine transition-path shape. Runnable validation in `computations/2026-06-21-conway-transition-path-vs-residence.py`; output `computations/2026-06-21-conway-transition-path-vs-residence.txt`.
- STEP 9 method #8 `Look for similar objects`; selected `A_phase_edge_dynamics` by Levenshtein.
- STEP 12 battery: `computations/2026-06-21-conway-STEP12-transition-edge-battery.py`, output `computations/2026-06-21-conway-STEP12-transition-edge-battery.txt`.
- Finding `[EXPERIMENTAL / CONJECTURE]`: at sigma `0.5`, true analytic `zeta'/zeta` has much softer phase-defect transition edges than finite Euler/random controls: true mean softness about `44.66` vs finite `8.91` and random `5.96` at band `0.12`; finite prime-count stress N=30..400 stays below `10`; right side sigma `1.2` collapses true/finite. Posted to `#research` as conway id 750.

## Penrose — Machine R10 — phase-locking tongues mimic quasiperiodicity `[DEAD END]`

- NODE constraint: finite observation can confuse true quasiperiodicity, near rational motion, and Arnold-tongue locking. Circle-map scan gave exact-looking tongues at `K=0.7, Ω=0.341 -> ρ=1/3` and `K=0.95, Ω=0.408 -> ρ=2/5`.
- STEP 8 selected by Levenshtein: `zero_spacing_periodic_mimic` (187). STEP 9 method #15 strengthened the mimic criterion to stable best period across zero-gap windows. Zeta best periods hopped (`13,9,15,20,17,...`) with random-control-comparable autocorrelation scores. Dead: finite-window pattern hunting.
- STEP 11 method #11 tested prime-log finite-window phase locks. Short windows give high apparent lock scores (e.g. `log2/log3` best `12/19`, score `0.9992` at `L=10`) but scores erode by `L=3000`. This reduces to sinc averaging plus known prime-log incommensurability/Baker. No chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Condensate crowding reduces active-site accessibility `[DEAD END — duplicate amplitude-vs-phase split]`
Seed RandomNode = "Mass-transfer limitations that mimic intrinsic catalytic hot-spot activity" -> Step 1 cold Codex broad list -> rng#4 = Enzyme crowding in phase-separated condensates -> Step 3 cold Codex narrow list -> rng#12 = NODE "Enzyme crowding can promote nonspecific interactions that reduce active-site accessibility".
- STEP 5 constraint: condensate enrichment/effective molarity is not equivalent to usable catalytic activity. Increasing crowding can raise local enzyme density while reducing diffusion and active-site accessibility through nonspecific interactions, producing an optimum and then decline.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-condensate-crowding-accessibility.py`; output `computations/2026-06-21-hgt-NODE-condensate-crowding-accessibility.txt`. The NODE model validates the constraint. Enrichment is monotone (`enrichment_high=6.33333`) while accessibility decreases; at nonspecific strength `0.22`, rate peaks at crowding `0.8` (`max_rate=2.78347`) and then falls to `0.05621` at high crowding with accessibility `0.04476`.
- STEP 7 gate: condensate partitioning/crowding/diffusion formulas do not apply unchanged to HT functions. A non-blind transfer must compare a scalar crowding/enrichment proxy to a phase/accessibility proxy on continuum differential data.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-condensate-crowding-ht-access.py` created three HT attempts: `amplitude-crowding-phase-access`, `partition-coefficient-strip`, and `condensate-diffusion-smoothing`. Levenshtein selected `amplitude-crowding-phase-access` (`70`, vs `75` and `76`). Output: `computations/2026-06-21-hgt-STEP8-condensate-crowding-ht-access.txt`.
- STEP 9 method rng#13 = find a monotone quantity. The finite Euler crowding/amplitude proxy increases with prime count while phase access remains zero or near zero: at `sigma=0.3`, `[100,170]`, finite amplitude goes `1.8323,2.0989,2.1746,2.3317,2.5628`, while access is `0,0,0.0076,0,0.0101`; true zeta has lower amplitude `1.312177` but access `0.431024`. At `[500,570]`, finite amplitude rises `1.8041->2.6892`, access stays exactly `0`; true access is `0.530177`. At `sigma=1.2`, true/finite/random collapse.
- STEP 10 verdict: DEAD END for new knowledge. This duplicates the existing specificity/promiscuity and amplitude-vs-phase results (Dyson hypercycle/root-anoxia pattern and Conway option-similarity controls): scalar amplitude/crowding can increase while phase-specific access is absent.
- STEP 11 method rng#2 = attack it as false. Script `computations/2026-06-21-hgt-STEP11-condensate-attack-false.py`; output `computations/2026-06-21-hgt-STEP11-condensate-attack-false.txt`. Varying nonspecific penalty strength only rescales the true phase-defect advantage (`sigma=0.3`, `[100,170]`: true penalized `0.431024 -> 0.013297` as penalty `0 -> 16`), while finite, amplitude-matched finite, and random-phase remain zero. The mechanism is phase destruction/control matching, not a new condensate-accessibility observable.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Enzyme crowding can promote nonspecific interactions that reduce active-site accessibility".

## Conway — broken detailed balance / sigma-lane current `[DEAD END — lane occupancy artifact]` (2026-06-21)

- STEP 1/2: seed `Transition-path dynamics differ from residence-time statistics`; cold list -> rng #12 `Non-equilibrium steady states in biochemical networks`.
- STEP 3/4: cold list -> rng #10 NODE `Broken detailed balance caused by ATP, GTP, ion gradients, or redox potentials held out of equilibrium`.
- STEP 5/6 NODE constraint: steady marginals can coexist with nonzero cycle current when reservoirs maintain affinity. Runnable validation in `computations/2026-06-21-conway-broken-detailed-balance-current.py`; output `computations/2026-06-21-conway-broken-detailed-balance-current.txt`.
- STEP 9 method #1 `Split it into subclaims`; three HT attempts tied, selected `A_sigma_lane_cycle_current`.
- Verdict: reducing. True sigma-lane winner sequence has essentially zero cycle current because the chosen lanes collapse to two states; finite/random currents are generic lane-switching artifacts. Direct detailed-balance transfer is already known FE/passivity material. No chat post.

## Penrose — Machine R11 — compression amplifies architectural aliasing `[DEAD END]`

- NODE constraint: transform compression can preserve repeated edges while discarding subtle context. Synthetic facade test raised moire/context from `13.47` to `20.67` at moderate quantization, before stronger quantization erased too much.
- STEP 8 selected by Levenshtein: `phase_trace_transform_quantization` (120). STEP 9 method #14 weakened to one left-strip phase-carrier trace. FFT compression left true edge/context near `0.16`, finite around `0.57-0.73`, random around `0.22`; no nontrivial class transition, only transform-statistic differences.
- STEP 11 method #23 found no clean context-collapse/edge-preserving boundary for NODE proxy or HT traces. Verdict: generic compression/sampling artifact, no chat post.

## Conway — hidden trajectory reconstruction `[DEAD END — amplitude/phase competitor restatement]` (2026-06-21)

- STEP 1/2: seed `Broken detailed balance caused by ATP, GTP, ion gradients, or redox potentials held out of equilibrium`; cold list -> rng #4 `Stochastic thermodynamics of information engines`.
- STEP 3/4: cold list -> rng #20 NODE `Separating experimentally inferred work and heat from model-dependent reconstructions of hidden stochastic trajectories`.
- STEP 5/6 NODE constraint: same observed scalar work can correspond to different hidden stochastic heat. Runnable validation in `computations/2026-06-21-conway-hidden-trajectory-reconstruction.py`; output `computations/2026-06-21-conway-hidden-trajectory-reconstruction.txt`.
- STEP 9 method #21 `Build a dependency chain`; selected `A_amplitude_work_hidden_phase_heat`.
- Verdict: reducing. Amplitude-matched random controls share true amplitude work but have different hidden phase heat; this is the already-posted amplitude-vs-phase false-competitor line. No chat post.

## Hawking THE-MACHINE tick — branching backward ancestry `[DEAD END]`

- **Seed RandomNode:** `Detachment is an active life-history process, not merely accidental sloughing`.
- **STEP 2 topic:** rng `17` -> `Branching processes with extinction/release events`.
- **STEP 4 NODE:** rng `19` -> `Backward-in-time ancestry differs from forward-in-time population growth, especially under conditioning on survival`.
- **NODE constraint:** terminal-survivor ancestry is size-biased by descendant count; a sampled backward spine follows `P*(K=k)=kP(K=k)/E[K]`, not the forward event-level offspring law.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-branching-backward-ancestry.py` / `.txt`. Direct draws matched original laws (`TV≈0.001–0.004`), while sampled terminal spines matched size-biased laws (`TV≈0.040–0.052`); lift grew with offspring variance.
- **STEP 7:** the branching formulas (`f(q)=q`, size-biased/spine law, Doob change-of-measure) do not apply unchanged to deterministic HT functions on `C`; any transfer must change the object to a continuum phase-survival field, so no unchanged formula was promoted.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_phase_ancestry_survivor_size_bias` (`12/96=0.1250`) over zero-shadow component and jet-curvature variants.
- **STEP 9:** rng `1` -> split into subclaims. Script/output: `computations/2026-06-21-hgt-STEP8-branching-ancestry-ht-spine.py` / `.txt`.
- **STEP 9 result:** terminal positive phase samples do size-bias dyadic interval ancestry, but the statistic mainly tracks run clustering. Finite Euler often matches or exceeds true `zeta'/zeta` (`sigma=0.7` finite excess `0.1070/0.0836/0.1198` vs true `0.0927/0.0576/0.1154`), and true/finite collapse on the right (`sigma=1.2`, excess about `0.19–0.24` for both).
- **STEP 11:** rng `18` -> look for the right theorem. Tested a Doob/h-transform metaphor: fit a local boundary survival weight on one window and port it across windows/controls. Script/output: `computations/2026-06-21-hgt-STEP11-branching-spine-htransform.py` / `.txt`.
- **STEP 11 result:** local h-weights port for true and finite comparably (`true`-trained `R2≈0.756/0.702` on right true and `0.773/0.704` on right finite; finite-trained similarly). Random controls have weaker but nonzero endpoint predictability. No true-specific portable survival transform appears.
- **Verdict:** dead end. The NODE constraint was real, but the HT transfer reduces to already-seen phase-run/zero-shadow topology and local persistence; not posted to `#research`.
- **Next RandomNode:** `Backward-in-time ancestry differs from forward-in-time population growth, especially under conditioning on survival`.

## Conway — gravitational entropy accounting `[DEAD END — phase-run structure restatement]` (2026-06-21)

- STEP 1/2: seed `Separating experimentally inferred work and heat from model-dependent reconstructions of hidden stochastic trajectories`; cold list -> rng #18 `Cosmological arrow-of-time models`.
- STEP 3/4: cold list -> rng #2 NODE `Low entropy early universe is not equivalent to small, hot, dense universe; gravitational entropy changes the accounting`.
- STEP 5/6 NODE constraint: matter/density entropy and gravitational clumping entropy are different accounts. Runnable validation in `computations/2026-06-21-conway-grav-entropy-accounting.py`; output `computations/2026-06-21-conway-grav-entropy-accounting.txt`.
- STEP 9 method #13 `Find a monotone quantity`; selected `B_zero_shadow_topology_entropy` by Levenshtein tie.
- Verdict: reducing. The amplitude entropy vs run/topology entropy split recovers existing phase-lifetime and zero-shadow-topology results, not a new monotone. No chat post.

## Penrose — Machine R12 — scale-dependent ornament loss `[DEAD END]`

- NODE constraint: ornament can be invisible at micro and macro scales but visible at a matched intermediate scale. Corrected matched-window detector validated this on a synthetic coarse-body/period-64-ornament/fine-grain signal.
- STEP 8 selected by Levenshtein: `prime_frequency_matched_scale` (129). STEP 9 method #10 tested micro-to-whole windows for a `|log 3 - log 2|` beat detector. The score is detector/trend dominated; even `Γ∞` can score high. Dead as finite-prime/matched-filter artifact.
- STEP 11 method #13 smoothing-scale monotone showed generic erasure for true and finite `Delta` traces. Verdict: generic smoothing/scale bookkeeping, no chat post.

## Conway — coarse-grained apparent entropy `[DEAD END — description artifact]` (2026-06-21)

- STEP 1/2: seed `Low entropy early universe is not equivalent to small, hot, dense universe; gravitational entropy changes the accounting`; cold list -> rng #18 `Maximum entropy production principle`.
- STEP 3/4: cold list -> rng #9 NODE `Coarse-graining can create apparent entropy production that depends on the chosen description`.
- STEP 5/6 NODE constraint: entropy-production estimates depend on coarse-graining/description. Runnable validation in `computations/2026-06-21-conway-coarse-grain-apparent-entropy.py`; output `computations/2026-06-21-conway-coarse-grain-apparent-entropy.txt`.
- STEP 9 method #6 `Ask what action is happening`.
- Verdict: reducing. Phase-defect entropy-rate estimates are tiny and description-sensitive without a stable HT signal. No chat post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Prion-like LCD mixing order changes material state `[DEAD END — path memory is phase-defect restatement]`
Seed RandomNode = "Enzyme crowding can promote nonspecific interactions that reduce active-site accessibility" -> Step 1 cold Codex broad list -> rng#7 = Prion-like low-complexity domains -> Step 3 cold Codex narrow list -> rng#17 = NODE "The order of mixing components in vitro can change the resulting assembly pathway and final material state".
- STEP 5 constraint: final component composition does not determine the material state; pathway and aging between additions can trap different liquid/gel/fiber states.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-prion-mixing-order-material-state.py`; output `computations/2026-06-21-hgt-NODE-prion-mixing-order-material-state.txt`. Identical final totals protein=1, RNA=1, salt=1 produced two material classes. `protein-salt-rna` ended fiber-dominant (`fiber=0.291652`), while most other orders remained liquid-dominant; max pairwise material L1 distance was `0.448837`.
- STEP 7 gate: mass-action/pathway ODEs apply to the NODE but not unchanged to HT functions. The minimal non-blind transfer is to keep final components fixed while changing nonlinear assembly order on continuum strip observables, not on discrete `zeta(n)` values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-prion-mixing-order-ht-pathway.py` created three attempts: `strip-pathway-order`, `zero-shadow-seeding`, and `prime-block-aging`; Levenshtein selected `strip-pathway-order` (`31`, normalized `0.4079`). Output: `computations/2026-06-21-hgt-STEP8-prion-mixing-order-ht-pathway.txt`.
- STEP 9 method rng#11 = run experiments. Component map: protein=`phase_defect(Gamma_infty,P)`, RNA=`log|Gamma_infty+P|`, salt=local phase roughness. True zeta has left-strip order spread where its defect median is positive (`sigma=0.3`, `[100,170]`: defect median `0.239672`, max order spread `0.017391`; `[500,570]`: `0.266676`, spread `0.022906`). Finite, amplitude-matched finite, random-phase, and gamma-only controls collapse to zero or near-zero spread; `sigma=1.2` also collapses.
- STEP 10 verdict: DEAD END for new knowledge. The order-memory readout is coherent but tracks the old left-strip phase-carrier defect; it does not isolate a new HT path-dependence invariant.
- STEP 11 method rng#23 = classify boundary cases. Script `computations/2026-06-21-hgt-STEP11-prion-pathway-boundaries.py`; output `computations/2026-06-21-hgt-STEP11-prion-pathway-boundaries.txt`. Boundary classification confirms reduction: no-aging kills the signal, `no_defect` kills it, `defect_only` is sufficient, shuffled defect keeps it, true right-strip `sigma=1.2` kills it, and finite/random controls do not reach the boundary-signal threshold. The metaphor experiment is therefore a phase-defect detector with pathway language.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "The order of mixing components in vitro can change the resulting assembly pathway and final material state".

## Conway — active tissue jamming `[DEAD END — prior failed route]` (2026-06-21)

- STEP 1/2: seed `Coarse-graining can create apparent entropy production that depends on the chosen description`; cold list -> rng #8 `Non-equilibrium morphogenesis`.
- STEP 3/4: cold list -> rng #10 NODE `Active fluidization and jamming transitions in tissues`.
- STEP 9 method #3 `Reverse it`.
- Verdict: already failed. This is the existing tissue-jamming route (`computations/2026-06-20-hgt-NODE-tissue-jamming.py`, `computations/2026-06-20-hgt-STEP8-tissue-jamming-ht-landscape.py`): the HT landscape packing/jamming statistic is instrument-dependent and not canonical. No rerun; no chat post.

## Hawking THE-MACHINE tick — rate-uncertainty pruning `[DEAD END]`

- **Seed RandomNode:** `Backward-in-time ancestry differs from forward-in-time population growth, especially under conditioning on survival`.
- **STEP 2 topic:** cold list first-20 order, rng `10` -> `Reaction-network pruning`.
- **STEP 4 NODE:** rng `15` -> `Error propagation from uncertain rate coefficients into pruning decisions`.
- **NODE constraint:** pruning must propagate rate-coefficient uncertainty; nominally low-importance reactions can have high-tail importance and cross the pruning threshold.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-rate-uncertainty-pruning.py` / `.txt`. Low-uncertainty control kept nominal and robust pruning aligned. With high minor-rate uncertainty, nominally pruned `A_to_D` had q90/q99 joint importance `0.1370/0.4617` and fail probability `0.215`; correlated uncertainty made robust pruning keep all minor reactions.
- **STEP 7:** sensitivity/quantile pruning formulas do not apply unchanged to deterministic HT functions; a non-blind transfer must put coefficient uncertainty on continuum differential data, not discrete `zeta(n)` values.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_uncertain_prime_coefficients_pruning` (`3/67=0.0448`) over phase-Jacobian and boundary-transport variants.
- **STEP 9:** rng `2` -> attack it as false. Script/output: `computations/2026-06-21-hgt-STEP8-rate-uncertainty-prime-pruning.py` / `.txt`.
- **STEP 9 result:** uncertainty-aware finite-prime pruning mostly keeps more groups and approximates the full finite mechanism better; it does not recover the true analytic carrier. At `sigma=0.3`, finite full phase-error vs true was `0.4222`; nominal pruning worsened to `0.4915`, robust pruning only returned to `0.4118`, with full finite field relative error still `2.694`. Matched random-phase groups showed the same high-tail pruning behavior.
- **STEP 11:** rng `22` -> compare nearby false statements. Script/output: `computations/2026-06-21-hgt-STEP11-rate-pruning-false-boundaries.py` / `.txt`.
- **STEP 11 result:** threshold/uncertainty sweeps broke the useful false statement. Robust pruning improves nominal pruning by retaining groups, but `false_F2=1` throughout: it still fails to recover the true analytic carrier. Right strip collapse is ordinary finite Euler convergence (`sigma=1.2` full finite error `0.0039`), not new HT content.
- **Verdict:** dead end. The NODE constraint was real, but HT transfer reduces to finite-group sensitivity, phase-defect error, and known right-strip convergence; not posted to `#research`.
- **Next RandomNode:** `Error propagation from uncertain rate coefficients into pruning decisions`.

## Penrose — Machine R13 — critical branching extinction at mean one `[DEAD END / REDUCED]`

- NODE constraint: mean offspring `1` does not imply survival; critical Galton-Watson dies out a.s. Vectorized Poisson test: critical mean `1.0` had only `0.005` survival past generation 400, while supercritical `1.1` had `0.165` survival.
- STEP 8 selected by Levenshtein: `scalar_rescaled_phase_branching` (187). STEP 9 method #20 named the missing lemma: equal phase occupancy/mean reproduction does not imply survival-tail depth. Occupancy-matched finite/true tests did not yield a robust new gap and reduce to existing phase-run proofreading.
- STEP 11 method #18 used spine/survival conditioning. It recovers Conway's kinetic-proofreading lifetime separation in spine language, but is not an independent non-reducing finding. No chat post.

### Crosslink compliance / slip under load -> phase-defect threshold survival

- NODE: `Considering crosslink compliance, unbinding, or slip under load`.
- Test: treat phase-defect exceedances as bound crosslinks and load as an increasing defect threshold.
- Evidence: `computations/2026-06-21-conway-crosslink-slip-load.py`, `computations/2026-06-21-conway-crosslink-slip-load.txt`.
- Outcome: reducing. Left-strip true survival is larger than finite/random, but the right strip collapses true and finite; this is the existing phase-lifetime threshold result in load language, not a separate invariant.

## Penrose — Machine R13 re-audit — branching-spine phase carrier `[FIND — corrected gate]`

- Correction: user clarified reduce-to-known means direct-promptability, not overlap with other agents' chat findings. R13 Step 11 was re-audited under this gate and counted.
- Finding: survival-conditioned positive-`Delta` spines separate true analytic `zeta'/zeta` from finite Euler/random controls in the left/middle strip. At `sigma=0.3`, true has full-window `spine_frac=1.0` on `[100,170]` and `[500,570]`; finite has `0.0499/0`, random `0/0`. At `sigma=0.5`, true has `0.421/0.316`, finite `0.166/0.044`, random `0`. By `sigma=0.7` the gap narrows.
- Interpretation: expectation/occupancy is the wrong branching invariant for the phase carrier; the survivor-conditioned spine is the informative object. Posted to `#research` id 752. Experimental only, not proof.

## Hawking THE-MACHINE tick — propensity identifiability `[DEAD END]`

- **Seed RandomNode:** `Error propagation from uncertain rate coefficients into pruning decisions`.
- **STEP 2 topic:** cold list first-20 order, rng `11` -> `Stochastic reaction networks with uncertain propensities`.
- **STEP 4 NODE:** rng `9` -> `Identifiability problems can make very different uncertain propensity models fit the same observed count data`.
- **NODE constraint:** the observation map from propensity mechanism to count histogram is non-injective; snapshot counts can identify neither rate heterogeneity nor bursty event structure without extra observables.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-propensity-identifiability.py` / `.txt`. Gamma-distributed birth propensities and bursty birth propensities both fit the same negative-binomial count law (`js_to_target≈0.0097` for both; mutual JS `0.0125`), but hidden jump structure differs (`multi_jump_fraction=0` vs `0.8017`).
- **STEP 7:** Poisson-gamma / burst negative-binomial formulas do not apply unchanged to HT functions on `C`; a non-blind transfer must use continuum differential observables and distinguish marginal distribution from hidden order.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_phase_histogram_hidden_transitions` (`36/102=0.3529`) over amplitude-distribution and zero-shadow-topology variants.
- **STEP 9:** rng `21` -> build a dependency chain. Script/output: `computations/2026-06-21-hgt-STEP8-propensity-identifiability-phasehist.py` / `.txt`. Quantile mapping forced finite/random controls and shuffled true to have the same phase-defect histogram as true zeta, then tested hidden run/autocorrelation/transition statistics.
- **STEP 9 result:** same marginal histogram is insufficient, but the hidden-order separation reduces to already-seen run/lifetime/edge-softness structure. Finite histogram-matched controls remain close to true in several cases (`sigma=0.7`, `[100,170]`: true run_q90 `11.0`, finite_histmatched `12.0`; trans entropy `0.704` vs `0.756`) and collapse on the right (`sigma=1.2`, finite_histmatched run/autocorrelation/entropy nearly identical to true).
- **STEP 11:** rng `9` -> test small cases. Script/output: `computations/2026-06-21-hgt-STEP11-propensity-identifiability-smallcases.py` / `.txt`. Small-case sequence-length sweep confirmed the boundary: random/shuffled order separates from true, but finite histogram-matched controls often stay close (`sigma=0.5`, samples `420`, hidden_distance `0.4539`; `sigma=1.2`, samples `420`, hidden_distance `0.0096`).
- **Verdict:** dead end. The NODE constraint was real, but the HT transfer is a histogram-matched restatement of existing phase-run / transition-edge / right-strip-collapse findings; not posted to `#research`.
- **Next RandomNode:** `Identifiability problems can make very different uncertain propensity models fit the same observed count data`.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Major-loop hysteresis fits fail on minor loops `[DEAD END — selected transfer reduces to FE residual]`
Seed RandomNode = "The order of mixing components in vitro can change the resulting assembly pathway and final material state" -> Step 1 cold Codex broad list -> rng#2 = Hysteresis -> Step 3 cold Codex narrow list -> rng#19 = NODE "Models fitted only to the major loop can fail badly under partial cycling or reversal".
- STEP 5 constraint: a major hysteresis loop is only a boundary trace of a memory operator; partial reversals require hidden memory state and are not determined by the major loop alone.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-hysteresis-major-loop-minor-failure.py`; output `computations/2026-06-21-hgt-NODE-hysteresis-major-loop-minor-failure.txt`. A major-loop lookup fit had `major_loop_rmse=0.00000000` but failed partial reversals (`rmse=0.115545–0.155024`, max error up to `0.688348`).
- STEP 7 gate: Preisach/minor-loop formulas do not apply unchanged to HT functions. A non-blind transfer must compare boundary trace versus hidden interior/mirror behavior on continuum strip data.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-hysteresis-major-loop-ht-minors.py` created three attempts: `functional-equation-return-point`, `prime-cutoff-coercivity`, and `strip-minor-loop-reversal`. Levenshtein selected `functional-equation-return-point` (`53`, normalized `0.7067`). Output: `computations/2026-06-21-hgt-STEP8-hysteresis-major-loop-ht-minors.txt`.
- STEP 9 method rng#10 = test extreme cases. The selected transfer measured completed FE mirror residual `log(1+|L(s)+L(1-s)|)`. True-completed residual is numerical zero in all windows (`~1e-8` to `1e-7`), while finite/random/gamma controls are positive. This is exactly the known completed functional equation, not a new minor-loop memory invariant.
- STEP 11 method rng#23 = classify boundary cases. Script `computations/2026-06-21-hgt-STEP11-hysteresis-boundary-trace.py`; output `computations/2026-06-21-hgt-STEP11-hysteresis-boundary-trace.txt`. Boundary-trace interpolation failure across sigma lanes was mixed: true has failures in left/interior lanes, but random-phase and amplitude-matched controls also produce failures in many windows. Gamma-only is zero. This does not isolate an HT-native hidden-memory observable.
- STEP 10 verdict: DEAD END for new knowledge. The selected Step 8 transfer reduces to the functional equation; the Step 11 metaphor reduces to phase-defect/boundary-interpolation artifacts with control leakage. No chat post.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Models fitted only to the major loop can fail badly under partial cycling or reversal".

## Hawking THE-MACHINE tick — epigenetic metastability `[DEAD END]`

- **Seed RandomNode:** `Identifiability problems can make very different uncertain propensity models fit the same observed count data`.
- **STEP 2 topic:** cold list first-20 order, rng `3` -> `Epigenetic state switching`.
- **STEP 4 NODE:** rng `18` -> `Epigenetic states can be metastable rather than permanently locked`.
- **NODE constraint:** a switched state may look fixed over short assays while still having finite escape/reversion probability; permanent lock is the singular zero-escape case.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-epigenetic-metastability.py` / `.txt`. Permanent lock has survival `1.0` throughout; metastable slow loss has `surv20=0.8860` but `surv_end=0.2693`; washout collapses by long horizon. Barrier sweep shows lifetime grows with barrier but remains finite unless loss is zero.
- **STEP 7:** two-state metastability/escape formulas do not apply unchanged to HT functions; a non-blind transfer must test finite dwell/escape of continuum phase states, not discrete values.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_phase_state_metastability` (`8/63=0.1270`) over zero-shadow-well escape and memory-barrier decay variants.
- **STEP 9:** rng `16` -> use a minimal counterexample. Script/output: `computations/2026-06-21-hgt-STEP8-epigenetic-metastability-phase.py` / `.txt`. High phase states have finite exits; true zeta often has longer dwell than random, but finite controls approach it near `sigma=0.7` and collapse with it on the right (`sigma=1.2` true/finite rows essentially identical).
- **STEP 11:** rng `8` -> look for similar objects. Script/output: `computations/2026-06-21-hgt-STEP11-epigenetic-metastability-similar.py` / `.txt`. Histogram-matched smooth sine and AR(1) controls reproduce or exceed the dwell/metastability scores, showing the observable is smooth-order/run-length structure rather than an HT-native invariant.
- **Verdict:** dead end. The NODE constraint was real, but the HT transfer reduces to existing phase-run lifetime plus generic smooth correlated sequence effects; not posted to `#research`.
- **Next RandomNode:** `Epigenetic states can be metastable rather than permanently locked`.

### Catch-bond context -> context-fragility monotone

- NODE: `Catch bonds are often context-dependent on cofactors, ions, pH, glycosylation, or membrane anchoring`.
- Transfer: Levenshtein-selected context-dependent phase-cancellation lifetime under force/context on continuous `s`-trajectories.
- Evidence: `computations/2026-06-21-conway-catch-context.txt`, `computations/2026-06-21-conway-catch-context-phase-noise.txt`, `computations/2026-06-21-conway-STEP12-catch-context-noise-battery.txt`.
- Finding: experimental/conjectural. The true left-strip context response decays monotonically when phase context is externally scrambled, unlike finite Euler and amplitude-random controls; right-strip true/finite collapse remains the boundary. This is adjacent to the phase-defect corpus but records a new fragility monotone rather than a plain threshold-survival statistic.

## Penrose — Machine R14 — directed-polymer endpoint/path localization `[DEAD END / PROMPTABLE]`

- NODE: `Endpoint localization and path localization are related but not identical phenomena` from directed polymers in random media.
- Constraint: endpoint concentration and full-path concentration are distinct; paths can merge into one endpoint or split from one localized stem.
- NODE validation: directed-walk DP separated both directions (`endpoint IPR 0.998` with path IPR `0.503`; and path IPR `0.706` with endpoint IPR `0.448`).
- HT transfer: sigma-lane polymer DP using `log(1+|zeta'/zeta|)` as the continuum differential strip field. Step 9 found true `zeta'/zeta` less lane-localized and more switchy than finite/random controls, but row-shuffling barely changed true metrics.
- Step 11 weakened to ordinal lane winners. True had lower path IPR and higher switching; after per-lane median subtraction, true residual winners concentrated near `sigma=0.5` while finite/random stayed edge/variance dominated.
- Verdict: promptable. A cold direct prompt predicted the central residual lane from `zeta'/zeta ~ 1/(s-rho)` near critical-line zeros. Useful diagnostic only; no `#research` post.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Battery temperature changes hysteresis and SOC calibration `[DEAD END — calibration artifact plus phase-defect restatement]`
Seed RandomNode = "Models fitted only to the major loop can fail badly under partial cycling or reversal" -> Step 1 cold Codex broad list -> rng#10 = Battery hysteresis and state-of-charge estimation -> Step 3 cold Codex narrow list -> rng#6 = NODE "Temperature changes alter both hysteresis behavior and OCV-SOC calibration".
- STEP 5 constraint: terminal voltage is not a temperature-invariant function of SOC. Temperature changes both equilibrium OCV-SOC calibration and hysteresis magnitude, so a calibration learned at one temperature can bias SOC estimates at another.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-battery-temperature-hysteresis-soc.py`; output `computations/2026-06-21-hgt-NODE-battery-temperature-hysteresis-soc.txt`. Same-SOC voltage spread was `0.073587` on charge and `0.169287` on discharge. A 25C estimator gave full median SOC error `0.054958` at -10C, `0.043353` at 0C, and `0.260000` at 45C; OCV-only and hysteresis-only ablations separated the sources.
- STEP 7 gate: battery OCV/hysteresis formulas do not apply unchanged to HT functions. A non-blind transfer must keep calibration drift plus history dependence on continuum strip observables, not discrete `zeta(n)` values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-battery-temperature-ht-calibration.py` created three attempts: `strip-temperature-calibration`, `prime-thermal-cutoff`, and `zero-thermal-relaxation`; Levenshtein selected `strip-temperature-calibration` (`13`, normalized `0.1757`). Output: `computations/2026-06-21-hgt-STEP8-battery-temperature-ht-calibration.txt`.
- STEP 9 method rng#23 = classify boundary cases. Reference calibration lane was `sigma=0.5`; hidden SOC analogue was phase defect and voltage analogue was amplitude+history. True zeta showed large off-lane calibration error (`sigma=0.3`, `[100,170]`: full error `0.328883`; `[500,570]`: `0.347918`), but controls and boundary cases leaked: finite at `sigma=0.7` had error `0.208430`, finite at `sigma=1.2` `0.258767`, random-phase at `sigma=1.2` `0.105629`.
- STEP 10 verdict: DEAD END for new knowledge. The strong true left-strip signal is not isolated; boundary/control leakage makes it a calibration artifact plus restatement of phase-defect mass.
- STEP 11 method rng#7 = strip to essentials. Script `computations/2026-06-21-hgt-STEP11-battery-strip-essentials.py`; output `computations/2026-06-21-hgt-STEP11-battery-strip-essentials.txt`. The full true errors survive under amplitude-only or history-only ablations, and right-strip true/finite also produce large errors (`true sigma=1.2 full 0.475917`, finite sigma=1.2 full `0.275269`). Shuffling defect can reproduce or enlarge error. This strips the metaphor down to ordinary calibration mismatch and known phase-defect behavior.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Temperature changes alter both hysteresis behavior and OCV-SOC calibration".

## Hawking THE-MACHINE tick — dissipative flux maintenance `[DEAD END]`

- **Seed RandomNode:** `Epigenetic states can be metastable rather than permanently locked`.
- **STEP 2 topic:** cold list first-20 order, rng `10` -> `Dissipative self-assembly`.
- **STEP 4 NODE:** rng `1` -> `Energy flux must be continuous to maintain the assembled state`.
- **NODE constraint:** the assembled state is a maintained throughput state; it persists only while fuel/energy flux balances turnover, and decays after feed cutoff.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-dissipative-flux-maintenance.py` / `.txt`. Ongoing feed gives maintained plateaus (`late/peak≈0.996–1.000`), while fuel cutoff leaves only small tails (`late/peak≈0.043–0.180`).
- **STEP 7:** dissipative assembly ODEs/fuel-balance formulas do not apply unchanged to HT functions; a non-blind transfer must make flux a continuum phase observable on `C`.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_continuous_phase_flux_assembly` (`6/52=0.1154`) over weld-turnover and prime-feed-cutoff variants.
- **STEP 9:** rng `7` -> strip it to essentials. Script/output: `computations/2026-06-21-hgt-STEP8-dissipative-flux-phase-assembly.py` / `.txt`. A one-input leaky state fed by phase defect was maintained while feed continued and decayed after cutoff, but random/shuffled controls often matched or exceeded true, and true/finite collapsed on the right.
- **STEP 11:** rng `12` -> find an invariant. Script/output: `computations/2026-06-21-hgt-STEP11-dissipative-flux-invariant.py` / `.txt`. The cutoff ratio is governed by leaky-integrator decay and cutoff timing; plateau tracks integrated positive flux (`corr≈0.7106`) rather than an HT-native invariant.
- **Verdict:** dead end. The NODE constraint was real, but HT transfer reduces to model-imposed leaky integration of the existing phase-defect amplitude distribution; not posted to `#research`.
- **Next RandomNode:** `Energy flux must be continuous to maintain the assembled state`.

### Hofmeister endpoint non-transfer -> amplitude ranking transfer failure

- NODE: `Surface tension trends do not automatically transfer to protein, membrane, or polymer systems`.
- Evidence: `computations/2026-06-21-conway-hofmeister-endpoint-transfer.txt`, `computations/2026-06-21-conway-hofmeister-dependency-chain.txt`.
- Outcome: reducing. The missing lemma “bulk amplitude rankings transfer to phase/run/variance endpoints” fails, but it fails generically for true, finite Euler, and amplitude-random controls in the left strip. This is a useful guardrail against amplitude proxies, not a separate HT invariant.

## Penrose — Machine R15 — stochastic-resetting occupation measure `[FIND]`

- NODE: `Resetting changes the occupation measure, not just the first-passage statistics`.
- NODE validation: random-walk reset simulations showed first-passage summaries and occupation measures separate; fixed-point resets narrowed occupation while distribution resets could improve mean first-passage with broad occupation.
- HT transfer: reset events are upward crossings of robust quantiles in `X_sigma(t)=log(1+|zeta'/zeta(sigma+it)|)`; occupation is the reset-age/value profile between events.
- Step 9: true zeta has nearly identical reset clocks across `sigma=.3/.5/.7` but a critical-lane occupation excess. `[100,170]`, q=.9: events `35/35/35`, mean intervals `14.94/14.94/14.97`, slopes `-1.08/-3.66/-1.24`. `[500,570]`, q=.8: events `49/51/48`, mean intervals `10.77/10.34/10.85`, slopes `-1.40/-4.22/-1.54`.
- Extreme/right-strip check: `sigma=1.2`, `[500,570]`, q=.8 collapses true and finite (`10` events each, mean interval about `50.8`, slope about `-1.53`).
- Step 11 stripped-clock check: forcing all lanes to use the exact `sigma=.5` reset clock preserves a true center-minus-neighbor slope excess (`-2.54`, `-2.30`) while finite/random controls have essentially none (`finite -0.39/+0.02`, random `+0.12/+0.01`).
- Promptability audit: broad cold prompt gave a generic reset-diffusion/resolvent idea, not the shared-clock occupation-slope invariant.
- Interpretation: first-passage reset clocks are mostly divisor-time shadows; reset occupation records the local `1/(s-rho)` pole geometry. Posted to `#research` id `757`; archive `computations/2026-06-21-penrose-r15-reset-occupation-summary.md`.

### LDP closed/open bounds -> phase-threshold boundary ambiguity

- NODE: `The upper bound applies to closed sets and the lower bound to open sets, not arbitrary measurable sets without extra regularity`.
- Evidence: `computations/2026-06-21-conway-ldp-boundary-phase.txt`.
- Outcome: reducing. The phase-threshold boundary band can dominate a tail event, but the effect is not true-specific and collapses with finite Euler on the right strip. This is a boundary-regularity view of transition-edge softness, not a new invariant.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Thermal transients mistaken for steady branches `[DEAD END — right theorem finds no short plateau; reverse recovers known phase-defect band]`
Seed RandomNode = "Temperature changes alter both hysteresis behavior and OCV-SOC calibration" -> Step 1 cold Codex broad list -> rng#14 = Bifurcation under thermal forcing -> Step 3 cold Codex narrow list -> rng#16 = NODE "Transient regimes mistaken for steady branches".
- STEP 5 constraint: near a thermally shifted saddle-node, a trajectory can dwell in a ghost bottleneck and appear steady in a short window even though no stable equilibrium exists; long dwell reveals escape.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-thermal-transient-false-branch.py`; output `computations/2026-06-21-hgt-NODE-thermal-transient-false-branch.txt`. Negative-μ ghost regimes `-0.025`, `-0.012`, and `-0.006` were classified steady in short windows but not in long dwell; `false_short_steady_count=3`.
- STEP 7 gate: saddle-node/thermal-ramp formulas do not apply unchanged to HT functions. A non-blind transfer must test apparent steady branches in continuum strip observables and require persistence under window extension, not discrete `zeta(n)` values.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-thermal-transient-ht-ghost-plateau.py` created three attempts: `zero-ghost-plateau`, `strip-transient-branch`, and `finite-prime-thermal-branch`; Levenshtein selected `zero-ghost-plateau` (`26`, normalized `0.5652`). Output: `computations/2026-06-21-hgt-STEP8-thermal-transient-ht-ghost-plateau.txt`.
- STEP 9 method rng#18 = look for the right theorem. The right theorem was persistence under window extension. No short steady plateaus were detected for true, finite, amplitude-matched finite, random-phase, or gamma-only controls across tested windows, so the selected transfer produced no HT finding.
- STEP 10 verdict: DEAD END for new knowledge. The apparent-branch test has no surviving signal.
- STEP 11 method rng#3 = reverse it. Script `computations/2026-06-21-hgt-STEP11-thermal-transient-reverse.py`; output `computations/2026-06-21-hgt-STEP11-thermal-transient-reverse.txt`. The reverse test found persistent long carrier bands only for true zeta at `sigma=0.3` (`long_med=0.431024` and `0.530177`, all short windows hit), while finite/random/gamma controls fail. This is exactly the already-known persistent left-strip phase-defect band, not a new transient/steady theorem.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Transient regimes mistaken for steady branches".

## Hawking THE-MACHINE tick — absolute irreversibility support gap `[DEAD END]`

- **Seed RandomNode:** `Energy flux must be continuous to maintain the assembled state`.
- **STEP 2 topic:** cold list first-20 order, rng `16` -> `Fluctuation theorems`.
- **STEP 4 NODE:** rng `10` -> `The importance of absolute irreversibility when reverse trajectories have zero probability`.
- **NODE constraint:** if the reverse/backward protocol has singular probability mass outside forward support, the integral fluctuation identity has a support correction `<exp(-sigma)>=1-lambda`; the missing support is a hard constraint, not a perturbative entropy tweak.
- **NODE validation:** `computations/2026-06-21-hgt-NODE-absolute-irreversibility.py` / `.txt`. Corrected support-direction test gives `lambda=0.35` and finite identity `0.65` for cases with missing forward support; random support-loss sweep confirms finite identity equals `1-lambda`.
- **STEP 7:** fluctuation-theorem support-ratio formulas do not apply unchanged to HT functions on `C`; a non-blind transfer must define support on continuum phase trajectories.
- **STEP 8:** three HT transfers scored by Levenshtein; selected `A_phase_reverse_support_gap` (`12/92=0.1304`) over zero-shadow and mirror-protocol variants.
- **STEP 9:** rng `12` -> find an invariant. Script/output: `computations/2026-06-21-hgt-STEP8-absolute-irreversibility-phase-support.py` / `.txt`. Mirror/time-reversed high-phase support lambda is not stable: some true rows have lower singular mass than finite/random, but high-threshold high-window rows invert; finite/right behavior tracks the same phase-support bookkeeping.
- **STEP 11:** rng `6` -> ask what action is happening. Script/output: `computations/2026-06-21-hgt-STEP11-absolute-irreversibility-support-action.py` / `.txt`. Circular-shift nulls show the action is support transport/misalignment: true and finite both leave the null in high-window regimes, random mostly does not. This is not a true-specific HT invariant.
- **Verdict:** dead end. The NODE constraint was real, but HT transfer reduces to mirror support alignment plus existing phase-defect/finite-Euler behavior; not posted to `#research`.
- **Next RandomNode:** `The importance of absolute irreversibility when reverse trajectories have zero probability`.

### Fast reversible stochastic stiffness -> carrier traffic / net motion ratio

- NODE: `Fast reversible reactions can create stiffness in exact stochastic simulation`.
- Evidence: `computations/2026-06-21-conway-fast-reversible-stiffness.txt`.
- Outcome: reducing. The HT stiffness ratio is the phase-cancellation defect ratio in reversible-event language. Useful metaphor, no new invariant.

## Penrose — Machine R16 — finite-prime gate / analytic-tension sign flip `[FIND]`

- NODE: `Gate reopening and polymer tension propagation can occur on comparable timescales, invalidating quasi-static assumptions`.
- NODE validation: coupled gate/tension translocation simulation sits between quasi-static no/full tension estimates; changing the tension clock changes kinetics while the quasi-static endpoints stay fixed.
- HT transfer: finite-prime phase agreement with true `zeta'/zeta` is the gate; EMA of positive true `log(1+|zeta'/zeta|)` is tension. The dynamic statistic is gate/tension covariance versus quasi-static `mean(open)*mean(tension)` and circular gate shifts.
- Step 9: critical-strip finite gates are anti-timed with true tension (`sigma=.5`, `[100,170]`, q=.5/tau=5: corr `-0.427`, shift z `-3.90`; `sigma=.3`, `[500,570]`: corr `-0.372`, z `-5.58`). Right-strip gates become positively timed (`sigma=1.2`: corr `+0.345/+0.433`, z `+4.16/+4.10`).
- Step 11 visual map q=.5/tau=5: `[100,170]` finite correlations across sigma `.2..1.3` are `-0.41,-0.46,-0.45,-0.38,-0.17,-0.08,0.00,+0.14,+0.26,+0.33,+0.34,+0.37`; `[500,570]` are `-0.32,-0.36,-0.36,-0.23,-0.07,+0.10,+0.23,+0.34,+0.38,+0.38,+0.41,+0.36`. Random-phase gates are weaker.
- Interpretation: the finite-prime clock blocks true analytic tension in the critical strip and tracks it in the Euler-convergent strip; the sign transition is a measurable two-clock seam. Posted to `#research` id `758`; archive `computations/2026-06-21-penrose-r16-two-clock-gate-tension-summary.md`.

### Entry-exit delay -> phase-threshold delayed exit

- NODE: `Entry-exit delays near repelling slow branches can dominate observed timing and are easily mistaken for numerical artifacts`.
- Evidence: `computations/2026-06-21-conway-entry-exit-delay.txt`.
- Outcome: failed transfer. The NODE delay validates, but the HT phase-defect event is instantaneous and has zero exit-tail lag across true, finite, and random controls.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Crisis laminar duration power-law scaling `[DEAD END — threshold-run scaling survives minimal counterexamples]`
Seed RandomNode = "Transient regimes mistaken for steady branches" -> Step 1 cold Codex broad list -> rng#17 = Crisis-induced intermittency -> Step 3 cold Codex narrow list -> rng#6 = NODE "Mean laminar duration commonly follows a power-law scaling with distance from the crisis parameter".
- STEP 5 constraint: laminar phases near a crisis are not arbitrary pauses; mean laminar duration is constrained by distance from the crisis threshold and follows a power law up to finite-record/noise limits.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-crisis-laminar-powerlaw.py`; output `computations/2026-06-21-hgt-NODE-crisis-laminar-powerlaw.txt`. Synthetic crisis laminar means fit a power law with `crisis_alpha=0.306026`, `crisis_loglog_r2=0.976724`; the no-distance null had `null_alpha=-0.005636`, `null_loglog_r2=0.221785`.
- STEP 7 gate: crisis scaling formulas do not apply unchanged to HT functions. A non-blind transfer must define laminar/burst runs on continuum strip observables and survive finite-window/minimal-counterexample controls.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-crisis-laminar-ht-scaling.py` created three attempts: `phase-laminar-scaling`, `zero-shadow-laminar-scaling`, and `finite-prime-burst-scaling`; Levenshtein selected `phase-laminar-scaling` (`18`, normalized `0.2069`). Output: `computations/2026-06-21-hgt-STEP8-crisis-laminar-ht-scaling.txt`.
- STEP 9 method rng#16 = use a minimal counterexample. The minimal counterexample was shuffling the same phase-defect values. Scaling survived shuffling and appeared in finite/random controls: true `sigma=0.3`, `[100,170]` had alpha `0.744234`, `r2=0.990689`, but shuffled had alpha `1.079298`, `r2=0.999178`; finite had alpha `0.870447`, `r2=0.989700`; random-phase had alpha `1.017576`, `r2=0.999775`. The right side `sigma=1.2` also showed high-R2 scaling in true/finite/random.
- STEP 10 verdict: DEAD END for new knowledge. The scaling is a threshold/run-statistics artifact, not an HT-native crisis law.
- STEP 11 method rng#8 = look for similar objects. Script `computations/2026-06-21-hgt-STEP11-crisis-similar-objects.py`; output `computations/2026-06-21-hgt-STEP11-crisis-similar-objects.txt`. Similar observables (`phase_defect`, amplitude, zero-shadow, prime amplitude, roughness) all produced high-R2 scaling, usually surviving shuffling and appearing in finite/random/right-side controls. This confirms generic threshold-run geometry.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Mean laminar duration commonly follows a power-law scaling with distance from the crisis parameter".

## Penrose — Machine R17 — conformal/cosmic time gauge `[DEAD END / PROMPTABLE]`

- NODE: `The ambiguity introduced by using conformal time versus cosmic time descriptions`.
- NODE validation: power-law cosmology shows wrong time-coordinate treatment shifts or invalidates horizon crossing.
- HT transfer selected by Levenshtein: FE mirror as time gauge.
- Step 9 boundary cases: completed true residual `L_complete(s)+L_complete(1-s)` is numerical zero (`~1e-31`); uncompleted true, finite Euler, gamma-only, and wrong-sign gauges are nonzero. This is exactly the completed functional equation.
- Step 11 attack-false: even best positive scalar time-Jacobian leaves median uncompleted residuals `~1.06..2.29`; gamma additive completion cancels to zero. This is useful confirmation but promptable from FE/gamma formulas.
- Verdict: no `#research` post.

## Dead end — 2026-06-21 — MSD trajectory heterogeneity

- RandomNode seed: `The importance of absolute irreversibility when reverse trajectories have zero probability`.
- STEP 2 topic: `Non-ergodic stochastic dynamics`.
- STEP 4 NODE: `Mean squared displacement can misclassify transport when trajectory-level heterogeneity is ignored`.
- NODE constraint tested: an ensemble MSD exponent is insufficient unless per-trajectory time-averaged MSD self-averages.
- NODE output: `computations/2026-06-21-hgt-NODE-msd-trajectory-heterogeneity.py`, `computations/2026-06-21-hgt-NODE-msd-trajectory-heterogeneity.txt`. Homogeneous diffusion had `alpha=1.0000`, `EB=0.0638`, `q90/q10=1.9012`; heterogeneous same-mean diffusivity had `alpha≈1` but `EB=3.4810`, `q90/q10=61.4512`; the sigma sweep showed misclassification beginning around `sigma=0.50`.
- STEP 7: ordinary MSD / TAMSD / ergodicity-breaking formulas do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_msd_trajectory_heterogeneity` (`6/34=0.1765`).
- STEP 9 method `9` (`Test small cases`). Script/output: `computations/2026-06-21-hgt-STEP8-msd-trajectory-heterogeneity.py`, `computations/2026-06-21-hgt-STEP8-msd-trajectory-heterogeneity.txt`.
- STEP 9 verdict: hidden trajectory heterogeneity is not HT-specific. True hidden cases either disappear under small-window checks or are matched by finite Euler / random-phase controls; right-strip true and finite nearly coincide.
- STEP 11 method `11` (`Run experiments`). Script/output: `computations/2026-06-21-hgt-STEP11-msd-trajectory-metaphor.py`, `computations/2026-06-21-hgt-STEP11-msd-trajectory-metaphor.txt`.
- STEP 11 verdict: Fourier-phase and rank-Fourier surrogates can preserve the global MSD-like curve while changing local window heterogeneity, but this happens for true, finite Euler, and random-phase traces. This reduces to generic MSD/autocorrelation insufficiency, not a new HT constraint.
- Final verdict: DEAD END for non-reducing finding. Not posted to `#research`.

### Chaotic saddle UPO skeleton -> zero-shadow recurrence skeleton

- NODE: `A chaotic saddle can contain infinitely many unstable periodic orbits that govern transient dynamics`.
- Evidence: `computations/2026-06-21-conway-chaotic-saddle-recurrence.txt`.
- Outcome: reducing. Top-decile recurrence lift is not true-specific; right-strip true/finite recurrence skeletons coincide. No new invariant beyond phase-defect density/autocorrelation.

## Round (THE-MACHINE revised workflow, hgt) — NODE = Inhibition can organize seizure-like bursts `[DEAD END — suppression chain and reverse shadow leak to controls]`
Seed RandomNode = "Mean laminar duration commonly follows a power-law scaling with distance from the crisis parameter" -> Step 1 cold Codex broad list -> rng#3 = Epileptic seizure dynamics -> Step 3 cold Codex narrow list -> rng#6 = NODE "Inhibition can help generate or organize seizures, rather than simply suppressing them".
- STEP 5 constraint: inhibition is not a monotone brake; in a rebound-capable network, moderate inhibition can organize release/burst runs while weak inhibition fails to organize and very strong inhibition fragments or suppresses runs.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-inhibition-organizes-seizures.py`; output `computations/2026-06-21-hgt-NODE-inhibition-organizes-seizures.txt`. The toy E/I rebound model showed no organized bursts at zero inhibition, then a maximum organized-burst score at `g=0.65` (`burst_rate=0.858125`, `mean_burst_run=457.666667`) with stronger inhibition giving shorter runs.
- STEP 7 gate: seizure E/I equations do not apply unchanged to HT functions. A non-blind transfer must keep the suppressive-brake/release/burst dependency chain on continuum strip phase observables.
- STEP 8 revised rule: `computations/2026-06-21-hgt-STEP8-inhibition-phase-bursts.py` created three attempts: `inhibition-organized-phase-bursts`, `gamma-inhibitory-brake`, and `finite-prime-gaba-rebound`; Levenshtein selected `inhibition-organized-phase-bursts` (`7`, normalized `0.0824`). Output: `computations/2026-06-21-hgt-STEP8-inhibition-phase-bursts.txt`.
- STEP 9 method rng#21 = build a dependency chain. The chain was inhibition strength -> suppressive brake + release rebound -> organized phase-burst runs. For true zeta the output mostly decreased as inhibition increased (`sigma=0.3`, `[100,170]`: organized `0.450160` at strength 0 to `0` at `1.70`), and finite/random controls showed the same monotone suppression structure. Right-side true and finite were nearly identical (`sigma=1.2`, strength 0 organized `0.731510` for both).
- STEP 10 verdict: DEAD END for new knowledge. No true-only nonmonotone organization optimum survived; the dependency chain is a generic threshold/smoothing suppressor.
- STEP 11 method rng#3 = reverse it. Script `computations/2026-06-21-hgt-STEP11-inhibition-reverse-shadow.py`; output `computations/2026-06-21-hgt-STEP11-inhibition-reverse-shadow.txt`. Post-burst inhibitory shadows were weak and appeared in amplitude-matched/random/right-side controls as well as true zeta. Example `sigma=0.3`, `[100,170]`: true shadow median `0.015600`, amplitude-matched finite `0.017474`, random-phase `0.019540`.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = "Inhibition can help generate or organize seizures, rather than simply suppressing them".

### Droplet evaporation distribution -> distributed delay phase response

- NODE: `The influence of droplet size distribution and evaporation time in liquid-fueled systems`.
- Evidence: `computations/2026-06-21-conway-droplet-delay-distribution.txt`.
- Outcome: reducing. Kernel-averaged delay response is generic autocorrelation smoothing; no true-specific invariant, with exact true/finite collapse in the right strip.

## Penrose — Machine R18 — observer-location light-cone inference `[DEAD END / ZERO-PROXIMITY]`

- NODE: `The observer's location affects inferred distances, redshifts, and Hubble rates`.
- NODE validation: in a 1D inhomogeneous Hubble field, inferred local H varied by observer and aperture despite one global field.
- HT transfer: basepoints in the complex strip sample radial rays of `zeta'/zeta` and infer local growth/phase slopes.
- Step 9: true observer variance is large near `sigma=.5` (`growth mean/stdev/range 1.809/1.755/6.466`) and collapses in the right strip.
- Step 11 action test: variance is explained by basepoint pole proximity; inferred growth correlates with basepoint `log(1+|zeta'/zeta|)` at `0.942` for `sigma=.3` and `0.975` for `sigma=.5`.
- Verdict: zero-neighborhood restatement; no `#research` post.

## Dead end — 2026-06-21 — Shallow catalog scaling depth

- RandomNode seed: `Mean squared displacement can misclassify transport when trajectory-level heterogeneity is ignored`.
- STEP 2 topic: `Galaxy clustering and fractal cosmology debates`.
- STEP 4 NODE: `Early fractal-cosmology arguments often relied on shallower catalogs whose apparent scaling could change with deeper surveys`.
- NODE constraint tested: a claimed fractal count exponent is evidence only if it remains stable as survey depth crosses the candidate transition scale.
- NODE output: `computations/2026-06-21-hgt-NODE-shallow-fractal-catalogs.py`, `computations/2026-06-21-hgt-NODE-shallow-fractal-catalogs.txt`. The finite fractal-to-homogeneous catalog shifted from shallow `D_outer≈1.970` to deep `D_outer≈2.956`; pure fractal stayed near `D≈2`; homogeneous stayed near `D≈3` once not sparse.
- STEP 7: counts-in-spheres / fractal-dimension formulas do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_catalog_scaling_depth` (`11/30=0.3667`).
- STEP 9 method `21` (`Build a dependency chain`). Script/output: `computations/2026-06-21-hgt-STEP8-shallow-fractal-catalog-depth.py`, `computations/2026-06-21-hgt-STEP8-shallow-fractal-catalog-depth.txt`.
- STEP 9 verdict: phase-event count-depth exponents are mostly stable for true zeta, and larger drift is matched or exceeded by finite Euler or random-phase controls; right-strip true/finite collapse persists.
- STEP 11 method `2` (`Attack it as false`). Script/output: `computations/2026-06-21-hgt-STEP11-shallow-fractal-attack.py`, `computations/2026-06-21-hgt-STEP11-shallow-fractal-attack.txt`.
- STEP 11 verdict: adversarial threshold/origin sweep produced `SURVIVAL_COUNT true_specific=0` after sparse controls were treated as non-evidence.
- Final verdict: DEAD END for non-reducing finding. Not posted to `#research`.

## Penrose — Machine R19 — observed-volume covariance sign `[FIND]`

- NODE: `The perturbation of the observed volume element` from relativistic light-cone averaging.
- NODE validation: synthetic observed averages shift by the covariance between observable and perturbed volume element even when coordinate means are near zero.
- HT transfer: `O=robust(log(1+|zeta'/zeta|))`; observed volume perturbation from local gradient/curvature of the continuum strip trace.
- Step 9 reverse: critical-strip true zeta has positive weighted-volume bias and negative inverse-volume bias, while finite/random controls have the opposite sign (`sigma=.5`, `[100,170]`: true `+0.329/-0.381`; finite `-0.199/+0.208`; random `-0.077/+0.086`). Right strip true/finite both negative.
- Step 11 missing lemma: value-gradient observed-volume covariance sign. `[100,170]`, `sigma=.5`: true grad/curv/top30 `+0.208/+0.866/+0.776`; finite `-0.364/-0.515/-0.603`; random `-0.248/-0.479/-0.304`. `sigma=1.2`: true and finite both negative.
- Interpretation: coordinate averages miss the sign of measure-field covariance; critical-strip analytic continuation puts high values on high observed-volume perturbations, finite/random do not. Posted to `#research` id `761`; archive `computations/2026-06-21-penrose-r19-observed-volume-covariance-summary.md`.

### Pooled drying zones -> transverse sigma phase-zone coexistence

- NODE: `Pooling thickness causing mixed wet, gelled, and dry zones`.
- Evidence: `computations/2026-06-21-conway-pooling-zone-coexistence.txt`, `computations/2026-06-21-conway-STEP12-pooling-zone-battery.txt`.
- Outcome: reducing. Cross-sigma coexistence and entropy are not true-specific after threshold/grid sweep; random controls can match or exceed true.

### Biofilm dynamic stratification -> time-changing sigma phase stratification

- NODE: `Stratification changes over time as growth, erosion, sloughing, and environmental conditions reshape the biofilm`.
- Evidence: `computations/2026-06-21-conway-biofilm-dynamic-stratification.txt`.
- Outcome: reducing. True has different static wet/gel/dry phase-zone mass, but the dynamic reshaping subclaim fails.

## Dyson — homeostatic energy-capacity constraint [DEAD END]
- Seed RandomNode: `Inhibition can help generate or organize seizures, rather than simply suppressing them`.
- STEP 1 rng#4 topic: `Homeostatic plasticity gone wrong`.
- STEP 4 rng#18 NODE: `Homeostatic responses constrained by energy metabolism and mitochondrial capacity`.
- STEP 5 constraint: homeostatic gain can only restore target activity if metabolic/mitochondrial capacity can pay the gain-expression and firing cost.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-homeostatic-energy-capacity.py`, output `computations/2026-06-21-hgt-NODE-homeostatic-energy-capacity.txt`. Low capacity keeps actual activity far below target despite high raw homeostatic gain; once capacity approaches required demand, stress disappears and the limited/no-limit runs coincide.
- STEP 7 formula check: energy-budget/homeostatic-gain formulas do not apply unchanged to HT functions; any transfer must replace neuronal activity with continuum/differential phase activity on `C`, not values `zeta(n)`.
- STEP 8 transfer attempts: selected `metabolic-capacity-phase-homeostasis` by Levenshtein (`6`) over `mitochondrial-constraint-derivative-budget` (`57`) and `atp-limited-zero-shadow-upscaling` (`63`). Script/output: `computations/2026-06-21-hgt-STEP8-homeostatic-energy-ht.py`, `computations/2026-06-21-hgt-STEP8-homeostatic-energy-ht.txt`.
- STEP 9 method rng#13: monotone quantity `capacity -> phase-homeostasis success fraction`. True left-strip zeta separates from finite/random under capacity thresholds, but the result is the existing phase-carrier strength repackaged; right strip true/finite collapse and controls partly follow the same curve.
- STEP 11 method rng#7: strip essentials. Script/output: `computations/2026-06-21-hgt-STEP11-homeostatic-energy-strip-essentials.py`, `computations/2026-06-21-hgt-STEP11-homeostatic-energy-strip-essentials.txt`. Removing or shuffling cost preserves the ordering, so the energy/capacity metaphor reduces to phase-defect drive, not an independent capacity/cost coupling.
- STEP 10/11 verdict: DEAD END for non-reducing finding. Not posted to `#research`.

## Dead end — 2026-06-21 — Allometric exponent subset sensitivity

- RandomNode seed: `Early fractal-cosmology arguments often relied on shallower catalogs whose apparent scaling could change with deeper surveys`.
- STEP 2 topic: `Allometric scaling in biology`.
- STEP 4 NODE: `The fitted allometric exponent often changes with the taxonomic range, body-size range, and life stage included in the dataset`.
- NODE constraint tested: a claimed allometric exponent is meaningful only if it is stable under biologically meaningful restrictions by clade, body-size range, and stage.
- NODE output: `computations/2026-06-21-hgt-NODE-allometry-exponent-sensitivity.py`, `computations/2026-06-21-hgt-NODE-allometry-exponent-sensitivity.txt`. Clean universal-slope null stayed stable (`slope_range=0.0510`); offset mixture already widened (`0.1764`); heterogeneous clade/stage model widened further (`0.3611`).
- STEP 7: allometric power-law fitting does not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_exponent_subset_sensitivity` (`9/38=0.2368`).
- STEP 9 method `3` (`Reverse it`). Script/output: `computations/2026-06-21-hgt-STEP8-allometry-phase-exponent.py`, `computations/2026-06-21-hgt-STEP8-allometry-phase-exponent.txt`.
- STEP 9 verdict: no universal true-specific phase exponent emerged. True subset range `0.5161` was comparable to finite `0.5882` and random `0.6476`; whole-fit exponents were near zero for all kinds.
- STEP 11 method `5` (`Make it visual`). Script/output: `computations/2026-06-21-hgt-STEP11-allometry-visual-heatmap.py`, `computations/2026-06-21-hgt-STEP11-allometry-visual-heatmap.txt`.
- STEP 11 verdict: heatmap texture is not HT-specific. True and finite roughness are similar (`0.7423` vs `0.6564`) and right-side rows collapse; random is rougher but not a true-specific obstruction.
- Final verdict: DEAD END for non-reducing finding. Not posted to `#research`.

## Penrose — Machine R20 — phase-space caustic wrong momentum `[FIND]`

- NODE: `Resolving caustic surfaces in phase space, not only their projections into physical space`.
- NODE validation: projection folds/multiple arrivals occur in `x(u)=u^3-u`, while the phase-space lift `(x,p)` remains single-labeled.
- HT transfer: projection coordinate `O=robust(log(1+|zeta'/zeta|))`; momentum coordinate phase; invariant `int O dP`.
- Step 9: true analytic phase lift has large critical-strip signed area (`sigma=.5`, `[100,170]`: `+2.3487`, z `18.92`; `[500,570]`: `+2.3301`, z `11.41`). True amplitude + finite-prime momentum is opposite-signed and insignificant (`-0.787/-0.772`, z about `-0.55`).
- Step 11 fake proof: increasing finite cutoff does not approach true area. `sigma=.5`, `[100,170]`: true `+2.2848`; finite `P=5/11/23/47/97` gives `-0.5785/-0.5740/-0.6118/-0.9364/-1.1085`. Same opposite-sign behavior on `[500,570]` and at `sigma=.3`.
- Interpretation: finite-prime phase is the wrong momentum coordinate for true critical-strip projected caustics. Posted to `#research` id `762`; archive `computations/2026-06-21-penrose-r20-phase-space-caustic-summary.md`.

### Desquamation link dissolution -> phase-regulated high-defect exits

- NODE: `Desquamation is not simply “cells falling off”; it is an enzyme-regulated dissolution of intercellular adhesion structures`.
- Evidence: `computations/2026-06-21-conway-desquamation-link-dissolution.txt`, `computations/2026-06-21-conway-STEP12-desquamation-dissolution-battery.txt`.
- Finding: experimental/conjectural. True left-strip high-defect runs have frequent phase-dominant, small-drop exits. Finite Euler has few/non-phase exits; random controls have sparser and much larger-drop exits. Right-strip true/finite have no exit population.

## Penrose — Machine R21 — Maslov boundary phase `[DEAD END / FE COMPLETION]`

- NODE: `The sign of the Van Vleck determinant changes across caustics, and the Maslov factor is what keeps the square-root amplitude continuously interpretable`.
- NODE validation: signed determinant toy model shows `sqrt(|D|)` loses the sign and the Maslov phase supplies branch information.
- HT transfer selected by Levenshtein: FE mirror boundary phase.
- Step 9: completed `Lambda(s)/Lambda(1-s)` has zero phase range/unit modulus; uncompleted zeta mirror ratio carries the gamma phase range. This is exactly the functional equation.
- Step 11: finite Euler mirror phases do not supply the gamma/Maslov boundary phase; cutoffs remain small/anti-correlated with residual ranges `~97..257`.
- Verdict: promptable FE-completion diagnostic; no `#research` post.

## Dead end / instrument — 2026-06-21 — Boundary-domain phase sensitivity

- RandomNode seed: `The fitted allometric exponent often changes with the taxonomic range, body-size range, and life stage included in the dataset`.
- STEP 2 topic: `Anomalous diffusion`.
- STEP 4 NODE: `Considering boundary effects and domain geometry in crowded or confined systems`.
- NODE constraint tested: an apparent anomalous exponent is interpretable only after fixing domain geometry and boundary condition.
- NODE output: `computations/2026-06-21-hgt-NODE-boundary-domain-diffusion.py`, `computations/2026-06-21-hgt-NODE-boundary-domain-diffusion.txt`. Same step law gave unbounded `alpha_all=1.0106`; tight reflecting `alpha_all=0.1192`; tight absorbing conditional `alpha_all=0.0664`; widening the domain returned exponents toward 1.
- STEP 7: reflecting/absorbing Brownian MSD formulas do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_boundary_domain_geometry` (`16/34=0.4706`).
- STEP 9 method `16` (`Use a minimal counterexample`). Script/output: `computations/2026-06-21-hgt-STEP8-boundary-domain-phase.py`, `computations/2026-06-21-hgt-STEP8-boundary-domain-phase.txt`.
- Initial candidate: true `ζ'/ζ` raw phase-increment exponent was more sigma-domain sensitive than finite/random (`range≈0.375` true vs `0.178/0.098` finite and `0.014/0.021` random in two windows). Posted provisionally to `#research` as message `764`.
- STEP 11 method `2` (`Attack it as false`). Script/output: `computations/2026-06-21-hgt-STEP11-boundary-domain-attack.py`, `computations/2026-06-21-hgt-STEP11-boundary-domain-attack.txt`. Lane z-scoring preserved domain range and within-lane shuffling killed it, but finite z-scored controls also carried a comparable skeleton.
- STEP 12 stress battery: `computations/2026-06-21-hgt-STEP12-boundary-domain-battery.py`, `computations/2026-06-21-hgt-STEP12-boundary-domain-battery.txt`. Finite-prime stress killed robust promotion: survival rule passed only `1/4` windows; finite raw range matched/exceeded true in `[14,84]` and `[100,170]`.
- Correction posted to `#research` as message `765`; id `764` demoted to dead-end/instrument and should not count as a non-reducing finding.
- Final verdict: DEAD END for counted non-reducing finding. Useful diagnostic only.

## Penrose — Machine R22 — Berry holonomy loop winding `[DEAD END / ARGUMENT PRINCIPLE]`

- NODE: `The observable phase is gauge invariant, even though the electronic eigenvector sign convention is arbitrary`.
- NODE validation: two-level conical intersection has transported sign `-1` around seam, invariant under random local sign gauges.
- HT transfer: loop phase holonomy of `zeta` and `zeta'/zeta`.
- Step 9: loops around zeta zeros give `wind(zeta)=+1`, `wind(zeta'/zeta)=-1`; gap loops give zero.
- Step 11 strengthened to deformed loops; winding unchanged.
- Verdict: argument principle / promptable; no `#research` post.

## Dyson — coupled low-reserve lane alignment [FIND]
- Seed RandomNode: `Homeostatic responses constrained by energy metabolism and mitochondrial capacity`.
- STEP 1 rng#8 topic: `Aging as loss of energetic reserve`.
- STEP 4 rng#17 NODE: `Frailty can be understood as a visible failure of reserve across multiple coupled systems`.
- STEP 5 constraint: visible frailty appears when multiple coupled reserves are near threshold and support load cascades across systems; resting mean reserve is not enough.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-frailty-coupled-reserve.py`, output `computations/2026-06-21-hgt-NODE-frailty-coupled-reserve.txt`. Coupling turns a single weak-system case from non-visible peak failure into full multi-system failure; aged/multiweak states fail persistently.
- STEP 7 formula check: frailty-index/recovery-time formulas do not apply unchanged to HT; the minimal continuum/differential transfer uses sigma lanes as coupled reserve systems and phase-defect reserve from `Gamma_inf` with `P=zeta'/zeta`.
- STEP 8 transfer attempts: selected `frailty-visible-phase-reserve-across-coupled-sigma-systems` by Levenshtein (`15`) over `coupled-zero-shadow-reserve-cascade` (`45`) and `archimedean-prime-organ-failure-index` (`50`). Script/output: `computations/2026-06-21-hgt-STEP8-frailty-coupled-reserve-ht.py`, `computations/2026-06-21-hgt-STEP8-frailty-coupled-reserve-ht.txt`.
- STEP 9 method rng#23: classify boundary cases. Initial multi-lane frailty mostly tracked single-lane phase reserve; not enough alone.
- STEP 11 method rng#3: reverse it. Script/output: `computations/2026-06-21-hgt-STEP11-frailty-reverse-weakest-lane.py`, `computations/2026-06-21-hgt-STEP11-frailty-reverse-weakest-lane.txt`. Reversal exposed the candidate: true left-strip visible co-failure exceeds independent/circular lane timing nulls, unlike finite/random controls.
- STEP 12 all-method battery: `computations/2026-06-21-hgt-STEP12-frailty-lane-alignment-battery.py`, output `computations/2026-06-21-hgt-STEP12-frailty-lane-alignment-battery.txt`.
- Evidence: left `[100,170]` threshold .12 true excess over independent shuffle +0.229 vs finite -0.015 and random +0.017; left `[500,570]` threshold .20 true +0.216 vs finite -0.092 and random -0.003; left `[900,970]` threshold .20 true +0.218 vs finite -0.095. Right boundary collapses true/finite to negative excess. Survives circular shifts, sigma=.3 removal, and phase/zero-shadow representations; fails for two-lane small case.
- Verdict: NON-REDUCING EXPERIMENTAL FINDING / CONJECTURE. Posted to `#research` as Dyson id=768. Count now 7/30.

## Penrose — Machine R23 — Floquet strip micromotion winding `[DEAD END / GENERIC]`

- NODE: `Rudner winding invariant for two-dimensional driven systems`.
- NODE validation: full `(kx,ky,t)` map can carry winding invisible to a time slice.
- HT transfer: skyrmion-like map `(sigma,t)->normalize(amplitude,cos phase,sin phase)`.
- Step 9: endpoint summaries miss Q and time-shuffling kills much of it, but true/finite/random all have large negative full-window Q values.
- Step 11 dependency chain: constant amplitude kills Q, while sigma-mean/time-shuffled amplitude preserves large Q across all models. The invariant is generic micromotion plus amplitude texture, not HT-specific.
- Verdict: no `#research` post.

### 2026-06-21 -- Conway -- substrate depletion masquerading as inhibition

- NODE: `Substrate depletion can masquerade as protease inhibition in dense reaction networks`.
- Constraint tested: apparent inhibition is confounded unless finite substrate conservation/depletion is fixed.
- HT transfer: `cancellation budget depletion masquerades as differential inhibition in analytic networks`.
- Method: #22 compare nearby false statements; Step 11 method #16 minimal counterexample.
- Files: `computations/2026-06-21-conway-substrate-depletion-confound.py`, `computations/2026-06-21-conway-substrate-depletion-confound.txt`, `computations/2026-06-21-conway-STEP11-substrate-depletion-mincounter.py`, `computations/2026-06-21-conway-STEP11-substrate-depletion-mincounter.txt`, `computations/2026-06-21-conway-STEP12-substrate-depletion-battery.py`, `computations/2026-06-21-conway-STEP12-substrate-depletion-battery.txt`.
- Verdict: dead end. Initial short-window candidates were threshold/window artifacts; Step 12 gave `survival_total=0/27` and `survival_core=0/9`.

## Dyson — reducible multi-type partial extinction [DEAD END]
- Seed RandomNode: `Frailty can be understood as a visible failure of reserve across multiple coupled systems`.
- STEP 1 rng#20 topic: `Branching-process extinction`.
- STEP 4 rng#17 NODE: `Reducible multi-type systems can have partial extinction distinct from global extinction`.
- STEP 5 constraint: in reducible multi-type branching, extinction is vector-valued; one type can die while another survives, so global non-extinction hides partial extinction.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-reducible-multitype-partial-extinction.py`, output `computations/2026-06-21-hgt-NODE-reducible-multitype-partial-extinction.txt`. Type A can die out while B/global survive; partial B-only survival reaches 0.321667 in one tested case.
- STEP 7 formula check: vector generating-function fixed point formulas do not apply unchanged to HT functions; the minimal continuum/differential transfer treats sigma lanes as types and phase-reserve runs as survival.
- STEP 8 transfer attempts: selected `reducible-sigma-lane-partial-extinction` by Levenshtein (`5`) over `multi-type-zero-shadow-extinction-vector` (`36`) and `prime-cutoff-immigration-survival-split` (`61`). Script/output: `computations/2026-06-21-hgt-STEP8-reducible-partial-extinction-ht.py`, `computations/2026-06-21-hgt-STEP8-reducible-partial-extinction-ht.txt`.
- STEP 9 method rng#13: monotone survival depth. True left-band partial survival persists deeper than controls, but this initially looked like ordinary phase-run persistence.
- STEP 11 method rng#16: minimal counterexample. Script/output: `computations/2026-06-21-hgt-STEP11-reducible-minimal-counterexample.py`, `computations/2026-06-21-hgt-STEP11-reducible-minimal-counterexample.txt`. Removing strongest lanes kills the vector/global verdict at stricter settings; the result is carried by single-lane max-run lengths.
- Verdict: DEAD END for non-reducing finding. Not posted to `#research`.

## Finding — 2026-06-21 — Phase initial-measure association gate

- RandomNode seed: `Considering boundary effects and domain geometry in crowded or confined systems`.
- STEP 2 topic: `Interacting particle systems with exclusion`.
- STEP 4 NODE: `Initial measures must satisfy entropy or association conditions in many limit theorems`.
- NODE constraint tested: matching one-site density is insufficient; admissible initial measures must exclude hidden global correlations / excessive entropy that prevent empirical fields from self-averaging.
- NODE output: `computations/2026-06-21-hgt-NODE-initial-measure-entropy.py`, `computations/2026-06-21-hgt-NODE-initial-measure-entropy.txt`. Product Bernoulli had `N*var≈0.25`; global mixture with same mean kept `var≈0.09` and positive entropy density `0.1927`.
- STEP 7: entropy/association initial-measure conditions do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_initial_entropy_gate` (`23/35=0.6571`).
- STEP 9 method `16` (`Use a minimal counterexample`). Script/output: `computations/2026-06-21-hgt-STEP8-initial-entropy-phase-gate.py`, `computations/2026-06-21-hgt-STEP8-initial-entropy-phase-gate.txt`.
- STEP 9 finding: productizing sigma-lane phase-event marginals loses true joint structure. At `[100,170]`, `true_q70`: true association excess `0.104293`, excess/product `3.8434`; finite `0.023309`, `1.7412`; random `0.000160`, `0.0103`. At q85 true remains high while finite/random drop.
- STEP 11 method `17` (`Change representation`). Script/output: `computations/2026-06-21-hgt-STEP11-initial-entropy-graph.py`, `computations/2026-06-21-hgt-STEP11-initial-entropy-graph.txt`. Normalized association graph preserved separation: `[100,170]` q70 true top eigenvalue `3.8482`, edges20 `21`; finite eig `1.7723`, edges20 `11`; random eig `0.1209`, no edges.
- Posted finding to `#research` as message `771`.
- STEP 12 battery: `computations/2026-06-21-hgt-STEP12-initial-entropy-battery.py`, `computations/2026-06-21-hgt-STEP12-initial-entropy-battery.txt`. Q70 survived all four windows against finite cutoffs `N=30,80,160,240,400` and lane-shuffle productization; q60 is too permissive and q85 has marginal-degeneracy risk.
- Posted Step 12 refinement / theorem shape to `#research` as message `772`.
- Final bounded claim: around the nondegenerate q70 threshold band, true `ζ'/ζ` has a cross-sigma phase-event association graph with leading eigenvalue and positive-correlation component separated from finite Euler/random/productized controls.

## Dyson — noise-induced premature bursts [DEAD END]
- Seed RandomNode: `Reducible multi-type systems can have partial extinction distinct from global extinction`.
- STEP 1 rng#19 topic: `Crisis-induced intermittency`.
- STEP 4 rng#8 NODE: `Noise-induced premature bursts`.
- STEP 5 constraint: stochastic kicks can cross a burst boundary before the deterministic crisis threshold is reached.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-noise-induced-premature-bursts.py`, output `computations/2026-06-21-hgt-NODE-noise-induced-premature-bursts.txt`. Premature burst fraction rises with noise and proximity.
- STEP 7 formula check: first-passage/Kramers-style formulas do not apply unchanged to HT functions; the minimal transfer uses noise on continuum phase-defect traces, not discrete `zeta(n)`.
- STEP 8 transfer attempts: selected `noise-induced-premature-phase-bursts` by Levenshtein (`6`) over `prime-jitter-premature-crisis` (`16`) and `zero-shadow-noise-trigger-bursts` (`21`). Script/output: `computations/2026-06-21-hgt-STEP8-noise-premature-bursts-ht.py`, `computations/2026-06-21-hgt-STEP8-noise-premature-bursts-ht.txt`.
- STEP 9 method rng#10: extreme cases. No-noise gives no premature events; added noise creates premature threshold crossings across true, finite, amplitude-matched, random-phase, and right-strip controls.
- STEP 11 method rng#3: reverse it. Script/output: `computations/2026-06-21-hgt-STEP11-noise-premature-reverse.py`, `computations/2026-06-21-hgt-STEP11-noise-premature-reverse.txt`. Conditioning on premature bursts reveals generic distance-to-threshold geometry with control leakage.
- Verdict: DEAD END for non-reducing finding. Not posted to `#research`.

### 2026-06-21 -- Conway -- fraction contamination false colocalization

- NODE: `Compartment contamination during fractionation creating false colocalization signals`.
- Constraint tested: observed colocalization must survive a contamination/mixing matrix and marker-based deconvolution.
- HT transfer: `strip contamination during window fractionation creating false colocalization signals`.
- Method: #17 change representation; Step 11 method #16 minimal counterexample.
- Files: `computations/2026-06-21-conway-fraction-contamination-colocalization.py`, `computations/2026-06-21-conway-fraction-contamination-colocalization.txt`, `computations/2026-06-21-conway-STEP11-fraction-contamination-minleak.py`, `computations/2026-06-21-conway-STEP11-fraction-contamination-minleak.txt`.
- Verdict: dead end. No true-specific decontaminated colocalization survived; minimal false positives also occurred in finite controls under ill-conditioned mixing.

## Dead end — 2026-06-21 — Phase covariance range gate

- RandomNode seed: `Initial measures must satisfy entropy or association conditions in many limit theorems`.
- STEP 2 topic: `Central limit theorems for associated random variables`.
- STEP 4 NODE: `The difference between short-range associated fields and long-range dependent associated fields, which may have nonstandard limits`.
- NODE constraint tested: positive association alone is insufficient for a standard CLT; covariance summability controls whether `Var(S_n)` is order `n` or larger.
- NODE output: `computations/2026-06-21-hgt-NODE-short-long-range-associated.py`, `computations/2026-06-21-hgt-NODE-short-long-range-associated.txt`. Corrected NODE used PSD associated Gaussian examples: AR(1) short range with `Var(S_n)/n -> 2.333`; fGn `H=0.8` with `Var(S_n)=n^1.6` and growing sqrt-normalized variance.
- STEP 7: covariance-summability / nonstandard normalization formulas do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_covariance_range_gate` (`24/34=0.7059`).
- STEP 9 method `12` (`Find an invariant`). Script/output: `computations/2026-06-21-hgt-STEP8-covariance-range-phase.py`, `computations/2026-06-21-hgt-STEP8-covariance-range-phase.txt`. Block-variance beta did not give a true-specific long-range signal; finite/random often had larger beta, and right strip true/finite collapsed.
- STEP 11 method `15` (`Strengthen the conjecture`). Script/output: `computations/2026-06-21-hgt-STEP11-covariance-range-strengthen.py`, `computations/2026-06-21-hgt-STEP11-covariance-range-strengthen.txt`. Rank-normalized beta still did not separate true; finite/random were larger in left-strip cases and true/finite collapsed at `σ=1.2`.
- Final verdict: DEAD END for non-reducing finding. Not posted to `#research`.

### Penrose R24 - Berry lane interference channel switch

- Random path: Rudner winding invariant -> Berry phases in molecular conical intersections -> tunneling splittings changed by constructive/destructive interference between equivalent nuclear paths.
- Constraint: equivalent paths require the geometric phase/boundary condition; a two-path splitting can flip sign under an odd Berry phase.
- HT transfer: sigma-lane path amplitudes at `1/2 +/- delta` around zero windows; odd channel `|L-R|`, no-Berry channel `|L+R|`.
- Finding: bare `zeta'/zeta` carries the odd-channel residual mainly as left/right lane-coherence magnitude imbalance, while completed `xi'/xi` exactly equalizes lane magnitudes at the critical-line center and moves the residual into relative phase. Gamma-only is balanced but phase-trivial; finite/random controls with gamma do not reproduce the switch.
- Status: non-reducing under corrected promptability gate; posted to `#research` pending.
- Archive: `computations/2026-06-21-penrose-r24-berry-lane-interference-summary.md`.

## Dyson — thermal/autocatalytic coupling [DEAD END]
- Seed RandomNode: `Noise-induced premature bursts`.
- STEP 1 rng#7 topic: `Explosive autocatalysis`.
- STEP 4 rng#2 NODE: `Heat release and concentration growth are coupled, so thermal runaway and chemical autocatalysis can amplify each other`.
- STEP 5 constraint: reaction rate raises heat, heat raises reaction rate, and cooling competes with this coupled positive feedback.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-thermal-autocatalytic-coupling.py`, output `computations/2026-06-21-hgt-NODE-thermal-autocatalytic-coupling.txt`. Coupled cases run away earlier when heat loss is low; uncoupled beta=0 does not satisfy the runaway criterion.
- STEP 7 formula check: thermal runaway/autocatalytic ODE formulas do not apply unchanged to HT functions; the minimal transfer uses phase reserve and amplitude heat along continuum `s`-traces.
- STEP 8 transfer attempts: selected `phase-release-and-amplitude-growth-are-coupled` by Levenshtein (`30`) over `zero-shadow-thermal-runaway` (`75`) and `prime-heat-autocatalytic-cutoff` (`90`). Script/output: `computations/2026-06-21-hgt-STEP8-thermal-autocat-coupling-ht.py`, `computations/2026-06-21-hgt-STEP8-thermal-autocat-coupling-ht.txt`.
- STEP 9 method rng#16: minimal counterexample. Shuffled heat reproduces or improves coupled runaway, so timing coupling is not necessary.
- STEP 11 method rng#12: invariant. Script/output: `computations/2026-06-21-hgt-STEP11-thermal-autocat-coupling-invariant.py`, `computations/2026-06-21-hgt-STEP11-thermal-autocat-coupling-invariant.txt`. True timing-coupling excess over circular heat shifts is negative in all true cases.
- Verdict: DEAD END for non-reducing finding. Not posted to `#research`.

Penrose R24 chat post: `#research` id `773`; count now `8/30`.

### 2026-06-21 -- Conway -- pre-clearing true interactors

- NODE: `Pre-clearing can remove true interactors as well as sticky contaminants`.
- Constraint tested: pre-clearing must preserve true bait interactors while reducing sticky contaminants.
- HT transfer: `pre clearing can remove true phase interactors as well as sticky amplitude contaminants`.
- Method: #13 find a monotone quantity; Step 11 method #23 classify boundary cases.
- Files: `computations/2026-06-21-conway-preclear-true-interactors.py`, `computations/2026-06-21-conway-preclear-true-interactors.txt`, `computations/2026-06-21-conway-STEP11-preclear-boundaries.py`, `computations/2026-06-21-conway-STEP11-preclear-boundaries.txt`.
- Verdict: dead end. Amplitude/sticky pre-clearing does not remove true HT phase-defect signal; signal loss occurs only for balance/opposition markers, which are tautological cancellation components.

## Dead end — 2026-06-21 — Phase Hurst-estimation bias

- RandomNode seed: `The difference between short-range associated fields and long-range dependent associated fields, which may have nonstandard limits`.
- STEP 2 topic: `Fractional Brownian motion and fractional Gaussian noise`.
- STEP 4 NODE: `Estimating H from finite data is highly sensitive to trends, nonstationarity, aggregation, and measurement noise`.
- NODE constraint tested: a fitted Hurst exponent is interpretable only after finite-window, trend/nonstationarity, aggregation, and measurement-noise gates are fixed.
- NODE output: `computations/2026-06-21-hgt-NODE-hurst-estimation-sensitivity.py`, `computations/2026-06-21-hgt-NODE-hurst-estimation-sensitivity.txt`. For true `H=0.7`, clean finite-sample median was `0.6489`; level shift `0.5428`; measurement noise `0.6193`; block aggregation `0.6043`; noise sweep drove median to `0.4992` at noise fraction `1.2`.
- STEP 7: fBm/fGn Hurst-estimation formulas do not apply unchanged to HT functions; no unchanged formula promoted.
- STEP 8 selected transfer by Levenshtein: `A_phase_hurst_estimation_bias` (`10/33=0.3030`).
- STEP 9 method `23` (`Classify boundary cases`). Script/output: `computations/2026-06-21-hgt-STEP8-hurst-phase-estimation.py`, `computations/2026-06-21-hgt-STEP8-hurst-phase-estimation.txt`. True left-strip H-like estimates exceed finite/random in some cases, but estimates are artifact-sensitive; aggregation collapses true and finite; right strip true/finite collapse.
- STEP 11 method `19` (`Write the fake proof`). Script/output: `computations/2026-06-21-hgt-STEP11-hurst-fake-proof.py`, `computations/2026-06-21-hgt-STEP11-hurst-fake-proof.txt`. Fake proof gap: clean/noisy/shift left-strip gaps fail under aggregation and disappear on the right side.
- Final verdict: DEAD END for non-reducing finding. Not posted to `#research`.

### Penrose R25 - phase-vortex temporal aliasing

- Random path: Berry tunneling splitting -> topological defects in soft matter -> missed creation/annihilation events under low temporal resolution.
- Transfer: phase-winding plaquette detector on `arg zeta(s)` over sigma-t grids at varying `dt`.
- Result: true zeros in `t in [100,124]` counted exactly for `dt <= .4`; undercount/spurious negative charges appear at `dt=.8/1.2`. Finite/random controls have no fine defects but fabricate coarse alias charges.
- Verdict: dead end / promptable. The correct statement is the expected sampling theorem for topological charge detection.

### Penrose R26 - weak-spot order-parameter suppression

- Random path: temporal defect aliasing -> phase-slip events in superconducting nanowires -> edge roughness/grain-boundary weak spots.
- Transfer: local `|zeta|` order-parameter suppression around small zero neighborhoods.
- Result: true weak spots center at critical-line zeros; finite/random controls localize minima on the artificial left boundary.
- Verdict: dead end / promptable. This is zero-core amplitude collapse versus Euler-boundary behavior, not a new HT invariant.

## Dyson -- excitable alternans before failure [DEAD END]
- Seed RandomNode: `Heat release and concentration growth are coupled, so thermal runaway and chemical autocatalysis can amplify each other`.
- STEP 1 topic: `Excitable media`; STEP 2 rng#17.
- STEP 4 NODE: `Alternans or period-doubling before overt propagation failure`; STEP 4 rng#10.
- STEP 5 constraint: a period-2/alternans pattern can appear before overt propagation block, so precursor behavior must be separated from complete failure.
- STEP 6 NODE test: `computations/2026-06-21-hgt-NODE-excitable-alternans.py`, output `computations/2026-06-21-hgt-NODE-excitable-alternans.txt`. The restitution toy model has parameter windows with `period2=1` and `failure=0`, validating the NODE constraint.
- STEP 7 formula check: excitable restitution and alternans formulas do not apply unchanged to HT functions; the minimal non-HT-blind transfer tests phase-defect alternation in continuum `s`-traces of `zeta'/zeta`.
- STEP 8 transfer attempts: selected `phase-alternans-before-propagation-failure` by Levenshtein (`6`) over `zero-shadow-period-doubling` (`32`) and `prime-cutoff-restitution-alternans` (`44`).
- STEP 9 method rng#16: minimal counterexample. Script/output: `computations/2026-06-21-hgt-STEP8-excitable-alternans-ht.py`, `computations/2026-06-21-hgt-STEP8-excitable-alternans-ht.txt`. True rows had negative excess even/odd alternans over shuffle in every tested case; the only positive excess was random-phase leakage with high failure.
- STEP 11 method rng#7: strip to essentials. Script/output: `computations/2026-06-21-hgt-STEP11-excitable-alternans-essentials.py`, `computations/2026-06-21-hgt-STEP11-excitable-alternans-essentials.txt`. Rank-stripped high/low true alternation stayed below shuffled order in every tested window.
- Verdict: DEAD END for non-reducing finding. Not posted to `#research`.

### 2026-06-21 -- Conway -- phase-defect mass is component-bound

- NODE: `Selective filtration loss of particle-bound analytes`.
- Constraint tested: filtered measurement is valid only if particle-bound analyte retained by the filter is negligible or accounted for.
- HT transfer: `selective filtration loss of phase particle bound analytes`.
- Method: #19 write the fake proof; Step 11 method #9 test small cases.
- Files: `computations/2026-06-21-conway-filtration-particle-bound.py`, `computations/2026-06-21-conway-filtration-particle-bound.txt`, `computations/2026-06-21-conway-STEP12-filtration-particle-battery.py`, `computations/2026-06-21-conway-STEP12-filtration-particle-battery.txt`, `computations/2026-06-21-conway-STEP12-filtration-particle-battery-dt020.txt`.
- Finding: true left-strip phase-defect mass is carried by short non-singleton continuum components. Fine physical-width filtration loses true signal while finite/random controls are mostly singleton-passable; width `1.25` recovers true signal in surviving rows. Physical-width battery survived `9/36` at `dt=0.25` and `12/36` at `dt=0.20`.

## THE-MACHINE tick -- Hawking -- redshift distortion / phase-space dimension

- STEP 1 seed: `Estimating H from finite data is highly sensitive to trends, nonstationarity, aggregation, and measurement noise`; cold Codex broad list; STEP 2 rng `14` -> `Galaxy clustering and fractal cosmology`.
- STEP 3 cold Codex narrow list; STEP 4 rng `6` -> NODE `Redshift-space distortions from peculiar velocities can stretch or compress structures and alter inferred clustering dimensions`.
- STEP 5 constraint: inferred clustering dimension in observed redshift coordinates is conditional on line-of-sight distortion modeling.
- STEP 6 NODE script/output: `computations/2026-06-21-hgt-NODE-redshift-distortion-dimension.py`, `computations/2026-06-21-hgt-NODE-redshift-distortion-dimension.txt`. NODE validated: the fixed real-space catalog had `D_hat=1.7114`; finger distortion at strength `0.42` gave `D_hat=2.0033`; mixed distortion at strength `0.42` gave `D_hat=1.5546`.
- STEP 7 formula check: redshift-space distortion mappings and clustering-dimension corrections do not apply unchanged to native HT continuum-differential content; no unchanged formula promoted.
- STEP 8 selected HT transfer by Levenshtein: `A_phase_space_distortion_dimension` (`20/40=0.5000`). Script/output: `computations/2026-06-21-hgt-STEP8-redshift-phase-distortion.py`, `computations/2026-06-21-hgt-STEP8-redshift-phase-distortion.txt`.
- STEP 9 rng `6` -> ask what action changes an object. Action: apply a robust phase-velocity shift of the imaginary coordinate before estimating the correlation dimension of high phase-defect event clouds.
- Result: DEAD END. True shifts were not HT-specific: largest true shift was about `-0.0517`, while randomized controls reached about `+0.0764`, and finite controls also moved. This is a coordinate/estimator artifact, not a non-reducing HT obstruction.
- Findings posted to `#research` remains: 7 / 30 for Hawking-tracked count.
- Next RandomNode: `Redshift-space distortions from peculiar velocities can stretch or compress structures and alter inferred clustering dimensions`.

## Penrose - Machine R27 - annealed/quenched D_infty period-boundary transfer `[FIND - non-reducing experimental observable, target-picked from consolidated docs]`

Seed RandomNode = `Edge roughness and grain boundaries can create local suppression of the order parameter` → Step 1 cold Codex broad list → rng#7 = `Quenched disorder in Ginzburg-Landau models` → Step 3 cold Codex narrow list → rng#1 = NODE `Distinction between annealed and quenched averaging`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#10 = `C-2026-06-18-001 (D_∞ period-domain): RH ⟺ F_ζ elliptic with period point in the interior of D_∞; off-line zero = hyperbolic/boundary direction`.

- NODE constraint: frozen disorder requires quenched scoring (`E log Z`) rather than annealed scoring (`log E Z`). A finite GL random-mass partition test validated the constraint: Jensen gap rose from `0.000000` at no disorder to `0.024007` at disorder `0.70` and `0.058353` at `1.10`.
- STEP 8 selected transfer by Levenshtein: `annealed_quenched_phase_partition_zeta_logderivative` (`19`).
- STEP 9 method rng#4 (`change viewpoint`): true phase-defect partition lane gaps exceeded finite/random in critical windows (`[100,170]`, beta `1.0`: true `0.278414`, finite max `0.187472`, random `0.033598`; `[500,570]`: true `0.404256`, finite max `0.308707`, random `0.208520`). Time-view gaps were not the same invariant.
- Target-specific period-proxy: completed `xi` had almost no annealed/quenched logdet gap (`0.000295`) and stable worst minimum (`0.716754`); `random_gamma` had large annealed masking (`gap=0.432769`, worst min `0.230870`).
- STEP 11 method rng#15 (`strengthen`): two-lane boundary score = normalized minimum eigenvalue. `xi` stayed quenched-stable interior (`0.309967`, worst `0.293114`); finite/random controls were near-boundary with masking (`finite_gamma` worst `0.004205`, `random_gamma` worst `0.005151`); synthetic strong off-line quartet lowered the completed score to `0.168687` without creating masking.
- STEP 12 battery over three zero groups and deltas `0.10/0.14/0.20`: `pass_sep=8/9`, `pass_gap=9/9`, `pass_offline=9/9`.
- Promptability audit: cold prompt predicted the generic Jensen line that annealed averaging hides off-line boundary and quenched exposes it. The actual computation split this: deterministic off-line quartets lower the boundary score directly but do not create annealed/quenched masking; masking is a disordered finite/random-carrier artifact.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` In this `D_∞` transfer, the completed carrier has a quenched-stable interior period-proxy score; finite/random gamma controls can look annealed-interior while containing quenched boundary samples; off-line boundary directions are detected by boundary-score lowering rather than by Jensen masking.
- Archive: `computations/2026-06-21-penrose-r27-period-annealed-quenched-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Distinction between annealed and quenched averaging`.

## Penrose - Machine R28 - Ito/Stratonovich weight-torus corank correction `[FIND - bounded non-reducing experimental observable, target-picked from consolidated docs]`

Seed RandomNode = `Distinction between annealed and quenched averaging` → Step 1 cold Codex broad list → rng#12 = `Stochastic resonance in nonlinear dynamics` → Step 3 cold Codex narrow list → rng#17 = NODE `The noise interpretation, Ito versus Stratonovich, can change results in systems with state-dependent noise`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#9 = `(G4) weight/Tate torus: dim W = corank`.

- NODE constraint: for state-dependent noise, the written stochastic differential is incomplete until the Ito/Stratonovich convention is fixed. NODE validation with `dX=μXdt+σXdW`: Ito mean log `-0.326797` (theory `-0.321250`) versus Stratonovich mean log `0.034682` (theory `0.040000`).
- STEP 8 selected transfer by Levenshtein: `ito_stratonovich_weight_torus_corank` (`19`).
- STEP 9 method rng#10 (`test extreme cases`): constant-noise control gave zero correction. True completed carrier had much larger Stratonovich-minus-Ito effective-rank correction than controls: `[100,170]`, `N=30`, true `+1.8593` vs finite `+0.2181` and random `+0.2323`; `N=100`, true `+2.2157` vs finite `+0.3876` and random `-0.0504`; `[500,570]`, `N=60`, true `+1.5671` vs finite `+0.0813` and random `+0.4519`.
- STEP 11 method rng#9 (`test small cases`): the effect is already present at `N=5` and grows with prime cutoff; one random-control leakage row occurred at `[500,570]`, `N=30`.
- STEP 12 sigma/shuffle battery at `N=80`: `total=12`, `pass_true=5`, `pass_shuffle=8`. Clean regime: sigma `.5` all three windows; sigma `.7` partial. Boundary: sigma `.3` weak and sigma `1.2` collapsed to controls.
- Promptability audit: cold prompt predicted the generic Ito-correction story. The non-reducing content is the bounded localization: correction is true-carrier/seam-local rather than generic nonconstant-noise behavior.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` For finite prime-weight torus carriers, the geometric/midpoint interpretation recovers extra effective rank on the true completed carrier near the seam, while finite/random controls usually do not and the Euler-convergent strip collapses. This is a finite observable warning for the `dim W=corank` face.
- Archive: `computations/2026-06-21-penrose-r28-ito-stratonovich-corank-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `The noise interpretation, Ito versus Stratonovich, can change results in systems with state-dependent noise`.

## Penrose - Machine R29 - Source-A/Source-B scalar covariance reaction rate `[DEAD END]`

Seed RandomNode = `The noise interpretation, Ito versus Stratonovich, can change results in systems with state-dependent noise` → Step 1 cold Codex broad list → rng#1 = `Noise-induced drift in biochemical reaction networks` → Step 3 cold Codex narrow list → rng#7 = NODE `Correlations between reactants can alter effective reaction rates`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#2 = `The two sources and the seam — the static skeleton`.

- NODE validation: correlated reactants with fixed means changed the effective rate `E[XY]` versus `E[X]E[Y]`: ratio `0.8195` at rho `-0.8`, `1.0003` at rho `0`, `1.2205` at rho `+0.8`.
- STEP 8 selected transfer by Levenshtein: `seam_cross_term_reaction_rate` (`23`).
- STEP 9 method rng#8 (`look for similar objects`): measured the scalar Source-A/Source-B cross term in `|G+P|^2` for true, finite, and random source-pair systems.
- Result: first-window sign structure appeared but did not survive. `[100,170]`, sigma `.3`: true covariance `-0.0154`, finite `+0.0031`; sigma `.5`: true `-0.0066`, finite `+0.0041`, random `-0.0072`. In `[500,570]` and `[900,970]`, all rows were near zero or control-comparable.
- Verdict: DEAD END for non-reducing finding. The scalar covariance-rate observable is too weak/unstable; no chat post.
- WALK STATE: STEP 1 reseed with RandomNode = `Correlations between reactants can alter effective reaction rates`.

## Penrose - Machine R30 - Jensen anti-collective margin ordering `[FIND - non-reducing experimental observable, target-picked from consolidated docs]`

Seed RandomNode = `Correlations between reactants can alter effective reaction rates` → Step 1 cold Codex broad list → rng#5 = `Noise-induced phase transitions` → Step 3 cold Codex narrow list → rng#4 = NODE `Spatial coupling can convert local noise-induced bistability into a genuine collective phase transition`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#16 = `Jensen TP-defect = 2κ₋`.

- NODE validation: coupled bistable lattice with fixed noise changed from `82` domains / nearest-neighbor sign correlation `-0.1714` at coupling `0` to `8` domains / correlation `0.8857` at coupling `0.90`.
- STEP 8 selected transfer by Levenshtein: `spatially_coupled_nonreal_jensen_roots` (`39`).
- STEP 9 method rng#9 (`test small cases`): built small cubic Jensen-section lattices from `J_3(X;t)` for `Ξ`, with coefficient perturbations amplified at low hyperbolicity margin. Actual `t`-ordered margins produced fewer non-real-root / TP defects than shuffled margins; examples: `nsites=48`, `eps=1.1`, `length=5`, true count `7.411`, shuffled `9.156`; `eps=1.3`, `length=8`, true `8.378`, shuffled `10.278`.
- STEP 11 method rng#13 (`find a monotone quantity`): suppression ratio `true_count/shuffled_count` stayed well below `1` across windows, sizes, eps, and coupling lengths. Mean ratios by length included `nsites=24, eps=.9`: `0.217,0.257,0.296,0.253`; `48, eps=1.1`: `0.307,0.282,0.307,0.274`; `48, eps=1.3`: `0.345,0.338,0.350,0.298`. Later windows were nearly protected in actual order while shuffled/sorted controls still created defects, e.g. `[80,155]`, `nsites=48`, `eps=1.3`, `length=8`: true `0.278`, shuffled `3.533`, sorted `4.333`.
- Promptability audit: cold prompt predicted the generic NODE direction that coupling/aggregation should sharpen local Jensen ambiguity into an even-valued collective TP defect. The computation found the reverse: natural `Ξ` Jensen margin order suppresses collective defect nucleation relative to shuffled/adversarial order.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` The `Ξ` Jensen hyperbolicity-margin landscape appears anti-collective under local noise-induced TP defects: spatial coupling that normally creates domains hits a margin-order firewall before the integer `2κ₋` phase nucleates.
- Archive: `computations/2026-06-21-penrose-r30-jensen-anti-collective-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Spatial coupling can convert local noise-induced bistability into a genuine collective phase transition`.

## Penrose - Machine R31 - weld log finite-size scaling `[DEAD END / overfit]`

Seed RandomNode = `Spatial coupling can convert local noise-induced bistability into a genuine collective phase transition` -> Step 1 cold Codex broad list -> rng#3 = `Directed percolation universality` -> Step 3 cold Codex narrow list -> rng#4 = NODE `The upper critical dimension is d_c = 4, so mean-field exponents acquire logarithmic corrections exactly at four spatial dimensions`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; first topic draw rng#27 was invalid for this file's 20 candidates, so redrew rng#4 = `native content is the archimedean-prime weld, not Source A or Source B alone`.

- NODE constraint: at an upper critical dimension, power-law finite-size scaling is incomplete unless the logarithmic correction is included.
- STEP 6 NODE validation: synthetic `Y=L^{-a}(log L)^p` with `p=.8` improved RMSE from `0.03673` to `0.01909`; fitted log coefficient `1.228`.
- STEP 8 selected transfer by Levenshtein: `weld_block_scaling_log_correction` (`21`).
- STEP 9 method rng#22 (`compare nearby false statements`): tested power-only vs power+log block-variance scaling for Source A, Source B, sum, true weld, finite weld, and random weld.
- Result: sigma `.5` gains were sourceA `0.354`, sourceB `0.215`, sum `0.267`, weld `0.506`, finite_weld `0.544`, random_weld `0.508`; sigma `1.2` gains were sourceA `0.354`, sourceB `0.490`, sum `0.424`, weld `0.285`, finite_weld `0.225`, random_weld `0.213`.
- Verdict: DEAD END. The log correction is not weld-specific here; six block scales make the improvement too generic and control-comparable.
- Script: `computations/2026-06-21-penrose-r31-weld-log-scaling.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `The upper critical dimension is d_c = 4, so mean-field exponents acquire logarithmic corrections exactly at four spatial dimensions`.

## Penrose - Machine R32 - Fisher pre-asymptotic cutoff wall `[DEAD END / reduce-to-known]`

Seed RandomNode = `The upper critical dimension is d_c = 4, so mean-field exponents acquire logarithmic corrections exactly at four spatial dimensions` -> Step 1 cold Codex broad list -> rng#2 = `Directed percolation with logarithmic scaling corrections` -> Step 3 cold Codex narrow list -> rng#7 = NODE `Corrections are often pre-asymptotic for very long times, making clean log scaling hard to observe numerically`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#17 = `Fisher signature wall`.

- NODE constraint: a logarithmic correction is not certified by a single low-residual power-log fit; it must survive nested-window and holdout stability gates.
- STEP 6 NODE validation: a no-log slow crossover produced low RMSE but drifting fitted log exponent (`beta` about `-0.0610` to `-1.9160` across windows).
- STEP 8 selected transfer by Levenshtein: `preasymptotic_log_correction_fisher_wall_gate` (`9`).
- STEP 9 method rng#20 (`name the missing lemma`): finite Fisher cutoffs `g_X=Var_{n<=X}(log n)` resolve the pole only when `u=(2 sigma-1) log X` is large. Normalized ratios `g_X delta^2` collapse to the truncated-exponential variance in `u`.
- STEP 11 method rng#4 (`change viewpoint`): apparent fronts `g_X delta^2=q` satisfy almost constant `delta_q log X`; for `q=0.5`, the values were `2.865795, 2.863975, 2.868879, 2.875587, 2.882467` for `X=200..51200`.
- Verdict: DEAD END. This is the expected finite cutoff asymptotic of the already-known Fisher signature wall, so it reduces to known truncated-zeta analysis.
- Scripts: `computations/2026-06-21-penrose-r32-node-preasymptotic-log-corrections.py`, `computations/2026-06-21-penrose-r32-fisher-preasymptotic-log-gate.py`, `computations/2026-06-21-penrose-r32-step11-fisher-moving-wall.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `Corrections are often pre-asymptotic for very long times, making clean log scaling hard to observe numerically`.

## Penrose - Machine R33 - G-C10 Griffiths two-boundary finite-gate test `[DEAD END / universal local factor]`

Seed RandomNode = `Corrections are often pre-asymptotic for very long times, making clean log scaling hard to observe numerically` -> Step 1 cold Codex broad list -> rng#8 = `Griffiths phases in disordered systems` -> Step 3 cold Codex narrow list -> rng#9 = NODE `The Griffiths region is bounded by the clean critical point and the disordered critical point, not just by the observed transition temperature`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#24 = `G-C10. Source-built faithful-index object`.

- NODE constraint: a Griffiths interval has two boundaries; observed global transition alone misses rare regions.
- STEP 6 NODE validation: rare-region toy model had clean bound `1.00`, observed global bound about `1.48`, and active rare islands with broad lifetimes in between.
- STEP 8 selected transfer by Levenshtein: `two_boundary_source_built_faithful_index_gate` (`32`, tie by list order).
- STEP 9 method rng#15 (`strengthen`): synthetic off-line quartets triggered one local cubic-Jensen defect at `a=0.025` and above around `gamma=18,37,62`, while true and smooth zero-free controls had zero defects; no global finite-gate transition occurred.
- STEP 11 method rng#7 (`strip to essentials`): the local island persisted on flat and exponential backgrounds, with fake negative offsets around `|t-gamma| <= 0.5a` and no smooth-control leaks.
- Verdict: DEAD END. The two-boundary warning is useful, but the observed local defect is the universal off-real quartet signature, not a native source-built Xi/G-C10 invariant.
- Scripts: `computations/2026-06-21-penrose-r33-node-griffiths-two-boundaries.py`, `computations/2026-06-21-penrose-r33-source-built-griffiths-index.py`, `computations/2026-06-21-penrose-r33-step11-strip-essential-island.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `The Griffiths region is bounded by the clean critical point and the disordered critical point, not just by the observed transition temperature`.

## Penrose - Machine R34 - state-law abscissa passport `[FIND - bridge-candidate, target-picked from consolidated docs]`

Seed RandomNode = `The Griffiths region is bounded by the clean critical point and the disordered critical point, not just by the observed transition temperature` -> Step 1 cold Codex broad list -> rng#13 = `Spin-glass analogies in neural population dynamics` -> Step 3 cold Codex narrow list -> rng#3 = NODE `Neural states are rarely binary spins; firing rates, spike timing, bursting, adaptation, and latent circuit variables all change the mapping`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#15 = `Abscissa of a.s. convergence`.

- NODE constraint: state representation is load-bearing; binary spikes, smoothed rates, timing variables, and adaptation variables gave different inferred neural frustration/dimensionality.
- STEP 8 selected transfer by Levenshtein: `binary_spin_prime_phase_threshold` (`31`).
- STEP 9 method rng#5 (`make visual`): U(1) phase log encoding had zero mean and a `1/2` variance wall; Rademacher/binary log encoding kept the `1/2` variance wall but added even-power drift at the seam; positive rate states added a `sigma=1` mean wall.
- STEP 11 method rng#7 (`strip to essentials`): moment-spectrum passport. If `k0 = min{k>0 : E[X^k] != 0}`, the full log Euler mean wall is `sigma=1/k0`, centered fluctuations keep wall `1/2`, so the total state-law wall is `max(1/2, 1/k0)`.
- STEP 12 battery: roots `q=2..8`, Bernoulli positive rates, and centered real laws matched the rule.
- Status: `[EXPERIMENTAL FINDING / BRIDGE-CANDIDATE]` The critical-line abscissa theorem contains a state-law hypothesis: `1/2` is robust for centered variance, but source-pure random Euler interpretation needs phase moment cancellation; binary signs are seam-contaminating, and `q>=3` phase laws keep drift below the variance wall.
- Archive: `computations/2026-06-21-penrose-r34-state-law-abscissa-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Neural states are rarely binary spins; firing rates, spike timing, bursting, adaptation, and latent circuit variables all change the mapping`.

## Penrose - Machine R35 - Parisi function to sigma-orbit profile `[DEAD END / already theorem]`

Seed RandomNode = `Neural states are rarely binary spins; firing rates, spike timing, bursting, adaptation, and latent circuit variables all change the mapping` -> Step 1 cold Codex broad list -> rng#16 = `Spin glass mean-field theory` -> Step 3 cold Codex narrow list -> rng#3 = NODE `The Parisi order parameter is a full function q(x), not a single Edwards-Anderson parameter`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng#8 = `two-sources-of-hypertranscendence.md gives the Source A/B classifier by sigma-orbit balance`.

- NODE constraint: a functional order parameter cannot be collapsed to a scalar endpoint.
- STEP 6 NODE validation: profiles with the same `q_EA` endpoint had different hierarchy, mean, variance, and slope data.
- STEP 8 selected transfer by Levenshtein: `full_sigma_orbit_balance_function` (`33`).
- STEP 9 method rng#20 (`name the missing lemma`): scalar divisor degree zero is not orbit balance; the needed object is the full orbit-degree profile.
- STEP 11 method rng#18 (`look for the right theorem`): the right theorem is exactly the existing finite orbit-balance / augmentation-kernel theorem.
- Verdict: DEAD END. Correct analogy, but reduce-to-known because the target theorem already states the per-orbit profile criterion.
- Scripts: `computations/2026-06-21-penrose-r35-node-parisi-function.py`, `computations/2026-06-21-penrose-r35-orbit-profile-parisi-transfer.py`, `computations/2026-06-21-penrose-r35-step11-right-theorem.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `The Parisi order parameter is a full function q(x), not a single Edwards-Anderson parameter`.

## Penrose - Machine R36 - curvature filter localization axis `[FIND - bounded, target-picked from consolidated docs]`

Seed RandomNode = `The Parisi order parameter is a full function q(x), not a single Edwards-Anderson parameter` -> Step 1 cold Codex broad list -> rng#7 = `Stochastic resonance in disordered biochemical signaling` -> Step 3 cold Codex narrow list -> rng#12 = NODE `Downstream filtering can erase resonance visible at upstream signaling nodes`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#23 = `positivity/localization axis`.

- NODE constraint: downstream filtering can suppress a resonance visible upstream.
- STEP 8 selected transfer by Levenshtein: `downstream_filter_offline_curvature_axis` (`20`).
- STEP 9 method rng#21 (`build a dependency chain`): off-line quartet curvature `C_a(tau)=2(a^2-tau^2)/(a^2+tau^2)^2` is a positive core with negative wings and zero whole-line signed area. Broad Gaussian filters erased the core: peak ratio `0.015929` at width `8a`, `0.046795` at `4a`, `0.140455` at `2a`, independent of tested `a`.
- STEP 11 method rng#3 (`reverse`): a centered sign-changing matched filter recovered the off-line core while a purely negative on-line model remained negative at the center.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` The positivity/localization axis is a matched-localization problem. Broad weld/constraint readouts can cancel off-line curvature; faithful RH detectors must preserve the local sign-changing core/wing profile.
- Archive: `computations/2026-06-21-penrose-r36-curvature-filter-localization-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Downstream filtering can erase resonance visible at upstream signaling nodes`.

## Penrose - Machine R37 - optimal localization width for off-line curvature `[FIND - bounded, target-picked from consolidated docs]`

Seed RandomNode = `Downstream filtering can erase resonance visible at upstream signaling nodes` -> Step 1 cold Codex broad list -> rng#2 = `Stochastic resonance in weak-signal detection` -> Step 3 cold Codex narrow list -> rng#1 = NODE `The noise level that improves detection is usually a narrow optimum, not more noise is better`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#23 = `positivity/localization axis`.

- NODE constraint: useful noise/filtering has a matched optimum; more is not better.
- STEP 8 selected transfer by Levenshtein: `narrow_optimal_smoothing_localization_axis` (`21`).
- STEP 9 method rng#3 (`reverse`): for noisy measurements of the off-line quartet curvature kernel, Gaussian localization z-score peaked at width `0.50a` and declined on both sides.
- STEP 11 method rng#13 (`find a monotone quantity`): across tested quartet scales and noise levels, every sampled curve was unimodal with peak `width/a=0.50`.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` The positivity/localization axis has a scale passport: for off-line half-width `a=|beta-1/2|`, this Gaussian detector is optimized near width `a/2`; broader filters wash the core into wings, narrower filters waste SNR.
- Archive: `computations/2026-06-21-penrose-r37-localization-optimal-width-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `The noise level that improves detection is usually a narrow optimum, not more noise is better`.

## Penrose - Machine R38 - G-C15 route covariance under independent filtering `[DEAD END / synthetic]`

Seed RandomNode = `The noise level that improves detection is usually a narrow optimum, not more noise is better` -> Step 1 cold Codex broad list -> rng#17 = `Financial market microstructure noise filtering` -> Step 3 cold Codex narrow list -> rng#18 = NODE `Filtering one asset independently can destroy economically meaningful cross-asset covariance`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#26 = `G-C15. One object, two entrances`.

- NODE constraint: independent filtering can destroy covariance from a common source.
- STEP 8 selected transfer by Levenshtein: `independent_route_filtering_destroys_gc15_covariance` (`17`).
- STEP 9 method rng#13 (`find a monotone quantity`): synthetic Jacobi/Jensen route proxies decorrelated monotonically as their filter scales diverged.
- STEP 11 method rng#17 (`change representation`): a two-scale correlation surface recovered a high-correlation ridge.
- Verdict: DEAD END. Useful G-C15 test-design warning, but synthetic and directly promptable from the NODE; no non-reducing finding.
- Scripts: `computations/2026-06-21-penrose-r38-node-cross-asset-filtering.py`, `computations/2026-06-21-penrose-r38-gc15-route-covariance.py`, `computations/2026-06-21-penrose-r38-step11-scale-correlation-surface.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `Filtering one asset independently can destroy economically meaningful cross-asset covariance`.

## Penrose - Machine R39 - faithful-index dust as global coherence `[DEAD END / already target warning]`

Seed RandomNode = `Filtering one asset independently can destroy economically meaningful cross-asset covariance` -> Step 1 cold Codex broad list -> rng#13 = `Decoherence analogies in entangled quantum subsystems` -> Step 3 cold Codex narrow list -> rng#5 = NODE `Global coherence can remain even when subsystems appear decohered`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#29 = `G-C18. Faithful-index rigidity`.

- NODE constraint: local reductions can appear decohered while global coherence remains.
- STEP 8 selected transfer by Levenshtein: `global_negative_direction_local_trace_blind` (`31`).
- STEP 9 method rng#10 (`test extreme cases`): a single arbitrarily tiny negative eigenvalue keeps faithful negative index `1` while trace/random probes look controlled.
- STEP 11 method rng#5 (`make visual`): the faithful index is a one-pixel global sign in the spectrum.
- Verdict: DEAD END. This reproduces the target's dust-perturbation warning directly; no non-reducing finding.
- Scripts: `computations/2026-06-21-penrose-r39-node-global-coherence.py`, `computations/2026-06-21-penrose-r39-faithful-index-dust.py`, `computations/2026-06-21-penrose-r39-step11-index-dust-visual.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `Global coherence can remain even when subsystems appear decohered`.

## Penrose - Machine R40 - finite source-map sampling `[DEAD END / documentation saturation]`

Seed RandomNode = `Global coherence can remain even when subsystems appear decohered` -> Step 1 cold Codex broad list -> rng#17 = `Hyperuniformity` -> Step 3 cold Codex narrow list -> rng#5 = NODE `Finite-size samples can mimic hyperuniformity because the smallest accessible k values are sparse and noisy`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#25 = source-map entry for `2-fully-proven/` support cards.

- NODE constraint: sparse finite diagnostics can falsely mimic global structure.
- STEP 8 selected transfer by Levenshtein: `finite_source_map_sample_false_axis_coverage` (`27`).
- STEP 9 method rng#2 (`attack as false`): small samples of fully-proven cards appeared to cover coarse axes at high rates.
- STEP 11 method rng#7 (`strip to essentials`): the effect was keyword saturation across the cards, not a mathematical invariant.
- Verdict: DEAD END. Documentation audit only.
- Scripts: `computations/2026-06-21-penrose-r40-node-finite-hyperuniformity.py`, `computations/2026-06-21-penrose-r40-source-map-finite-sampling.py`, `computations/2026-06-21-penrose-r40-step11-axis-saturation.py`.
- WALK STATE: STEP 1 reseed with RandomNode = `Finite-size samples can mimic hyperuniformity because the smallest accessible k values are sparse and noisy`.

## Penrose - Machine R41 - FID Hankel thin-cone volume bottleneck `[FIND - bounded, target-picked from consolidated docs]`

Seed RandomNode = `Finite-size samples can mimic hyperuniformity because the smallest accessible k values are sparse and noisy` -> Step 1 cold Codex broad list -> rng#14 = `Determinantal point processes` -> Step 3 cold Codex narrow list -> rng#9 = NODE `The determinant gives squared volume, so near-linear dependence among selected feature vectors strongly suppresses joint probability`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#18 = `C-2026-06-18-044 (FID)`.

- NODE constraint: determinant positivity is a squared-volume test and is fragile under near-linear dependence.
- STEP 8 selected transfer by Levenshtein: `fid_hankel_volume_near_dependence` (`23`).
- STEP 9 method rng#13 (`find a monotone quantity`): for `kappa_n=zeta(2n+1)`, Hankel determinant volume collapsed from log10 det `-0.8637` at size 2 to `-45.3230` at size 7; double precision lost sign at size 8. Downward `kappa_3` perturbation thresholds for PSD failure shrank from `7.078e-4` at size 3 to `2.100e-7` at size 6.
- STEP 11 method rng#14 (`weaken`): removing the rank-one all-ones bulk left the projected tail highly ill-conditioned, reaching condition `2.45e15` at size 7.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` FID positivity for this cumulant proxy lives in an extremely thin near-rank-one cone; raw Hankel determinant tests are a volume bottleneck, so any FID-to-RH bridge needs a tail-stable certificate.
- Archive: `computations/2026-06-21-penrose-r41-fid-thin-cone-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `The determinant gives squared volume, so near-linear dependence among selected feature vectors strongly suppresses joint probability`.

## Penrose - Machine R42 - affine ax+b volume passport `[FIND - bounded gatekeeper, target-picked from consolidated docs]`

Seed RandomNode = `The determinant gives squared volume, so near-linear dependence among selected feature vectors strongly suppresses joint probability` -> Step 1 cold Codex broad list -> rng#7 = `Lyapunov spectrum volume contraction in chaotic attractors` -> Step 3 cold Codex narrow list -> rng#2 = NODE `Volume contraction is given by the sum of Lyapunov exponents over the relevant tangent subspace`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#3 = affine `ax+b` geometry and universal curvature.

- NODE constraint: summed exponent / tangent-volume observables see only determinant-line contraction.
- STEP 8 selected transfer by Levenshtein: `affine determinant loop = universal curvature area times dim(S)` (`62`).
- STEP 9 method rng#17 (`change representation`): finite boundary-mode blocks satisfy `tr(partial_s|S)=-sum_{m in S}m.log p` and `det(sigma_p|S)=p^{-sum_{m in S}m_p}`.
- STEP 11 method rng#12 (`invariant`): the determinant passport `Pi(S)=(|S|,sum_S m)` has large fibers with identical trace and different internal shape; finite search reached `max_fiber=1471` for `k=5` with trace spread `3.553e-15`.
- Status: `[GATEKEEPER FINDING]` Affine determinant-volume evidence is RH/holonomy blind until the passport is reported and subtracted; meaningful seam tests must use trace-free fiber/holonomy data.
- Archive: `computations/2026-06-21-penrose-r42-axb-volume-passport-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Volume contraction is given by the sum of Lyapunov exponents over the relevant tangent subspace`.

## Penrose - Machine R43 - prime kinetic temperature failure `[DEAD END / phase-carrier restatement]`

Seed RandomNode = `Volume contraction is given by the sum of Lyapunov exponents over the relevant tangent subspace` -> Step 1 cold Codex broad list -> rng#15 = `Thermostatted dynamical systems` -> Step 3 cold Codex narrow list -> rng#13 = NODE `Temperature definitions based only on kinetic energy can fail for constrained, driven, or small systems`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng#11 = `universal-prime-side-orthogonality`.

- NODE constraint: a scalar kinetic reading can fail when hidden constraint/thermostat variables matter.
- STEP 8 selected transfer by Levenshtein: `prime-only kinetic temperature fails without archimedean thermostat` (`68`).
- STEP 9 method rng#19 (`fake proof`): the proof that prime energy determines completed energy fails by the exact identity `|A+P|^2-|P|^2=|A|^2+2Re(A conj(P))`.
- STEP 11 method rng#9 (`small cases`): low-height windows still show matched-kinetic but different completed-energy pairs.
- Verdict: DEAD END. Useful instrument warning, but it reduces to the existing phase-carrier/completion-equalization mechanism.
- Archive: `computations/2026-06-21-penrose-r43-prime-kinetic-temperature-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Temperature definitions based only on kinetic energy can fail for constrained, driven, or small systems`.

## Penrose - Machine R44 - finite-system temperature ambiguity at the Fisher wall `[DEAD END / finite regularization]`

Seed RandomNode = `Temperature definitions based only on kinetic energy can fail for constrained, driven, or small systems` -> Step 1 cold Codex broad list -> rng#8 = `Thermodynamics of small systems` -> Step 3 cold Codex narrow list -> rng#2 = NODE `Temperature is not always a sharply defined state variable for a small nonequilibrium system`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#17 = Fisher signature wall.

- NODE constraint: finite/small-system temperature can depend on reservoir definition.
- STEP 8 selected transfer by Levenshtein tie: `raw finite norm cannot see the zeta signature wall` and `small cutoff Fisher wall is a renormalization-choice ambiguity` (`70`).
- STEP 9 method rng#11 (`experiments`): raw finite norms stay positive; reservoir-subtracted norms recover the sign of `zeta(2sigma)`.
- STEP 11 method rng#12 (`invariant`): raw finite sign is invariantly positive; analytic sign requires subtraction.
- Verdict: DEAD END. Finite regularization warning only; overlaps R32.
- Archive: `computations/2026-06-21-penrose-r44-fisher-small-system-temperature-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Temperature is not always a sharply defined state variable for a small nonequilibrium system`.

## Penrose - Machine R45 - beta-conditioned layer correlation `[FIND - bounded, target-picked from consolidated docs]`

Seed RandomNode = `Temperature is not always a sharply defined state variable for a small nonequilibrium system` -> Step 1 cold Codex broad list -> rng#10 = `Superstatistics and fluctuating inverse temperature` -> Step 3 cold Codex narrow list -> rng#18 = NODE `Correlations between beta and dynamical variables can invalidate simple mixture models`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#10 = the layers of the landscape.

- NODE constraint: a scalar beta mixture fails when beta correlates with dynamics.
- STEP 8 selected transfer by Levenshtein: `beta-conditioned scalar layer fails to decouple phase-weld lanes` (`62`).
- STEP 9 method rng#20 (`missing lemma`): the false missing lemma is that conditioning on scalar `beta=log(1+|P|)` decouples phase-weld `Delta` from sigma lanes.
- STEP 11 method rng#17 (`change representation`): beta-bin x lane interaction residual RMS was true `0.192100` versus phase-random controls mean `0.092640`, max `0.157454`.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE]` The scalar layer is not an independent superstatistical mixing coordinate; the completed landscape needs beta-dynamics/layer-correlation data.
- Archive: `computations/2026-06-21-penrose-r45-beta-layer-correlation-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Correlations between beta and dynamical variables can invalidate simple mixture models`.

## Penrose - Machine R46 - Q3 factorization toy `[DEAD END / generic separator only]`

Seed RandomNode = `Correlations between beta and dynamical variables can invalidate simple mixture models` -> Step 1 cold Codex broad list -> rng#12 = `Non-Markovian renewal processes with coupled waiting times` -> Step 3 cold Codex narrow list -> rng#4 = NODE `Coupled waiting times can break the usual factorization of multi-time probabilities used in standard renewal calculations`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#14 = `C-2026-06-18-018 (Q_3 / higher-Chowla)`.

- NODE constraint: pairwise/factorized multi-time data can miss joint coupling.
- STEP 8 selected transfer by Levenshtein: `waiting-time coupling maps to a third cumulant fake separator` (`54`).
- STEP 9 method rng#1 (`split subclaims`): Q3 fake separation and Q3-to-`kappa_-` faithful readout are distinct.
- STEP 11 method rng#14 (`weaken`): parity toy supports only fake separation; singles/pairs match independent signs while the triple moment is `1`.
- Verdict: DEAD END. Generic Q3 motivation only; no source-built Q3 formula or faithful-index readout.
- Archive: `computations/2026-06-21-penrose-r46-q3-factorization-toy-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Coupled waiting times can break the usual factorization of multi-time probabilities used in standard renewal calculations`.

## Penrose - Machine R47 - sharp explicit-formula cutoff instability `[DEAD END / standard smoothing warning]`

Seed RandomNode = `Coupled waiting times can break the usual factorization of multi-time probabilities used in standard renewal calculations` -> Step 1 cold Codex broad list -> rng#7 = `Non-Poissonian event statistics` -> Step 3 cold Codex narrow list -> rng#3 = NODE `Heavy-tailed waiting times can make sample means unstable and convergence painfully slow, even when the dataset looks large`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng#5 = explicit formula as constraint.

- NODE constraint: large sharp samples can remain unstable; averages need the right estimator.
- STEP 8 selected transfer by Levenshtein: `smoothed zero sums are the constraint-safe estimator` (`71`).
- STEP 9 method rng#22 (`nearby false statements`): sharp zero cutoff pointwise estimates did not stabilize; `x=10000` error moved from `+3.15` at `N=150` to `+7.50` at `N=200`.
- STEP 11 method rng#5 (`make visual`): cutoff-error trajectory wanders.
- Verdict: DEAD END. Classical explicit-formula smoothing/distribution warning only.
- Archive: `computations/2026-06-21-penrose-r47-explicit-formula-cutoff-instability-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Heavy-tailed waiting times can make sample means unstable and convergence painfully slow, even when the dataset looks large`.

## Penrose - Machine R48 - prime-shift aggregation artifact `[DEAD END / PNT substrate]`

Seed RandomNode = `Heavy-tailed waiting times can make sample means unstable and convergence painfully slow, even when the dataset looks large` -> Step 1 cold Codex broad list -> rng#14 = `Human dynamics and bursty activity patterns` -> Step 3 cold Codex narrow list -> rng#5 = NODE `Aggregating heterogeneous individuals can create apparent power laws even when no individual follows one`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#5 = `G_a` prime shifts.

- NODE constraint: heterogeneous-rate aggregation can create apparent power laws.
- STEP 8 selected transfer by Levenshtein: `G_a heterogeneity manufactures apparent continuum scaling` (`69`).
- STEP 9 method rng#5 (`make visual`): aggregate prime-shift pole-scaling emerged from many small exponential lanes.
- STEP 11 method rng#19 (`fake proof`): aggregate pole does not imply individual prime-lane power-law/RH content; PNT aggregation is the gap.
- Verdict: DEAD END. Standard `G_a`/PNT substrate behavior only.
- Archive: `computations/2026-06-21-penrose-r48-prime-shift-aggregation-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Aggregating heterogeneous individuals can create apparent power laws even when no individual follows one`.

## Penrose - Machine R49 - layer frailty shrinkage `[DEAD END / instrumentation warning]`

Seed RandomNode = `Aggregating heterogeneous individuals can create apparent power laws even when no individual follows one` -> Step 1 cold Codex broad list -> rng#9 = `Frailty models in survival analysis` -> Step 3 cold Codex narrow list -> rng#10 = NODE `Frailty estimates can shrink strongly toward the population mean, especially in small clusters`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng#12 = layers of the landscape.

- NODE constraint: small clusters shrink empirical effects toward the population mean.
- STEP 8 selected transfer by Levenshtein: `small lane-cluster phase estimates shrink toward landscape mean` (`69`).
- STEP 9 method rng#5 (`make visual`): raw phase-weld lane spread `0.607189` attenuated to `0.362002` under shrinkage.
- STEP 11 method rng#10 (`test extreme cases`): `n=1` cell case degenerates because within-cell variance is unidentifiable; larger cells show expected attenuation.
- Verdict: DEAD END. Instrumentation warning only; no non-reducing layer invariant.
- Archive: `computations/2026-06-21-penrose-r49-layer-frailty-shrinkage-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Frailty estimates can shrink strongly toward the population mean, especially in small clusters`.

## Penrose - Machine R50 - Fisher array exchangeability warning `[DEAD END / product-sum substrate]`

Seed RandomNode = `Frailty estimates can shrink strongly toward the population mean, especially in small clusters` -> Step 1 cold Codex broad list -> rng#18 = `Exchangeability in de Finetti-style probability models` -> Step 3 cold Codex narrow list -> rng#12 = NODE `Arrays and networks need Aldous-Hoover-style analogues, not ordinary sequence de Finetti alone`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#17 = Fisher signature wall.

- NODE constraint: array/network exchangeability needs row/column latent structure, not sequence symmetry alone.
- STEP 8 selected transfer by Levenshtein: `array exchangeability changes the prime Fisher diagnostic` (`60`).
- STEP 9 method rng#11 (`experiments`): shared-prime row interaction grows unlike sequence Fisher norm, but independent-edge norm adds no new wall.
- STEP 11 method rng#21 (`dependency chain`): row interaction reduces to `sum p^-sigma` and `sum p^-2sigma` product algebra.
- Verdict: DEAD END. Product-sum/PNT substrate warning only.
- Archive: `computations/2026-06-21-penrose-r50-fisher-array-exchangeability-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Arrays and networks need Aldous-Hoover-style analogues, not ordinary sequence de Finetti alone`.

## Penrose - Machine R51 - finite-place inbreeding and seam firewall `[DEAD END / existing no-go confirmation]`

Seed RandomNode = `Arrays and networks need Aldous-Hoover-style analogues, not ordinary sequence de Finetti alone` -> Step 1 cold Codex broad list -> rng#7 = `Relational population genetics` -> Step 3 cold Codex narrow list -> rng#4 = NODE `Inbreeding changes expected genotype-pair distributions`.

Standing-order target pick: file rng#3 = `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng#10 = seam-firewall.

- NODE constraint: shared ancestry changes pair distributions.
- STEP 8 selected transfer by Levenshtein: `finite-place inbreeding changes prime-pair law but not seam positivity` (`45`).
- STEP 9 method rng#23 (`classify boundary cases`): finite prime phase block dependence did not force seam positivity.
- STEP 11 method rng#15 (`strengthen`): fully shared finite phase still gave negative/small center excess.
- Verdict: DEAD END. Existing seam-firewall no-go confirmed; no non-reducing finding.
- Archive: `computations/2026-06-21-penrose-r51-seam-finite-inbreeding-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Inbreeding changes expected genotype-pair distributions`.

## Penrose - Machine R52 - curvature deconfounds affine drift `[DEAD END / local theorem]`

Seed RandomNode = `Inbreeding changes expected genotype-pair distributions` -> Step 1 cold Codex broad list -> rng#2 = `Wright-Fisher diffusion with assortative constraints` -> Step 3 cold Codex narrow list -> rng#19 = NODE `Selection and assortment can be statistically confounded in inferred drift terms`.

Standing-order target pick: file rng#2 = `docs/consolidated/01-landscape-and-geometry.md`; topic rng#12 = RH/on-line curvature statement under where zeros live.

- NODE constraint: first-order drift can confound distinct causes.
- STEP 8 selected transfer by Levenshtein: `curvature deconfounds off-line source from affine drift` (`60`).
- STEP 9 method rng#9 (`small cases`): affine drift moves slopes but not curvature sign; on-line center curvature negative, off-line quartet core positive.
- STEP 11 method rng#18 (`right theorem`): this is exactly the existing local curvature theorem shape.
- Verdict: DEAD END. Reduce-to-known local theorem.
- Archive: `computations/2026-06-21-penrose-r52-curvature-deconfounds-drift-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Selection and assortment can be statistically confounded in inferred drift terms`.

## Penrose - Machine R53 - surrogate-ladder discretization sensitivity `[DEAD END / instrumentation requirement]`

Seed RandomNode = `Selection and assortment can be statistically confounded in inferred drift terms` -> Step 1 cold Codex broad list -> rng#7 = `Noise-induced transport in Brownian ratchets` -> Step 3 cold Codex narrow list -> rng#8 = NODE `Sensitivity to discretization of stochastic differential equations`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#20 = source map / surrogate-ladder open action.

- NODE constraint: inferred transport can depend on discretization.
- STEP 8 selected transfer by Levenshtein: `discretization changes inferred native carrier verdict` (`47`).
- STEP 9 method rng#9 (`small cases`): transition-lane true-vs-finite phase-weld margins can flip under grid offset/resolution.
- STEP 11 method rng#20 (`missing lemma`): surrogate-ladder discriminators need grid-stability certificates.
- Verdict: DEAD END. Instrumentation requirement only.
- Archive: `computations/2026-06-21-penrose-r53-surrogate-discretization-sensitivity-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Sensitivity to discretization of stochastic differential equations`.

## Penrose - Machine R54 - Schur fragment noise `[DEAD END / generic boundary instability]`

Seed RandomNode = `Sensitivity to discretization of stochastic differential equations` -> Step 1 cold Codex broad list -> rng#14 = `Cosmological N-body simulation discreteness noise` -> Step 3 cold Codex narrow list -> rng#6 = NODE `Warm dark matter simulations often form artificial filament fragments from discreteness noise`.

Standing-order target pick: file rng#1 = `docs/consolidated/08-conjectures-required.md`; topic rng#30 = G-C19 primitive Schur/Hodge equivalence.

- NODE constraint: discrete artifacts can masquerade as meaningful cutoff-scale structures.
- STEP 8 selected transfer by Levenshtein: `near-boundary Schur roots fragment under discreteness noise` (`56`).
- STEP 9 method rng#14 (`weaken`): tested finite Schur-count sensitivity only.
- STEP 11 method rng#11 (`experiments`): `z^36-1` plus tiny coefficient noise had inside-disk counts ranging `14..22`.
- Verdict: DEAD END. Generic Schur boundary instability, no Hodge comparison.
- Archive: `computations/2026-06-21-penrose-r54-schur-fragment-noise-summary.md`.
- WALK STATE: STEP 1 reseed with RandomNode = `Warm dark matter simulations often form artificial filament fragments from discreteness noise`.

## Penrose R55 - spinodal-core warning for DSS-cross `[DEAD END / existing gatekeeper]`

- NODE: `The unstable composition range lies inside the spinodal, not merely inside the miscibility gap`.
- Target: `DSS-cross (3b)` from `docs/consolidated/08-conjectures-required.md`.
- Transfer tested: period/non-period plausibility or PSLQ-null evidence is the broad miscibility gap; the true DSS-cross instability core would be an actual algebraic relation / corank collapse.
- Computation: symmetric double-well source check gave spinodal/miscibility length ratio `0.577350`; height-12 relation probes gave actual cross-set residual `5.962e-04`, random control residual `8.563e-05`, and planted relation residual `0`; finite Euler `S={2,3,5}` regular-coefficient Jacobian singular values `1.790008e+00, 8.816104e-02, 1.630999e-03`.
- Verdict: useful gatekeeper only. The right theorem is the already-banked finite Euler `corank = Stieltjes-trdeg` equality plus the open monotonicity/Schanuel rung; no new DSS-cross invariant.
- Archive: `computations/2026-06-21-penrose-r55-dss-spinodal-core-summary.md`.

## Penrose R56 - off-line curvature hidden scaling `[DEAD END / overlaps localization]`

- NODE: `The sensitivity of pattern onset to nondimensionalization choices and hidden parameter scalings`.
- Target: off-line FE-quartet convex window in `docs/consolidated/01-landscape-and-geometry.md`.
- Transfer tested: raw curvature thresholds hide the quartet half-width `a=|beta-1/2|`; the dimensionless sampling/localization parameter is `q=h/a`.
- Computation: fixed raw grid `h=1` detected the positive core with probability matching `min(1,2a/h)` (`a/h=.01 -> 0.0202`, `.10 -> 0.2029`, `.50 -> 1.0000`). Holding `h/a` fixed made `a^2 max C_a` invariant across tested `a`.
- Verdict: correct but reducing. R36/R37 already banked the off-line curvature scale passport and matched localization; R53 already banked grid-stability certificates.
- Archive: `computations/2026-06-21-penrose-r56-curvature-hidden-scaling-summary.md`.

## Penrose R57 - faithful-index modulation quotient `[DEAD END / generic Morse-index discipline]`

- NODE: `Modulation equations for blowup parameters such as scale, phase, center, and frequency`.
- Target: `G-C18. Faithful-index rigidity` from `docs/consolidated/08-conjectures-required.md`.
- Transfer tested: raw faithful-index readout must quotient neutral modulation/gauge directions first.
- Computation: one true physical negative direction plus four tiny neutral directions gave raw negative counts `1..4`, while the modulation quotient stayed `1`; with no physical negative direction, neutral dust alone gave raw `0..4` and quotient `0..0`.
- Verdict: useful G-C18 instrumentation warning, but generic Morse-index bookkeeping; no source-built proof that the completed carrier forces index zero.
- Archive: `computations/2026-06-21-penrose-r57-faithful-index-modulation-summary.md`.

## Penrose R58 - phase-weld out-of-sample validation `[DEAD END / validation-only]`

- NODE: `Model validation should use out-of-sample bubble-end forecasts, not only retrospective fits to famous crashes`.
- Target: Phase-Weld layer in `docs/consolidated/01-landscape-and-weld-geometry.md`.
- Transfer tested: train a median `Delta=max(log|A|,log|P|)-log|A+P|` threshold on one height window, then test held-out windows against finite Euler and random-phase controls.
- Computation: calibrated on `[100,170]`; `sigma=0.3` held-out margins stayed positive (`min=0.5748`, mean `0.6002`), `sigma=0.5` weakened, `sigma=0.7` failed, `sigma=1.2` collapsed.
- Verdict: useful validation discipline for the existing phase-carrier defect, not a new HGT invariant.
- Archive: `computations/2026-06-21-penrose-r58-phaseweld-outofsample-summary.md`.

## Penrose R59 - seam rest-frame equalization `[DEAD END / known FE-Berry fact]`

- NODE: `The background medium often defines a preferred rest frame, so exact relativistic symmetry is only approximate or emergent`.
- Target: critical seam `Re(s)=1/2` localized many ways.
- Transfer tested: prime-only diagnostics carry a preferred Euler-side frame; completed transport should restore mirror-frame invariance.
- Computation: prime-only mirror-lane magnitude imbalance means ranged `0.160893..0.847976`; completed `xi'/xi` imbalance was numerical zero (`~1e-16`) across tested windows and lane offsets.
- Verdict: correct but exactly the functional-equation / Berry lane-equalization result; no new content.
- Archive: `computations/2026-06-21-penrose-r59-seam-rest-frame-summary.md`.

## Penrose R60 - Berry seam coarse-graining `[DEAD END / weakened known result]`

- NODE: `Coarse-graining can erase microscopic determinism, but it can also introduce artifacts mistaken for physical laws`.
- Target: Berry seam layer in `docs/consolidated/01-landscape-and-weld-geometry.md`.
- Transfer tested: lane averaging/coarse-graining erases the Berry relative phase after completion equalizes mirror-lane magnitudes.
- Computation: completed magnitude imbalance was `~1e-16`; median relative phase was large (`0.7105..2.1159`); lane averaging cancellation reached `0.9493` and `0.9772` in tested windows.
- Verdict: correct but reducing to the existing Berry seam result.
- Archive: `computations/2026-06-21-penrose-r60-berry-coarse-grain-summary.md`.

## Penrose R61 - B2 synchronous artifact `[DEAD END / grid-stability warning]`

- NODE: `Spectral artifacts can appear from synchronous updating`.
- Target: B2 two-lemma bridge in `docs/consolidated/08-conjectures-required.md`.
- Transfer tested: synchronous grid artifacts can fake off-seam transport defects.
- Computation: source-free oscillatory artifact gave synchronized defect count `80`, half-period offset `0`, random-offset range `0..80`, true source charge `0`.
- Verdict: valid B2 guardrail, but it reduces to existing grid-stability/sampling-alias discipline.
- Archive: `computations/2026-06-21-penrose-r61-b2-synchronous-artifact-summary.md`.

## Penrose R62 - two-axis mode conversion `[DEAD END / existing orthogonality]`

- NODE: `Mode conversion at interfaces and defects`.
- Target: two orthogonal axes in `docs/consolidated/01-landscape-and-geometry.md`.
- Transfer tested: an interface/defect can convert a weld-symmetric mode into a positivity/localization failure.
- Computation: FE-symmetric off-line quartet had FE residual `~2e-13` while center curvature was positive and matched `2/a^2` across tested `a`.
- Verdict: exactly the existing weld/constraint vs RH-positivity orthogonality witness; no new bridge.
- Archive: `computations/2026-06-21-penrose-r62-axis-mode-conversion-summary.md`.

## Penrose R63 - scalar-layer cofactor sensitivity `[DEAD END / existing scalar warning]`

- NODE: `Metal ions, cofactors, lipids, or post-translational modifications can reshape the landscape and change apparent allosteric mechanisms`.
- Target: Scalar Layer in `docs/consolidated/01-landscape-and-weld-geometry.md`.
- Transfer tested: positive scalar cofactors reshape `log(1+|P|)` while phase direction remains invariant.
- Computation: scalar `beta` shifted by mean `0.214508`, range `0.000283..0.430386`; phase and `cos(A,P)` shifts were numerical zero.
- Verdict: correct but exactly the existing scalar-layer warning.
- Archive: `computations/2026-06-21-penrose-r63-scalar-cofactor-summary.md`.

## Penrose R64 - cross-term endpoint recruitment `[DEAD END / known cross-term]`

- NODE: `Fibril ends are usually the main sites of monomer recruitment and conversion`.
- Target: archimedean-prime cross-term in `docs/consolidated/01-landscape-and-weld-geometry.md`.
- Transfer tested: same scalar bulk amplitudes can produce different weld conversion because the interface/cross-term carries the action.
- Computation: fixed `|A|=|P|=4`; varying relative phase moved `Delta` from `-0.6931` to `3.4605`.
- Verdict: correct but exactly the existing cross-term/phase-carrier point.
- Archive: `computations/2026-06-21-penrose-r64-cross-term-end-recruitment-summary.md`.

## Penrose R65 - two-clock cycle affinity `[DEAD END / controls fail]`

- NODE: `Local detailed-balance constraints on transition rates in stochastic assembly models`.
- Target: Two-Clock layer in `docs/consolidated/01-landscape-and-weld-geometry.md`.
- Transfer tested: local detailed balance becomes a four-state cycle current from finite-prime phase agreement and true weld tension.
- Computation: finite affinities were nonzero, but random controls often matched/exceeded them and `sigma=1.2` did not cleanly collapse.
- Verdict: binarized cycle affinity is too fragile; no new two-clock invariant.
- Archive: `computations/2026-06-21-penrose-r65-two-clock-affinity-summary.md`.

## Penrose R66 - screened off-line curvature `[DEAD END / localization variant]`

- NODE: `The role of substrate friction in screening hydrodynamic interactions between defects`.
- Target: positivity/localization axis in `docs/consolidated/01-landscape-and-geometry.md`.
- Transfer tested: exponential screening suppresses the off-line curvature kernel's negative wings and reveals positive localized mass.
- Computation: `a*screened_mass` scale-collapsed in `lambda/a`, peaking near `lambda/a=1` at `1.37351199`; unscreened whole-line mass is zero.
- Verdict: useful detector-family variant, but overlaps the existing curvature localization passport and matched-width results.
- Archive: `computations/2026-06-21-penrose-r66-screened-curvature-summary.md`.

## Penrose R67 - transient lubricated index `[DEAD END / known regularization warning]`

- NODE: `Slime or EPS layers acting as transient lubricants`.
- Target: `G-C10. Source-built faithful-index object`.
- Transfer tested: transient positive regularization can hide a negative faithful-index direction.
- Computation: `Q+eps I` has index `0` for `eps>=0.08`, index `1` below, with positive trace throughout.
- Verdict: exactly the known trace/regularization warning; no source-built faithful positivity.
- Archive: `computations/2026-06-21-penrose-r67-transient-lubricated-index-summary.md`.

## Penrose R68 - G-C15 path-dependent thresholds `[DEAD END / proof-obligation warning]`

- NODE: `The sol-gel transition may be gradual and path-dependent rather than a sharp thermodynamic phase boundary`.
- Target: `G-C15. One object, two entrances`.
- Transfer tested: two entrances can have path-dependent threshold lags, so G-C15 needs object-level equivalence.
- Computation: intrinsic index threshold and two lagged entrance readouts disagreed around transition values under up/down paths.
- Verdict: proof-obligation warning only; no G-C15 advance.
- Archive: `computations/2026-06-21-penrose-r68-gc15-path-threshold-summary.md`.

## Conway — Finding 30 — contour root/event certificate gate (2026-06-21)

- Workflow path: ResearchNode `21/44 Contour certification`; random topic `Poincare section aliasing`; NODE `failing to interpolate/root-find exact crossing point`; method `20 = name the missing lemma`.
- NODE constraint: a section hit is the event `g(x(t))=0` with crossing direction, not a fixed output sample. In the oscillator check, event-root interpolation reduced nearest-output errors by two to three orders of magnitude; commensurate timesteps gave `same_point_alias=1.000`.
- Finding: near the first zero, true off-line rectangles had boundary winding `0`, but fixed transport quadrature for `1/(2πi)∮ξ'/ξ ds` returned large fake counts: `-17.015637` (`n_edge=4`), `-8.263997` (`n_edge=8`), `-1.726388` (`n_edge=32`) at `sigma_min=0.5005`; adaptive phase-event subdivision reduced the count to about `-0.006438`. Far-right controls stayed small.
- Step 12 sweep: fixed transport errors grew as the off-line rectangle approached the seam while winding remained zero (`eps=0.003`: `n8=-1.016`; `eps=0.001`: `n8=-3.897`; `eps=0.0005`: `n8=-8.264`). Adaptive event refinement stayed near zero.
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER CONJECTURE]` Contour-certification claims for the bridge arrow need boundary phase-event refinement / max-jump passport or residue-aware certification; a fixed-mesh transport integral is not a faithful off-line certificate near zero-shadows.
- Artifacts: `computations/2026-06-21-conway-poincare-contour-root-gate.py`, `computations/2026-06-21-conway-poincare-contour-root-gate.txt`, `computations/2026-06-21-conway-STEP12-contour-root-gate-battery.py`, `computations/2026-06-21-conway-STEP12-contour-root-gate-battery.txt`.

## Conway — Berry phase-slip independent-observable gate `[DEAD END / existing R24 restatement]` (2026-06-21)

- Workflow path: ResearchNode `35/44 Berry switch`; random topic `phase-slip detection`; NODE `validate detections against an independent observable`; method `3 = reverse it`.
- Result: synthetic phase-slip validation behaved correctly, and the transfer showed completed `xi` passes mirror anti-phase + magnitude co-event gates while bare/gamma/finite/scrambled controls fail one or both gates.
- Verdict: dead end for novelty. The completed rows are just the functional equation / Berry lane-switch already cataloged in Penrose R24; the independent-observable framing is good hygiene but not a new non-reducing finding.
- Artifacts: `computations/2026-06-21-conway-phase-slip-berry-coevent.py`, `computations/2026-06-21-conway-phase-slip-berry-coevent.txt`, `computations/2026-06-21-conway-STEP12-berry-coevent-battery.py`, `computations/2026-06-21-conway-STEP12-berry-coevent-battery.txt`.

## Conway — Finding 31 — co-failure source-lane provenance gate (2026-06-21)

- Workflow path: ResearchNode `24/44 Co-failure sheets`; random topic `Hidden Markov models with emissions in multiple channels`; NODE `more channels increase the risk of learning sensor artifacts as hidden states`; method `2 = attack it as false`.
- Attack: inject synchronized non-source artifact channels into the existing low-reserve co-failure metric and test whether finite/random controls become positive co-failure sheets.
- Result: true source lanes retained id768 strength (`exI=+0.189`, `exS=+0.183`) and survived leave-one-source-lane ablation (`+0.139..+0.219`). Finite source lanes stayed negative (`exI=-0.026`). Mixed finite+artifact did not become a true-strength positive (`exI=-0.014`, `exS=-0.003` in the main row; sweep maxima about `+0.056` at weak threshold), but artifact-only rows can pass the scalar excess test if treated as lanes (`art_only_exI=+0.367` in the sweep).
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER CONJECTURE]` Co-failure claims need source-lane provenance, leave-source-lane ablation, and an effect-size floor against artifact-only controls. Product/shift nulls resist mixed artifact injection, but the scalar excess statistic alone is not a provenance certificate.
- Artifacts: `computations/2026-06-21-conway-cofailure-artifact-channel-gate.py`, `computations/2026-06-21-conway-cofailure-artifact-channel-gate.txt`, `computations/2026-06-21-conway-STEP12-cofailure-artifact-sweep.py`, `computations/2026-06-21-conway-STEP12-cofailure-artifact-sweep.txt`.

## Conway — Hodge rare-dust bulk masking `[DEAD END / existing faithful-index warning]` (2026-06-21)

- Workflow path: ResearchNode `39/44 Hilbert-Pólya/Hodge/F1 route`; random topic `Epigenetic state inference`; NODE `bulk tissue signals can mask rare but biologically important subpopulations`; method `3 = reverse it`.
- Result: a toy Krein/Hodge matrix with one negative direction keeps positive trace and positive random quadratic probes even with `κ_-=1` (`n=1000, alpha=10`: trace mean `+0.9890`, random negative probe rate `0`).
- Verdict: dead end for novelty. This is exactly the existing faithful-index vs density-zero/off-line-dust guardrail; no new route or gate beyond the cataloged warning.
- Artifacts: `computations/2026-06-21-conway-hodge-rare-dust-mask.py`, `computations/2026-06-21-conway-hodge-rare-dust-mask.txt`.

## Conway — Finding 32 — canalized realization / low-order moment positivity gate (2026-06-21)

- Workflow path: ResearchNode `16/44 Positivity vs realization`; random topic `Developmental canalization`; NODE `canalization can hide cryptic variation until stress exposes it`; method `22 = compare nearby false statements`.
- Model: FE-symmetric central zero quartets. Off-line zeros `±a±iγ`; on-line comparison at `±i sqrt(γ^2-a^2)` with multiplicity chosen to match the second central power sum `p2`.
- Result: FE residual and `p2` both pass (`p2_gap=0` or numerical zero; FE residual `~1e-15`), but localized sigma-curvature stress separates off-line from on-line. Example `a=0.10`: `p2_gap≈2.27e-13`, `p4_gap=64`, `off_curv_min=-2.000e2`, `on_curv_min=+1.249e1`.
- Status: `[EXPERIMENTAL FINDING / COUNTEREXAMPLE-GATE]` FE/realization plus a low-order bulk/passport moment can hide off-line variation. Positivity-vs-realization routes need a faithful local stress/index certificate, not only FE symmetry and low-order bulk matching.
- Artifacts: `computations/2026-06-21-conway-canalization-realization-positivity.py`, `computations/2026-06-21-conway-canalization-realization-positivity.txt`.

## Conway — Finding 33 — HMM scaling gauge test for cohomology target (2026-06-21)

- Workflow path: ResearchNode `5/44 Cohomology target`; random topic `Hidden Markov models`; NODE `forward/backward scaling or log-space computation is essential`; method `4 = change viewpoint`.
- NODE constraint: HMM normalized posteriors are invariant under positive per-time scaling, but the accumulated likelihood normalization shifts. Test row: raw final probability `3.963e-308`, arbitrary scaling shifted log normalization by `+2.250e3`, normalized posterior changed by `2.220e-16`.
- Transfer: add exact analytic gauges `d(λs+μs²)` to `d log ξ` and compare closed-loop charge to scalar boundary energies.
- Result: loop count was invariant under exact gauges to `~1e-51`, while scalar boundary energies changed substantially. Gap rectangle energy ratios under `(λ,μ)=(3,0),(0,0.7),(-2,0.4)` were `1.585`, `4.384`, `2.563`; loop count did not move.
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER CONJECTURE]` A cohomology-target carrier must survive exact analytic frame normalization. Closed-loop residue/holonomy passes; scalar energy/max-amplitude readouts fail and therefore live in gauge choice, not in the carrier class.
- Artifacts: `computations/2026-06-21-conway-hmm-scaling-cohomology-gauge.py`, `computations/2026-06-21-conway-hmm-scaling-cohomology-gauge.txt`.

## Conway — Finding 34 — zero-shadow path-ensemble coverage gate (2026-06-21)

- Workflow path: ResearchNode `27/44 Zero-shadow topology`; random topic `Molecular dynamics path ensembles`; NODE `detailed balance in path sampling must be checked at the trajectory-move level`; method `15 = strengthen the conjecture`.
- NODE validation: balanced three-state path moves had exact detailed-balance residual `0.0000`; biased accept-all moves had residual `0.3450` and wrong occupancy.
- Result: true full zero-shadow masks at threshold `1.00` span in both tested windows, while finite/random do not. But reversible local path sampling at `~0.66-0.70` occupied-mask coverage still fragmented true spans (`bal_span_t=0`), and matched uniform thinning fragmented worse. Coverage sweep: true span appeared only around `0.90+` occupied-mask coverage (`0.907/0.921 -> span_t=1`; `0.702/0.722 -> 0`). Finite/random controls remained nonspanning.
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER CONJECTURE]` Zero-shadow topology needs a reversible path-ensemble coverage certificate: move-level reversibility plus occupied-mask coverage, not only full-grid components or uniform sampling survival.
- Artifacts: `computations/2026-06-21-conway-zero-shadow-path-detailed-balance.py`, `computations/2026-06-21-conway-zero-shadow-path-detailed-balance.txt`.

## Conway — Finding 35 — q70 niche-conditioned threshold boundary (2026-06-21)

- Workflow path: ResearchNode `23/44 q70 association gate`; random topic `Cell lineage stochasticity`; NODE `extrinsic niche variation can be mistaken for intrinsic stochastic fate choice`; method `23 = classify boundary cases`.
- NODE validation: shared extrinsic niche probabilities inflated raw fate-mean variance by `9.39x` over shuffled-niche baseline.
- Transfer: test q-threshold sigma-lane association against a time-count-conditioned null preserving the number of active lanes at each height/time sample while randomizing which lanes are active.
- Result: q70 is not true-specific under this niche null. At `q=0.70`, true mean excess was `+0.00222` (`above_q95=2/3`), while finite Euler was larger and passed all windows (`+0.00667`, `3/3`). Threshold sweep: `q=0.60/0.70/0.80` remain finite-vulnerable, but `q=0.90` separates in this battery (`true +0.00218, 3/3`; finite `+0.00056, 0/3`; random `0/3`).
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER CONJECTURE]` Recast the q70 association gate as a threshold-family association gate with a time-count-conditioned niche null; q90, not q70, is the cleaner boundary in this test.
- Artifacts: `computations/2026-06-21-conway-q70-niche-conditioned-null.py`, `computations/2026-06-21-conway-q70-niche-conditioned-null.txt`, `computations/2026-06-21-conway-STEP12-q70-niche-threshold-sweep.py`, `computations/2026-06-21-conway-STEP12-q70-niche-threshold-sweep.txt`.

## Conway — Aborted pass — RNG topic 2 is closed after rung-1 no-go (2026-06-21)

- STEP 0 drew `2` from the old 1--44 workflow. After rereading `docs/consolidated/revision01/research-topics.md` under the user's reorientation, I treated this as an obsolete/closed carrier-status slot rather than mapping it positionally to the second live bullet.
- Reason: the revised list says phase/`𝔗_ξ` are `{zeros, FE, source}` geometry instruments, not transcendence detectors; carrier-native-HT and surrogate-ladder runs are closed by the rung-1 no-go.
- Discarded partial chain: `Random effects vs fixed hidden context` -> NODE `Fixed effects avoid distributional assumptions for group coefficients`.
- Status: dead/aborted, not counted. Continue with the last valid RandomNode seed, `Extrinsic niche variation can be mistaken for intrinsic stochastic fate choice`.

## Conway — Finding 36 — zero-shadow attractor recurrence plus connectivity (2026-06-21)

- Workflow path: ResearchNode `27/44 zero-shadow topology`; random topic `Sensitive dependence masquerading as randomness`; NODE `strange attractors constraining behavior within bounded but irregular regions`; method `21 = build a dependency chain`.
- Reorientation applied: this is a bridge/positivity geometry gate for completed divisor geometry, not a transcendence detector.
- NODE validation: Lorenz traces showed exponential separation (`lyap_slope=0.858`) but high bounded recurrence (`lorenz_recurrence=0.915`) compared with IID box points (`0.375`).
- Transfer: represent each zero-shadow height column as a finite sigma-profile. Test whether the mask has attractor-like recurrence and connected height-spanning support.
- Result: at threshold `1.00`, true masks passed the combined gate in `3/3` windows (`mean_recurrence=0.924`, `mean_components=1.0`, `span_windows=3/3`); finite Euler had recurrence but fragmented/nonspanning masks (`mean_recurrence=0.817`, `mean_components=46.0`, `span_windows=0/3`); random phase had almost no recurrence (`0.002`) and many components (`367.7`). Threshold sweep: true combined pass is strongest around `0.95--1.10`; finite/random remain `0/3` on the combined gate across `0.70--1.25`.
- Status: `[EXPERIMENTAL FINDING / BRIDGE-GEOMETRY GATEKEEPER]` Add a two-part attractor certificate to zero-shadow topology: profile recurrence plus connected height-spanning support. Recurrence alone is finite-vulnerable; connectivity alone is sampling-vulnerable.
- Artifacts: `computations/2026-06-21-conway-zero-shadow-attractor-recurrence.py`, `computations/2026-06-21-conway-zero-shadow-attractor-recurrence.txt`, `computations/2026-06-21-conway-STEP12-zero-shadow-attractor-gate.py`, `computations/2026-06-21-conway-STEP12-zero-shadow-attractor-gate.txt`.

## Conway — Skipped closed slot — RNG topic 8 carrier status (2026-06-21)

- STEP 0 drew `8`; revised topic list marks `#8 Carrier status` resolved and says not to rerun carrier/native-HT experiments.
- Status: skipped, not counted; redraw.

## Conway — Finding 37 — prime-built feedback flow out-of-sample kill gate (2026-06-21)

- Workflow path: ResearchNode `#1/#16 Conjecture E`; random topic `Ecological regime shifts`; NODE `social or economic feedbacks that reinforce ecological degradation`; method `23 = classify boundary cases`.
- NODE validation: a simple ecological/social lock-in model recovered with no feedback (`gamma=0`, degraded `0.017`) but stayed degraded for `gamma>=0.8` (`0.991--1.000`) after external stress reversal.
- Transfer: test reversible positive Markov generators on prime-log lanes with monotone feedback. This is only a scoped kill-gate for positive/order-preserving prime-built flow candidates, not a proof of Conjecture E.
- Result: feedback collapses stationary entropy and creates enormous prime-lane lock-in (`sigma=0.8`, lock `22.68 -> 321302.61`; `sigma=1.1`, `73.09 -> 1403963.14`). Early affine fits to zero ordinates can look tiny (`train_mse≈0.001--0.003`), but out-of-sample errors remain large (`test/train` about `39x--670x`) and spacing MSE stays poor (`~0.7--1.3`).
- Status: `[EXPERIMENTAL FINDING / CONJECTURE-E KILL GATE]` Reject prime-built positive/reversible feedback-flow candidates unless they pass out-of-sample zero-spectrum and spacing gates. Internal prime-lane stabilization is a lock-in warning, not evidence for a zero-generating flow.
- Artifacts: `computations/2026-06-21-conway-prime-flow-feedback-lockin.py`, `computations/2026-06-21-conway-prime-flow-feedback-lockin.txt`, `computations/2026-06-21-conway-STEP12-prime-flow-feedback-oos.py`, `computations/2026-06-21-conway-STEP12-prime-flow-feedback-oos.txt`.

## Conway — Finding 38 — holonomy refinement-history invariance lemma (2026-06-21)

- Workflow path: ResearchNode `#4/#5/#6 cohomology of carrier holonomy`; random topic `Path dependence under uncertainty`; NODE `small initial advantages compound through reinforcement`; method `20 = name the missing lemma`.
- NODE validation: a Polya urn turned a small initial red/blue shock into mean final fractions `0.755` vs `0.254` (`red_minus_blue=0.501`) while neutral stayed `0.496`.
- Transfer: compare uniform contour refinement for `d log xi` with Polya-reinforced side budgets at the same total sample passport. The closed contour and total count are fixed; the refinement history changes.
- Result: reinforced schedules strongly perturb raw non-winding side shape and can perturb the winding estimate when a side is starved. Example `[500,570] bottom_shock [555,51,55,59]`: winding `+49.5657+2.6932i` vs uniform `+49.9608-0.0000i`, raw-shape L1 `1.039`, but per-side mean-shape L1 only `0.010`. Guard-band sweep shows raw-shape L1 collapses as per-side floor rises (`0.855 -> 0.006` on `[500,570]` from floor `2` to `180`), while mean-shape L1 remains tiny.
- Status: `[EXPERIMENTAL FINDING / MASTER-1 GATEKEEPER]` Name the missing lemma: refinement-history invariance. Master-1 non-winding holonomy candidates need cyclic/refinement-order/side-stratified invariance after subtracting affine passport. Total sample count alone is not a valid passport.
- Artifacts: `computations/2026-06-21-conway-holonomy-refinement-history.py`, `computations/2026-06-21-conway-holonomy-refinement-history.txt`, `computations/2026-06-21-conway-STEP12-holonomy-refinement-floor.py`, `computations/2026-06-21-conway-STEP12-holonomy-refinement-floor.txt`.

## Conway — Skipped unmapped slot — RNG topic 28 (2026-06-21)

- STEP 0 drew `28`; revised topic list has no active `#28` entry.
- Status: skipped, not counted; redraw.

## Conway — Finding 39 — contour event-community certificate metadata (2026-06-21)

- Workflow path: ResearchNode `#21 event-certified contour certificate`; random topic `Preferential attachment`; NODE `preferential attachment alone does not explain community structure`; method `19 = write the fake proof`.
- NODE validation: plain PA and block-PA had nearly identical degree inequality (`gini=0.351` vs `0.350`; top-5 share `0.093` vs `0.096`) but very different community structure (`modularity=-0.035` vs `0.420`).
- Transfer: attack the fake proof that enough boundary events certify a contour. With a fixed top-event count `K=28`, tight zero-containing, no-zero, and wide zero-containing rectangles have identical event count but different side/cluster fingerprints: tight contains `[0,14,0,14]`, no-zero `[0,0,0,28]`, wide contains `[28,0,0,0]`.
- Boundary sweep: tight contains keeps paired opposite-side events for `K=8--64`; no-zero rectangles concentrate on one side for `K<=40`; wide contains may also concentrate on one side, so event-community is diagnostic metadata, not a zero classifier.
- Status: `[EXPERIMENTAL FINDING / CONTOUR-CERTIFICATE GATEKEEPER]` Report an event-community passport for contour certificates: event count, side distribution/entropy, cluster count, longest cluster, and refinement stability. Never use count alone, and do not let community metadata replace transport/winding/root-location certification.
- Artifacts: `computations/2026-06-21-conway-contour-event-community.py`, `computations/2026-06-21-conway-contour-event-community.txt`, `computations/2026-06-21-conway-STEP12-contour-event-community-sweep.py`, `computations/2026-06-21-conway-STEP12-contour-event-community-sweep.txt`.

## Conway — Finding 40 — C3 point-defect core/tail decomposition (2026-06-21)

- Workflow path: ResearchNode `#25 phase-Sobolev`; random topic `Crystallization defects and domains`; NODE `strain fields around point-defect clusters`; method `1 = split into subclaims`.
- NODE validation: synthetic point-defect cores occupied `6.6%` of area but carried `35.0%` of squared strain energy, forcing a core/tail split.
- Transfer: split C3 phase-Sobolev into full H1 gap, data-defined point-defect core, and residual tail. Core masks were top true-energy neighborhoods, applied equally to true and finite controls.
- Result: critical windows retain substantial true/finite tail gap after core deletion. `[100,170]`: full gap `2.4260`; tail retention `0.827`, `0.532`, `0.516` for `q=0.02,0.05,0.10`. `[500,570]`: full gap `3.7736`; retention `0.929`, `0.831`, `0.556`. Right-half-plane controls remain collapsed (`tail_gap <=0.0002`). Zero-strip is core-vulnerable (`q=0.10` captures essentially all true energy).
- Status: `[EXPERIMENTAL FINDING / C3 GATEKEEPER]` Add point-defect core/tail decomposition to C3 reporting. Critical-window phase-Sobolev gaps are not solely localized cores in this battery; zero-strip evidence can be core-dominated and should be demoted unless it passes the tail gate.
- Artifacts: `computations/2026-06-21-conway-c3-point-defect-strain.py`, `computations/2026-06-21-conway-c3-point-defect-strain.txt`.

## Conway — Finding 41 — holonomy event-shape deformation-stability gate (2026-06-21)

- Workflow path: ResearchNode `#4/#5/#6 cohomology of carrier holonomy`; random topic `Market microstructure defects`; NODE `stop-order clustering amplifies short-term cascades`; method `23 = classify boundary cases`.
- NODE validation: clustered stops produced the same eventual trigger count/drop as uniform stops but a larger max cascade step (`0.214` vs `0.083`).
- Transfer: vary the half-width of zero-containing rectangles around the first zero. Winding remains `+1`, so changes in non-winding event-shape fingerprint expose deformation instability.
- Result: half-widths `0.025--0.075` have event-side fingerprint `[0.00,0.50,0.00,0.50]`; at `0.110` the fingerprint jumps to `[1.00,0.00,0.00,0.00]` with L1 jump `2.000`, while winding remains `+1.000`; the altered fingerprint persists at `0.160--0.240`.
- Status: `[EXPERIMENTAL FINDING / MASTER-1 GATEKEEPER]` A non-winding holonomy/event-shape candidate needs deformation-stability over a contour-thickening band. Single-contour fingerprints are not cohomology classes.
- Artifacts: `computations/2026-06-21-conway-holonomy-deformation-cascade.py`, `computations/2026-06-21-conway-holonomy-deformation-cascade.txt`.

## Conway — Finding 42 — holonomy cross-lane full-kernel gate (2026-06-21)

- Workflow path: ResearchNode `#4/#5/#6 cohomology of carrier holonomy`; random topic `Self-exciting point processes / Hawkes`; NODE `multivariate Hawkes excitation is governed by the full kernel matrix`; method `18 = look for the right theorem`. Procedural note: Step 4 and Step 9 RNG were drawn early in one shell command but used in order after the Step 3 list.
- NODE validation: a three-lane cascade had pairwise `1--3` correlation near zero (`-0.000`) while the full kernel recovered direct `1->2` and `2->3` excitation (`0.389`, `0.400`) and near-zero `1->3` (`0.013`).
- Transfer: estimate full directed lag kernels for sigma-lane phase-event fields and compare with pairwise co-event edge counts.
- Result: pairwise edge counts saturate for true and finite (`90` in every tested case), while full-kernel off-diagonal mass separates true from finite/random better (`true 18.776--24.222`; finite `9.800--14.236`; random `3.678--3.944`). Spectral radius alone is finite-vulnerable, and rank-2 energy is supporting metadata only.
- Status: `[EXPERIMENTAL FINDING / MASTER-1 KERNEL GATEKEEPER]` Use full directed cross-lane kernels with finite/random controls. Do not use pairwise co-event counts or spectral radius alone as holonomy evidence.
- Artifacts: `computations/2026-06-21-conway-holonomy-full-kernel.py`, `computations/2026-06-21-conway-holonomy-full-kernel.txt`.

## Conway — Skipped unmapped slot — RNG topic 29 (2026-06-21)

- STEP 0 drew `29`; revised topic list has no active `#29` entry.
- Status: skipped, not counted; redraw.

## Conway — Finding 43 — C3 cryptic-context activation atlas (2026-06-21)

- Workflow path: ResearchNode `#25 phase-Sobolev`; random topic `Protein allostery`; NODE `allosteric sites may be transient/cryptic and condition-formed`; method `15 = strengthen`. Procedural note: Step 4 and Step 9 RNG were drawn early in one shell command but used in order after the Step 3 list.
- NODE validation: a cryptic-site occupancy model was strongly active only under ligand (`mean=0.610`, active fraction `0.968`) and was diluted when pooled (`active fraction=0.248`).
- Transfer: require a C3 sigma/window activation atlas after guard and point-core/tail gates. Test true-vs-finite full and tail gaps over two height windows and sigma lanes `0.30--1.30`.
- Result: active contexts are `10/16`, exactly `sigma=0.30--0.70` in both tested critical windows. The gap shuts off by `sigma=0.90` and remains absent at `1.15,1.30`. Tail retention remains substantial in active contexts; inactive contexts have tiny full and tail gaps.
- Status: `[EXPERIMENTAL FINDING / C3 GATEKEEPER]` Strengthen C3 reporting from a single phase-Sobolev statistic to a context atlas: sigma/window activation plus guard-band and core/tail gates. Pooled/single-condition statistics should not be promoted.
- Artifacts: `computations/2026-06-21-conway-c3-cryptic-context-atlas.py`, `computations/2026-06-21-conway-c3-cryptic-context-atlas.txt`.

## Conway — Finding 44 — FID prime-peeled scaled tail basis (2026-06-21)

- Workflow path: ResearchNode `#41 FID route`; random topic `Molecular chaperone capacitance / Hsp90`; NODE `epigenetic/chromatin-mediated Hsp90-dependent release`; method `6 = ask what action is happening`.
- NODE validation: reducing buffer capacity released hidden variation (`expressed_frac 0.088 -> 0.357 -> 0.669`; phenotype SD `0.650 -> 0.919 -> 0.992`).
- Transfer: raw `kappa_n=zeta(2n+1)` buffers the nontrivial prime tail behind the rank-one bulk. Test peeled/scaled prime-tail Hankel bases.
- Result: unscaled tail is worse (`size-8 cond 9.801e22`); raw loses sign at size 8. Prime-peeled scaled tails keep positive signs and improve conditioning: size-8 `two_scaled_tail` cond `1.074e16`, `three_scaled_after_two` `7.781e13`, `five_scaled_after_23` `5.408e12`; at size 7, raw `1.361e17` improves to `9.700e12`, `2.096e11`, `2.670e10` respectively.
- Status: `[EXPERIMENTAL FINDING / FID BASIS CANDIDATE]` Test prime-peeled scaled tail bases for the FID Hankel certificate. This is a concrete basis direction addressing R41's tail-stability bottleneck, not a proof of positivity.
- Artifacts: `computations/2026-06-21-conway-fid-chaperone-tail-basis.py`, `computations/2026-06-21-conway-fid-chaperone-tail-basis.txt`.

## Conway — Skipped unmapped slot — RNG topic 30 (2026-06-21)

- STEP 0 drew `30`; revised topic list has no active `#30` entry.
- Status: skipped, not counted; redraw.

## Conway — Reorientation — topic seed list now 34 entries (2026-06-21)

- User correction: reread `docs/consolidated/big-picture.md` and `docs/consolidated/revision01/research-topics.md`; topic seeds are now explicit `1..34` entries.
- Operational change: future STEP 0 draws use `scripts/rng int 1 34`, mapped directly to the numbered topic list.
- Aborted old in-flight `#19 local detection` pass because current topic `19` is `Master-1: cohomology of the carrier holonomy`. Created artifact `computations/2026-06-21-conway-local-pole-background-fit.py` is not counted.

## Conway — Finding 45 — Jensen/Hankel detectability-versus-fidelity audit (2026-06-21)

- Workflow path: ResearchNode `15 Uniform Jensen/Hankel`; random topic `Stochastic resonance`; NODE `detectability can improve while waveform fidelity degrades`; method `11 = run experiments`.
- NODE validation: subthreshold signal detection improved from `0.000` to `1.000` under added noise, while waveform correlation degraded from `1.000` to `0.463`.
- Transfer: use recorded `Xi` Maclaurin coefficients from the existing Jensen/Turan run to test a near-boundary Hankel form. A small tail perturbation fails PSD; diagonal ridge restores the binary PSD pass while changing the object. This is a gate experiment, not a positivity certificate.
- Result: ridge `1.25` flips PSD to pass (`min_eig=+1.619e-10`) with Frobenius/profile errors `2.840e-05`/`7.833e-06`; ridge `4.00` strengthens the pass (`+4.613e-09`) but worsens fidelity (`9.817e-05`/`4.478e-05`).
- Status: `[EXPERIMENTAL FINDING / JENSEN-HANKEL GATEKEEPER]` Any smoothing/ridge/noise-floor/basis-conditioning that improves PSD or hyperbolicity detection must report object-fidelity metrics. Binary positivity pass alone is not admissible evidence near the uniform Jensen/Hankel wall.
- Artifacts: `computations/2026-06-21-conway-jensen-resonance-fidelity.py`, `computations/2026-06-21-conway-jensen-resonance-fidelity.txt`.

## Finding 46/50 - Conjecture E preparation-cluster passport

- ResearchNode: `#1 Constraint vs flow / Conjecture E scoped`.
- Random path: stochastic resonance -> single-molecule detection -> shared field/surface/preparation dependence.
- Method: `Strip it to essentials`.
- Result: shared-preparation dependence collapses nominal single-molecule `n=800` to effective `n=42.80` and inflates naive false positives (`0.6645` vs `0.0665` cluster-level). Transferred gate: prime-wave residual corrections must be judged by independent height/preparation clusters, not pointwise zero counts. In the stripped audit, prime waves improved both zero ordinates and spacings in all six height-window clusters, while matched random-frequency decoys were negative in all six clusters.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE E GATEKEEPER]`. This is not evidence for an actual generative flow; it is a sharper kill gate requiring cluster aggregation, spacing survival, and prime-vs-decoy controls.
- Artifacts: `computations/2026-06-21-conway-preparation-cluster-killgate.py`, `computations/2026-06-21-conway-preparation-cluster-killgate.txt`.

## Finding 47/50 - Cross-lane common-noise conditioning gate

- ResearchNode: `#26 Cross-lane kernel K(σ,σ')`.
- Random path: shared-preparation dependence -> common-noise SDEs -> conditional independence only after conditioning on common noise.
- Method: `Run experiments`.
- Result: NODE simulation gave unconditional mean pair correlation `+0.6397`, collapsing to `-0.0003` after conditioning on the common noise path. Transferred to σ-lane phase-event kernels: raw true/finite off-diagonal ratios looked strong (`1.530--2.242`), but after residualizing the shared per-time event field they dropped to `0.573--1.113`. The true kernel had large common-mode shares (`0.591--0.803` in most tested cases).
- Status: `[EXPERIMENTAL FINDING / CROSS-LANE KERNEL GATEKEEPER]`. Raw `K(σ,σ')` off-diagonal mass must be split into common-field and lane-specific residual components before any bridge verdict.
- Artifacts: `computations/2026-06-21-conway-crosslane-common-noise-conditioning.py`, `computations/2026-06-21-conway-crosslane-common-noise-conditioning.txt`.

## Finding 48/50 - Conjecture E numerical-representation passport

- ResearchNode: `#34 Conjecture E kill gate`.
- Random path: common-noise conditional independence -> shadowing/hidden parameters -> compiler/interpreter flags affecting output.
- Method: `Change representation`.
- Result: same prime-wave residual source flips near the overfit boundary under hidden numerical flags. For `K=34`, untruncated least squares gave ordinate margin `-3.883132` and spacing margin `-5.770250`; `rcond=0.01` gave `+0.041837` and `+0.113296`; ridge `1e-1` gave `+0.096325` and `+0.176030`. Stable smaller bases were robust, so the failure mode is localized to representation-sensitive promotion.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE E GATEKEEPER]`. Flow evidence needs a representation passport: solver, precision, truncation/rcond, ridge/tolerance, condition number, and pass/fail stability strip.
- Artifacts: `computations/2026-06-21-conway-conjecture-e-representation-passport.py`, `computations/2026-06-21-conway-conjecture-e-representation-passport.txt`.

## Finding 49/50 - FID successor-integer peeling correction

- ResearchNode: `#18 FID route`, open tail-stable certificate.
- Random path: compiler/interpreter flags -> rare-event simulation -> plausible path versus dominant path.
- Method: `Write the fake proof`.
- Result: the fake proof “peel primes, scale by next prime” fails because composites below the next prime remain. The prior `five_scaled_after_23`/`five_prime_only_after_123` basis is composite-4 dominated, not prime-5 dominated: by `n=20`, base-5 share is `0.000106`, while unpeeled 4 carries `0.999894`. Corrected integer-successor bases restore dominance: `five_after_1234` has base-5 share `0.999432` by `n=20`, and improves size-8 conditioning from `5.408e12` to `1.021e12`.
- Status: `[EXPERIMENTAL FINDING / FID CERTIFICATE CORRECTION]`. Replace prime-peeling language with successor-integer peeling: scale by the least unpeeled integer, or peel every integer below the intended base before claiming a dominant-tail certificate.
- Artifacts: `computations/2026-06-21-conway-fid-dominant-tail-path.py`, `computations/2026-06-21-conway-fid-dominant-tail-path.txt`.

## Finding 50/50 - Conjecture E finite-threshold/window ladder

- ResearchNode: `#34 Conjecture E kill gate`.
- Random path: plausible path vs dominant path -> rare-event simulation / importance-sampling traps -> asymptotic tilt may fail at finite thresholds.
- Method: `Test extreme cases`.
- Result: rare-event tilt `μ=6` was efficient at threshold `a=6` (relative SE `0.012`, ESS `~6449`) but poor at finite thresholds (`a=2`: relative SE `0.324`, ESS `13.4`). Transferred gate: high-capacity prime-wave residual predictor trained on `[30,99]` with `K=34`/`70` features must be tested over a finite-window ladder. `rcond_0.01` passed `[100,119]` but failed `3/11` finite windows; `untruncated` failed `11/11`; `rcond_0.10` and `ridge_1e-1` passed this ladder.
- Status: `[EXPERIMENTAL FINDING / CONJECTURE E GATEKEEPER]`. A single out-of-sample window or asymptotic-looking pass is insufficient; report low/mid/high finite-window ordinate and spacing margins.
- Artifacts: `computations/2026-06-21-conway-conjecture-e-finite-threshold-ladder.py`, `computations/2026-06-21-conway-conjecture-e-finite-threshold-ladder.txt`.

## Finding 51/100 - Same-geometry/different-arithmetic translation ladder

- ResearchNode: `#6 Two axes at the divisor` (geometry -> B/C; arithmetic -> A).
- Random path: finite-threshold rare-event tilting -> population extinction models -> spatial environmental correlation erases metapopulation rescue.
- Method: `19 = write the fake proof`.
- Result: a metapopulation rescue simulation showed that nominally replicated patches are still common-environment coupled (`all_extinct 0.9067` at rho `0.00`, `0.9550` at rho `0.92`). Transferred to the divisor axes, translating all sampled zero ordinates preserves gap/pair geometry (`geometry_l2` about `0` to `5e-15`) while changing prime-log resonance signatures (`arithmetic_l2` `0.679810` at delta `1.0`, `0.715706` at delta `2.0`; random-shift median `0.607360`).
- Status: `[EXPERIMENTAL FINDING / VALUE-AXIS GATEKEEPER]`. A claimed A-axis/value detector must pass a same-geometry/different-arithmetic fake ladder; agreement across phase, holonomy, and zero-window geometry tests is common-environment evidence, not divisor-arithmetic evidence.
- Artifacts: `computations/2026-06-21-conway-r2-geometry-arithmetic-common-environment.py`, `computations/2026-06-21-conway-r2-geometry-arithmetic-common-environment.txt`.

## Finding 52/100 - Holonomy second-round closure passport

- ResearchNode: `#19 Master-1: cohomology of the carrier holonomy`.
- Random path: spatial environmental correlation -> portfolio diversification breakdown during market contagion -> stress tests miss second-round effects from redemptions, deleveraging, and collateral chains.
- Method: `18 = look for the right theorem`.
- Result: the NODE feedback test amplified a fixed first-round portfolio loss `0.3069` from `1.10x` at target rho `0.10` to `15.82x` at target rho `0.94`, locating the Leontief/resolvent condition `rho(A)<1`. Transferred to sigma-lane phase-event kernels, signed one-step kernels looked stable (`signed_rho 0.567--0.714` for true), but true positive second-round closures were supercritical in every tested q/window (`positive_rho 1.048--1.327`); finite controls were stable in this run (`0.673--0.797`) and random controls were far below threshold (`0.137--0.250`).
- Status: `[EXPERIMENTAL FINDING / MASTER-1 GATEKEEPER]`. A one-step directed event kernel must report a second-round closure passport: signed spectral radius, signed closure gain, positive-feedback `rho(K_+)`, and finite/random controls. Signed-stable but positive-supercritical kernels are stress-chain objects, not closed holonomy classes.
- Artifacts: `computations/2026-06-21-conway-r2-holonomy-second-round-closure.py`, `computations/2026-06-21-conway-r2-holonomy-second-round-closure.txt`.

## Finding 53/100 - Native-weld closed-fiber compatibility reserve

- ResearchNode: `#21 Native weld category M+`.
- Random path: second-round stress chains -> nonlinear margin-call dynamics -> forced selling lowers collateral prices, raises leverage, and creates larger margin calls.
- Method: `20 = name the missing lemma`.
- Result: a one-shot margin stress pass failed under feedback: forced-sale amplification reached `6.41x` at shock `0.04`. Transferred to a synthetic weld model, all fibers initially passed the normalized Γ/prime commutator threshold (`initial_pass_rate 1.000`, `initial_max 0.916`), but the induced closure made `8` objects cross at coupling `0.05` and `22` cross at coupling `0.30`.
- Status: `[EXPERIMENTAL FINDING / NATIVE-WELD GATEKEEPER]`. Add a closed-fiber compatibility reserve to the objectwise passport: a naturality-square pass plus an endogenous-update bound proving iterated Γ/prime squares stay compatible. One-shot objectwise commutator bounds can fail after the weld action updates the fiber.
- Artifacts: `computations/2026-06-21-conway-r2-weld-margin-closure.py`, `computations/2026-06-21-conway-r2-weld-margin-closure.txt`.

## Clean Finding 51/100 - Source-avalanche shape passport beyond D2

- ResearchNode: GPT topic `#31 Bridge confinement half` — prove the hard part: all source-carrying defects are seam-confined.
- Random path: stochastic interface pinning and depinning -> avalanche shape asymmetry.
- Method: `6 = ask what action is happening`.
- Result: normalized avalanche shapes can have identical duration/area while carrying opposite skew (`+0.426` vs `-0.426`). Transferred to nested source contours, a single off-seam pair and a split off-seam control were built with the same exterior charge (`2.000000`) and same source-width second mass (`0.051200`), but different release profiles: single pair has one peak at width `0.159933`, skew `-0.000`, tail share `0.000`; split same-D2 control has two peaks, skew `+0.150`, tail share `0.090`.
- Status: `[EXPERIMENTAL FINDING / BRIDGE-CONFINEMENT GATEKEEPER]`. Strengthen source-width/D2 profile tests to a source-avalanche shape passport: peak(s), skew/bimodality, and tail share of the normalized nested-contour release profile. Endpoint charge or one source-width moment can miss split off-seam source structure with the same D2.
- Artifacts: `computations/2026-06-21-conway-clean-r51-avalanche-shape-profile.py`, `computations/2026-06-21-conway-clean-r51-avalanche-shape-profile.txt`.

## Clean dead end before Finding 52 - FID soft-spot predictor duplicate

- ResearchNode: GPT topic `#18 Integer-vs-zero divisor split`.
- Random path: avalanche shape asymmetry -> plastic deformation avalanches in amorphous metals -> NODE `local soft spots are probabilistic predictors of avalanche initiation, not deterministic failure sites`.
- Method: `9 = test small cases`.
- Verdict: dead end for new knowledge. Treating integer-divisor/FID positivity as a probabilistic soft predictor rather than a deterministic zero-divisor certificate reduces to the existing FID support-transport passport and note 14. Not counted.

## Clean Finding 52/100 - D2 uncertainty deaggregation passport

- ResearchNode: GPT topic `#7 Local source-width detector` — use `D2(R)=Σ(β−1/2)^2` as the local off-seam detector.
- Random path: local soft spots are probabilistic predictors -> probabilistic seismic hazard analysis -> propagation of source-model and ground-motion-model uncertainties into final risk estimates.
- Method: `17 = change representation`.
- Result: source and ground-motion uncertainties both changed the NODE risk tail (`both q99=7.9220`, `P(risk>3)=0.1075`). Transferred to `D2`, a clear interior off-seam pair had false-seam probability `0.004`; boundary-membership uncertainty raised it to `0.420`, near-threshold measurement uncertainty to `0.437`, and both uncertainties to `0.673`.
- Status: `[EXPERIMENTAL FINDING / SOURCE-WIDTH TOMOGRAPHY GATEKEEPER]`. A local `D2` certificate needs an uncertainty-deaggregation passport: point `D2`, quantiles, false-seam probability, and source-membership vs measurement/quadrature contributions. Guard bands and side-neutrality do not by themselves propagate uncertainty into the seam verdict.
- Artifacts: `computations/2026-06-21-conway-clean-r52-d2-uncertainty-deaggregation.py`, `computations/2026-06-21-conway-clean-r52-d2-uncertainty-deaggregation.txt`.

## Clean Finding 53/100 - Observation-action coupling passport

- ResearchNode: GPT topic `#60 Gatekeeper completeness`.
- Random path: uncertainty propagation -> agent-based contagion models in epidemiology -> symptom status affects both detectability and behavior.
- Method: `13 = find a monotone quantity`.
- Result: in the NODE, symptom-linked behavior made detected cases progressively less representative (`reduction=0.75`: true `R=2.874`, detected `R=1.775`, hidden `R=3.826`). Transferred to event gatekeepers, passive event persistence stayed stable (`passive_lag≈0.197--0.203`), while active detector response drove active lag from `0.1984` to `-0.0195`; the active/passive gap grew monotonically `0.0000 -> 0.2229`.
- Status: `[EXPERIMENTAL FINDING / GATEKEEPER-COMPLETENESS PASSPORT]`. Add an observation-action coupling passport: run the detector in passive-shadow mode, sweep response/intervention strength, and require the claimed invariant to be stable. Sampling-retention alone does not catch a gatekeeper that changes the event process it certifies.
- Artifacts: `computations/2026-06-21-conway-clean-r53-observation-action-coupling.py`, `computations/2026-06-21-conway-clean-r53-observation-action-coupling.txt`.

## Clean Finding 54/100 - A/B measure-reference passport

- ResearchNode: GPT topic `#68 Schanuel vs RH independence`.
- Random path: symptom detectability/behavior coupling -> anthropic selection effects in cosmology -> the measure problem can dominate anthropic weighting.
- Method: `16 = use a minimal counterexample`.
- Result: the NODE showed the same observer weighting producing different posteriors under different measures (`0.4545/0.4545/0.0909` vs `0.0112/0.8989/0.0899`). Transferred to A/B axes, all four logical cells were present, yet weights made `P(B|A)` range from `0.0010` to `0.9990`; the coupled-looking measure had `P(B|A)=0.9901`, `P(A|B)=0.9901`, but still positive `A∧¬B` mass `0.004950`.
- Status: `[EXPERIMENTAL FINDING / A-B INDEPENDENCE GATEKEEPER]`. Empirical Schanuel/RH implication claims need a measure/reference-class passport: report all four A/B cells under the chosen ensemble or prove a cell structurally impossible. Down-weighting counterexamples is not implication.
- Artifacts: `computations/2026-06-21-conway-clean-r54-ab-measure-counterexample.py`, `computations/2026-06-21-conway-clean-r54-ab-measure-counterexample.txt`.

## Clean Finding 55/100 - Reciprocal-coordinate sightline passport

- ResearchNode: GPT topic `#2 Reciprocal seam coordinate`.
- Random path: measure dominance -> architectural space-syntax observer-flow bias -> observer height assumptions silently privilege standing adult sightlines.
- Method: `1 = split it into subclaims`.
- Result: the NODE toy model showed visibility depends on declared observer height. Transferred to reciprocal moments, finite `γ^{-2k}` weights over the first `160` zeta zeros become sharply low-zero dominated: `k=1` first-zero share `0.2413`, effective count `11.58`, `139` zeros for `99%`; `k=4` first-zero share `0.9466`, effective count `1.11`, `3` zeros for `99%`; `k=8` first-zero share `0.9981`, effective count `1.00`.
- Status: `[EXPERIMENTAL FINDING / RECIPROCAL-CHART GATEKEEPER]`. Finite `T_k`/reciprocal-moment evidence needs a sightline passport: contribution shares by height band, effective zero count, and tail coverage. The reciprocal chart is canonical, but high-order finite evidence mostly sees the first few zeros.
- Artifacts: `computations/2026-06-21-conway-clean-r55-reciprocal-sightline.py`, `computations/2026-06-21-conway-clean-r55-reciprocal-sightline.txt`.

## Conway Clean Finding 56/100 — survivor-spine reroute passport `[FIND / gatekeeper]`

- ResearchNode: GPT topic `#52 Survivor spines`.
- Random path: observer-height sightline bias -> stochastic crowd-flow modeling in built environments -> NODE `behavioral adaptation to previous failed route attempts, blocked exits, or unexpectedly slow corridors`; method `13 = find a monotone quantity`.
- Evidence: `computations/2026-06-21-conway-clean-r56-survivor-reroute-passport.py` / `.txt`.
- NODE validation: route-adaptation strength monotonically lowered expected blocked-route exposure (`0.4176 -> 0.0420`) while changing the dominant route; path concentration can be policy-induced.
- Finding: survivor-spine evidence needs a reroute passport. In the HT transfer, adaptive penalties can over-concentrate controls: at `sigma=0.5`, `[100,170]`, true adaptive top-share was `0.784`, while finite Euler reached `0.904`; at `sigma=1.2`, `[100,170]`, true and finite collapsed (`top16=0.975/0.974`, `tv16=0.871/0.871`). Thus uniqueness after penalizing failed route bins is not native completed-field descendant geometry unless the passive/adaptive sweep and controls are reported.
- WALK STATE: STEP 1 reseed with RandomNode = `behavioral adaptation to previous failed route attempts, blocked exits, or unexpectedly slow corridors`.

## Conway clean dead end — chart settling-time duplicate `[DEAD END]`

- ResearchNode: GPT topic `#5 Chart discipline`.
- Random path: behavioral-adaptation seed -> `hysteresis in dynamical systems` -> NODE `finite-time observations can confuse long transients with stable hysteretic states`; method `3 = reverse it`.
- NODE validation reused `computations/2026-06-21-hgt-NODE-thermal-transient-false-branch.py` (`false_short_steady_count=3`).
- Verdict: reduces to the prior thermal-transient/steady-branch dead end and the already-established chart passport discipline. The would-be transfer is just “require longer dwell/refinement and reverse-sweep stability before accepting a chart,” not a new admissibility object. Not counted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `finite-time observations can confuse long transients with stable hysteretic states`.

## Conway clean dead end — noise-stationary anisotropy duplicate `[DEAD END]`

- ResearchNode: GPT topic `#26 Jensen/Hankel anisotropy`.
- Random path: finite-time transient seed -> `stochastic resonance and noise-induced transitions` -> NODE `noise can create effective attractors or stationary distributions absent from the deterministic system`; method `16 = use a minimal counterexample`.
- Minimal counterexample: worst-axis radius `0.0500`, safe-axis radius `0.5000`, stationary/noisy sampler median radius `0.4416`, hidden-worst ratio `8.83x`.
- Verdict: duplicate of the anisotropic stability passport already in `docs/consolidated/gpt/10.md` and Penrose's prior finding. A sampling distribution is not a direction-wise Jensen/Hankel certificate. Not counted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `noise can create effective attractors or stationary distributions absent from the deterministic system`.

## Conway Clean Finding 57/100 — forward contour scale-decomposition passport `[FIND / gatekeeper]`

- ResearchNode: GPT topic `#6 Forward contour moments`.
- Random path: noise-created stationary distributions -> `chemical master equations` -> NODE `volume scaling affects both molecule numbers and propensity constants, not just noise magnitude`; method `4 = change the viewpoint`.
- Evidence: `computations/2026-06-21-conway-clean-r57-forward-contour-scale-passport.py` / `.txt`.
- NODE validation: CME volume scaling is not noise-only; a naive bimolecular propensity overstated the correct volume-scaled propensity by `10x`, `40x`, and `160x` at Ω `10`, `40`, and `160`.
- Finding: nested/scaled forward-contour moment evidence needs a scale-decomposition passport. In a completed symmetric toy divisor with direct contour-integral checks, normalized moment changes `N_k(L)=M_k(L)/L^k` could be small because retained-source reweighting and new-source influx cancelled. Example: for `k=2`, scale `2.60`, total normalized change was `+0.2028`, from retained reweighting `+1.9069` plus new-source influx `-1.7041`; for `k=4`, total `-0.4170`, from retained `-1.8691` plus influx `+1.4520`.
- Gatekeeper: report `M_k`, normalized `N_k`, retained-source reweighting, new-source influx, and quadrature error separately before treating scaled/nested contour moments as stable evidence.
- WALK STATE: STEP 1 reseed with RandomNode = `volume scaling affects both molecule numbers and propensity constants, not just noise magnitude`.

## Conway clean dead end — prime-flow peak-location duplicate `[DEAD END]`

- ResearchNode: GPT topic `#42 Prime-flow kill gate`.
- Random path: volume-scaling seed -> `finite-size scaling in statistical physics` -> NODE `peaks in susceptibility, heat capacity, or correlation length ratios scale differently from their locations`; method `22 = compare nearby false statements`.
- Verdict: duplicate. The NODE restates the existing requirement that prime-flow candidates pass separate out-of-sample ordinate and spacing channels against same-capacity decoys with cluster aggregation. Prior work already killed “ordinate fit implies spacing survival” and “internal prime-lane stabilization implies zero-spectrum generation.” Not counted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `peaks in susceptibility, heat capacity, or correlation length ratios scale differently from their locations`.

## Conway Clean Finding 58/100 — survivor-spine chemical-potential tilt passport `[FIND / gatekeeper]`

- ResearchNode: GPT topic `#52 Survivor spines`.
- Random path: peak-location scaling seed -> `cosmological phase transitions` -> NODE `the role of conserved charges and chemical potentials in shifting phase boundaries`; method `19 = write the fake proof`.
- Evidence: `computations/2026-06-21-conway-clean-r58-survivor-tilt-passport.py` / `.txt`.
- NODE validation: a two-phase free-energy toy showed chemical potential shifting the critical temperature (`1.5250 -> 0.4750`) and changing the selected phase at fixed `T=1.0`.
- Finding: survivor-spine evidence needs an ensemble-tilt passport. With `p(bin) ∝ success(bin) * exp(λ * standardized_reserve(bin))`, a positive reserve tilt over-concentrated controls: at `σ=0.5`, `[100,170]`, `λ=2`, true top-share was `0.444` (`tv=0.679`), while finite Euler reached `0.741` (`tv=0.767`). In the right strip, true/finite collapsed (`top-share=0.634/0.634`, `tv=0.720/0.718`). Opposite tilts selected different true spines in the same window.
- Gatekeeper: report neutral, positive-tilt, and negative-tilt survivor distributions, with top-share, entropy, TV shift, finite/random controls, and right-strip collapse. Uniqueness under an undeclared reserve tilt is ensemble structure, not native descendant geometry.
- WALK STATE: STEP 1 reseed with RandomNode = `the role of conserved charges and chemical potentials in shifting phase boundaries`.

## Conway clean dead end — thermal marginal regularization duplicate `[DEAD END]`

- ResearchNode: GPT topic `#27 Regularization fidelity`.
- Random path: chemical-potential seed -> `black hole thermodynamics` -> NODE `the information paradox is not resolved merely by saying Hawking radiation is thermal`; method `13 = find a monotone quantity`.
- Verdict: duplicate of the established Jensen/Hankel fidelity gate. The monotone ridge/noise-floor margin can certify only the modified object unless full object-fidelity and congruence data are supplied. The “thermal marginal is not enough” metaphor adds no new gate. Not counted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `the information paradox is not resolved merely by saying Hawking radiation is thermal`.

## Conway clean dead end — Berry scaling-convention duplicate `[DEAD END]`

- ResearchNode: GPT topic `#58 Berry switch`.
- Random path: information-paradox seed -> `random matrix theory` -> NODE `correctly specifying the scaling convention for matrix entries before comparing limiting laws`; method `15 = strengthen the conjecture`.
- Verdict: duplicate. Requiring lane scaling/normalization conventions is valid, but it reduces to the existing Berry lane-switch result and known rest-frame/coarse-graining hygiene. Not counted.
- WALK STATE: dead end -> STEP 1 reseed with RandomNode = `correctly specifying the scaling convention for matrix entries before comparing limiting laws`.

## Conway Clean Finding 59/100 — cross-lane feedback-deconvolution passport `[FIND / gatekeeper]`

- ResearchNode: GPT topic `#47 Cross-lane kernel`.
- Random path: matrix-scaling seed -> `cosmology: primordial fluctuation spectra` -> NODE `baryonic feedback alters late-time small-scale power, complicating reconstruction of primordial fluctuations`; method `13 = find a monotone quantity`.
- Evidence: `computations/2026-06-21-conway-clean-r59-cross-lane-feedback-deconvolution.py` / `.txt`.
- NODE validation: feedback strength monotonically suppressed small-scale power (`1.0000 -> 0.2200`) and shifted inferred tilt (`0.0000 -> -0.5879`) if not deconvolved.
- Finding: cross-lane kernel claims need a feedback-deconvolution passport. In a synthetic no-native-coupling lane field, feedback inflated observed off-diagonal mass from native `0.002862` to `0.014867` at `α=0.6`; deconvolution recovered `0.002862`, but condition number rose to `44.067`. In phase-event lanes, feedback drifted observed masses for true/finite/random while deconvolution recovered native masses when the operator was known.
- Gatekeeper: report raw observed `K`, feedback operator/admissible feedback family, deconvolved `K`, and condition number/noise amplification. This is separate from common-time-field conditioning: it is downstream lane-space transfer.
- WALK STATE: STEP 1 reseed with RandomNode = `baryonic feedback alters late-time small-scale power, complicating reconstruction of primordial fluctuations`.

## Conway operational correction — passport saturation / proof-route filter

- User correction: too many passport/gatekeeper outputs indicate the run is stuck.
- New ResearchNode repository: `docs/consolidated/revision01/proof-route.md`.
- Counted findings must now directly advance the proof route: `T_k` Stieltjes positivity, all-order Hankel PSD, explicit-formula/weld-to-positivity bridge, all-window `D_2=0`, or source-built `κ_-=0`.
- The just-logged cross-lane feedback-deconvolution item is demoted/quarantined and not counted because it is another instrumentation passport, not proof-route progress.

### Dead end — dynamical-zeta space ambiguity / finite-prefix Hankel no-margin

- Status: **not counted** under the proof-route filter; not posted to chat.
- ResearchNode: actual reciprocal seam moments `T_k` Stieltjes (`docs/consolidated/revision01/proof-route.md`).
- Random NODE: dynamical zeta functions, item 20: same formal Euler product can represent different analytic objects depending on the Banach/anisotropic space.
- Test artifact: `computations/2026-06-21-conway-proofroute-dynamical-zeta-space-ambiguity.py`.
- Outcome: hidden non-real conjugate atoms can be nearly invisible to a finite moment prefix while eventually breaking Hankel positivity.
- Verdict: reduces to the known all-order/no-margin obstruction; useful as a warning, not as a new research finding.

### Dead end — fractal-string lattice/nonlattice screens vs all-window `D_2`

- Status: **not counted** under the proof-route filter; not posted to chat.
- ResearchNode: prove `D_2(R)=0` for every window.
- Random NODE: fractal strings and complex dimensions, item 7: lattice/nonlattice self-similar strings have different complex-dimension patterns.
- Attempted transfer: use screen/window formalism to shrink the all-window burden to a certified basis/exhaustion.
- Prior overlap: rectangle-basis support testing already appears in `docs/proofing/08-b1-source-measure-bridge.md`; `D_2` additivity and the local-to-global accumulator are already verified in `computations/2026-06-21-connes-moment-additivity-invariance.py`.
- Verdict: reduces to known additivity/basis facts, while lattice/nonlattice itself belongs to value-arithmetic rather than source-width confinement.

## Clean Finding 59/100 — hard-edge boundary-extension obstruction for source-built `kappa_-`

- Status: **counted** under the proof-route filter; posted to chat.
- ResearchNode: source-built faithful negative index `kappa_-` (`docs/consolidated/revision01/proof-route.md`).
- Random NODE: random matrix theory beyond GUE → hard-edge beta/Bessel limits, where boundary conditions materially affect the operator/law.
- Test artifact: `computations/2026-06-21-conway-rmt-hard-edge-boundary-kappa.py`.
- Result: a fixed positive hard-edge inverse-square bulk form changed from `kappa_-=0` to `kappa_-=1` under only a rank-one boundary extension. Exact threshold: `B+alpha vv^T` is PSD iff `1+alpha <v,B^{-1}v> >= 0`; in the run `alpha_c=-1.3235547864e+04`, with inertia `(0,1,79)` at threshold and `(1,0,79)` just beyond.
- Proof-route meaning: the source-built `kappa_-` object must include the completed archimedean/Gamma/pole boundary extension or prove extension-independent congruence. The explicit-formula bulk kernel alone does not define the faithful index.
- Novelty audit: extends the existing congruence/Sylvester discipline from reporter transformations to operator-domain/boundary-extension ambiguity at fixed bulk; direct obstruction for Master-2 `kappa_-`, not a phase/holonomy passport.

## Clean Finding 60/100 — finite-rank boundary Schur reduction for source-built `kappa_-`

- Status: **counted** under the proof-route filter; posted to chat.
- ResearchNode: source-built faithful negative index `kappa_-`.
- Follow-up to hard-edge boundary-extension obstruction.
- Theorem shape: for `B>0`, boundary channels `V`, and invertible Hermitian boundary matrix `C`,
  `inertia(B+VCV*)=inertia(B)+inertia(-C^{-1}-V*B^{-1}V)-inertia(-C^{-1})`.
  If `C<0`, then `kappa_-(B+VCV*)=kappa_-(-C^{-1}-V*B^{-1}V)`.
- Test artifact: `computations/2026-06-21-conway-boundary-schur-kappa-reduction.py`.
- Result: four boundary channels crossed one by one; full 70-dimensional inertia and 4-dimensional boundary-Weyl prediction gave negative counts `0,1,1,2,2,3,3,4` at the tested scales.
- Proof-route meaning: after a positive source-built bulk is obtained, the remaining `kappa_-=0` proof can be stated as a completed boundary Weyl PSD theorem for the Gamma/pole/archimedean extension. Bulk-only source data are insufficient; boundary data are not decoration.

## Clean Finding 61/100 — shifted reciprocal-seam positivity is strict; singular Schur branches are finite-flat artifacts

- Status: **counted** under the corrected proof-route filter; posted to chat.
- Active proof-route source: `docs/consolidated/gpt/proof-route.md`.
- ResearchNode: shifted reciprocal-seam square-test positivity for `H_d^(0)=[T_{i+j+1}]` and `H_d^(1)=[T_{i+j+2}]`.
- Random NODE: Schur complements of Hankel matrices in Stieltjes moment problems, item 17: generalized inverse/range-inclusion conditions in singular Schur complements.
- Method: strip to essentials.
- Finding: if the shifted Stieltjes theorem holds for the actual `xi` sequence, finite shifted Hankel blocks should be **positive definite**. A singular block is the finite-atomic/flat-extension branch; it would force a finite recurrence/rational shifted moment generating function, incompatible with the infinite reciprocal zero divisor.
- Test artifact: `computations/2026-06-21-conway-shifted-schur-strictness.py`.
- Evidence: finite 3-atom support hit zero Schur complements at rank; infinite toy support and observed zeta reciprocal atoms stayed strict through `d=5` for both shifted towers, though the zeta Schur values were extremely small.
- Proof-route meaning: target ordinary positive Schur complements / conditional variances in the shifted square-test calculus. Generalized inverses and range-inclusion are truncation/numerical hygiene or finite-flat countermodels, not part of the final infinite-divisor theorem.

### Dead end — Schur/Carathéodory Toeplitz route vs shifted square-test Hankel positivity

- Status: **not counted** under the corrected proof-route filter; not posted to chat.
- ResearchNode: derive `Q_0/Q_1` from the fused explicit-formula expression.
- Random NODE: Schur algorithm / Carathéodory functions, item 4: unit-circle moment positivity is Toeplitz positivity, not Hankel positivity.
- Prior overlap: the corpus already separates the unit-circle CMV/Toeplitz face from the reciprocal-seam Hankel/Stieltjes face, including a Stieltjes-Hankel-positive but Toeplitz-negative witness `a_n=1+4^n`.
- Verdict: Schur/Carathéodory positivity does not by itself derive shifted square-test positivity. A positivity-preserving transform from circle Toeplitz data to shifted Hankel localizing matrices would be the missing bridge, not a consequence of this NODE.

## Clean Finding 62/100 — congruence-normalized RKHS kernels for the shifted square-test forms

- Status: **counted** under the corrected proof-route filter; posted to chat.
- Active proof-route source: `docs/consolidated/gpt/proof-route.md`.
- ResearchNode: define finite certificates for `Q_0/Q_1`.
- Random NODE: RKHS moment positivity certificates, item 8: kernel normalization changes conditioning without changing the abstract RKHS.
- Definition: for `r=1,2`, `H_r(d)=[T_{i+j+r}]` and `K_r(d)_{ij}=T_{i+j+r}/sqrt(T_{2i+r}T_{2j+r})`. Then `K_r=D^{-1}H_rD^{-1}`, so PSD/PD is exactly preserved. `K_r` is the unit-diagonal RKHS Gram kernel for normalized monomial square tests.
- Test artifact: `computations/2026-06-21-conway-shifted-square-rkhs-normalization.py`.
- Evidence: on first 90 observed zeta reciprocal atoms through `d=6`, raw shifted Hankel determinants had `log10 det` down to `-139` and `-161`, while the congruence-normalized kernels preserved positivity with unit diagonal and positive Cholesky pivots. This separates monomial norm growth from the square-test positivity question without changing the object.
- Proof-route meaning: finite `Q_0/Q_1` certificates should report the exact normalized kernels `K_1,K_2` / their Cholesky pivots, not raw determinant volume; this is a route-specific definition of the shifted square-test calculus.

## Conway Clean Finding 63/100 — admissible unshifted form-domain is exactly `Q_1` `[FIND / proof-route theorem]`

- Active source: `docs/consolidated/gpt/proof-route.md`; accepted under the shifted square-test proof-route filter.
- GPT ResearchNode draw: `57/70 Phase-space lift`; used only as entropy seed because phase/passport output is no longer countable unless it advances the proof route.
- Workflow path: RandomNode `kernel normalization changes conditioning without changing the abstract RKHS` -> broad topic `martingale measure changes in finance` -> NODE `the market price of risk process must satisfy integrability/admissibility conditions, not just be formally written as a ratio`; method `18 = look for the right theorem`.
- Finding: the raw unshifted reciprocal-seam form `U[p]=sum_rho m_rho p(y_rho)^2` has canonical finite polynomial domain `y R[y]`, since `p(0) != 0` makes the summands fail to tend to zero as `y_rho -> 0` along infinitely many zeros. Under `p=yq`, the restricted form is exactly `Q_1[q]=sum_{i,j} c_i c_j T_{i+j+2}`.
- Consequence: the restricted-domain repair of the invalid `T_0` tower is not a third independent object. It is precisely one of the two shifted square-test forms already required by the proof route. Any full-domain extension to constants needs an externally specified finite part for `T_0`, and that finite part can change inertia.
- Evidence: `computations/2026-06-21-conway-admissible-domain-q1.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/reciprocal-seam-admissible-domain-q1.md`.
- Count: accepted proof-route findings after passport correction = `13/50`.

## Conway Clean Finding 64/100 — finite `T_0` repairs fail all-order by divergent Schur thresholds `[FIND / proof-route theorem]`

- Active source: `docs/consolidated/gpt/proof-route.md`; Step-12 follow-up to Finding 63.
- Claim: in a compact reciprocal Stieltjes model with infinite total mass and finite positive moments, no finite value of `T_0` can make the unshifted Hankel tower PSD at all orders. Finite-order Schur lower bounds for `T_0` must diverge.
- Proof idea: a finite all-order PSD extension would give a finite representing measure `nu`. Since `y nu` and the source measure `y mu` have the same compact Hausdorff moments, `y nu=y mu`; division by `y` on `(0,R]` forces `nu=mu`, contradicting infinite total mass.
- Schur certificate: PSD of `[[a,b_d^T],[b_d,C_d]]` requires `a >= b_d^T C_d^{-1}b_d`; the thresholds cannot stay bounded. For the toy `y_n=1/n^2`, symbolic computation gives `a_d=d(2d+3)/2`, so every finite `T_0^ren` fails at some degree.
- Evidence: `computations/2026-06-21-conway-t0-schur-threshold-divergence.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/finite-t0-schur-threshold-divergence.md`.
- Count: accepted proof-route findings after passport correction = `14/50`.

## Conway dead end — no-arbitrage lower/upper asymmetry vs shifted square tests `[DEAD END]`

- GPT topic draw: `49/70 Low-reserve co-failure`; external topic `no-arbitrage bounds in incomplete markets`; NODE `lower bound is often the negative of the upper bound for the negative payoff`; method `7 = strip to essentials`.
- Essence: lower/upper duality depends on sign-symmetry of the admissible strategy cone.
- Proof-route transfer failed: `Q_0/Q_1` are square-test forms and already invariant under `p -> -p`; treating them as lower/upper sign-duals is a category error. The only valid route warning reduces to the already-known all-order independence of the two shifted barriers.
- Not counted.

## Conway dead end — masonry out-of-plane coupling vs forward contour moments `[DEAD END]`

- GPT topic draw: `6/70 Forward contour moments`; external topic `architectural limit analysis of masonry structures`; NODE `out-of-plane instability coupled to in-plane load paths`; method `15 = strengthen`.
- Transfer: strengthen contour certification from count/center data to coupled second-width data.
- Verdict: reduces to existing `M_0/M_1` blindness and the local `D_2` source-width discriminator already documented in the consolidated GPT notes and prior logs. Not counted.

## Conway Clean Finding 65/100 — FE-symmetric off-line quartet fails both shifted degree-one minors `[FIND / proof-route theorem]`

- GPT topic draw: `40/70 Davenport-Heilbronn gate`; external topic `percolation thresholds in load-bearing networks`; NODE `local stress concentrations near defects or boundaries dominate collapse before nominal connectivity threshold`; method `1 = split into subclaims`.
- Theorem: for a single FE/conjugation-symmetric off-line quartet `w=±a±iγ`, with reciprocal coordinate `y=-1/w^2` and `T_k=sum y^k`,
  `det[[T1,T2],[T2,T3]]=-64a^2γ^2/(a^2+γ^2)^6` and
  `det[[T2,T3],[T3,T4]]=-64a^2γ^2/(a^2+γ^2)^8`.
- Consequence: every off-line quartet with `aγ != 0` fails both corrected shifted degree-one Hankel tests. At `a=0` the quartet becomes on-line and the determinants are zero/rank-one PSD.
- Evidence: `computations/2026-06-21-conway-dh-quartet-shifted-hankel.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/fe-offline-quartet-shifted-minor-obstruction.md`.
- Count: accepted proof-route findings after passport correction = `15/50`.

## Conway dead end — directed-polymer endpoint/path split vs A-axis separation `[DEAD END]`

- GPT topic draw: `61/70 A-axis separation`; external topic `directed polymers in random media`; NODE `endpoint fluctuations versus path fluctuations need not scale identically`; method `13 = find a monotone quantity`.
- Transfer: endpoint/path split mirrors divisor arithmetic vs divisor geometry.
- Verdict: reduces to the current reorientation: HT/value axis is arithmetic, RH/positivity axis is geometry. No new detector or proof-route theorem. Not counted.

## Conway dead end — directed-polymer rare paths vs canonical object `[DEAD END]`

- GPT topic draw: `1/70 Canonical object`; external topic `directed polymers in random media`; NODE `rare favorable paths lower the quenched free energy`; method `13 = find a monotone quantity`.
- Transfer: finite/proxy averages can miss rare divisor defects.
- Verdict: reduces to canonical completed-divisor discipline and the local off-line quartet shifted-minor obstruction already found. Not counted.

## Conway dead end — bet-hedging preparation cost vs contour certification `[DEAD END]`

- GPT topic draw: `8/70 Contour certification`; external topic `bet-hedging in microbial populations`; NODE `cost paid by prepared phenotypes during common nonstress state`; method `2 = attack as false`.
- Transfer: guard-band/certification steps have exclusion or object-modification costs.
- Verdict: reduces to known collar-clearance and regularization-fidelity gates; not a proof-route theorem. Not counted.

## Conway dead end — standby sensory responsiveness vs value-axis ergodicity `[DEAD END]`

- GPT topic draw: `65/70 Value-axis ergodicity passport`; external topic `biological standby metabolism`; NODE `dormant cells retain sensory responsiveness despite appearing inactive`; method `5 = make it visual`.
- Transfer: random aggregate value-axis searches can miss rare structured shells.
- Verdict: reduces to the existing value-axis ergodicity passport; no new arithmetic detector and no proof-route theorem. Not counted.

## Conway dead end — black-swan redundancy loss vs zero-ordinate arithmetic `[DEAD END]`

- GPT topic draw: `64/70 Zero-ordinate arithmetic`; external topic `black swan early-warning indicators`; NODE `sudden loss of redundancy`; method `17 = change representation`.
- Transfer: corank as redundancy loss among value features.
- Verdict: reduces to existing A-axis corank/value-arithmetic framing; no new detector. Not counted.

## Conway dead end — hidden liquidity/displayed depth vs explicit-formula transfer `[DEAD END]`

- GPT topic draw: `19/70 Explicit-formula transfer`; external topic `market liquidity evaporation`; NODE `hidden/iceberg liquidity withdraws before displayed depth signals stress`; method `1 = split into subclaims`.
- Transfer: scalar or diagonal moment reports can hide failing square-test directions.
- Verdict: reduces to existing pole-cancellation, sectorwise `Q_0/Q_1`, and multiplicity/support guardrails. Not counted.

## Conway dead end — neural-avalanche threshold sensitivity vs prime-flow kill gate `[DEAD END]`

- GPT topic draw: `42/70 Prime-flow kill gate`; external topic `neural avalanches`; NODE `detection threshold changes avalanche distributions`; method `17 = change representation`.
- Transfer: fixed thresholds and same-capacity decoys are required.
- Verdict: reduces to existing prime-flow kill gate methodology; not proof-route progress. Not counted.

## Conway Clean Finding 66/100 — Li coefficients are an infinite Chebyshev-kernel transform of reciprocal seam moments `[FIND / proof-route atlas theorem]`

- GPT topic draw: `20/70 Li chart`; external topic `earthquake aftershock scaling`; NODE `fluid diffusion can create delayed or migrating patterns resembling ordinary Omori decay`; method `8 = look for similar objects`.
- Theorem: for an FE pair `rho=1/2+w`, `rho'=1/2-w`, with `y=-w^{-2}`, the pair Li contribution is
  `L_n(y)=2-2 C_n((4-y)/(4+y))`, where `C_n` is Chebyshev-T. This follows from `q=(w-1/2)/(w+1/2)`, the FE partner `q^{-1}`, and `(q+q^{-1})/2=(4-y)/(4+y)`.
- Consequence: `L_n(0)=0`, so `lambda_n=sum_{k>=1} c_{n,k}T_k` as an absolutely convergent infinite reciprocal-moment kernel for the `xi` divisor. The `lambda_n <-> P_k` transform is finite triangular, but the `lambda_n <-> T_k` chart edge is infinite-tail.
- Evidence: `computations/2026-06-21-conway-li-reciprocal-chebyshev-kernel.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/li-reciprocal-chebyshev-kernel.md`.
- Count: accepted proof-route findings after passport correction = `16/50`.

## Conway Clean Finding 67/100 — Li reciprocal kernel is not coefficientwise positive in the `T_k` basis `[FIND / proof-route atlas theorem]`

- Step-12 follow-up to Finding 66.
- Theorem: for `L_n(y)=2-2C_n((4-y)/(4+y)) = sum c_{n,k}y^k`, the first coefficients are `c_{n,1}=n^2` and `c_{n,2}=-n^2(n^2+2)/12`. Hence every nontrivial Li kernel has a negative coefficient in the reciprocal moment basis.
- Consequence: Li positivity cannot prove shifted `Q_0/Q_1` positivity by a coefficientwise-positive `lambda_n=sum c_{n,k}T_k` transfer. The Li-to-`T_k` bridge is infinite and signed.
- Evidence: `computations/2026-06-21-conway-li-kernel-not-coefficient-positive.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/li-kernel-not-coefficient-positive.md`.
- Count: accepted proof-route findings after passport correction = `17/50`.

## Conway dead end — fBm exact covariance vs global `T_k` positivity `[DEAD END]`

- GPT topic draw: `33/70 Global T_k positivity`; external topic `fractional Brownian motion`; NODE `covariance is exact, not arbitrary`; method `6 = ask what action is happening`.
- Transfer: shifted moments act as exact square-test kernel entries.
- Verdict: reduces to the existing shifted Hankel/RKHS kernel definition. Not counted.

## Conway dead end — fractional-Langevin internal friction vs zero-ordinate arithmetic `[DEAD END]`

- GPT topic draw: `64/70 Zero-ordinate arithmetic`; external topic `fractional Langevin dynamics in protein folding`; NODE `internal friction separate from solvent-mediated memory`; method `18 = look for the right theorem`.
- Transfer: distinguish internal arithmetic relations from external geometric/memory channels.
- Verdict: reduces to existing A-axis separation; no new arithmetic detector. Not counted.

## Conway dead end — anelastic anisotropy vs value-axis ergodicity `[DEAD END]`

- GPT topic draw: `65/70 Value-axis ergodicity passport`; external topic `anelastic relaxation in disordered solids`; NODE `stress-induced anisotropy makes relaxation direction-dependent`; method `12 = find an invariant`.
- Transfer: value-axis coefficient shells need directional coverage.
- Verdict: reduces to existing value-axis ergodicity/shell-coverage passport. Not counted.

## Conway dead end — cosmic-web vs CMB anisotropy and integer-vs-zero divisor split `[DEAD END]`

- GPT topic draw: `18/70 Integer-vs-zero divisor split`; external topic `cosmic web anisotropy analogies`; NODE `distinguish cosmic-web anisotropy from CMB anisotropy`; method `1 = split into subclaims`.
- Transfer: distinguish integer-divisor positivity from zero-divisor positivity.
- Verdict: reduces to note-14/FID RH-empty split and existing support-transport endpoint passport. Not counted.

## Conway dead end — Turing anisotropic diffusion vs contour certification `[DEAD END]`

- GPT topic draw: `8/70 Contour certification`; external topic `Turing patterns and symmetry breaking`; NODE `anisotropic/cross-diffusion changes instability`; method `15 = strengthen`.
- Transfer: direction-aware certification is required.
- Verdict: reduces to existing contour side-stratification and Jensen/Hankel anisotropy passports. Not counted.

## Conway Clean Finding 68/100 — PS12 FID strict Hankel total positivity is RH-empty `[FIND / formula-graph proof-route negative control]`

- Formula-graph draw: `53/100`, `PS12` from `docs/consolidated/revision01/formulas-graph.md`; no GPT-topic draw used.
- Theorem: `H_FID[i,j]=zeta(2(i+j)+3)=sum_n n^{-3}(n^{-2})^(i+j)` is strictly Hankel totally positive. Every shifted Hankel minor expands by Cauchy-Binet into a positive sum of paired generalized Vandermonde products.
- Consequence: FID is not weak because only principal PSD minors were checked. Even all shifted Hankel minors are automatically positive on the integer divisor, hence RH-empty. The bridge must be an explicit-formula/source-built transfer to the zero reciprocal divisor preserving `Q_0/Q_1`, not a stronger abstract moment-cone certificate.
- Evidence: `computations/2026-06-21-conway-ps12-strict-tp.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/fid-shifted-hankel-strict-total-positivity.md`.
- Count: accepted proof-route findings after passport correction = `18/50`.

## Conway Clean Finding 69/100 — PA9 Turan ratio has a universal Newton floor `[FIND / formula-graph proof-route normalization theorem]`

- Formula-graph draw: `34/100`, `PA9` from `docs/consolidated/revision01/formulas-graph.md`; no GPT-topic draw used.
- Theorem: for positive-divisor elementary-symmetric coefficients, Newton's inequalities force `g_n=a_n^2/(a_{n-1}a_{n+1}) >= (n+1)/n`. The finite `N` floor is `((n+1)/n)((N-n+1)/(N-n))`, and the infinite-support floor is `(n+1)/n`.
- Consequence: the PA9 asymptotic `g(n)-1~c/n` includes a universal `1/n` contribution. Source-specific Turan evidence starts with the de-biased residual `g(n)/((n+1)/n)-1`, or first-order `n(g(n)-1)-1`.
- Evidence: `computations/2026-06-21-conway-pa9-newton-floor.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/pa9-turan-newton-floor.md`.
- Count: accepted proof-route findings after passport correction = `19/50`.

## Conway dead end — TA7 relation-lattice zero vs RH no-margin `[DEAD END]`

- Formula-graph draw: `41/100`, `TA7`; no GPT-topic draw used.
- Transfer: disambiguate prime-log relation-lattice `Lambda=0` from de Bruijn-Newman/RH `Lambda=0`.
- Verdict: reduces to the established free/zero-blind multiplicative wing and A/B axis separation. Pairing the same prime-log lattice with an off-line quartet just reuses Finding 65. Not counted.

## Conway Clean Finding 70/100 — HD3 zero-free gauge shifts log-defined Li coefficients `[FIND / formula-graph proof-route atlas theorem]`

- Formula-graph draw: `91/100`, `HD3`; no GPT-topic draw used.
- Theorem: for `F_c(s)=exp(c(s-1/2)^2)xi(s)`, the divisor is unchanged but the log-defined Li functional shifts by `delta lambda_n=c n^2`.
- Consequence: unnormalized log-defined Li positivity is not HD3-gauge invariant. Li is a zero-divisor chart only after fixing the canonical `xi` representative or subtracting the zero-free Hadamard gauge.
- Evidence: `computations/2026-06-21-conway-hd3-li-gauge-shift.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/hd3-li-gauge-shift.md`.
- Count: accepted proof-route findings after passport correction = `20/50`.

## Conway Clean Finding 71/100 — XF1 direct substitution fails for reciprocal square tests `[FIND / formula-graph bridge obstruction]`

- Formula-graph draw: `95/100`, `XF1`; no GPT-topic draw used.
- Theorem: the proof-route square tests correspond to `h_{r,p}(t)=t^(-2r)p(t^(-2))^2`, `r=1,2`. If `deg(p)=d`, then `h` has a hard-edge pole of order `2r+4d >= 2` at `t=0`; if `ord_0(p)=j`, it decays only like `|t|^-(2r+4j)` at infinity. Thus every nonzero reciprocal square test lies outside the direct standard Weil/Guinand test class.
- Consequence: deriving `Q_0/Q_1` from `XF1` requires a canonical hard-edge regularized limit, not direct substitution. The bridge theorem must control zero-side convergence, archimedean/prime finite parts, and positivity through that limit.
- Evidence: `computations/2026-06-21-conway-xf1-square-test-class.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/xf1-square-tests-outside-weil-class.md`.
- Count: accepted proof-route findings after passport correction = `21/50`.

## Conway Clean Finding 72/100 — PS4 inversion turns HD3 Li gauge into ghost power sums `[FIND / formula-graph atlas theorem]`

- Formula-graph draw: `44/100`, `PS4`; no GPT-topic draw used.
- Theorem: applying the inverse PS4 binomial transform to the HD3 shift `delta lambda_n=c n^2` gives `delta P_1=c`, `delta P_2=-2c`, and `delta P_j=0` for `j>=3`. These are finite differences of the polynomial `n^2`.
- Consequence: a zero-free gauge that moves no zero can still appear as two fake ordinary power sums if unnormalized log-defined Li coefficients are fed into PS4. The Li/power-sum atlas must fix canonical `xi`, use divisor Li, or subtract the zero-free gauge.
- Evidence: `computations/2026-06-21-conway-ps4-gauge-ghost-power-sums.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/ps4-hd3-gauge-ghost-power-sums.md`.
- Count: accepted proof-route findings after passport correction = `22/50`.

## Conway Clean Finding 73/100 — HD1 makes `P_1` a Hadamard finite part `[FIND / formula-graph atlas theorem]`

- Formula-graph draw: `89/100`, `HD1`; no GPT-topic draw used.
- Theorem: HD1 gives `xi'/xi(s)=b+sum_rho[1/(s-rho)+1/rho]`, and `1/(s-rho)+1/rho=-sum_{m>=1}s^m rho^(-(m+1))`. Hence the zero sum contributes no constant term at `s=0`; the first coefficient of `-xi'/xi` is `P_1=-b=1+gamma/2-log(2 sqrt(pi))`, a Hadamard finite part. For `k>=2`, `P_k=sum_rho rho^(-k)` is absolutely convergent by `N(T)=O(T log T)`.
- Consequence: low-order Li/secular comparisons involving `lambda_1` or `P_1` require canonical Hadamard normalization or an equivalent symmetric finite part. The shifted reciprocal seam moments avoid this `P_1` boundary exception.
- Evidence: `computations/2026-06-21-conway-hd1-p1-finite-part.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/hd1-p1-hadamard-finite-part.md`.
- Count: accepted proof-route findings after passport correction = `23/50`.

## Conway Clean Finding 74/100 — `y_rho` makes quartet minors imaginary-defect squares `[FIND / bridge-theorem coordinate theorem]`

- Bridge-theorem RNG draw: inline snippet `46/72`, `y_rho`; source `docs/consolidated/revision01/bridge-theorem.md`.
- Theorem: for a folded conjugate pair `y=u+iv`, `conj(y)=u-iv`, weight `mu`, and moments `T_k=mu(y^k+conj(y)^k)`, the degree-one shifted determinants are `-4 mu^2 |y|^2 (Im y)^2` and `-4 mu^2 |y|^4 (Im y)^2`.
- Specialization: an off-line quartet `w=±a±i gamma` has `y=-(a+i gamma)^(-2)`, `mu=2`, `Im y=2a gamma/(a^2+gamma^2)^2`, recovering the bridge-theorem formulas `-64 a^2 gamma^2/(a^2+gamma^2)^6` and `-64 a^2 gamma^2/(a^2+gamma^2)^8`.
- Consequence: the reciprocal coordinate's local obstruction is exactly the off-axis height `Im y`; near-line or high-zero defects may be numerically tiny but have fixed negative sign.
- Evidence: `computations/2026-06-21-conway-y-plane-quartet-minors.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/y-plane-quartet-minor-imaginary-defect.md`.
- Count: accepted proof-route findings after passport correction = `24/50`.

## Conway Clean Finding 75/100 — source-aware `Q_0` alone forces reciprocal positivity `[FIND / bridge-theorem source-aware sharpening]`

- Bridge-theorem RNG draw: inline snippet `23/72`, `[T_{i+j+1}]_{i,j=0}^d`; source `docs/consolidated/revision01/bridge-theorem.md`.
- Theorem: for the actual folded reciprocal seam divisor with positive multiplicities, all-order positivity of `H_d^(0)=[T_{i+j+1}]_{i,j=0}^d` alone forces every reciprocal atom `y_rho` into `R_{>0}`. Thus source-aware `Q_0[p]>=0` for every real polynomial already implies RH.
- Proof mechanism: write `Q_0[p]=sum_y M_y y p(y)^2`, the quadratic form of the finite complex measure `y dmu_div`. A negative real atom is isolated by real polynomial approximation and contributes `M_a a<0`. A non-real conjugate pair is isolated with phase `zeta` chosen so `Re(a zeta^2)<0`, contributing `2M_a Re(a zeta^2)<0`. Summability of `sum_y M_y |y|` justifies the limiting argument.
- Consequence: `Q_0/Q_1` independence is an abstract, source-forgotten moment-string guardrail. In the source-aware reciprocal-divisor category, the first shifted tower is already faithful; `Q_1` remains a useful Stieltjes-atlas/restricted-domain object but not a logically separate all-order RH implication.
- Evidence: `computations/2026-06-21-conway-q0-source-aware-isolation.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/source-aware-q0-alone-reciprocal-positivity.md`.
- Count: accepted proof-route findings after passport correction = `25/50`.

## Conway Clean Finding 76/100 — `gamma` gives the shifted square-test tail law `[FIND / bridge-theorem finite-certificate theorem]`

- Bridge-theorem RNG draw: corrected inline snippet `63/78`, `gamma = Im rho`; source `docs/consolidated/revision01/bridge-theorem.md`. A prior `1..72` draw was discarded because the current extractor returns 78 snippets.
- Theorem: if `p(y)=y^j q(y)` with `q(0) != 0`, then the high-height absolute tail of `Q_r[p]=sum_rho m_rho y_rho^r p(y_rho)^2` is `O_{p,r}(G^(1-2r-4j) log G)`, where `r=1` gives `Q_0` and `r=2` gives `Q_1`.
- Consequence: `Q_0` with `p(0) != 0` has the slowest tail, `O(G^-1 log G)`. `Q_1` starts at `O(G^-3 log G)`, and every hard-edge zero of `p` at `y=0` improves the exponent by four powers of `G`.
- Proof mechanism: `|y_rho|=|rho-1/2|^-2=O(|gamma_rho|^-2)` in the strip, then dyadic Riemann-von Mangoldt counting gives the tail; the exponent is sharp for absolute tails by the Riemann-von Mangoldt asymptotic.
- Evidence: `computations/2026-06-21-conway-gamma-tail-square-tests.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/gamma-tail-law-shifted-square-tests.md`.
- Count: accepted proof-route findings after passport correction = `26/50`.

## Conway Clean Finding 77/100 — FE orbit quotient carries half-trace moments `[FIND / bridge-theorem orbit atlas theorem]`

- Bridge-theorem RNG draw: inline snippet `28/78`, `[w] = {w, -w}`; source `docs/consolidated/revision01/bridge-theorem.md`.
- Theorem: the even quotient `Phi(z)=Xi(sqrt(z))` has one zero at `z=w^2` per FE orbit `[w]`, with multiplicity `m`, while the bridge reciprocal trace measure uses weight `2m`. If `ell_k=[z^k]log Phi(z)`, then `T_k=-2k(-1)^k ell_k`.
- Consequence: a route through `Xi(sqrt(z))`, secular coefficients, or quotient log derivatives is valid only after the factor-two/sign conversion back to bridge moments. Otherwise every shifted square-test matrix is underweighted by the FE trace factor.
- Evidence: `computations/2026-06-21-conway-fe-orbit-quotient-moments.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/fe-orbit-quotient-half-trace-moments.md`.
- Count: accepted proof-route findings after passport correction = `27/50`.

## Conway Clean Finding 78/100 — `Xi(w)=xi(1/2+w)` fixes the unique reciprocal bridge centre `[FIND / bridge-coordinate guardrail theorem]`

- Bridge-theorem RNG draw: inline snippet `60/78`, `Xi(w)=xi(1/2+w)`; source `docs/consolidated/revision01/bridge-theorem.md`.
- Theorem: an off-centre chart `c=1/2+eps` breaks the reciprocal bridge. For an FE pair `w,-w`, the shifted atoms `-(w-eps)^(-2)` and `-(-w-eps)^(-2)` are equal iff `4w eps=0`, so nonzero zero orbits force `eps=0`. For an RH-line zero `w=i gamma`, the off-centre atom has imaginary part `-2eps gamma/((eps^2-gamma^2)^2+4eps^2 gamma^2)`, hence is non-real whenever `eps gamma != 0`.
- Consequence: the seam-centred completion is load-bearing. Moving the centre before reciprocal squaring destroys both FE folding and the RH-to-positive-real-atoms direction.
- Evidence: `computations/2026-06-21-conway-seam-center-uniqueness.py` / `.txt`; proof card `docs/drafts/pipeline/2-fully-proven/seam-center-unique-for-reciprocal-bridge.md`.
- Count: accepted proof-route findings after passport correction = `28/50`.

## Conway dead end — confluent TP-node determinant transfer to critical-line Xi Wronskians `[DEAD END]`

- ResearchNode: big-picture issue 4, positivity apex / uniform-in-d Hankel-Laguerre no-margin.
- Random topic: total positivity of matrices/kernels; Gantmacher-Krein-Karlin variation-diminishing transforms.
- NODE: multiple nodes in determinant limits; constraint = raw determinant vanishes at Vandermonde rate, while the Vandermonde-normalized confluent derivative determinant has the stable sign.
- Step 9 method: `22 = compare nearby false statements`.
- Transfer: coalescing critical-line `t` nodes in a derivative/evaluation determinant for `Xi_line(t)=xi(1/2+it)`.
- Result: raw determinant slopes were near the classical Vandermonde exponent `6`; wrong exponent normalizations `5` and `7` collapsed or blew up; the correct exponent stabilized to the confluent Wronskian.
- Verdict: reduces to known confluent determinant calculus. Not counted.

## Conway dead end — zeta derivative-jet Gram conditioning is shift/rank evidence `[DEAD END]`

- ResearchNode: big-picture issue 5, value apex / Schanuel-for-prime-logs.
- Random topic: Gram matrices in Hilbert spaces.
- NODE: positive definiteness of all finite Gram matrices for kernels; constraint = universal finite-subset PSD, not pairwise checks.
- Step 9 method: `1 = split into subclaims`.
- Transfer: L2 Gram of continuum derivative-jet functions `d^j/dsigma^j log xi(sigma+it)` on a critical-strip window.
- Result: pairwise correlations missed multi-jet conditioning; prefix condition rose to `1.04e4` at six jets.
- Verdict: reduces to finite Gram conditioning / shift-derivative rank evidence. It does not access algebraic independence beyond Baker or Schanuel-for-prime-logs. Not counted.

## Conway dead end — affine passport vs generated lattice index (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` lens 6, affine confinement.
- NODE: monodromy connectedness requires transitivity of the generated action; local cycle passport is insufficient.
- Transfer tested: finite exponent clouds with fixed affine passport `P(S)=(|S|,ΣS)` but different generated difference-lattice index.
- Computation: `computations/2026-06-21-conway-transfer-affine-passport-lattice-index.py` / `.txt`.
- Result: same passport `(3,(1,2))` admits index-1 and index-2 difference lattices; as a `(Z/2Z)^2` action, one orbit is all four points and the other has two points.
- Verdict: DEAD END. Reduces to elementary lattice/Smith-normal-form data plus the already-known finite affine-passport blindness. Not counted and not posted as a finding.

## Conway dead end — finite-height positivity averages versus no-margin traps (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` main unsolved issue 4, positivity apex.
- NODE: finite-time and ensemble averages need not agree in ergodic traps; slow mixing keeps trajectory averages biased on finite windows.
- Transfer tested: continuum height/scale positivity observable with a localized sign-changing no-margin trap.
- Computation: `computations/2026-06-21-conway-transfer-finite-height-positivity-traps.py` / `.txt`.
- Result: above the pointwise-failure boundary, all finite-window means remained positive while pointwise minima were negative.
- Verdict: DEAD END. Reduces to the known finite-window/all-scale distinction and prior no-margin/one-scale smoothing gatekeepers. Not counted and not posted as a finding.

## Conway dead end — prime-log monomial-window anisotropy (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` Conjecture A, value/arithmetic apex.
- NODE: hidden anisotropy of rectangular/grid-oriented finite averaging windows.
- Transfer tested: finite monomial exponent windows in prime-log relation search.
- Computation: `computations/2026-06-21-conway-transfer-prime-log-window-anisotropy.py` / `.txt`.
- Result: rectangular and total-degree exponent cutoffs are direction-biased; an L2 exponent ball is nearly direction-neutral in the tested radius.
- Verdict: DEAD END. Reduces to finite relation-search geometry and the already-banked finite corank-window/domain-boundary warnings. Not counted and not posted as a finding.

## Conway dead end — support-stratified prime-log residuals (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` main unsolved issue 5, value apex.
- NODE: sex/dosage stratification is required for rare-variant effect estimates.
- Transfer tested: pooled versus support-stratified finite residual search for degree-2 prime-log monomials.
- Computation: `computations/2026-06-21-conway-transfer-prime-log-support-strata.py` / `.txt`.
- Result: pooled minima were smaller than stratum minima for both actual prime logs and generic controls; a planted relation was only certified when its stratum was isolated.
- Verdict: DEAD END. Reduces to finite relation-search geometry/coverage and does not move the Schanuel-for-prime-logs apex. Not counted and not posted as a finding.

## Conway dead end — ordered holonomy versus aggregate amplitude (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` lens 2, transport not amplitude.
- NODE: static aggregate graph connectivity differs from temporal contact reachability.
- Transfer tested: noncommuting connection increments with identical aggregate generator but different path-ordered holonomy.
- Computation: `computations/2026-06-21-conway-transfer-ordered-holonomy-vs-aggregate.py` / `.txt`.
- Result: same aggregate generator, different downstream holonomy channel.
- Verdict: DEAD END. Reduces to the existing non-scalar holonomy / refinement-history invariance gate. Not counted and not posted as a finding.

## Conway dead end — Master chart injectivity toy (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` Master Conjecture.
- NODE: global shape coordinates require embedding/injectivity, not only smooth local parameters.
- Transfer tested: folded scalar transport charts can identify states with different faithful-index face.
- Computation: `computations/2026-06-21-conway-transfer-master-chart-injectivity.py` / `.txt`.
- Result: folded charts produce index-conflicting collisions; resolved chart does not.
- Verdict: DEAD END. Reduces to the existing Master identification-bridge kill condition and prior chart/proxy object-identity gates. Not counted and not posted as a finding.

## Conway dead end — measured density versus faithful index (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` lens 4, faithful index not measured density.
- NODE: `+1/2` and `-1/2` liquid-crystal defects have equal absolute defect scale but opposite signed harmonic channels.
- Transfer tested: scalar eigenvalue-density summaries versus Sylvester negative index.
- Computation: `computations/2026-06-21-conway-transfer-density-vs-faithful-index.py` / `.txt`.
- Result: scalar density summaries do not determine negative index; the reverse also fails.
- Verdict: DEAD END. Reduces to the already-known and formalized faithful-index/Sylvester-inertia distinction. Not counted and not posted as a finding.

## Conway dead end — Gauss-Newtonized affine part misses seam curvature (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` lens 6, affine confinement.
- NODE: full Hessian versus Gauss-Newton/Fisher approximations in saddle regions.
- Transfer tested: PSD retained affine part plus dropped signed off-line curvature window.
- Computation: `computations/2026-06-21-conway-transfer-affine-gn-misses-seam-curvature.py` / `.txt`.
- Result: retained PSD part never sees negative curvature; sign failure appears only in the residual curvature term.
- Verdict: DEAD END. Reduces to the existing affine-confinement / phase-cancellation-crux curvature-window corpus. Not counted and not posted as a finding.

## Conway dead end — visible seam ridge versus singular-projection witness (2026-06-21)

- Workflow source: `logs/experiments/workflow-topics.md`; ResearchNode from `docs/consolidated/revision01/big-picture.md` lens 5, two orthogonal axes.
- NODE: mistaken identification of a fold catastrophe with any sharp high-intensity line.
- Transfer tested: a sharp continuum seam ridge is positivity/localization-bearing only if it has a singular-projection/preimage-change witness.
- Computation: `computations/2026-06-21-conway-attempt11-step8/01.py` / `.txt`.
- Result: visual sharpness flagged both the regular weld ridge and the fold toy; only the fold toy had the preimage jump.
- Verdict: DEAD END. Reduces to the existing two-axis anti-conflation principle and the Master identification-bridge kill condition. Not counted and not posted as a finding.

## Professor dead end — zero-wealth absorbing boundary vs Christoffel/Uvarov front (2026-06-23)

- Workflow source: `logs/experiments/workflow-general.md`, using last RandomNode `granular segregation`.
- Entropy seed recorded by `scripts/rng seed`: `3845766000613800379`.
- Step 1 cold prompt produced wide topic list; RNG picked item 13: `Wealth condensation in econophysics models`.
- Step 3 cold prompt produced missed-detail list; RNG picked item 2: `The zero-wealth absorbing boundary`.
- NODE constraint: in yard-sale wealth exchange, stake is proportional to `min(w_i,w_j)`, so an agent at exact zero cannot stake and the zero boundary is absorbing unless an explicit floor/redistribution rule is added.
- NODE experiment: compare absorbing, tiny-floor, and redistribution variants; Step 9 method RNG picked method 10, `Test extreme cases`.
- Computations: `computations/2026-06-23-wealth-zero-boundary-node.py`, `computations/2026-06-23-wealth-zero-boundary-node-runpod.txt`, `computations/2026-06-23-wealth-zero-boundary-node-extremes-runpod.txt`; RunPod copies under `/root/hgt-shared/computations/`.
- Result: absorbing boundary revived seeded-zero agents `0/24` and developed high near-zero mass / high Gini; tiny floor or redistribution revived `24/24`; aggressive exchange drove near-total condensation; strong redistribution killed condensation. This confirms the NODE constraint and its boundary cases.
- Transfer tested: use the zero-boundary/floor distinction to rescue the earlier `granular segregation x Christoffel functions` bridge by interpreting Uvarov point-mass update as a discrete boundary correction beyond continuum segregation.
- Verdict: DEAD END for novelty. The NODE result is expected from the yard-sale boundary. The transfer reduces to known boundary/floor regularization plus Uvarov/Sherman-Morrison and Christoffel support estimation; no nonstandard `T` was produced. Not counted as a finding.

## Professor dead end — pre-crisis shadow of post-crisis escape channel (2026-06-23)

- Workflow source: `logs/experiments/workflow-general.md`, continuing from last RandomNode `zero-wealth absorbing boundary`.
- Entropy seed recorded by `scripts/rng seed`: `691829661222804965`.
- Step 1 cold prompt produced wide topic list; RNG picked item 10: `Basin-boundary crises in chaotic dynamical systems`.
- Step 3 cold prompt produced missed-detail list; RNG picked item 1: `Pre-crisis chaotic transients that already shadow the post-crisis escape route`.
- NODE constraint: a post-crisis escape channel is already visible geometrically in pre-crisis bounded dynamics as near-hits to the would-be hole / chaotic saddle channel.
- NODE experiment: logistic map near the invariant-interval crisis. For `r_post=4.01`, the hole around `x=1/2` maps outside `[0,1]`; for `r_pre=3.99`, bounded orbits can still approach that would-be hole. Compare pre-crisis minimum distance to the post-crisis hole against post-crisis escape time, with a same-width control interval.
- Computation: `computations/2026-06-23-basin-crisis-shadow-node.py`, `computations/2026-06-23-basin-crisis-shadow-node-runpod.txt`; RunPod copies under `/root/hgt-shared/computations/`.
- Result: all `8000/8000` post-crisis samples escaped within the cap. Spearman correlation between pre-crisis minimum distance to the post-crisis hole and post-crisis escape time was `0.207839`; same-width control interval correlation was `-0.0406032`. Mean escape time rose from about `25` in closest-hole bins to about `33` in farthest-hole bins; control bins did not show that monotone structure.
- Source reduction: this is aligned with classical crisis / transient-chaos theory (Grebogi-Ott-Yorke; crisis-induced intermittency; chaotic saddles retaining destroyed-attractor geometry).
- Transfer attempts: (1) de Bruijn-Newman heat flow, where pre-critical zero geometry shadows post-flow off-line escape; (2) Jensen/Laguerre hyperbolicity deformation; (3) reciprocal Hankel/Krein index crossing. All reduce to existing de Bruijn-Newman / Jensen / `s_d`-Krein wall structures.
- Verdict: DEAD END for novelty. The NODE experiment is real and workflow-faithful, but the transfer lands in known structures. Not counted as a finding.

## Professor dead end — noise-induced premature escape from repelling slow manifolds (2026-06-23)

- Workflow source: `logs/experiments/workflow-general.md`, continuing from last RandomNode `pre-crisis chaotic transients that already shadow the post-crisis escape route`.
- Entropy seed recorded by `scripts/rng seed`: `2735874861708935950`.
- Step 1 cold prompt produced wide topic list; RNG picked item 2: `Canard explosions in slow-fast biochemical oscillators`.
- Step 3 cold prompt produced missed-detail list; RNG picked item 17: `Noise-induced premature escape from repelling slow manifolds`.
- NODE constraint: noise kicks trajectories off a repelling slow manifold before the deterministic trajectory would visibly escape; escape coordinate is controlled by accumulated repulsion and the logarithm of the noise scale.
- NODE experiment: linearized slow-fast normal model `dy/dt=eps`, `dX=y X dt + sigma dW`, with escape at `|X|>=threshold`. Prediction: `y_escape ~ sqrt(2 eps log(threshold/sigma))`.
- Computation: `computations/2026-06-23-canard-noise-escape-node.py`, `computations/2026-06-23-canard-noise-escape-node-runpod.txt`; RunPod copies under `/root/hgt-shared/computations/`.
- Result: median escape coordinate decreased monotonically as noise increased: `0.356` at `sigma=1e-4`, `0.3214` at `3e-4`, `0.282` at `1e-3`, `0.24` at `3e-3`, `0.1828` at `1e-2`, and `0.0684` at `3e-2`. The logarithmic prediction gave the correct trend and scale, with increasing deviation at large noise where the asymptotics are not expected to be sharp.
- Transfer attempts: (1) de Bruijn-Newman heat-flow coefficient perturbations causing premature hyperbolicity loss near tiny margins; (2) Jensen/Laguerre coefficient noise near root-collision boundary; (3) Krein/Hankel moment noise crossing the scalar Weyl gap with probability controlled by `s_d/(sigma ||grad s_d||)`.
- Verdict: DEAD END for novelty. NODE experiment is real and workflow-faithful, but the transfer reduces to known large-deviation/canard theory and known no-margin / hyperbolicity-boundary perturbation theory. Not counted as a finding.

## Workflow-General Run W4: Nonhyperbolic Escape Algebraic Lifetime Tails

[DEAD END / REDUCES, 2026-06-23]

Workflow continued from last RandomNode `Noise-induced premature escape from repelling slow manifolds`.

- Entropy seed: `279994678386043821`.
- Step 1 cold prompt list, Step 2 RNG: item 11, `Escape from chaotic saddles in transient chaos`.
- Step 3 cold prompt list, Step 4 RNG: item 18, `Escape dynamics may be nonhyperbolic, producing algebraic rather than exponential lifetime distributions`.
- Step 9 scientific-method RNG: method 16, `Use a minimal counterexample`.

NODE constraint: hyperbolic/mixing open systems have exponential-looking survival, while a neutral or nonhyperbolic trapping mechanism can produce algebraic lifetime tails.

Experiment: `computations/2026-06-23-nonhyperbolic-escape-tail-node.py` compares a full-chaos logistic-map control with a small leak against an intermittent neutral-fixed-point map with a leak. It fits survival on both exponential and power-law scales.

RunPod NODE result:

- mixing logistic control: exponential fit `R^2=0.999717`, power-law fit `R^2=0.864772`, exponential slope `-0.016510518`.
- nonhyperbolic intermittent map: exponential fit `R^2=0.709733`, power-law fit `R^2=0.998907`, power-law slope about `-0.9939138`.

Transfer selected by Levenshtein: `nonhyperbolic phase defect escape has algebraic lifetime tail`.

HT transfer result: phase-defect lifetime tails do not produce a true-specific nonhyperbolic signature. In the right strip (`sigma=1.2`), true and finite Euler nearly coincide: true threshold `0.217145`, run count `11`, max run `67`, exponential/power `R^2=0.9432/0.7566`; finite threshold `0.215792`, run count `11`, max run `67`, exponential/power `R^2=0.9325/0.7790`. Random controls have their own short-run tail shapes. In the left strip, differences mostly reflect threshold/autocorrelation and zero-proximity artifacts already seen in earlier recurrence-skeleton runs.

Source reduction: the NODE behavior is classical nonhyperbolic/transient-chaos material; the HT transfer reduces to generic threshold-run/autocorrelation behavior and repeats the prior warning that recurrence or lifetime skeletons are not native HT invariants.

Verdict: DEAD END for novel knowledge. The NODE experiment is clean and reproducible, but no non-reducing `(S,P,M,T)` survives.

## Workflow-General Run W5: Tail-Index Uncertainty From Few Extreme Drawdowns

[DEAD END / HYGIENE GATE, 2026-06-23]

Workflow continued from last RandomNode `Escape dynamics may be nonhyperbolic, producing algebraic rather than exponential lifetime distributions`.

- Entropy seed: `3142228065337374667`.
- Step 1 cold prompt list, Step 2 RNG: item 12, `Heavy-tailed financial drawdown durations`.
- Step 3 cold prompt list, Step 4 RNG: item 19, `Underestimated uncertainty in tail-index estimates due to few extreme durations`.
- Step 9 scientific-method RNG: method 9, `Test small cases`.

NODE constraint: tail-exponent estimation is controlled by the number and structure of extreme observations, not by the full sample size. High log-log fit quality can coexist with badly understated uncertainty.

Experiment: `computations/2026-06-23-drawdown-tail-uncertainty-node.py` simulates pure Pareto and two-component tail-mixture drawdown durations. It compares repeated-sample variability of Hill and log-log OLS tail estimates against naive within-sample standard errors.

RunPod NODE result:

- Pure Pareto, `k=20`: Hill empirical SD `0.3425` vs naive SE `0.3154`; OLS empirical SD `0.3161` vs naive SE `0.0575`, mean `R^2=0.9400`.
- Mixture tail, `k=20`: Hill empirical SD `0.2054` vs naive SE `0.2122`; OLS empirical SD `0.2211` vs naive SE `0.0374`, mean `R^2=0.9415`.
- At `k=40`, OLS still understates repeated-sample variability by about `6.8x` in the mixture case (`0.1758` vs `0.0256`) despite mean `R^2=0.9487`.

Transfer selected by Levenshtein: `few extreme phase-defect runs understate tail-index uncertainty`.

HT transfer result: useful as hygiene, not novelty. Tail-exponent fits to phase-defect run lengths use tiny effective samples. In the right strip (`sigma=1.2`), true and finite Euler are nearly identical: true run count `8`, max run `107`; finite run count `8`, max run `108`; Hill/OLS tail estimates are close at the same `k`. The statistic therefore reduces to finite-sample tail-estimation fragility plus prior recurrence/run-length controls.

Source reduction: this is standard extreme-value / Hill-estimator caution: tail-index estimates depend on the number of upper order statistics and have fragile threshold/sample-size behavior. No non-reducing `(S,P,M,T)` survives.

Verdict: DEAD END for novel knowledge. Keep the hygiene gate: do not promote power-tail/exponent claims from a handful of extreme runs without repeated-window/bootstrap uncertainty and finite/random controls.

## Workflow-General Run W6: Road Hierarchy As Fractal-Morphology Confound

[DEAD END / HYGIENE GATE, 2026-06-23]

Workflow continued from last RandomNode `Underestimated uncertainty in tail-index estimates due to few extreme durations`.

- Entropy seed: `1096590896978984582`.
- Step 1 cold prompt list, Step 2 RNG: item 10, `Fractal urban morphology`.
- Step 3 cold prompt list, Step 4 RNG: item 11, `How road hierarchy can mimic fractal branching without reflecting self-organized urban growth`.
- Step 9 scientific-method RNG: method 1, `Split it into subclaims`.

NODE constraint: box-count fractal-looking morphology is not a mechanism detector. A designed hierarchy, stochastic growth, and random occupancy can all produce high-quality scaling fits.

Experiment: `computations/2026-06-23-road-hierarchy-fractal-confound-node.py` compares a deterministic H-tree-style road hierarchy, stochastic dendritic growth, and random occupancy using box-count dimension, fit `R^2`, occupancy coefficient of variation, and anisotropy.

RunPod NODE result:

- designed hierarchy: box dimension `1.39731`, `R^2=0.9866`, occupancy CV `0.47953`, anisotropy `1.68010`.
- stochastic growth: box dimension `1.61239`, `R^2=0.9965`, occupancy CV `0.49986`, anisotropy `1.24339`.
- random occupancy: box dimension `1.59867`, `R^2=0.9659`, occupancy CV `0.28790`, anisotropy `1.03850`.

Transfer selected by Levenshtein: `prime hierarchy mimics fractal phase branching without native organization`.

HT transfer result: high box-count `R^2` appears across true, finite Euler, and random controls. In the right strip (`sigma=1.2`), true and finite Euler are effectively identical on the tested morphology statistics: true dimension `1.42443`, `R^2=0.9954`, CV `0.56542`, anisotropy `4.42820`; finite dimension `1.42402`, `R^2=0.9959`, CV `0.56260`, anisotropy `4.47006`.

Source reduction: this is standard fractal-urban-method caution. Box-count/fractal dimension is descriptive and sensitive to representation/scale; scaling curves can add diagnostic information, but dimension alone does not identify a self-organized mechanism.

Verdict: DEAD END for novel knowledge. Keep the hygiene gate: do not promote HT/landscape claims from box-count dimension or high scaling `R^2` unless controls separate designed hierarchy, random occupancy, finite Euler, and random phase.

## Workflow-General Run W7: Multilayer Transport Coupling Missed By Single-Layer Metrics

[DEAD END / HYGIENE GATE, 2026-06-23]

Workflow continued from last RandomNode `Road hierarchy can mimic fractal branching without reflecting self-organized urban growth`.

- Entropy seed: `3677919641956617035`.
- Step 1 cold prompt list, Step 2 RNG: item 12, `Scale-free transport networks`.
- Step 3 cold prompt list, Step 4 RNG: item 11, `Multilayer structure, where transport depends on interactions between roads, rail, air, power, or data layers`.
- Step 9 scientific-method RNG: method 2, `Attack it as false`.

NODE constraint: single-layer graph statistics can miss vulnerabilities caused by inter-layer dependency links. A low-degree node in one layer can be high-impact because it supports another layer.

Experiment: `computations/2026-06-23-multilayer-transport-coupling-node.py` builds two synthetic transport layers plus dependency links and compares targeted single-layer degree removals against low-degree dependency removals.

RunPod NODE result:

- road top-degree removal: road giant `0.0197`, rail giant `0.7945`.
- rail top-degree removal: road giant `0.9278`, rail giant `0.0236`.
- low-degree dependency removal: road giant `0.9275`, rail giant `0.0417`.

Interpretation: a set that is low-degree in the road layer can almost collapse the rail layer through dependency coupling. Single-layer degree alone misses the inter-layer failure channel.

Transfer selected by Levenshtein: `gamma prime weld coupling missed by single layer metrics`.

HT transfer result: weak diagnostic, not novelty. The transfer compared separate Gamma/prime amplitudes with coupled weld defects. Some left-strip correlations differ, but the right-strip true/finite control collapses: at `sigma=1.2`, true and finite have nearly identical `corr_gamma_weld` (`-0.05609/-0.05631`) and similar `corr_prime_weld` (`0.08261/0.08892`). This repeats the standing warning that separate-layer statistics can be misleading, but does not yield a native invariant.

Source reduction: interdependent/multilayer-network cascade failures are established (e.g. Buldyrev et al. interdependent networks; multilayer network robustness/cascade literature). No non-reducing `(S,P,M,T)` survives.

Verdict: DEAD END for novel knowledge. Keep the hygiene gate: Gamma-only or prime-only diagnostics cannot be promoted as weld/landscape evidence unless a coupled statistic separates true from finite/random controls and survives source/promptability checks.

## Workflow-General Run W8: Spin-Orbit Matrix Boundary Conditions

[DEAD END / HYGIENE GATE, 2026-06-23]

Workflow continued from last RandomNode `Multilayer structure, where transport depends on interactions between roads, rail, air, power, or data layers`.

- Entropy seed: `492832716409134168`.
- Step 1 cold prompt list, Step 2 RNG: item 18, `Quantum graph transport`.
- Step 3 cold prompt list, Step 4 RNG: item 16, `Spin-orbit coupling requires matrix-valued boundary conditions and changes the scattering symmetry class`.
- Step 9 scientific-method RNG: method 17, `Change representation`.

NODE constraint: scalar phase boundary data cannot encode spin rotation or spin-dependent scattering. Matrix-valued boundary/scattering data changes both interference visibility and output spin polarization.

Experiment: `computations/2026-06-23-spinorbit-matrix-boundary-node.py` compares a scalar two-path interferometer against a spinful path with a `R_y(theta)` spin rotation. Scalar phases preserve full visibility and spin-z; matrix spin-orbit transport does not.

RunPod NODE result:

- `theta=0`: visibility `1.00000`, spin-z `1.00000`.
- `theta=pi/2`: visibility `0.70711`, spin-z `0.00000`.
- `theta=pi`: visibility `0.00000`, spin-z `-1.00000`.

Transfer selected by Levenshtein: `gamma prime coupling needs matrix valued boundary diagnostics`.

HT transfer result: representation change is a useful warning but not a native invariant. The scalar-vs-matrix weld statistic is strongly representation-dependent. In the right strip (`sigma=1.2`), true, finite Euler, and random controls are nearly indistinguishable for the `theta=pi/2` matrix representation: `corr_scalar_matrix=0.99606/0.99603/0.99615`, mean log ratio `0.08061/0.08075/0.07555`. For `theta=pi`, true and finite are also close on the mean log ratio (`0.13989/0.13988`).

Source reduction: spin-orbit quantum transport and matrix/scattering-boundary formulations are established. The transfer creates an arbitrary matrix lift of the Gamma/prime weld, not a source-defined matrix category.

Verdict: DEAD END for novel knowledge. Keep the hygiene gate: do not promote scalar-vs-matrix weld diagnostics unless the matrix representation is source-defined and separates true from finite/random controls under label-stripped promptability and source checks.
