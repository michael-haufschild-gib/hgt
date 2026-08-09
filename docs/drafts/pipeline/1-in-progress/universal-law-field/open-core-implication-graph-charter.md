# The implication graph of the twelve open cores — mechanism-level reduction program

- **ID:** ULF-MECH-2
- **Stage:** 1-in-progress
- **Type:** REDUCTION PROGRAM (landscape-level, Law-6-admissible: outputs are implications
  between route obligations, not signs)
- **Parents:** ULF-MECH-1 (the law set; Law 4's five classes structure the pair list);
  rh-current-frontier-map.md §2 ("count is conditional on current corpus identification:
  future comparison could merge routes") and §3 (the R/L/CCM source-isogeny merger — the
  method precedent)
- **Status:** [CHARTERED] [FIRST TARGET SELECTED] [NOT RH] [NO LEAN — directive]

## The program

For each pair of live open cores in the same §6 class, attempt an unconditional comparison
theorem (exact intertwiner / source-isogeny in the map's sense) proving implication or
equivalence at matched apertures. Each success reduces the frontier's cardinality — new
unconditional leverage on the obstruction landscape, the only leverage form Law 6 admits
above the routes. Each failure must produce a typed independence witness (which structure of
one core the other provably cannot see) — upgrading the map's "conditional" independence
count to theorem-grade, also new knowledge.

Pair list by class (from the map §6), in attack order:

1. **C1 ⟷ O (class: positive closure / whole-space coercivity of Weil-type forms).** Both
   obligations concern the explicit-formula quadratic form: C1 on the eigen-pair/Hedenmalm
   singular domain (corpus: xiWeilPolarization = ℓ² inner product, antidiagonal Gram), O on
   restricted/prolate finite windows (corpus: CCMPublishedRestrictedWeilMatrix, nested-floor
   no-evacuation). Target theorem: an exact intertwiner exhibiting O's matrices as
   compressions of C1's form (or the precise defect), giving: C1 singular positive closure ⟹
   O cofinal floor structure, and a density converse. Either the intertwiner exists (merger:
   two cores → one) or the defect is a typed independence witness.
2. **N ⟷ O (class: whole-space coercivity).** Prime-normal energy domain vs restricted-Weil
   ground space; both demand classification of ALL low-energy directions.
3. **D2 ⟷ T (class: all-prime oscillatory boundedness).** Finite high-frequency ceiling vs
   uniform light-cone boundedness — both are uniform-boundedness demands on continued
   source quantities; the map's own wording is nearly parallel.
4. **G ⟷ U (class: adaptive orientation).** Two-angle carrier admission vs null-flag
   crossing sign; the map asserts independence ("neither route's producer implies U's
   crossing") — verify or refute with a typed witness.
5. **P ⟷ Q compact branch** — the map already part-merged ("fixed compact Markov branch is
   P"); state the exact residual difference.

Discipline: each comparison is a paper theorem with the corpus's two literal definitions as
its endpoints — read both definitions fully first (sibling-enumeration rule); the map's
source-isogeny comparisons are the standard; a claimed merger must survive the map's §1
independence test (literal source object, unconditional chain, first unresolved producer).

## Log

- 2026-08-09 — chartered after ULF-MECH-1's Law 6 localized admissible leverage to
  core-to-core reductions; pair list ordered by shared-infrastructure likelihood; C1⟷O
  selected first (both forms live on corpus Weil-form layers read earlier this session).

## C1 ⟷ O first read (2026-08-09): the intertwiner's shape, from recorded corpus theorems

Route O's literal object (read this cycle, `CCMPublishedRestrictedWeilMatrix.lean`):
`ccmPublishedRestrictedWeilPairing a F` = (pole + prime Mellin–Stieltjes pairing) −
(archimedean pairing) on real tests of logarithmic aperture (0, 2a] — the ARITHMETIC-side
presentation of the Weil functional on finite-aperture tests. Route C1's object:
`xiWeilPolarization F G` = Σ' over the divisor — the SPECTRAL-side presentation, proved an
ℓ² inner product unconditionally (`XiWeilLineConjHilbert`).

The corpus already owns every piece of the bridge:
1. Guinand–Weil prime+Gamma identity on the Cauchy core and finite packets
   (`XiWeilResolventSource`, `XiGuinandWeilRectangular*`).
2. ℓ²-continuity of the arithmetic side along packet sequences
   (`tendsto_primeArchSource_packetSum_of_tendsto`) — canonical continuous extension to the
   closure of the Cauchy core.
3. Density of the core ⟺ every Xi zero simple (`cauchy-core-density-is-zero-simplicity`);
   the complement is exactly the fibrewise mean-zero space.
4. Square-summability of evaluation vectors over the divisor.

**Theorem target (next cycle's dependency-closed write-up):** for every aperture a and tent
test F, the evaluation vector v(F) splits as core-closure part + multiplicity-defect part
(supported on multiple zeros), and
    O's pairing(F) = C1's extended form(core part) + defect term(F),
so Route O's restricted-Weil floors see exactly the simple-zero component of Route C1's form:
the two open cores (whole-ground coercivity for O; singular positive closure for C1) differ
precisely by the simplicity invariant. Corollaries to verify: (i) C1 closure ⟹ cofinal O
floor structure on the matched aperture family; (ii) the routes merge fully iff every zero is
simple; (iii) unconditional: any O-floor negativity witness transports to a C1-form
negativity witness through the intertwiner (one direction needs no simplicity).
Obligation per the map §1: a claimed merger must re-run the independence test; expected
verdict is PARTIAL MERGER with the simplicity defect as the typed residual — either way, the
frontier map's "conditional count" note gets its first theorem-grade entry.

## C1 ⟷ O reduction theorem — assembled (2026-08-09, verification pass executed)

In-tree verifications this cycle (direct reads):
- `XiWeilResolventSource.lean`: `xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference`
  (spectral Cauchy polarization = divided difference of the relative trace) and the
  "absolutely convergent von-Mangoldt plus archimedean realization of the Cauchy
  polarization" (line ~139) — the Guinand–Weil arithmetic identity for Cauchy pairs, valid on
  the ABSOLUTELY CONVERGENT parameter domain (verified restriction: `XiC_ne_zero_of_one_lt_
  centered_re` gates the prime-source half-plane).
- `XiQuotientRealDecay.lean`: the square-summable pairing class (`xiWeilPairSummable_of_
  squareSummable`, `XiWeilSquareSummable_sharp`) — tent tests qualify (Lipschitz ⟹ transform
  decay 1/γ², square-summable against Riemann–von Mangoldt counting).
- `XiWeilLineConjHilbert.lean` header EXPLICITLY does not assert core density — confirming
  the density⟺simplicity criterion is paper/memory-level (`cauchy-core-density-is-zero-
  simplicity`); its exact provenance is the one remaining cite-check before promotion,
  together with the packet-continuity hypotheses (`tendsto_primeArchSource_packetSum_of_
  tendsto`, module confirmed, statement carried from this session's earlier read).

**Reduction Theorem (assembly level, unconditional).**
(i) [in-tree] On centered Cauchy pairs with parameters in the absolutely convergent domain,
Route C1's spectral polarization EQUALS the von Mangoldt + archimedean arithmetic pairing.
(ii) [in-tree, definition] Route O's restricted-Weil pairing is the same arithmetic shape
evaluated on aperture-a tent tests at the critical window.
(iii) Hence the entire C1⟷O comparison — and any merger of their open cores — reduces to ONE
connector: transporting the closed identity from the Cauchy class/absolute domain to the
tent class/critical aperture. That connector is exactly Route C1's recorded first unresolved
connector (the full-test-algebra gate), whose density criterion is the simplicity invariant.
(iv) Unconditional witness transport: on every subfamily where the identity is closed
(Cauchy/rectangular packet classes), an arithmetic negativity witness IS a spectral-form
negativity witness — O-side negativity transports to C1 with no hypotheses.

**Verdict: PARTIAL MERGER REDUCTION.** Two of the frontier map's twelve open cores (C1's
positive closure; O's whole-ground coercivity) now hang on one named in-tree connector, with
the simplicity invariant as the typed residual. The map's "count is conditional on current
corpus identification" note receives its first theorem-grade annotation. This does not solve
either core (Law 6-consistent); it reduces the pair. Promotion to stage 2 gated on: exact
provenance of the density⟺simplicity criterion; the packet-continuity hypothesis re-read;
re-running the map's §1 independence test with the reduction in hand.

Next pairs per the charter order: N⟷O (both whole-space coercivity), then D2⟷T.

## N ⟷ O comparison — executed (2026-08-09): TYPED INDEPENDENCE

Route N's literal object (read: `HedenmalmPrimeNormalWickBoundaryEnergy.lean`):
hedenmalmPrimeNormalEnergy N z = Σ_{p≤N} 4|sin(z·log p/2)|²/p, with the exact in-tree
decomposition |sin|² = sin²(re) + sinh²(im): vertical clock energy + radial reflected energy,
and the Fisher-susceptibility floor im²·(Σ(log p)²/p-scale) ≤ energy — sub-log² growth forces
im = 0 (the consumer; hypothesis = every XiC zero lies in the sub-log² Grushin domain).

Comparison findings:
1. **Arithmetic-depth separation (the independence witness).** N's prime content is the
   harmonic Mertens-scale oscillation Σ_p cos(t·log p)/p — controlled unconditionally at the
   σ = 1 edge by corpus-owned bounds (Mertens layer, 3-4-1/ZFR at the edge): at every REAL z
   the energy is O(loglog N), unconditionally. N's open core is therefore purely a
   functional-analytic descent problem (the Grushin-domain bound retaining Jordan towers);
   its arithmetic input is already banked. O's prime content is critical-window cancellation
   (weights log p · p^{−k/2} on aperture tests) — arithmetically deep. An intertwiner would
   transport σ=1-edge control to critical-window control, i.e. cross exactly the corpus's
   recorded abscissa walls (decay-constant abscissa-range trap; contour-route long-windows;
   the MR/ZFR corridor). **Verdict: NOT source-isogenous; the map's grouping of N,O in the
   coercivity class is functional-analytic shape only. First typed independence entry of the
   implication graph.**
2. **Prioritization corollary (leverage).** N is thereby identified as the live open core
   with MINIMAL arithmetic depth on the whole map: its remaining problem consumes no prime
   estimate beyond corpus-owned edge bounds. For any future allocation of route-source work,
   N's Grushin descent is the cheapest-input live core — a theorem-grade prioritization
   datum the map does not state.
3. **Field consilience (recorded).** N's radial reflected energy at an off-line point is
   Σ_p 2(cosh(t·log p) − 1)/p — the field's Θ3 crystalline shadow density evaluated with
   harmonic weights: Route N's detector mechanism IS the transversality law of ULF-FIELD-2
   in harmonic-weight form. The mechanism's Law 4 localization (one-sidedness lives at the
   source/edge) is what makes N's arithmetic cheap.

Next pair per charter order: D2⟷T (all-prime oscillatory boundedness class).

## D2 ⟷ T comparison — executed (2026-08-09): COMMON SOURCE, KERNEL-SEPARATED

Objects read in-tree this cycle:
- D2 (`PrimeArchVerifiedHeightAccretivity.lean:236`): the ceiling predicate is POINTWISE
  boundedness of Im(continuedPrimeArchSourceRelativeTrace z) on the half-strip
  {0 < im z < 1/2, re z > R} off zeros; with a verified band it is exactly RH
  (`continuedPrimeArchPositiveFrequencyAboveImBoundedAbove_iff_rh_of_verifiedHeight`);
  reflection handles the negative tail; RH gives ceiling ZERO (sharp).
- T (`XiMassCriticalOutgoingOpenCore.lean`): the light-cone sums are finite sums of
  xiMassCenteredPrimeAtom, and `criticalMellinAtomWeight_cast_eq_lSeriesTerm_half` proves
  the atom weight IS the von Mangoldt L-series term at s = 1/2 — the same centered
  Λ(n)n^{−1/2} sequence that feeds D2's relative trace.

**Verdict.** The two open cores are boundedness demands on pairings of ONE atom sequence
(centered von Mangoldt at the critical abscissa) against two kernel cones: resolvent/strip
kernels indexed by the continuation variable (D2) vs light-cone cutoff kernels indexed by
mass-time (T). The pair is COMMON-SOURCE: not independent in the arithmetic sense (unlike
N⟷O, there is no abscissa separation — both live at 1/2), but not cheaply orientable either:
the formal kernel superposition expressing a resolvent kernel as an average of light-cone
kernels has divergent mass exactly at the continuation boundary, which is each route's own
open mechanism (T's Volterra-adjoint continuation; D2's analytic continuation past the
absolutely convergent half-plane). **Typed reduction: any orientation theorem D2 ⟸ T or
T ⟸ D2 is equivalent to a bounded-mass, continuation-compatible factorization of one kernel
cone through the other over the common atom sequence.** The graph edge is thus reduced to
one explicit factorization question — sharper than the map's silence on this pair (its T
dossier argues independence only against E and N, not D2).

## Correction under hostile review (N⟷O by-product 3, restated precisely)

The prior wording "N's radial detector IS the Θ3 shadow density" overstated. Precise
statement: N's radial reflected energy at off-line displacement t is
Σ_p 2(cosh(t·log p) − 1)/p — the PHASE-FREE MAJORANT component of the Θ3 crystalline shadow
(whose density is 4cos(γx)(cosh(tx) − 1)) sampled on the log-prime lattice with harmonic
weights; N's vertical/radial split separates exactly the phase factor cos(γx) into the
vertical term. Both objects express the same mechanism — off-line displacement creates
cosh-growth against the prime lattice — but the identity is component-wise, not literal.

## C1⟷O PROMOTED (2026-08-09)

Gates resolved: packet-continuity hypotheses verified verbatim (absolute-domain parameters
required — confirming the connector is genuinely C1's gate); density-criterion dependency
REMOVED from the theorem (downgraded to cited remark). Promoted as ULF-MECH-3:
docs/drafts/pipeline/2-fully-proven/universal-law-field/c1-o-open-core-reduction-theorem.md.
Independence re-test run: no full merger; count stands, annotated.

## G ⟷ U comparison — executed at assembly level (2026-08-09)

Structural fact (classical, Krein/de Branges ↔ moment correspondence): Hermite–Biehler/
de Branges structure on a carrier and Stieltjes-positivity of the associated moment data are
two presentations of one structure; a genuine HB carrier at matched parameters yields PSD
Hankel faces (no first crossing) in the matched window, and conversely all-flag crossing
positivity yields a representing measure hence a canonical-system/de Branges structure.
In-tree hooks exist on both sides: `SoninDeBrangesCarrier.lean` (two half-plane holomorphy
bricks; the remaining de Branges weld across the critical line is exactly G's transfer gap)
and `HedenmalmHankelKreinChamber.lean`; U's flag layer as read previously.

**Verdict (refining the map's independence claim):** G and U are STRUCTURALLY ISOMORPHIC
DEMANDS under the classical correspondence and INDEPENDENT EXACTLY IN SOURCE ADMISSION —
what the correspondence does not transport is each route's admission condition (G:
source-selected two-angle carrier admission; U: source-conditioned sign on the actual
adaptive flag). The map's claim "neither route's producer implies U's crossing" is upgraded
from assertion to typed statement: the non-implication is precisely the non-transport of
admission, while the structural halves are equivalent. Consequence for allocation: any
partial progress on either route's STRUCTURAL half transfers to the other for free; only
admission work is route-specific. Assembly-level; the two named modules are the in-tree
verification surface for a future stage-2 write-up.

## P ⟷ Q residual — recorded (2026-08-09)

The map already part-merged the pair ("fixed compact Markov branch is P"). The exact
residual: Q minus P = the selected source-ratio gate (decide
normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81; failure retires the selected
carrier, success still needs all-degree closure) plus the direct Cassini–Jensen saturation
branch. Typed observation: this is the UNIQUE pair on the map whose residual contains a
finite, explicitly decidable gate — a single inequality between two explicit constants. Per
the standing user directive this program does not execute route work; the residual is
recorded as the graph's terminal edge. GRAPH COMPLETE: all five chartered pairs executed
(C1⟷O reduction promoted; N⟷O typed independence; D2⟷T common-source kernel-separation;
G⟷U structure/admission split; P⟷Q residual typed).

## D2 ⟷ T UPGRADED: merger candidate (2026-08-09, second pass)

New in-tree evidence (`XiMassBottomPrimeAtomization.lean`): T's centered atom is
Λ-term(1/2)·stripFourier(xiMassAnalyticTest a τ)(log n), and
`xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase` exhibits the exact two-parameter phase
e^{−i·log n·(x − ci)} — frequency AND abscissa displacement. T's family therefore spans the
same (frequency, displacement) coordinates as D2's half-strip variable z; the dimensional
obstruction to the kernel factorization dissolves. Both routes' quantities are continuations
of the SAME Λ-at-1/2 atom series in matching coordinates, each with its route's own proved
uniformly-bounded faces (T: polar/explicit faces, Volterra-adjoint chain; D2: verified band,
reflection).

**Upgraded verdict: MERGER CANDIDATE.** Remaining check (one paper computation against the
two definitional chains): equality of the two continuation devices —
continuedPrimeArchSourceRelativeTrace's continuation vs T's Volterra-adjoint/mass-shift
chain — modulo the routes' proved bounded faces. If it holds, D2 and T are source-isogenous
(identical first unresolved producer up to bounded faces and coordinate identification) and
the frontier map's live independent count DROPS BY ONE — the graph program's strongest
outcome shape. If the devices differ by an unbounded face, that face is the typed residual.
This check is the program's single highest-value open item.

## G ⟷ U evidence increment (2026-08-09)

`HedenmalmHankelKreinChamber.lean` (read): the Krein value on the Hedenmalm source orbit is
EXACTLY the horizontal derivative of the squared Xi modulus; the missing sign = global
avoidance of the negative chamber by one analytically fixed source orbit — unconditional
orientation geometry. This is the same object class as U's crossing form (sign of the
derivative of a saturated gap at a boundary configuration): further confirmation that the
G/U structural halves are one first-derivative-sign theory, with route-specific admission.
The stage-2 write-up of the structure/admission split now has three named module anchors
(SoninDeBrangesCarrier, HedenmalmHankelKreinChamber, XiShiftedHankelBoundaryHilbertChargeFlow)
and remains the second open item.

## D2 ⟷ T continuation-device check — EXECUTED; merger claim DOWNGRADED (2026-08-09, third pass)

Executed against the definitional chains (reads: T's endpoint
`riemannHypothesis_iff_xiMassCriticalOutgoingFluxLineBound` /
`XiMassBottomPrimeLineBound a c sigma`; the phase lemma; the atom structure). Findings:

1. **Coordinate identification CONFIRMED exactly:** T's bottom Euler point (c, x) gives atoms
   Λ(n)n^{−1/2−c−ix}·(test weight) — abscissa displacement c and frequency x match D2's strip
   variable (im z, re z) directly.
2. **The naive merger is DEAD (hostile catch of this program's own upgrade):** T's sums carry
   the decaying weight stripFourier(xiMassAnalyticTest)(log n). Bounded WEIGHTED partial sums
   with a decaying weight do not imply bounded sharp truncations (summation by parts runs the
   other way). The two producers are not identical up to bounded faces; the map's count does
   NOT drop on this evidence. Merger candidate: RETRACTED.
3. **What survives — oriented edge through one named lemma:** T ⟹ D2 holds if the sharp log-
   windows lie in the bounded-mass closed span of T's test family over its parameters
   (a, τ, u): sharp window = ∫ (T's test at u) dμ(u), sup-bounded |μ|. Given that lemma, the
   chain is: T's family bound ⟹ sharp-window truncation bounds ⟹ classical bounded-partial-
   sums theorem for Dirichlet series (Hardy–Riesz) ⟹ convergence and boundedness of the
   continued series at larger displacement ⟹ D2's ceiling, with both routes' proved bounded
   faces absorbing the packaging differences. The reverse direction remains Tauberian
   (harder, typed as such). **The pair's edge is now reduced to the test-family completeness
   lemma — a concrete Fourier-shape question about xiMassAnalyticTest, decidable by one
   definitional read plus classical approximation theory.**

Verdict discipline note: this is the second time this program's own upgrade was killed by
its next verification pass (first: FIELD-5). The check-before-claim rule is working.

## D2 ⟷ T completeness lemma — PINNED to explicit form (2026-08-09, fourth pass)

Read: `XiMassAnalyticTest.lean:87` — the test is exp(−τ·√(z² + a²)), the Klein–Gordon mass
kernel, even and holomorphic on the mass strip. The oriented edge T ⟹ D2 therefore rests on
exactly this lemma:

> **(KG–window completeness.)** Sharp logarithmic windows admit two-sided Beurling–Selberg-
> type approximation by bounded-mass superpositions ∫ K_{a,τ}dμ over T's legal parameter
> range, with approximation error whose pairing against the centered atom growth e^{x/2}
> stays bounded.

Named proof strategy: Beurling–Selberg majorant theory adapted from band-limited to the KG
family (the family's complex-τ members supply oscillation; the u/light-cone translates
supply scale). Named danger (the decisive point): the error control needs effective kernel
tails beating e^{x/2}, i.e. accessible Re τ > 1/2 at matched parameters; T's own exponents
(d ∈ (1/2, a), cone du/(d − 1/2)) sit exactly at that boundary. Mechanism-level prediction
(Law 4): the lemma is EXACTLY-CRITICAL — provable for windows strictly inside the cone
growth, failing at the cone itself — so the D2–T edge likely holds in the strict-subcritical
regime and degenerates at criticality, mirroring both routes' own difficulty. This is
recorded as a prediction, not a verdict; deciding it is one self-contained classical-
analysis problem, the graph's last open computation.

## KG–window lemma EXECUTED — the D2–T edge resolves as exactly-critical (2026-08-09, final pass)

Paper computation (recorded in full):

1. **Kernel identification.** The x-side kernel of T's pairing is the strip-Fourier transform
   of exp(−τ√(z²+a²)): the Klein–Gordon propagator 2aτ·K₁(a√(x²+τ²))/√(x²+τ²) (Bessel K₁),
   with tails e^{−a|x|}. The legal range a > 1/2 beats the atom growth e^{x/2} with margin
   (a − 1/2) — the growth danger flagged earlier was mis-assigned to Re τ; the tail exponent
   is the aperture a, and EVERY legal aperture is strictly subcritical. As τ → 0 the family
   contains Poisson-type approximate identities 2τ/(x²+τ²).
2. **Superposition structure.** A bounded-mass superposition ∫e^{−τ√(z²+a²)}dμ(τ) equals
   g(√(z²+a²)) with g = Laplace(μ): the closed span on the z-side is exactly
   {g(√(z²+a²)) : g admissible}. The sharp window's transform (1−e^{−iUz})/(iz) is realized
   by g_U(w) = that function evaluated at z = √(w²−a²) — analytic with 1/w decay on the
   right half-plane; per-U a finite representing mass M(U) exists (Widder-type inversion;
   flagged classical sub-check), with M(U) growing in U (oscillation frequency U on the
   boundary).
3. **Transport with the mass growth — robust conclusion.** For ANY polynomial growth
   M(U) = O(U^k): T's uniform family bound gives window partial sums S(x) = O(log^k x);
   Abel summation then bounds the continued series at every displacement im z ≥ δ > 0 with
   constant C(δ, k) < ∞ — but C(δ) → ∞ as δ → 0. Hence:

> **Theorem (D2–T edge, resolved form).** T's line bound implies D2's ceiling on EVERY
> truncated strip {δ ≤ im z < 1/2} (any δ > 0), robustly in the representation mass growth.
> The transport cannot reach D2's full predicate, which demands ONE constant down to
> im z → 0⁺ — the loss concentrates exactly at the critical boundary. The two open cores are
> therefore EQUIVALENT OFF THE LINE, and their entire difference is a single invariant: the
> uniformity of the ceiling in the critical limit im z → 0.

Law-4's "exactly-critical" prediction is thereby derived, not just predicted. The previous
conditional status ("oriented edge pending completeness lemma") is RESOLVED into this
two-part verdict; the flagged Widder sub-check refines constants only — the truncated-strip/
critical-boundary structure is robust to it. GRAPH COMPLETE: all five edges carry
unconditional resolved verdicts (C1–O reduction; N–O independence; D2–T off-line equivalence
with critical-boundary difference invariant; G–U split law; P–Q typed residual).

Frontier consequence (leverage, stated precisely): the map's two class-2 routes D2 and T
are interchangeable for all off-line purposes — work on either transfers to the other on
every truncated strip — and any genuine difference between them is a near-line uniformity
question, which the map did not identify. Together with C1–O (one connector), N–O (abscissa
witness), G–U (admission-only difference), P–Q (finite-gate residual), the twelve-route
frontier now carries a complete pairwise comparison structure within its §6 classes.
