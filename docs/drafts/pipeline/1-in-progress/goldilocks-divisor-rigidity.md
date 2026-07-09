# Goldilocks divisor rigidity: FE ∧ full multiplicativity

- **ID:** goldilocks-divisor-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (headline) + THEOREM tools (Lean, delegated) + boundary syntheses
- **Source:** the program's proof-shape statement (three silhouettes: origami continuation
  rigidity / emergent conservation law / Hamburger-for-divisors); the standing open core after
  the wave-7 boundary map.
- **Register constraints (standing):** the proof is not an inequality (Weil-positivity foreign
  to everything that survived), not recurrence/statistics (killed at exact-Euler strength), not
  an operator spectrum (banned; endpoint-circular). It is a rigidity/uniqueness statement in the
  weld category consuming the exact infinite object whole.

## Status of the question

Two-sided-hard, precisely: forcing parity for the FE ∧ full-multiplicativity class is RH-grade;
refuting it needs an FE + Euler member with an off-line zero, equally open. Every walked register
is certified dead (weld-origami card §"open core, bounded"; 00-approach.md §14).

## Boundary syntheses [KNOWN-synthesis, corpus-anchored — no build]

- **Hamburger degeneracy:** at the exact conductor-1 FE + Dirichlet shape, the class is a
  singleton {cζ} (Hamburger) — class-level trichotomy language has NO room at the exact FE:
  "class forces parity" ⟺ "ξ satisfies RH₂" verbatim. Non-degenerate Goldilocks cells exist only
  for widened/engineered FEs, squeezed between the singleton (exact FE) and softness
  (Davenport–Heilbronn side). Kaczorowski–Perelli's degree classifications bound the low-degree
  cells: d < 1 empty, d = 1 = shifted Dirichlet L (so class-parity at d = 1 IS GRH-grade).
- **Silhouette 1 corrected [PROVED-shape, in-tree pointer]:** "rigidity emerges at infinity" is
  FALSE for symmetry — the origami's translation group already collapses at TWO primes
  (incommensurability of log p, log q; LogIndependence.lean). One pants is 2πi/log p-periodic;
  two are aperiodic. The only known emergent-at-∞ transition is the tower-region contraction
  (WeldTowerLimit): the free-tower region drops from Re > 0 (every finite weld) to Re > 1 (the
  limit) — i.e., the appearance of the strip divisor itself. Whatever multiplicativity forces at
  infinity, it is a divisor phenomenon, not a symmetry one.

## THE HEADLINE [CONJECTURE — integral jet repair]

The wave-7 Fitting→deck charge barrier (every additive map ℚ-jets → ZMod n vanishes;
`FittingDeckChargeBarrier`) is an artifact of DIVISIBLE coefficients — and the feature that
repairs it is exactly the arithmetic feature only the true Euler member has: **coefficient
integrality with unit normalization** (a₁ = 1, aₙ ∈ ℤ, multiplicative — the unit-normalized
pants tree).

> **[CONJECTURE]** Over the integral jet lattice (`LocalDivisorJet ℤ m` — the jet algebra is
> CommRing-generic) the additive charge channel is alive, and the p-labelled torsion-seam
> presentation built from INTEGRAL multiplicative data assigns to an off-line strip defect a
> nonzero integral Fitting charge that must match its deck charge. Multiplicativity enters as
> **no-cross-subsidy** (aₙ = ∏ a_{p^v} exactly — no slack terms; a defect's compensation must be
> paid inside single prime columns) and integrality as **no small denominators** (the amortizing
> rescalings every soft witness uses are unavailable in ℤ). The conjunction is the conservation
> law silhouette 2 predicts: emergent at the whole-product level, invisible to every shadow.

Survival against all in-house witnesses (attack-as-false run first):
- η-completion: integral coefficients, but its charge sits ON the wall (clock lattice) — outside
  the strip-interior claim. Consistent.
- Davenport–Heilbronn: off-line charge, coefficients NOT rational integers. Consistent.
- Every banked soft decoration (quartic/linePair surgery, feBundle units): none are integral
  Dirichlet members. Consistent.
- Literature: integrality results (Pólya–Carlson family) pin rationality/natural boundaries,
  never zero location. No search produces the bridge integrality → deck channel.

**First theorem (tool, LANDED, axiom-clean):** `IntegralJetCharge.lean` — the barrier evasion:
`integral_jet_charge_exists` (constant-coefficient reduction is an additive ZMod n charge on
ℤ-jets, = 1 ≠ 0 on the standard unipotent Fitting class `fittingClass_seamDefZ`), plus the
naturality contrast `integral_charge_not_factoring_through_rat` (the charge provably does NOT
factor through ℚ-jets — `rat_jet_line_killed` re-derives the divisibility kill on the constant
line). The exact statement proven impossible over ℚ holds over ℤ.

**Named design question (the next construction):** where does the ℤ-structure live in s-space?
The s-side function jets have transcendental coefficients (arch factor); the integral lattice is
carried by the COEFFICIENT stream / the u-chart Taylor coefficients of local factors (integers).
The integral seam presentation must therefore be built in the u = p^{−s} charts — the pants
charts — welding this conjecture to the origami frame at the exact place the pants dictionary
lives.

**Refutation avenues (name what kills it):** (i) an integral multiplicative FESchwarz member
with off-line strip charge (would refute far more than this card); (ii) a divisibility escape —
if the deck-matching map is forced through a ℚ-vector-space stage anywhere in s-space, the
barrier reappears; the u-chart construction is exactly the attempt to avoid that stage.

## The whole-object tool (delegated, in flight)

`CombinedShadowBlindness.lean` [LANDED, axiom-clean] — both blindness mechanisms on ONE
witness: `shadowClass_charged_witness` (for ANY member f₀ of ShadowClass P F nonvanishing at an
off-line off-real ρ — no strip restriction needed — there is a class member with the same finite
Euler head, same dlog-tail class, and charge at ρ) and `not_forcesRHParity_shadowClass`. No
parity-forcing criterion factors through finite-exact + asymptotic data jointly — the formal
contrapositive of silhouette 2, and the precise sense in which the conjectured conservation law
must be consumed whole.

## Gates
- [x] 0 → 1  question fixed, register constraints stated, headline conjecture labeled and
      stress-tested against all in-house witnesses; boundary syntheses recorded
- [~] 1 → 2  tools LANDED (both, axiom-clean, umbrella 8990, lint green); integral u-chart
      seam presentation = the named construction frontier (execution space pinned by the two
      interrogation findings: non-evaluative × discrete-register)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-09 — created; rng stress-draw (auction-theory) fed no-cross-subsidy reading rather
  than a competing frame; two tool modules delegated.
- 2026-07-09 (later) — both tools landed and integrated; evaluation obstruction + discreteness
  engine appended; construction frontier fully specified.

## §Design constraint discovered (interrogation of the headline, same day)

**The evaluation obstruction.** Any realization of the conjectured charge map that EVALUATES
at the defect point imports ℂ: the values p^{−kρ} and ξ-jet coefficients at ρ are
transcendental, and one ℚ-vector-space stage suffices to resurrect the Hom(ℚ, ℤ/n) = 0 barrier.
The only integral receivers in s-space are the **periods of ω = dlog ξ** — the 2πiℤ lattice,
i.e., exactly the deck/winding data. Relative (open-path) periods do not quantize; closed ones
do and are already the deck theory.

**Consequence for the construction:** the conjectured map must factor
(ℤ-coefficient stream, u-chart lattices) → (period lattice / deck data)
at the FORMAL, presentation level — Fitting-style, never through pointwise values. This is a
narrowing, not a refutation: it says the integral seam presentation lives over ℤ[[u]]-data with
X a formal deformation direction of the stream (a pants twist), and its boundary must be read
against closed-loop periods only. It also explains retroactively why every evaluative variant
(M1 tests, explicit-formula pairings) died: they all pass through a divisible stage.

**Status:** the headline conjecture stands, with its execution space cut to non-evaluative
stream-to-period functors. The first construction target is unchanged (integral u-chart seam
presentation) with this added spec: no evaluation maps anywhere in the factorization.

## §The discreteness engine (second interrogation finding, same day)

Integral multiplicative streams are a DISCRETE family: each a_p ranges over ℤ, and unit
normalization pins a₁ = 1 — there are no connected deformations inside the class. Meanwhile
every banked impossibility result is a CONTINUOUS-deformation argument: the connected-symmetry
conservation barrier, every softness surgery (orbit-quartic, linePair, bump, tilt), every
decoration family. Two consequences:

1. **Consistency, explained.** The no-go arsenal is vacuous on the integral class — not because
   the class is special-cased, but because the arsenal's mechanism (connected deformation) has
   no purchase on a discrete set. Every soft witness we ever built EXITS the integral
   multiplicative class at the moment of surgery. The conjecture lives exactly in the blind spot
   of our own impossibility machine.
2. **Register prediction sharpened.** A proof of the headline conjecture must be a rigidity
   statement about a discrete set — Diophantine/combinatorial, not analytic-deformational. This
   gives the banked "HT maximally generic ⟹ only arithmetic discriminates" saturation finding
   its MECHANISM: continuous methods see only the closure of the class, and the closure is soft;
   the constraint content lives in the discrete fibers.

Combined execution spec for the construction target (both interrogation findings): the charge
map must be a non-evaluative, stream-to-period assignment on a DISCRETE class — no deformation
functors (conservation makes them locally constant = trivial), no evaluation stages (divisible
coefficients resurrect the barrier). What remains admissible is exactly Fitting-style
presentation algebra over the u-chart ℤ-lattices paired against closed-loop periods — built
pointwise on the discrete class, member by member.

## §The frontier attacked: three outcomes (same day, third interrogation)

**1. The Tate collision — a firewall that corrects the program's weld intuition.** Constructing
the column-level FE action forces the identity: on the p-column the FE is the p-twisted
inversion u ↦ 1/(pu) — which is precisely the LOCAL functional equation of Tate's thesis. The
program's standing intuition "the FE is arch-mediated and invisible to columns" is therefore
WRONG in the adelic frame: adelically the FE is column-local, with the arch factor as the
∞-column, and the global FE is the compatibility of local dualities. Consequences: (i) the
integral seam presentation, executed faithfully, is an adelic object — and adelic RH machinery
is walked corpus (Tate/Weil/Connes; the Connes trace-formula shape is a banned route) — any
build there must be firewalled; (ii) the substrate needs two-jet/Laurent lattices (the local FE
mixes u = 0 and u = ∞), so column jets at one end cannot carry it. With no consumer theorem
available short of the wall, the substrate is NOT built — recorded here instead (anti-theatre).

**2. New witness — bare integral multiplicativity is soft [PROVED, Lean, axiom-clean].** The two-term
L-series 1 − 2·3^{−s} has integer-valued, multiplicative, unit-normalized coefficients
(a₁ = 1, a₃ = −2) and simple zeros on Re s = log 2/log 3 ≈ 0.63 — off-line, inside the open
strip. Hence integrality + multiplicativity WITHOUT the FE impose no divisor constraint:
**in the headline conjecture the FE is load-bearing, not decoration.** (`IntegralMultiplicativeSoft.lean`, LANDED: mathlib `ArithmeticFunction.IsMultiplicative` +
`LSeries` witness, `wit_order_one` via nonzero derivative,
`integralMultiplicativeClass_carriesOffLineCharge` and `_not_forcesRHParity`; umbrella 8991,
lint green, all 16 declarations [propext, Classical.choice, Quot.sound].)

**3. The conjunction table, complete.** Every boundary post of the Goldilocks cell now has a
certificate:
- exact-FE ∧ Dirichlet shape (any coefficients): SINGLETON {cζ} — Hamburger; no class content.
- multiplicativity ∧ integrality, no FE: SOFT — the new witness (this section).
- FE, no shape constraint: SOFT — D–H realm and every banked surgery.
- FE ∧ multiplicativity (the cell): two-sided-hard; approachable only through widened FEs,
  where it sits squeezed between the Hamburger singleton and D–H softness.
The cell's interior remains the open core; its boundary is now fully labeled.

## §The widened-FE moduli entered (fourth interrogation): collapse + the depth-1 exhibit

**The moduli collapses (relabeling lemma, PROVED-shape).** The apparent freedom of engineered
FEs lives entirely in the completion factor γ. If γ is allowed strip zeros, "widening" merely
relabels who owns the divisor (re-split Λ = γ′·F′ moves zeros between the ledgers — the honest
object is Λ's divisor). Forcing γ nonvanishing-in-strip (Γ-shapes: the only honest bookkeeping)
makes EVERY widened cell isomorphic to the original question. The "space between the Hamburger
singleton and D–H" is parameterized by where one hides the zeros — in γ (dishonest) or in F
(the wall). The widened moduli is a no-op for the cell — recorded so it is never re-entered.

**The depth-1 exhibit [PROVED, Lean, `ColumnRigidity.lean`, axiom-clean, umbrella 8992] — the
first POSITIVE rigidity theorem of the exact conjunction.** At the polynomial floor (single integral factor
1 − a·b^{−s}, zero-line σ = log a/log b; FE demands the mirror 1−σ integrally realized, i.e.
a·a′ = b):
- **prime frequency ⟹ walls only** (no nontrivial splitting of p): the single-pants case is
  rigid;
- **composite non-prime-power frequency** (b = 6 = 2·3: off-line FE-pair log2/log6, log3/log6)
  admits off-line pairs — but such single-frequency streams are NOT multiplicative (a₆ ≠ a₂a₃);
- **multiplicative column (b = p^k) ⟹ unique factorization quantizes**: a·a′ = p^k forces
  a = p^i, lines σ = i/k ∈ ℚ — irrational off-line lines (the no-FE witness's log2/log3) are
  excluded by UNIQUE FACTORIZATION; **σ = 1/2 is the unique self-dual integral line**.
Dropped-hypothesis witnesses, one each: no-FE → 1 − 2·3^{−s} (banked, IntegralMultiplicativeSoft);
no-multiplicativity → the frequency-6 pair; no-integrality → free a. The three-way interaction
FE × multiplicativity × integrality rigidifies where every proper sub-pair is free — the
headline conjecture's mechanism, exhibited as theorem at depth one.

**The honest caveat (dissolution at infinite depth).** The depth-k quantization σ ∈ (1/k)ℤ
densifies as k → ∞: the naive infinite-depth limit of the per-column mechanism is EMPTY. The
surviving content at full depth must be COHERENCE ACROSS COLUMNS — which is exactly where the
conjecture located the wall (the exact infinite product as a whole). The depth-1 theorem is the
mechanism's existence proof, not its limit.

## §CORRECTION: the three-way conjunction is refuted as sufficient (fifth interrogation)

**Counterexample [Lean in flight, `DegreeZeroOffline.lean`].** F(s) = (1−2·8^{−s})(1−4·8^{−s}):
integer coefficients (1, −6 at 8, +8 at 64), multiplicative (single 2-column), real, and it
satisfies the EXACT degree-0 functional equation F(s) = 8^{1−2s}F(1−s) (conductor 64, ε = 1) —
with zero lattices on Re s = 1/3 and 2/3: **off-line strip zeros inside FE ∧ multiplicativity ∧
integrality.** The §headline conjecture AS ORIGINALLY STATED (three-way) is FALSE; the depth-1
quantization theorem permitted exactly this (lines i/k) — quantization ≠ confinement, and the
self-dual-line theorem was the only line-forcing statement.

**What the counterexample teaches:**
- Its local roots have modulus 8^{2/3} > 8^{1/2}: it violates exactly the TEMPERED HALF-BOUND
  (Selberg's Euler-axiom θ < 1/2). Adding that bound as the fourth conjunct lands the cell in
  Selberg-class territory — real mathematics, but corpus (search-reachable; "Selberg + tempered
  ⟹ RH" is everyone's conjecture). Fails the program's novelty gate as OUR fourth axis.
- It is DIFFERENTIALLY ALGEBRAIC (exponential polynomial) — as is EVERY charged witness this
  program has ever constructed, in every cell.

**The corrected headline [CONJECTURE — the four-way conjunction]:**
> Within FE ∧ full multiplicativity ∧ integrality, divisor rigidity holds on the
> **hypertranscendental fiber**: an HT member of the conjunction cannot carry off-line strip
> charge. Equivalently: all off-line charge in the three-way cell is differentially algebraic —
> DA members exhaust the off-line divisor freedom (they have finite pants rank and live on
> quantized lattices), and the infinite-pants (HT) regime is where the conjectured conservation
> law binds.
Derived sub-conjecture **[C-DA]**: within FE ∧ mult ∧ ℤ, every DA member's strip divisor is a
finite union of quantized vertical lattices (lines i/k). VERIFICATION OBLIGATION before any
promotion: Ostrowski's structure theory for DA Dirichlet series (the hypertranscendence
machinery) — if DA Dirichlet members are finite-frequency-generated, C-DA reduces to
Ostrowski + ColumnRigidity + FiniteEulerInert shapes. Check the actual Ostrowski statement; do
not assume it.

**Why HT passes the gate where θ < 1/2 fails it:** the tempered bound is the Selberg axiom
(corpus, promptable). HT as the fourth coordinate is posed nowhere (HT literature never touches
zero location — and here HT is HYPOTHESIS, not conclusion, so the natural-boundary≠HT no-go
does not apply); the selecting evidence (every constructed charged witness is DA) is this
program's own corpus; and it welds the Goldilocks question to the branch's founding axis — the
fourth coordinate of the rigidity conjunction is the defining property of the field itself.

## §Ostrowski verified — C-DA corrected to C-DA′ (sixth interrogation)

**Verification landed** (`checks-ostrowski-da-dirichlet.md`; translation arXiv:2211.02088 of
Ostrowski, Math. Z. 8 (1920) 241–298, Theorems 1/6/7/8 read verbatim):

- **[VERIFIED-KNOWN] Ostrowski's structure theorem:** a convergent ordinary Dirichlet series
  satisfying an algebraic differential equation is a convergent power series
  Ψ(p₁^{−s}, …, p_β^{−s}) in FINITELY MANY prime exponentials (exponent ℤ-module finitely
  generated; coefficients with finite rational basis). Not merely "ζ is HT" — a genuine
  classification.
- **"DA ⟹ finite support" is FALSE** (exp(2^{−s}) is DA with infinite support, = Ψ(2^{−s}),
  Ψ = exp) — the finitely-many-PRIMES form is the correct reading.
- **[ABSENT] Q3:** no literature uses hypertranscendence as a hypothesis constraining zero
  location. The four-way conjecture's novelty is documented, not assumed.

**C-DA corrected → C-DA′.** The old "quantized to i/k lines" clause was single-factor
arithmetic only (integral power-series columns have algebraic-modulus roots — Ψ = 1−u−u² gives
an irrational line with integer coefficients). The correct invariant is PERIODICITY:

> **[C-DA′ — now theorem-shaped]** A multiplicative member whose stream is differentially
> algebraic has, by Ostrowski + column splitting (multiplicative smooth-supported streams
> factor as F = ∏ᵢ Ψᵢ(pᵢ^{−s}), finitely many columns), a strip divisor that is a union of
> VERTICAL ARITHMETIC PROGRESSIONS of periods 2π/log pᵢ — a vanishing column factor is
> invariant under its own period. (`DAColumnDivisor.lean` LANDED, axiom-clean, umbrella 8993:
> `columnForm_zero_periodic` — the transfer; `not_columnForm_of_aperiodic_zero` — the
> aperiodicity marker; `columnForm_example` — the degree-0 counterexample family inhabits
> ColumnForm.)

**The four-way conjecture, sharpest form:** within FE ∧ multiplicativity ∧ integrality, all DA
charge is vertically-PERIODIC charge; the HT fiber is the aperiodic-divisor regime.
Complementary unconditional fact [RECALLED-CHECK in flight]: ζ's zeros contain no infinite
vertical arithmetic progression (Putnam-type; Lapidus–van Frankenhuijsen/Martin–Ng
refinements) — verification running; if it lands, ξ sits outside every DA divisor pattern
UNCONDITIONALLY, and "the divisor's aperiodicity is the hypertranscendence signature" becomes
fully certified at the boundary.

## §The boundary certified at both ends (round close)

All verification and formalization landed (`checks-ostrowski-da-dirichlet.md` now carries both
literature sections; modules in umbrella at 8994, lint green, all axiom-clean):

- **DA side [THEOREM + VERIFIED]:** DA ∧ multiplicative ⟹ divisor = union of vertical
  arithmetic progressions (Ostrowski [VERIFIED, arXiv:2211.02088 translation] + column
  splitting + `columnForm_zero_periodic` [Lean]).
- **ξ side [VERIFIED-KNOWN, full strip]:** ζ's zero set contains no infinite vertical
  arithmetic progression ANYWHERE in the strip — Putnam (Amer. J. Math. 76 (1954), line),
  van Frankenhuijsen (J. Number Theory 115 (2005), quantitative, D ≥ 1/2),
  Lee–Sourmelidis–Steuding–Suriajaya (arXiv:1710.11367, all σ ∈ (0,1)∖{1/2}), FE reflection
  for σ < 1/2. (Correction banked: Martin–Ng/Li–Radziwiłł bound AP-terms that are NON-zeros —
  the AP-of-zeros bound is van Frankenhuijsen's.)
- **Counterexample [PROVED, Lean]:** `DegreeZeroOffline.lean` — dzo = (1−2·8^{−s})(1−4·8^{−s})
  with exact FE `dzo_fe`, multiplicative integral stream, order-1 off-line zero at σ = 1/3,
  class softness (`integralMultiplicativeFEClass_not_forcesRHParity`). The three-way
  conjunction's insufficiency is machine-checked end to end.

**The consolidated statement of the program's proof shape (register-marked):**
ξ's divisor is vertically APERIODIC [VERIFIED-KNOWN] while every DA member of the
multiplicative class has vertically PERIODIC divisor [THEOREM-shaped: verified Ostrowski +
Lean transfer] — the divisor itself already witnesses the escape from the differentially
algebraic regime, unconditionally. The four-way conjecture [CONJECTURE] is that this escape is
also exactly where divisor RIGIDITY begins: within FE ∧ multiplicativity ∧ integrality, the
periodic (DA) fiber exhausts all off-line freedom, and the aperiodic (HT) fiber — where ξ
provably lives — carries the conservation law. Its two halves now have entirely different
statuses: the DA half is a short paper-register proof away from theorem (assemble Ostrowski +
splitting + transfer); the HT half is the open core, now with a certified boundary, a
documented-ABSENT novelty position, and the branch's founding axis as its subject.

## §C-DA′ assembled [PROVED HERE — paper register, mixed Lean/verified-literature]

**Theorem (C-DA′).** Let F = Σ aₙ n^{−s} be an ordinary Dirichlet series, convergent in a
half-plane, with multiplicative coefficients, whose stream is differentially algebraic. Then
the zero set of F in its half-plane of analyticity is a union of vertical arithmetic
progressions: every zero s₀ lies on a full progression {s₀ + 2πik/log p : k ∈ ℤ} ⊆ Z(F) for
one of finitely many primes p.

*Proof.* (1) Ostrowski's structure theorem [VERIFIED, arXiv:2211.02088 translation of Math. Z.
8 (1920), Thms 1/6/7/8]: F = Ψ(p₁^{−s}, …, p_β^{−s}), a convergent power series in finitely
many prime exponentials — the support lives on p₁…p_β-smooth integers. (2) Column splitting
[elementary]: multiplicativity of aₙ on smooth support factors the series, on its half-plane of
absolute convergence, as the FINITE product F = ∏ᵢ Ψᵢ(pᵢ^{−s}) of one-variable column series
(aₙ = ∏ a_{pᵢ^{vᵢ}}; finitely many columns, each a sub-series of the absolutely convergent
whole); the identity extends to the domain of analyticity by the identity theorem. (3) The
periodicity transfer [Lean: `columnForm_zero_periodic`]: a zero of a finite column product
forces one factor to vanish, and that factor is invariant under its own period 2π/log pᵢ. ∎

**Corollary (unconditional DA-escape of ξ).** ζ's zero set contains no infinite vertical
arithmetic progression anywhere in the strip [VERIFIED-KNOWN: Putnam; van Frankenhuijsen;
Lee–Sourmelidis–Steuding–Suriajaya + FE reflection], and ζ has zeros; hence ζ's stream is not
(multiplicative ∧ DA)-column-structured — the divisor alone witnesses the escape from the
differentially algebraic regime. (Consistent with — and a divisor-level strengthening of the
reading of — Ostrowski's own hypertranscendence of ζ.)

Gate note: NOVEL (the divisor-level statement and the periodicity invariant are posed nowhere;
Q3 search documented ABSENT) × SIGNIFICANT (it is the DA half of the four-way conjecture — the
proof shape's first fully discharged fiber). The open core is now exactly the HT fiber.
