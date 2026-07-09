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

---

## The four-way conjecture refuted at both ends; the repair is a dichotomy (2026-07-09)

### Refutation, degree-zero end [PROVED HERE — Lean]

`IntegralFEPolynomial.lean`. Structure theorem for the exact degree-zero class
(`IntegralMultiplicativeFEClass`: integral multiplicative coefficients, L-series representation
at every point, exact FE `f s = Q^{1−2s} f(1−s)`):

> **Theorem.** Every member is either identically zero or the L-series of a **finite-support**
> stream — a Dirichlet polynomial in finitely many prime columns
> (`integralMultiplicativeFEClass_finite_or_zero`, `finiteSupport_multiplicative_columnForm`).
> Consequently every zero of a member is vertically periodic
> (`integralMultiplicativeFEClass_zero_periodic`).

Mechanism: integrality forces nonzero coefficients to have norm ≥ 1, so an infinite-support
series is non-summable on `Re s ≤ 0`, where mathlib's junk-value convention forces `f = 0`; the
FE transports the vanishing to `Re s ≥ 1`; the eventually-zero dichotomy for L-series then
collapses the member. Integrality here **replaces the finite-order axiom** of the classical
degree-zero classification (Kaczorowski–Perelli, Acta Math. 182 (1999): degree-0 members of S♯
are Dirichlet polynomials supported on divisors of the conductor — [VERIFIED-KNOWN], see
checks-ostrowski-da-dirichlet.md). **The HT fiber of the degree-zero cell is empty**: the
four-way conjecture is vacuous there.

### Refutation, gamma-widened end [PROVED HERE — Lean + one paper step]

`GammaCellMobility.lean`, `ZetaRealStrip.lean`, `DichotomyInstances.lean`. The widened cell
`GammaFECell`: integral multiplicative coefficients, L-series representation on `Re s > 1`, and
a strip-nonvanishing completion factor γ with `γ(1−s)f(1−s) = γ(s)f(s)` on the open strip.

- `zeta_mem_gammaFECell` — ζ is a member (γ = Γ_ℝ, FE = `completedRiemannZeta_one_sub`).
- `gammaFECell_mul_dzo` — **convolution mobility**: the cell absorbs multiplication by the
  degree-zero counterexample `dzo`.
- `zetaMulDzo_order_one` / `gammaFECell_carriesChargeAt_ρdzo` — ζ·dzo has a **simple zero at
  Re = 1/3** (odd, charge −1), interior to the strip. The input ζ(1/3) ≠ 0 is now a tree
  theorem: `riemannZeta_real_strip_neg` (ζ < 0 on the real strip segment, via the paired
  Dirichlet eta series — a mathlib gap closed in `ZetaRealStrip.lean`).
- Paper step (register: [PROVED HERE, paper]): ζ·dzo is **hypertranscendental** — DA functions
  form a differential field, dzo is a nonzero Dirichlet polynomial (DA), so ζ·dzo DA would force
  ζ = (ζ·dzo)/dzo DA, contradicting Ostrowski [VERIFIED, arXiv:2211.02088 translation].

**The four-way headline is dead**: FE ∧ multiplicativity ∧ integrality ∧ hypertranscendence does
NOT confine the divisor to the line. The HT fiber carries off-line charge.

### The mobility principle [PROVED HERE — Lean, the mechanism of the refutation]

The cell is a monoid under Dirichlet convolution, and its off-line-charged DA members act on it.
Any rigidity predicate closed under the class operations is invariant under this action, so
**"divisor ⊆ line" is unprovable for every convolution-stable class** — the only rigidity shape
that survives the action is a statement about the action-invariant part of the divisor. The
constructed charge is exactly the mobile kind: `zetaDzo_witness_zero_periodic` — the off-line
zero of ζ·dzo rides the full base-8 vertical progression.

### The repair: the periodicity dichotomy [CONJECTURE C-PD]

> **C-PD.** Every strip zero of a `GammaFECell` member lies on the critical line or on a full
> vertical arithmetic progression of zeros. Equivalently: **off the critical line, the divisor
> is vertically periodic** — the aperiodic part of the divisor lives on the line.

Formal predicate: `PeriodicityDichotomy` (`PeriodicityDichotomy.lean`). Status matrix, all Lean:

| region / operation | status | anchor |
|---|---|---|
| DA fiber (column forms) | **theorem** | `columnForm_periodicityDichotomy` |
| degree-zero class | **theorem** | `integralMultiplicativeFEClass_periodicityDichotomy` |
| stability under DA action | **theorem** | `periodicityDichotomy_mul_columnForm` |
| aperiodic-core subadditivity | **theorem** | `aperiodicZeroAt_mul` |
| constructed witnesses | consistent | `zetaDzo_witness_zero_periodic` |
| ζ-instance ⟺ RH (mod no-AP) | **theorem** | `periodicityDichotomy_zeta_iff_riemannHypothesis` |
| C-PD ⟹ RH (mod no-AP) | **theorem** | `gammaFECell_dichotomy_implies_rh` |

The no-AP hypothesis is [VERIFIED-KNOWN]: Putnam 1954, van Frankenhuijsen (quantitative), LSSS
arXiv:1710.11367 (all σ ≠ 1/2); for Dirichlet L-functions Martin–Ng arXiv:1109.1788 (nonzero
values in every vertical AP, precluding full zero-progressions). So **C-PD implies RH by a
machine-checked composition**, with a single literature-discharged hypothesis.

Boundary table — each clause certified load-bearing:

| drop | witness | certificate |
|---|---|---|
| multiplicativity | Epstein ζ of x²+5y² (h=2): proven off-line zeros | non-multiplicativity machine-checked: `repCount_not_multiplicative` (r(2)=0, r(3)=0, r(6)=4); off-line zeros [VERIFIED-KNOWN] Davenport–Heilbronn/Voronin/Lee |
| FE | Σ 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s) [VERIFIED identity] | off-line **aperiodic** poles at ρ/2 (aperiodicity from ζ's no-AP; ρ₁/2 at height ≈7.07 is no ζ-zero) |
| integrality | — | truth-side irrelevant (C-DA′ holds without ℤ); its role is proof-register (discreteness engine) |
| nothing | — | no witness constructible; the corpus contains **no** multiplicative self-dual series with a proven off-line zero at all [Q2, VERIFIED-KNOWN] |

Novelty: [ABSENT] — no prior periodicity dichotomy, no "aperiodic part on the line," no
GRH-relative-to-temperedness statement (Q3, seven searches, checks file). Corpus relation: C-PD
**extends Grand-RH-for-the-Selberg-class beyond temperedness** — inside S the dichotomy plus
no-AP collapses to GRH; outside S, where GRH is false (dzo violates θ < 1/2 and has off-line
zeros), C-PD predicts the exact failure mode: periodic. Strength marker: C-PD for L(s,χ), real χ,
forbids Landau–Siegel zeros (a lone real off-line zero would have to ride a vertical progression,
excluded by Martin–Ng) — apex-grade, as expected for the card's headline.

Branch reading (constraint, not flow): a vertical progression of period 2π/log b is the orbit of
the b-column clock — **flow-generated divisor**; DA = finitely many clocks (Ostrowski); an
aperiodic divisor has no generating clock — **constraint-only divisor**. C-PD says: clockwork
divisor may sit anywhere in the strip (dzo does); constraint-only divisor is pinned to the fixed
locus of the involution s ↦ 1−s. The founding metaphor, at the divisor level, with the DA/HT
axis as the separating hypothesis.

### The completion-parity dichotomy [PROVED HERE — Lean]

`CompletionParity.lean`. Interrogating the γ-clause itself produced a theorem: in central normal
form F = (s−1/2)^m·G (G a symmetric nonvanishing unit on the strip),

> a **bare** completion factor always exists (`completion_raw_exists` — a locally constant sign
> pattern over the half-strips realizes the sign cocycle; the unrestricted γ-clause carries no
> information beyond divisor symmetry), while a **continuous** completion exists **iff the
> central order m is even** (`completion_continuousOn_iff_even_center` — odd m forces
> γ(1−s) = −γ(s) off the center, and continuity at the reflection's fixed point gives
> γ(1/2) = 0).

The obstruction is the reflection's fixed-point μ₂-charge — **the same seam-sign bit as the
equivariant root program** (crease ledger anchored at ξ(1/2) > 0, `EquivariantRootDissolution`/
`CreaseHolonomy`). Completing a functional equation and taking equivariant square roots are
obstructed by one and the same fixed-point invariant: the Goldilocks lane and the seam-sign lane
weld here. For ξ: m = 0, completable — consistent.

### The proven region of C-PD, completed this round [PROVED HERE — Lean]

**Finite-prime sector** (`FinitePrimeSectorDichotomy.lean`): a multiplicative stream supported
on numbers composed of finitely many primes, absolutely summable on the open right half-plane,
has every half-plane zero of its L-series on a full vertical arithmetic progression
(`finitePrime_zero_periodic`), hence satisfies the dichotomy (`finitePrime_periodicityDichotomy`).
**No differential-algebraicity is assumed — the columns may be hypertranscendental.** The first
HT cases of C-PD are theorems: finitely many column clocks produce only clockwork zeros,
whatever the transcendence of the columns. Carried by mathlib's
`EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers` + termwise column shift invariance.

**Unbounded gear count** (`UnboundedGearCount.lean`): the parametric gear family
`gear m = (1 − 2·(2^m)^{−s})(1 − 2^{m−1}·(2^m)^{−s})` (exact FE, conductor 2^m, single-2-column
integral multiplicative stream) and its finite products certify that the degree-zero class
carries members with arbitrarily many distinct off-line zero lines σ = 1/m
(`integralMultiplicativeFEClass_gear_count_unbounded`) — each member's clockwork is finite, but
the class's gear count is unbounded. C-PD's periodic clause must and does accommodate this.

### Where C-PD's content now lives — the open frontier, exactly bounded

The dichotomy is proven on: the DA fiber, the degree-zero class, the finite-prime sector (HT
included), and it is stable under the DA action. Every proven region is **finite clockwork**;
every escape from periodicity therefore requires **infinite prime support** — the exact infinite
Euler product, consumed whole. This matches the card's register constraint from the start, and
it names the mechanism: an aperiodic strip zero of an infinite product is a **collision of
incommensurable column clocks** — the periods 2π/log p over all p generate a dense (gapless)
rate spectrum, which is precisely the weld spectrum density invariant of the branch. Finitely
many clocks: zeros locked to progressions. All clocks at once: the divisor can leave every
progression — and C-PD says that where it does, it sits on the constraint's fixed line.

Next generative moves (the round opens, not closes):
1. **Clock-collision analysis** — the smallest infinite-support attack: quantify how zeros of
   finite-prime truncations (all periodic, periods 2π/log p) move as columns are added; an
   aperiodic limit zero is a joint resonance of the dense rate lattice. The rate-lattice/weld
   instruments (`weld spectrum density`, rate-lattice interface) now have a divisor-level
   consumer.
2. **Completion parity up the tower** — the central-order bit obstructing continuous completions
   is the τ = 0 germ of the crease ledger; transport it along the 2^k-rungs: does rung-k
   equivariant completability read the ledger parity at depth k? The two welded lanes now share
   one invariant to push jointly.
3. **C-PD on sparse infinite supports** — between finite-prime (proven) and full Euler products
   (ζ): streams on infinitely many primes with lacunary column data; the first place a genuinely
   new periodicity/aperiodicity mechanism can be isolated.

### The three named moves, executed [PROVED HERE — Lean] (2026-07-09, continuation)

**Move 1 — clock collision, re-cut as constraint (`ClockEscape.lean`).** Not a dynamical study
of moving zeros but a closure theorem: vertical progressions with periods from a FIXED finite
inventory are closed under locally uniform limits of their carriers
(`periodic_zero_limit` — pigeonhole on the finite period set + limit exchange through
`TendstoLocallyUniformlyOn.tendsto_comp`). Contrapositive, machine-checked
(`aperiodic_zero_clock_escape`): **an aperiodic zero of a limit function admits no approximation
by clockwork zeros of bounded period inventory — the responsible clock escapes every finite
set.** For Euler products: an aperiodic strip zero is a tail-of-the-prime-spectrum phenomenon;
no finite sub-clockwork produces it. This is germ-blindness at the divisor level, now with a
certificate: "consume the exact infinite object whole" is a theorem about the divisor, not a
slogan. (The Hurwitz zero-approximation input is carried as an explicit hypothesis.)

**Move 2 — completion parity up the tower (`CompletionParityTower.lean`).** The rung-k central
normal form `(s−1/2)^{m/2^k}·G` admits a continuous completion **iff `2^{k+1} ∣ m`**
(`rung_completion_iff_next_dyadic`): each completed rung certifies one more dyadic divisibility
— **the completability bits of the root ladder are the 2-adic digits of the central order.**
Total completability of the ladder ⟺ m = 0 ⟺ the carrier does not vanish at the reflection's
fixed point (`completion_tower_iff_center_order_zero`). The crease anchor (ξ(1/2) > 0) is
equivalent to total completability — the two welded lanes now share a joint tower invariant, and
the 2^k-rung hierarchy of the program is readable at ONE point as a 2-adic digit string.

**Move 3 — the columnar/interferential split (`ColumnarInterferential.lean`).** A zero of a
factored carrier is *columnar* (some factor vanishes — rides that column's progression,
`columnar_zero_periodic`) or *interferential* (every factor nonvanishes). Location theorem: an
absolutely convergent product with all factors nonvanishing is nonvanishing
(`tprod_one_add_ne_zero`, via summable complex logs), so **interferential zeros exist only where
the product representation has broken down — in the analytic continuation**
(`no_interferential_zero_in_product_region`). For ζ every Euler factor is strip-nonvanishing:
ζ's strip divisor is 100% interferential — flow-invisible, constraint-only. Final form of the
conjecture:

> **C-PD, sharpest register:** the flow-visible (columnar) divisor is clockwork [THEOREM]; the
> constraint-only (interferential) divisor lies on the fixed line of the involution
> [CONJECTURE]. Sparse infinite products of single columns stay columnar — consistent; genuine
> interference requires the continuation of a divergent product, and there the dichotomy asserts
> the constraint pins what no clock generates.

**Statement hygiene** (μ-member): 1/ζ is a cell member (μ(n): integral, multiplicative,
completed FE) whose strip POLES are ζ's zeros — C-PD for meromorphic members is a divisor
statement (zeros and poles), exchanged under inversion; the zero-form and pole-form carry the
same content.

### The theory of the interferential divisor [PROVED HERE — Lean, + one labeled mechanism conjecture]

The named native object now has a theory. Its proven sides:

**Location** (`ColumnarInterferential.lean`): interferential zeros exist only in the analytic
continuation — never in the absolute-convergence region of the product.

**Approximation** (`ClockEscape.lean`): no approximation by clockwork zeros of bounded period
inventory; the responsible clock escapes every finite set.

**Finite-support impossibility, both mechanisms.** Summable regime:
`FinitePrimeSectorDichotomy.lean` — finitely many columns with strip-summable data have only
columnar (periodic) zeros. Boundary regime (`NoCrossColumnHealing.lean`): **cross-column healing
is impossible** — an analytic element of the product at a boundary point where the partner is
regular and nonvanishing yields an analytic element of the obstructed column
(`no_healing`, `no_healing_finset` via the healing-transfer quotient). A natural boundary of one
column is inherited by every finite column product except along the partners' discrete divisors.
So continuation beyond the columns — the interferential habitat — is unreachable with finitely
many factors through either mechanism: **interference is irreducibly an infinite-product
phenomenon.**

**Depletion invariance** [already in tree]: dividing out finitely many strip-nonvanishing Euler
factors does not change the strip divisor (`FiniteEulerInert` machinery) — the interferential
divisor is a fixed point of the depletion action, common to the whole family of P-depleted
streams; no finite coefficient modification along depletion can see it.

**The global-clock trichotomy** (`DivisorStabilizer.lean`): the vertical stabilizer of a zero
set is an additive subgroup of ℝ, closed for closed carriers; for a nonzero analytic carrier it
is cyclic — one primitive global clock or none (`vStab_cyclic_of_analytic`, dense case killed by
the identity principle). Separation: the two-prime member `(1 − 2·2^{−s})(1 − 9·3^{−s})` is
pointwise clockwork at every zero yet has trivial global stabilizer
(`twoClock_vStab_trivial` — a common period would force `2^a = 3^b`): **the rate lattice's
incommensurability shatters global vertical symmetry into per-column clocks.** The pointwise
period, not the global stabilizer, is the invariant C-PD correctly uses; and single columns keep
a genuine global clock (`dzo_vStab_nontrivial`).

**Mechanism reading [CONJECTURE — mechanism register].** An interferential zero is an exact
resonance of the incommensurable column-clock phases — an event no finite sub-community of the
Euler product produces (now a theorem, both regimes). The classical folklore that on-line
vanishing is codimension-one (the completed FE makes the carrier effectively real on the fixed
line — the Hardy Z shape) is [KNOWN]; the C-PD complement is the new statement-shape: **off the
line, vanishing is codimension-two and has no alignment resource except a column clock** — so
off-line divisor is clockwork, and exact resonance without a clock happens only where the
involution supplies the reality constraint. The round's theorems are precisely this conjecture's
finite shadows: clock escape (no bounded inventory aligns), no-healing (no finite regrouping
reaches the habitat), finite-prime dichotomy (finite communities are clockwork), stabilizer
separation (incommensurability forbids a global surrogate clock).

---

## Re-cut: constraint side, no clocks (2026-07-09, after audit)

**Verdict correction absorbed:** C-PD decomposes as (trivial on DA members) ∪ (RH restated on ζ)
— synonym, dual-gate FAIL; the periodicity/orbit framing was a flow picture. The fourteen-module
complex is retained as the FLOW-SIDE NO-GO BANK only. What survives on the constraint side:
completion parity (fixed-point μ₂-bit) and its 2-adic tower.

**The canonical constraint-side object: the reflection cocycle** `h_F(s) = F(1−s)/F(s)` —
intrinsic (no completion chosen), multiplicative in the carrier (`h_{FG} = h_F·h_G`), satisfying
`h(s)·h(1−s) = 1`; a completion factor is exactly a trivialization; the completion-parity bit is
its fixed-point value. For an exact-conductor member, `h_f = Q^{2s−1}`: the FE datum is the weld
ray `log Q`, unique for nondegenerate members, ADDITIVE under Dirichlet convolution through the
tree's injective weld-class homomorphism. The functional equation stops being an axiom and
becomes a computed class in 𝓜⁺. (Lean: `ReflectionCocycleClass.lean`.)

**The FE datum's transcendence class stratifies the cell [derivable from KNOWN — recorded as
reading, not claimed as new]:** dlog h_ζ(s) = ψ(s) − log 2π − (π/2)tan(πs/2) (digamma exposed by
the reflection + duplication formulas), so ζ's reflection cocycle is HYPERTRANSCENDENTAL (one
step from Hölder); every degree-zero member's cocycle is elementary. Paired with the structure
theorem (degree-0 = Dirichlet polynomials): **DA cocycle ⟺ degree zero; genuine archimedean
content ⟹ HT cocycle.** The constraint of the arithmetic object has no generative rule either —
the branch's object is the welded pair (carrier, cocycle), both hypertranscendental, and the
field's questions are about the classes of cocycles multiplicativity admits, not about orbits of
zeros.
