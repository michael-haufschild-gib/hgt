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

**The completion obstruction located exactly [derivable from KNOWN + this card's cocycle
computation — reading, one paragraph]:** if γ is ANY completion of ζ (γ(s)/γ(1−s) = h_ζ(s)) and γ
were differentially algebraic, then h_ζ = γ(s)/γ(1−s) would be differentially algebraic (DA
functions form a differential field closed under the affine substitution s ↦ 1−s), contradicting
the hypertranscendence of h_ζ (dlog h_ζ exposes ψ; Hölder). Hence **every completion of ζ is
hypertranscendental**: the reflection constraint of the arithmetic carrier cannot be trivialized
inside any differentially algebraic algebra. The Γ-function's hypertranscendence is not an
accident of the classical completion — it is forced by the cocycle. This is obstruction-shape (i)
of the mission (why no rule exists), located at the completion: the constraint's own trivializers
are constraint-only objects.

## [CONJECTURE C-COC] The cocycle-transcendence dichotomy (the branch-native successor)

> For an integral multiplicative carrier with meromorphic continuation: the reflection cocycle
> `h_F = F(1−s)/F(s)` is differentially algebraic **iff** `F` is a Dirichlet polynomial.
> Equivalently: the involution `s ↦ 1−s` never acts differentially-algebraically on a genuine
> Euler product — the σ-antisymmetrization of `log F` (pure prime-frequency data) is never DA
> unless the arithmetic is finite.

Position. Not Ostrowski (carrier-HT does not force cocycle-HT — an exact DA functional equation
for an HT carrier is a priori possible; the conjecture is that arithmetic forbids the
cancellation). Not Kaczorowski–Perelli (no postulated Γ-shape, no finite-order axiom). Not a
zero statement (no RH content, no synonym risk). The naked fact "every completion of ζ is HT" is
[BRIDGE] to parametrized difference Galois theory (the ∂-Galois group of the order-1 ℤ/2-module
is maximal) — refused as progress; C-COC is what the parent cannot state: which ARITHMETIC
carriers admit DA cocycles at all. This is the Ostrowski theorem for the FE datum: carrier
hypertranscendence was 1920; datum hypertranscendence is the branch's.

Proven cases [Lean]: everywhere-valid representations (structure theorem — the cocycle is
`Q^{2s−1}`, DA, and the carrier is a polynomial: both sides of the dichotomy verified);
`h = 1` with everywhere-valid representation (`CocycleKernelTrivial.lean`: exact self-reflection
forces the constant carrier — the kernel of the cocycle map is trivial).

Killed en route: splitting-uniqueness of the arch/prime class decomposition (reduces to K–P
H-invariant theory — [SEARCH]); the 2-torsion of H¹(ℤ/2, units) (its instantiation is the
triviality that `F(s)F(1−s)` is symmetric).

**[OPEN CORE]** exactly located: half-plane representation + continuation, `h` DA, no order
axiom. Smallest cell `h = 1`: can a genuine integral Euler product satisfy `F(1−s) = F(s)`
exactly? Hamburger's method is unavailable by design (no Γ, no theta); the two Dirichlet
representations live on disjoint half-planes and meet only through the continuation.
First lemma to attempt: symmetry pins the modulus on line-pairs symmetric about `Re = 1/2`
while integrality bounds the convergence side from below — make the two bounds collide.

**The h = 1 cell, finite order: EMPTY [one-paragraph proof; also VERIFIED-KNOWN via K–P degree-0
at conductor 1].** Let F be an ordinary Dirichlet series with a₁ = 1 and finite abscissa,
entire of finite order, with F(1−s) = F(s) exactly. Far right (re = σ₁ large) the tail bound
gives |F − 1| ≤ 1/2 uniformly in t; symmetry copies this to re = 1 − σ₁; Phragmén–Lindelöf
(finite order) bounds F on the strip between; F is bounded entire, hence constant, hence ≡ 1.
Integrality is UNUSED — finite order is the load-bearing axiom, so the open core of C-COC's
smallest cell is exactly: **infinite-order symmetric continuations of genuine Dirichlet
series.**

**Attack mechanism for the infinite-order cell [CONJECTURE — the frequency-sign obstruction]:**
a symmetric carrier wants F = exp(E) with E symmetric; symmetrizing any right-half-plane
frequency content (n^{−s}) necessarily creates the mirrored positive frequencies (n^{s−1}), and
exponentiation propagates them — while an ordinary Dirichlet series admits only nonpositive
frequencies. The conjecture: no infinite-order escape exists because the continuation cannot
launder positive frequency content out of a symmetric exponent; integrality, if needed at all,
enters as the discreteness that forbids frequency cancellation in the limit. First falsification
target: construct any (non-integral) symmetric ordinary Dirichlet series of infinite order — the
naive exp-constructions all fail on frequency signs.

**Correction to the attack mechanism (self-attack, same day):** the frequency-sign obstruction as
stated is too naive — the right-end Dirichlet expansion and its left-end mirror live on disjoint
half-planes, and disjoint asymptotic expansions never clash for a generic entire function. The
true crux is quantitative: by the Phragmén–Lindelöf alternative, an infinite-order escape must
sustain `log log |F| ≳ π|t|/w` along a sequence inside the fixed transition strip while staying
within `1/2` of `1` on both sides (and Arakelyan approximation on the two-half-plane set fails —
the strip complement is not locally connected at infinity — so analysis forbids nothing cheaply
in either direction). The h = 1 cell therefore splits into: (i) [CONSTRUCTION TARGET] a
non-integral analytic escape — if built, it proves C-COC's content is genuinely arithmetic;
(ii) a directed check whether integrality already forces finite order for continued Dirichlet
series (a Pólya–Carlson-type circle — if the literature has it, the cell closes by the
Phragmén–Lindelöf paragraph above); (iii) failing both, the named crux: **arithmetic versus
harmonic measure** — an integral multiplicative Euler product cannot sustain doubly exponential
strip growth at fixed configuration. No flow enters any branch.

**Boundary of the known, quoted (checks file, integrality-vs-order round): [ABSENT]².**
(i) No theorem derives an order/growth bound on the continuation from integer coefficients — the
integer-coefficient corpus (Estermann 1928, Kurokawa 1985, Bhowmik et al.) is exclusively
continuation-vs-natural-boundary dichotomies keyed to cyclotomy, with no vertical-order control;
"finite order" occurs only as a hypothesis (Hamburger, Hecke, Selberg (P2), Carlson), never as a
conclusion. (ii) The infinite-order gammaless symmetric case is unposed: Hamburger's hypothesis
is verbatim "(s−1)^m F(s) is entire of finite order", Hecke's "an entire function of finite
order"; the excised gap is exactly our cell. Consequently the [OPEN CORE] stands as stated —
**order control from arithmetic** — and its novelty position is maximal: the question itself is
absent from the corpus, not merely its answer. (Side note: Estermann's natural-boundary members
are the classical stock feeding the no-healing theorem's hypotheses — the NB-column regime is
populated by exactly the non-cyclotomic integral Euler products.)

**C-COC architecture at current depth.** Conjecture posed (cocycle-transcendence dichotomy);
machine-checked cases: everywhere-rep (structure theorem) and h = 1 everywhere-rep
(`CocycleKernelTrivial.lean`: `symmetric_multiplicative_integral_eq_one`,
`reflCocycle_eq_one_iff_const` — the reflection-cocycle map is faithful); paper case: h = 1
finite order (Phragmén–Lindelöf paragraph; integrality unused, isolating the order axiom);
boundary of the known quoted verbatim; crux named (arithmetic vs harmonic measure at fixed
configuration); standing falsification target: a non-integral infinite-order symmetric escape
(its difficulty is exactly the Arakelyan two-ends failure). No clause of this consumes a flow.

**Overlap rigidity and the thick-support sharpening (h = 1 cell, third cut).**
[Tool, Lean in flight — `OverlapRigidity.lean`]: a Dirichlet series absolutely convergent past
the reflection center (`σ_a < 1/2`) and symmetric on the overlap strip is constant — evaluating
the symmetry ON the central line turns it into an absolutely convergent sine series in the
frequencies log n vanishing identically; mean-value orthogonality kills every coefficient. No
order hypothesis, no Phragmén–Lindelöf, no contour. Consequences (the knowledge):
- **Sparse integral streams cannot escape**: infinite integral support that is sparse has
  σ_a < 1/2, and symmetry kills it — sparseness and symmetry are incompatible; the two threats
  to rigidity cannot coexist.
- **Thickness is forced**: an escape needs σ_a ≥ 1/2; with |aₙ| ≥ 1 on support this forces
  support counting size ≳ x^{1/2}. The open core sharpens to: can √x-THICK multiplicative
  integral arithmetic sustain infinite order while exactly symmetric?
- **Termwise constructions all die**: any candidate built as Σ cₙ(n^{−s} + n^{s−1}) explodes
  pointwise on the right flank whatever the decay of cₙ — the mirror content of an escape can
  never be series-visible on the right; the continuation must transcend the series.
- [CONJECTURE] The boundary case σ_a = 1/2 falls to an L²/Besicovitch boundary-value refinement
  (both expansions carry the same boundary function on the shared line from opposite sides; the
  ±log n frequency systems then force zero). [OPEN CORE after that]: σ_a ∈ (1/2, 1] — the thick
  regime.

**Pattern note (the program's recurring mechanism):** the kill reads the constraint AT ITS FIXED
LOCUS — on the central line the reflection degenerates to a linear condition (a vanishing sine
series), exactly as the completion obstruction degenerated to the fixed-point parity bit and the
crease ledger read the on-line orders. The involution's fixed locus is where the constraint
becomes computable; every load-bearing theorem of this card so far is a fixed-locus evaluation.

**Exploration of the fixed-locus principle (h = 1 cell, fourth cut).**
- [BRIDGE, named honestly] The program's recurring mechanism — completion parity, crease ledger,
  sine-kill — is ℤ/2-equivariant localization (Smith-type): after inverting 2, the equivariant
  theory of the strip is the theory of the fixed line. The principle is corpus; the instances are
  ours; the PREDICTION is the value: every σ-symmetric carrier question admits a line-reduction.
- [PROVED-shape, corollary of overlap rigidity] Divergence criterion: a symmetric integral escape
  has Σ‖aₙ‖n^{−σ} = ∞ for every σ < 1/2 — sparse-and-small is dead in one line.
- [CONJECTURE, attackable] Besicovitch stratum: at moderate thickness (Σ_{supp} 1/n < ∞, density
  up to ~√x·polylog), the carrier is line-L²; both expansions have mean-square boundary values on
  the shared line from opposite sides, and the ±log n frequency systems carrying one boundary
  function kill all coefficients — the σ_a = 1/2 kill extends across the stratum.
- [OPEN CORE, irreducible cell after the above] ζ-thick support (Σ_{supp} 1/n = ∞): line-L² fails,
  no boundary pairing exists; the carrier is mean-square-visible only strictly right of the line.
  The final form of the h = 1 question: can ζ-THICK integral multiplicative arithmetic sustain an
  exactly symmetric infinite-order continuation? Everything thinner is closed or closable.
- [SEARCH, restated in cocycle language] Phase pinning: on the fixed line FE + Schwarz determine
  arg F (the Hardy Z fact); overlap rigidity is the degenerate collision where the series reaches
  the line and pins the modulus too — the open core is exactly the regime where the constraint
  holds the phase and the arithmetic withholds the modulus.

**Correction (self-attack on the fourth cut, same day): the Besicovitch stratum is DEAD.**
The proposed line-L² pairing miscalibrated the Hardy geometry of Dirichlet series: by the Bohr
shift, an ℓ²-coefficient Dirichlet series has its L² boundary theory half a plane to the right
of its convergence boundary (the HLS space lives at +1/2). With bₙ = aₙn^{−1/2} ∈ ℓ², the Hardy
boundary line of F − 1 is re s = 1, not the critical line: mean-square data never reaches the
involution's fixed line for σ_a ≥ 1/2. Both the σ_a = 1/2 Besicovitch conjecture and its stratum
extension are withdrawn. The h = 1 open core stands as: σ_a ≥ 1/2, infinite order — with the
sparse-kill (overlap rigidity) and the finite-order kill (Phragmén–Lindelöf) as its only proven
reductions; ζ-thickness remains a heuristic emphasis, not a proven stratum boundary.

**Residue of the failed attack [the structural reason the core is hard]:** the Hardy line
re = σ_a + 1/2 of a Dirichlet series is symmetric under s ↦ 1−s only when σ_a = 0 — exactly the
regime overlap rigidity already kills. Wherever a symmetric carrier survives, the involution's
pairing (across re = 1/2) and the mean-square pairing (across the Bohr-shifted line) are
STRICTLY misaligned: no line carries both structures. Any future attack must either build an
L²-type theory native to the involution's line (not Bohr-shifted — i.e., not inherited from the
ℓ²-coefficient geometry), or find a third structure that lives on the fixed line outright — the
crease/parity data being the only currently known example.

## [CONJECTURE INT-ORDER] — the keystone: integrality bounds order

> An ordinary Dirichlet series with integer coefficients and finite abscissa whose continuation
> is entire (or meromorphic with finitely many poles) is of FINITE ORDER.

A Pólya–Carlson analogue in the order variable: the corpus's integrality theorems control
DOMAIN (continuation vs natural boundary — Pólya–Carlson, Estermann, Kurokawa), never GROWTH;
"finite order" occurs in the literature only as a hypothesis, never a conclusion ([ABSENT],
verified this session). Position: keystone — INT-ORDER closes the h = 1 cell outright (the
Phragmén–Lindelöf paragraph applies) and collapses every open cell of C-COC to finite order,
where the DA-side classification finishes. Flowless: growth vs discreteness at fixed
configuration.

Consistency checks run: integral single columns cannot violate it (integral power series =
polynomial or radius ≤ 1; Pólya–Carlson splits into rational = finite order vs natural boundary
= no continuation); the corpus's continuable integral examples (cyclotomic/Estermann) are
shifted-zeta products, finite order. No cheap kill in either direction: the Mellin-dual
integer-jump floor (A(x) jumps by ≥ 1 forever on infinite support — a permanent lower bound on
the remainder against any smooth main term) bounds left-vertical DECAY from below, while
infinite order concerns upper growth — the two-sidedness is genuine.

Native attack surface: the Mellin dual, where integrality acts pointwise (integer jumps), not
through coefficient norms — the first purchase point for the discreteness engine that is not
filtered through absolute convergence. Falsification target: polynomial-size integer
coefficients with an entire infinite-order continuation; the column examples show infinite
order demands factorial-type fine-tuning, which integrality forbids — that sentence is the
conjecture's content, and its proof or refutation is a new rigidity axis either way.

**INT-ORDER worked (both directions, same day).**
- [CONJECTURE, mechanism form] Every known entire-continuation mechanism for ordinary Dirichlet
  series (theta/FE, periodic-coefficient Hurwitz combinations, cyclotomic/Estermann products) is
  finite-order by construction; the sole known infinite-order route is everywhere-convergence of
  the series itself — and integrality provably forbids it (norm-≥-1 terms cannot vanish at
  σ ≤ 0; the structure theorem's mechanism). INT-ORDER ⟺ "there is no third mechanism." A
  counterexample must contain a continuation mechanism new to mathematics.
- [PROVED-shape, execution register] The discreteness floor: A(x) = Σ_{n≤x} aₙ is integer-valued
  and unit-interval-constant; each support point has an adjacent gap with |A| ≥ 1, so
  μ{x ≤ X : |A(x)| ≥ 1} ≥ S(X)/2 — positive-measure integrality, unfiltered by coefficient
  norms. (Lean tool candidate, queued.)
- [OPEN, the exact gap] Transport: left-plane values of the continuation are unique functionals
  of A but admit no growth-free representation; Perron-type inversion needs the growth that is
  the conclusion. The transport gap is the misalignment residue in a third guise: every
  data-function pairing lives right of σ_a, while the constraint acts at and left of the line.
  INT-ORDER's remaining content = one growth-free bridge from tail data to left-plane values, OR
  a proof that no such bridge is needed (an entire-function-theoretic argument from the floor's
  two-sided divergence directly to an order bound).

## [PROVED HERE — paper] Order-free degree-zero classification on the small-abscissa stratum

**Theorem.** Let F(s) = Σ aₙ n^{−s} converge absolutely for Re s > σ_a with σ_a < 1/2, and
suppose on the overlap strip σ_a < Re s < 1−σ_a a reflection identity
F(s) = (Σⱼ cⱼ Qⱼ^{1−2s})·F(1−s) holds (finitely many Qⱼ ∈ ℕ≥1, cⱼ ∈ ℂ). Then
supp(a) ⊆ ⋃ⱼ divisors(Qⱼ²); F is a Dirichlet polynomial (hence entire of finite order), and in
the single-conductor case aₜ = c·(t/Q)·a_{Q²/t}. **No growth or order hypothesis.**

**Proof.** On s = 1/2 + iy both series converge absolutely and Qⱼ^{1−2s} = e^{−2iy log Qⱼ} —
the conductor data is a pure phase on the reflection's fixed line. The identity is an equality
of absolutely convergent Bohr expansions: Σ aₙn^{−1/2}e^{−iy log n} =
Σⱼ cⱼ Σₙ aₙn^{−1/2}e^{−iy log(Qⱼ²/n)}. Mean-value orthogonality of distinct real frequencies
(the sine-kill lemma) matches coefficients at each frequency −log t: aₜ ≠ 0 forces some j with
Qⱼ²/t ∈ supp ∩ ℕ, i.e. t ∣ Qⱼ² — support bounded by max Qⱼ², hence finite; single-conductor
matching gives the stated pairing. ∎

**Checks.** Q = 1 recovers overlap rigidity (h = 1 cell). dzo (Q = 8): support {1,8,64} ⊆
div(64) ✓, a₁ = (1/8)a₆₄ = 1 ✓, a₈ self-paired ✓ — the pairing reproduces the machine-checked
witness exactly. Flow check: fixed-locus evaluation + coefficient matching; nothing evolves.

**Position.** The classical degree-zero classification (K–P) hard-wires "entire of finite
order"; the certified-absent territory ([ABSENT]², checks file) was precisely the growth-free
case. This theorem removes the order axiom on the σ_a < 1/2 stratum, with elementary proof —
the novelty is the position (order-axiom removal), flagged honestly. Consequence: **C-COC's
pure-conductor cell is PROVEN on the small-abscissa stratum** (third proven case, no
everywhere-rep crutch, no order crutch); every remaining open cell of C-COC is now literally
the single INT-ORDER wall (σ_a ≥ 1/2 ∧ infinite order). The Lean-able analytic core is the
Bohr-uniqueness lemma already in build (OverlapRigidity's sine orthogonality, generalized from
sine to complex exponentials).

---

## Gammaless strip-rigidity family — the INT-ORDER wall localized quantitatively [PROVED HERE — reduction]

**Landed in Lean (axiom-clean).** `OverlapRigidity.lean` machine-checks the h=1 core of the
order-free degree-0 classification: `overlap_rigidity` — an ordinary Dirichlet series absolutely
convergent at a real point σ₀ < 1/2 with `L(s)=L(1−s)` on the overlap strip has aₙ=0 ∀ n≥2. The
proof is the pure fixed-locus evaluation at `s=½+iy`, reducing symmetry to a vanishing absolutely
convergent sine series `∑ (aₙ n^{−½}) sin(y log n)=0 ∀y` and killing all coefficients by
Kronecker–Weyl mean-value orthogonality (`sine_series_coeffs_zero`, reusing
`Weyl.trig_time_average`). Independently verified: compile + `#print axioms`
[propext, Classical.choice, Quot.sound]; in umbrella; lint green; index regenerated.

**The quantitative family.** Package the reflection-symmetric (`h=1`) integer-coefficient entire
carriers by their abscissa of absolute convergence σ_a. Constancy is forced across a single
one-parameter family:

| σ_a range | verdict | input needed |
|---|---|---|
| σ_a < 1/2 | constant | none (overlap rigidity — the two convergence regions overlap) |
| σ_a = 1/2 | constant | none (degenerate width-0 strip) |
| σ_a > 1/2 | constant | admissible strip growth, threshold `c < π/(2σ_a − 1)` |

The gap strip is `1 − σ_a < Re s < σ_a`, width `2σ_a − 1`. `PhragmenLindelof.vertical_strip`
requires an O-bound `exp(B·exp(c|Im s|))` with `c < π/width`. As σ_a → 1/2⁺ the width → 0 and the
threshold π/(2σ_a−1) → ∞ — the growth hypothesis becomes vacuous exactly where overlap rigidity
already gives constancy unconditionally. **Overlap rigidity is the width-0 limit of the
Phragmén–Lindelöf reduction: one continuous structure, not two theorems.**

**Why this is a localization, not just the P–L paragraph.** The substantive content is that the
two edges of the gap strip are *automatically bounded*: from `LSeriesSummable a σ_a`, the right
edge Re s = σ_a is bounded by `∑ |aₙ| n^{−σ_a}`, and the left edge Re s = 1−σ_a by the same bound
through the symmetry F(s)=F(1−s). So every hypothesis of the P–L closure is discharged by
convergence + symmetry *except* the admissible growth inside the strip. That growth clause is
exactly INT-ORDER (integer coefficients + finite abscissa + entire ⟹ finite order). The whole h=1
open cell (σ_a ≥ 1/2, infinite order) is thereby reduced to ONE explicit analytic Prop, with all
other inputs machine-checked.

**Lean:** `GammalessStripRigidity.lean` — `gammaless_strip_rigidity` (entire + symmetric +
right-half-plane bound + admissible strip growth ⟹ constant, growth as explicit residual) and
`lseries_bounded_on_halfplane` (convergent Dirichlet series ⟹ uniformly bounded on its
half-plane — the edges-are-free lemma).

**Forward moves (not termini):**
1. Prove the admissible bound `c < π/(2σ_a−1)` FROM integrality — this IS INT-ORDER; the strip is
   narrow (width 2σ_a−1 small for σ_a near 1/2) so the threshold is generous there.
2. Build the falsifying family: an integer-coefficient symmetric entire series with σ_a > 1/2
   whose strip growth *saturates* threshold π/(2σ_a−1) — if it exists, INT-ORDER is false and the
   program pivots.
3. Extend from h=1 to conductor datum ΣcⱼQⱼ^{1−2s}: the sine-orthogonality lemma generalizes to
   complex exponentials (the conductor is a pure phase e^{−2iy log Qⱼ} on the fixed line), which
   would machine-check the full conductor-datum order-free classification.

### Refinement of forward-move 1 — the natural-boundary reframing of INT-ORDER [CONJECTURE, strategic]

INT-ORDER (integer multiplicative + finite abscissa + entire ⟹ finite order) is equivalent, on
entire members, to its contrapositive mechanism: **infinite order ⟹ natural boundary.** The known
integer-multiplicative Dirichlet series split empirically into (a) finite-order arithmetic
L-functions and (b) Estermann–Kurokawa–Dahlquist Euler products with a natural boundary (local
factor zeros/poles accumulating on a line) — with no known infinite-order-entire member between.
So a route to INT-ORDER: show the *only* obstruction to finite order for an integer-multiplicative
Euler product is a natural boundary, built constructively from the local data; the entire
hypothesis removes that boundary, forcing bounded local complexity ⟹ finite order. This converts a
growth problem into a domain (natural-boundary) problem where the criteria are constructive.
Caveat (attacked): this is a *reframing* of INT-ORDER, equivalent to it on entire members, not an
independent object — the honest content is the strategy, not a new theorem. The general dichotomy
"integer multiplicative ⟹ finite-order XOR natural-boundary" is [ABSENT] as a stated theorem
(integrality is known to control domain and to control order only *separately*); uniting them is
the novel framing. NOT reducible to the in-tree NBT engine (that lane is dynamical/smooth-boundary,
a different mechanism).

### Residual is a MILD double-exponential ceiling, not full finite order [refinement]

`PhragmenLindelof.vertical_strip` consumes an O-bound `exp(B·exp(c|Im s|))` with rate
`c < π/(2σ_a−1)` on the gap strip — a *double-exponential* ceiling, strictly WEAKER than
finite order (single-exponential). So `gammaless_strip_rigidity` forces constancy under a
hypothesis milder than INT-ORDER's conclusion: it suffices that F does NOT grow as fast as
`exp(exp(π|t|/(2σ_a−1)))` in the strip. Consequences: (i) proving INT-ORDER (finite order) more
than triggers the reduction — the reduction's demand is far below finite order; (ii) a
falsifying member must grow at least double-exponentially with rate ≥ π/(2σ_a−1) inside the strip
while staying entire and integer-multiplicative — an extremely violent growth requirement, which
makes the *existence* of a counterexample correspondingly implausible and sharpens the target for
forward-move 2. The width-0 limit (σ_a→1/2⁺) sends the required rate →∞, consistent with overlap
rigidity needing no growth control at all.

## Quiet-crossing rigidity — the residual re-quantified (smoothed-Perron shift)

**[PROVED HERE — paper] Quiet-crossing rigidity (h = 1).** Let `F(s) = Σ_{n≥1} aₙ n^{−s}` be an
ordinary Dirichlet series with finite abscissa of absolute convergence `σ_a`, entire continuation,
and exact symmetry `F(s) = F(1−s)`. Suppose there exists ONE sequence `T_k → ∞` with

    sup { |F(σ ± iT_k)| : 1−σ_a−ε ≤ σ ≤ σ_a+ε }  =  o(T_k²).

Then `F` is constant. No order hypothesis, no integrality, no growth ceiling — one quiet height
sequence suffices.

*Proof.* Fix `ε > 0` and `c = σ_a + ε`. Absolute convergence at `c` gives `|F| ≤ C := Σ|aₙ|n^{−c}`
on `Re s ≥ c`; symmetry transports this to `|F| ≤ C` on `Re s ≤ 1−c`. Smoothed Perron: for the
kernel `1/(s(s+1))` one has, for `y > 0`,

    (1/2πi) ∫_(c) y^s ds/(s(s+1)) = (1 − 1/y)₊

(close the contour left for `y ≥ 1`: residues `1` at `s=0` and `−1/y` at `s=−1`; close right for
`y < 1`: no poles; the kernel decays like `|s|^{−2}` so both closings are legitimate). Multiplying
by `x·aₙ` with `y = x/n` and summing (exchange justified: the line integral converges absolutely
and `Σ|aₙ|n^{−c}` converges):

    A₁(x) := Σₙ aₙ (x−n)₊ = ∫₀ˣ A(u) du = (1/2πi) ∫_(c) F(s) x^{s+1} ds/(s(s+1)).

Shift the contour to `Re s = −M` (`M > 1`) across the rectangle with horizontal edges at heights
`±T_k`. `F` is entire; the kernel contributes poles at `s = 0, −1` with residues `F(0)·x` and
`−F(−1)`. The horizontal edges split into flank parts (`|F| ≤ C`, length `≤ M + 2σ_a`, kernel
`≤ T_k^{−2}`) and the strip part (`≤ w · o(T_k²) · x^{σ_a+1+ε} / T_k²`); both `→ 0` as `k → ∞`
with `M` fixed. The left vertical converges absolutely with total mass
`≤ C x^{1−M} ∫ dt/|s(s+1)| = O(C x^{1−M})`. Hence for every `x > 1`:

    A₁(x) = F(0)·x − F(−1) + O(C x^{1−M})   for all M  ⟹  A₁(x) = F(0)x − F(−1) exactly.

`A₁` is piecewise linear with slope jump `aₙ` at each integer `n`; exact global linearity on
`(1,∞)` forces `aₙ = 0` for all `n ≥ 2`. ∎

**[PROVED HERE — paper] Conductor-datum quiet-crossing classification.** Same hypotheses but with
the reflection identity `F(s) = D(s)·F(1−s)`, `D(s) = Σⱼ cⱼ Qⱼ^{1−2s}` a finite exponential
polynomial, `Q := max Qⱼ`. The left-flank bound becomes `|F(s)| ≤ (Σ|cⱼ|) Q^{1+2M} C` on
`Re s = −M`; the left vertical is then `O((Q²/x)^M · x)`, which `→ 0` for every `x > Q²`. The same
shift yields `A₁(x) = F(0)x − F(−1)` exactly for `x > Q²`, i.e. `aₙ = 0` for all `n > Q²`: `F` is a
Dirichlet polynomial supported on `[1, Q²]`. Once `F` is a finite exponential sum, the identity
`F(s) = D(s)F(1−s)` between finite sums of exponentials `e^{−s log n}`, `e^{−s(log Qⱼ² − log m)}`
forces, by linear independence of characters (elementary Bohr uniqueness for FINITE sums), the
support refinement `supp a ⊆ ⋃ⱼ div(Qⱼ²)` and the K–P pairing `a_t = c_{(j)} a_{Qⱼ²/t}`. This is
the full Kaczorowski–Perelli degree-0 classification with the finite-order standing axiom replaced
by one quiet height sequence — valid on EVERY abscissa stratum, not only `σ_a < 1/2`. ∎

**Strictness.** Finite order ⟹ (P–L, `gammaless_strip_rigidity` edge mechanism) bounded on the gap
strip ⟹ `O(1)` crossings everywhere ⟹ quiet. So the quiet-crossing hypothesis strictly weakens the
K–P order axiom given the (automatic) flank bounds. Conversely `e^{√|t|}`-type growth at every
height is finite-order-admissible but never sub-polynomially quiet — the two reductions
(P–L ceiling / Perron quiet sequence) are genuinely incomparable sufficient conditions; a
counterexample must dodge both.

**Kernel escalation.** Replacing the kernel by `1/(s(s+1)⋯(s+k))` (decay `|s|^{−(k+1)}`, poles at
`0, −1, …, −k`, residues assembling a degree-k polynomial in `x`) weakens the quiet requirement to
`o(T_k^{N})` for any fixed `N`: the k-fold integrated counting function `A_k` becomes an exact
polynomial, and its k-th distributional derivative jumps by `aₙ` at `n`, so the same rigidity
follows. Hence:

**[CONJECTURE NO-QUIET-ESCAPE] — the residual, final quantifier form.** A nonconstant (resp.
non-polynomial) symmetric entire member must be SUPERPOLYNOMIALLY LOUD AT EVERY HEIGHT: for every
`N`, `liminf_{T→∞} T^{−N} · sup_{σ ∈ strip} |F(σ+iT)| > 0` (and in both vertical directions —
independent top/bottom sequences each suffice for the rectangle). Combined with the P–L side it
must ALSO exceed the admissible double-exp ceiling `exp(B e^{c|t|})`, `c < π/(2σ_a−1)`, along some
sequence. The INT-ORDER keystone is correspondingly weakened to
**[CONJECTURE INT-QUIET]**: integer coefficients + finite abscissa + entire ⟹ one quiet height
sequence exists. INT-ORDER ⟹ INT-QUIET ⟹ classification; INT-QUIET is the strictly cheaper wall.

**Forward moves opened.** (i) Attack INT-QUIET directly: quiet heights are a measure-theoretic
plentiful property for every classically constructed continuation (Estermann continuables,
polynomial-growth columns); the counterexample needs a gapless tract — collide this with the
Denjoy–Carleman–Ahlfors tract count (an entire function bounded outside a width-w strip with a
two-ended ∞-tract has log log M(r) ≳ πr/w — Ahlfors distortion), i.e. the escape is pinned to
EXACTLY the P–L-critical tract geometry. (ii) Lean target: kernel identity + A₁ exchange + rectangle
shift (`QuietCrossingRigidity.lean`) — check tree for contour/Mellin infrastructure first.
(iii) The finite-pole variant: allowing finitely many poles adds finitely many residue monomials
`x^{ρ+1}` to `A₁`, so the conclusion becomes "A₁ = finite explicit combination" — a rigidity for
pole-bearing symmetric carriers worth its own pass.

## Wave 2 — kernel escalation to all finite-order rates; the dip window; the seam reading

**[PROVED HERE — paper] Finite-order-quiet rigidity.** In the quiet-crossing theorem (h = 1 and
conductor-datum forms alike), the kernel `1/(s(s+1))` may be replaced by
`K_{m,λ}(s) = exp((−1)^{m+1} s^{2m}/λ) / (s(s+1))` for any `m ≥ 1`, `λ > 0`. On any horizontal
segment `σ ∈ [−M, c]`, `Re((−1)^{m+1}(σ+iT)^{2m}) = −T^{2m} + O(σ²T^{2m−2})` uniformly (the odd
binomial terms are purely imaginary), so the horizontal edges of the rectangle carry the factor
`e^{−T^{2m}(1+o(1))/λ}` and tolerate strip loudness up to `o(e^{T^{2m}/λ})` at the crossing
heights. The right-edge exchange (deliverable B) improves (kernel decays faster); the residues at
`s = 0, −1` acquire the factor `K_{m,λ}·s(s+1)|_{poles} → e^{(−1)^{m+1}s^{2m}/λ}|_{0,−1} → 1` as
`λ → ∞`; the left vertical at fixed `M` is `O(C x^{1−M} e^{M^{2m}/λ})`, harmless at fixed `M`.
Order of limits: validity at each fixed `(m, λ)` needs one quiet sequence at `o(e^{T^{2m}/λ})`;
then `λ → ∞` at fixed `M` recovers the SHARP kernel identity by dominated convergence on both
verticals (no transform-injectivity needed); then `M → ∞` as before. Conclusion: if a symmetric
entire member has ONE height sequence along which the strip cross-section maximum is
`O(exp(T^A))` for SOME finite `A` (choose `2m > A`), it is constant (h = 1), resp. a Dirichlet
polynomial on `⋃div(Qⱼ²)` with the K–P pairing (conductor datum). Quietness is now any
finite-order rate. ∎

**The dip window.** Ahlfors distortion forces any nonconstant member's ∞-tract (confined to the
width-w gap strip by the free flank bounds) to satisfy `log log M(r) ≳ πr/w` — loud heights exist
and reach the double-exponential rate. Wave 2 shows dips below every finite-order rate are fatal.
The surviving counterexample profile is pinched into the window

    exp(T^A) (∀A, excluded)  <  strip max at EVERY height  ≤  exp(e^{πT/w}) (Ahlfors-critical),

with the P–L module excluding everything under `exp(B e^{cT})`, `c < π/w`, globally. Residual, final
form: **[CONJECTURE GAPLESS-TRACT]** — a nonconstant symmetric entire member's strip loudness
exceeds every `exp(T^A)` at every sufficiently large height; equivalently the ∞-tract admits no
finite-order dips. INT-QUIET correspondingly weakens to: integrality forces one finite-order-quiet
height. This subsumes the P–L reduction's conclusion for Dirichlet carriers (finite order ⟹ all
heights finite-order-quiet); the P–L module retains independent scope (abstract entire F, no
carrier).

**[CONJECTURE — branch-native seam reading] Orientation-reversal weld.** On the right flank
`Re s ≥ σ_a + ε` the member is Bohr almost periodic with spectrum in the rate lattice
`{−log n : n ≥ 1}`; the symmetry `F(s) = F(1−s)` makes the left flank almost periodic with the
REFLECTED spectrum `{+log n}`. The h = 1 cell is thus exactly: can an entire function weld a rate
lattice to its orientation reversal across a width-w seam while bounded on both flanks? Every
finite exponential sum fails (unbounded on one flank unless spectrum = {0}); GAPLESS-TRACT asserts
the infinite version fails too, and quantifies the obstruction as a flux cost — loudness in the
seam is the price of reversing the spectrum's sign. Forward object: a Beurling–Malliavin /
de Branges–type extremal problem for the seam — the minimal loudness functional
`L(T) = max_{strip} log |F(σ+iT)|` compatible with spectrum reversal of density `d(λ) ~ e^λ`
(the rate lattice `log n` has exponentially growing density — far beyond the BM finite-density
regime; the seam asks the completeness question in the regime classical theory never poses).

## Wave 3 — GAPLESS-TRACT attacked as false: the pure class is nontrivial; rigidity is carrier-forced

**[PROVED — modulo Arakelyan's approximation theorem (1964); condition verified here] The pure
class is nontrivial.** Let `E = {Re s ≤ 0} ∪ {Re s ≥ 1} ∪ {Re s = 1/2}` — closed in ℂ. Its sphere
complement is (two open substrips) ∪ {∞}: connected (each substrip adheres to ∞) and locally
connected at ∞ (a punctured neighborhood meets it in four half-strip ends, each adhering to ∞), so
Arakelyan's condition holds. The data `f = 0` on the half-planes (holomorphic on int E) and
`f = h(Im s)` on the midline (`h` continuous, even, `h → ∞`) is in `A(E)`; Arakelyan gives entire
`G` with `|G − f| < ε` on `E`. Then `F(s) := G(s) + G(1−s)` is entire, satisfies `F(s) = F(1−s)`
exactly, is bounded by `2ε` on `{Re ≤ 0} ∪ {Re ≥ 1}` (reflection maps flank to flank), and
`F(1/2 + it) = 2h(t) + O(ε) → ∞`. The class {entire + reflection-symmetric + flank-bounded}
therefore contains nonconstant members with arbitrarily violent loudness profile. ∎

**Methodological theorem (the point).** h = 1 rigidity is NOT a function-theoretic fact: the
hypotheses consumed by Phragmén–Lindelöf and by the flank bounds admit nonconstant models. Any
proof on the open cell must use the carrier structure (the Dirichlet series / a.p. flank data).
The P–L and Perron reductions are each optimal within their data: the surviving cell — loud
carriers — is exactly where function theory provides models and only arithmetic can discriminate.

**Consistency checks (both pass).** (i) `gammaless_strip_rigidity` forces the constructed member
to violate admissible strip growth: with slow midline data `h`, P–L applied to each SUBSTRIP
(edges: flank ≤ ε, midline ≈ h) would bound `F` and Liouville would kill it — so `G` is forced to
be doubly-exponentially wild in the open substrips, off the prescribed set: the Ahlfors tract
floor materializes in the unprescribed region. (ii) Prescribing QUIET crossings (small data on
horizontal segments `{0 ≤ σ ≤ 1, t = T_k}`) together with a loud midline destroys Arakelyan's
condition: the complement disintegrates into bounded boxes — disconnected — so the approximation
route cannot manufacture quiet-crossing members. This is consistent with (and structurally aligned
to) the Perron theorem, which proves quiet-crossing CARRIERS are rigid.

**GAPLESS-TRACT, corrected register.** As a statement about the pure class: FALSE (members with
any loudness profile ≥ double-exp-in-substrips exist). As a statement about carriers: open, and
now the exact content of h = 1 rigidity. Falsification program, localized: make an
Arakelyan-type construction INSIDE the carrier class — "Dirichlet–Arakelyan approximation." The
named obstruction: symmetric approximants within ordinary Dirichlet series are constants (degree-0
rigidity), so any carrier-side construction must weld the two one-sided structures — realize the
pair (Σ aₙ n^{−s} on the right, Σ aₙ n^{s−1} on the left) as one entire function through a width-w
seam. Equivalently: h = 1 rigidity ⟺ the rate lattice admits no nontrivial bounded-flank weld to
its reflection. The forward object stands: the seam-flux extremal problem at exponential spectral
density (wave 2), now known to be the ONLY possible source of a proof.

## Wave 4 — the discriminating invariant: pure-point vs continuous flank spectrum; the coboundary near-miss

**One-sidedness is free.** A bounded analytic function on a right half-plane has one-sided
distributional boundary spectrum (classical H^∞/Beurling–Paley–Wiener). Hence the wave-3
Arakelyan member ALREADY welds two orientation-reversed one-sided spectra boundedly across the
seam — with CONTINUOUS spectrum. What the carrier cell adds is not orientation but
DISCRETENESS: Bohr almost-periodic flank traces with pure-point spectrum in a discrete Λ.
**[CONJECTURE — refined invariant]** h = 1 rigidity is a Bohr-discreteness phenomenon: for EVERY
discrete one-sided Λ (not only log ℕ), a nonconstant entire flank-bounded weld with pure-point
flank spectrum in ±Λ fails to exist; continuous-spectrum welds exist (wave 3). The invariant
separating the proved-nontrivial pure class from the conjecturally-rigid carrier cell is the
spectral TYPE of the flank trace.

**Supporting anchors.** (i) Width-0 case: at σ_a = 1/2 the flanks share a line; F ∈ H^∞ of both
closed half-planes ⟹ globally bounded ⟹ constant (Liouville) — rigidity is trivial with no room
in the seam; all content is w > 0. (ii) The two-sided model `Σ 2bₖ e^{−λₖ/2} cosh(λₖ(s − 1/2))`
is exactly symmetric with pure-point spectrum ±Λ but violates flank boundedness identically —
one-sidedness of the flank expansion is the load-bearing clause of the cell, and it is FREE
analytically (H^∞) while binding algebraically (series support). (iii) Pólya-density axis:
lacunary/zero-density spectra cannot even continue entire (gap theorems put the natural boundary
at the convergence line); the carrier lattice log ℕ has maximal density k/λₖ → ∞ —
continuability is unobstructed and the WELD is the sole constraint. Known theory measures
continuability by density; the branch's new axis is weldability of Λ against −Λ.

**The coboundary device and its exact near-miss.** For an ε′-almost-period τ of the flank trace
(one τ serves BOTH flanks — the spectra ±Λ impose identical conditions `|e^{iλτ} − 1|` small),
the difference `G_τ(s) = F(s + iτ) − F(s)` is an ordinary Dirichlet series with coefficients
`aₙ(n^{−iτ} − 1)`, entire, and bounded by 2ε′ on BOTH flanks directly — no symmetry hypothesis.
The quantitative Perron floor (second-difference kink extraction at x = n against the shifted
rectangle) gives: a carrier with flank bound ε′ and one coefficient of modulus β has strip
loudness ≥ c·(β/n^{c+1} − c₂ε′)·T² at every height. The Bohr coefficient bound on the line Re = c
locks β ≤ ε′ n^c. The two exponents differ by EXACTLY ONE power of n: the contradiction machine
fails at `n^c` (lock) vs `n^{c+1}` (Perron counting weight `x^{s+1}`). Self-attack verdicts on
the two repair branches: (b) "almost-periods with a loud phase at one frequency" is DEAD — the
lock `β ≤ ε′ n^c` is an unconditional identity for every τ, because ε′ is by definition the
flank sup of `G_τ` and the Bohr coefficient bound binds it; no choice of τ escapes. (a) A cheaper
extraction (sharp Perron at weight `x^s`, truncated kernel `1/s`) removes the extra power and
puts the race at CONSTANT level — but even closed it proves only "G_τ is loud at every height,"
which is CONSISTENT with F loud: the coboundary lane has no contradiction endpoint until some
UPPER bound on strip loudness exists, and none is known (that absence is the wall itself). The
coboundary device is therefore a structure probe, not a proof shape: its yield is the
unconditional per-height floor family (for F itself, integrality gives m(T) ≥ κₙT² − C with
explicit κₙ ~ |aₙ|/n^{c+1} for every nonzero coefficient) and the exact bookkeeping of why
flank-recurrence alone cannot cap the seam. [OPEN CORE — restated correctly]: produce ANY
mechanism that bounds strip loudness from carrier data (a.p. flank structure + entirety); every
lower-bound mechanism is now in place and effective, and no upper-bound mechanism exists.

## Lean status — conductor-datum support theorem LANDED

`BohrCoefficientUniqueness.lean` (RHTower) verified and integrated: `char_avg_finsum` /
`char_avg_tendsto` (exponential Kronecker–Weyl mean-value orthogonality, doubly-indexed),
`char_series_coeff_zero` (Lemma A), and `conductor_datum_finite_support` (Theorem B: σ₀ < 1/2,
absolute convergence at σ₀, reflection identity with finite datum Σ c_j Q_j^{1−2s} on the overlap
strip ⟹ coefficients vanish off ⋃_j div(Q_j²)). Axioms: [propext, Classical.choice, Quot.sound];
umbrella build 8476 jobs; lint green. The small-abscissa stratum of the order-free classification
is machine-checked in full conductor-datum generality; `overlap_rigidity` is its Q = 1 cell. Not
formalized: the K–P pairing refinement a_t = c·a_{Q²/t} (paper, elementary finite-sum matching) —
queued behind the quiet-crossing module.

## Wave 5 — quiet paths, min-cut duality, and the seam curtain

**[PROVED HERE — paper] Path-quiet rigidity.** The rectangle shift in the quiet-crossing theorem
tolerates DEFORMED crossings: replace each straight horizontal edge by any rectifiable
flank-to-flank path γ (entering the strip from Re = c, leaving at Re = 1−c, heights within a
window around ±T_k, then straight within the flanks where |F| ≤ C). The path contribution is
bounded by `sup_γ |F| · x^{c+1} · length(γ) / min_γ |s(s+1)|`. Hence: if there exist
flank-to-flank paths at heights T_k → ∞ (both vertical directions), of lengths Λ(T_k), on which
|F| ≤ R_k, with `R_k · Λ(T_k) = o(T_k²)` — then F is constant (h = 1), resp. a Dirichlet
polynomial with the K–P support/pairing (conductor datum). Kernel escalation applies verbatim:
`o(T_k²)` relaxes to any finite-order budget. Quietness is a property of the SUBLEVEL SET's
connectivity, not of straight segments. ∎

**[PROVED HERE — paper] Curtain duality.** Fix a height window `W_T = {1−c ≤ Re s ≤ c} ×
{T ≤ Im s ≤ 2T}` and a threshold R. Planar min-cut duality in the rectangle: either the sublevel
set `{|F| ≤ R} ∩ W_T` contains a left-edge-to-right-edge path, or the superlevel set
`{|F| > R} ∩ W_T` contains a connected set joining the window's top and bottom edges. Applying
path-quiet rigidity (paths of length ≤ O(T) suffice; budget o(T²) absorbs it): a NONCONSTANT
member's tract contains, for every A and every sufficiently large T, in both vertical directions,
a connected set crossing the full window `W_T` vertically on which `|F| > exp(T^A)` — the **seam
curtain**. By `F(s) = F(1−s)` the curtain configuration is point-symmetric about s = 1/2. The
residual GAPLESS-TRACT is upgraded from a per-height loudness profile to a connected geometric
object: an unbroken curtain of super-finite-order values climbing the seam forever, wedged
between two flanks where |F| ≤ C. ∎

**What the curtain opens (forward).** A connected curtain is exposed to potential theory in a way
a diffuse profile is not: (i) harmonic measure — the curtain together with the two flank lines
bounds two unbounded subregions; two-constants estimates on them relate C, R and the curtain's
horizontal position, and the point-symmetry pins the pair of subregions to each other; (ii) the
level curves {|F| = R} crossing each window are analytic arcs whose number counts d/ds-critical
points — Rolle-type bookkeeping along the curtain against the carrier's Bohr structure on the
flanks; (iii) for the falsification side, any Dirichlet–Arakelyan construction must now
manufacture a symmetric connected curtain, not merely loud cross-sections. [OPEN CORE unchanged:
an upper mechanism = a proof that carriers cannot sustain a curtain; the curtain is the exact
object such a mechanism must kill.]

## Lean status — pairing LANDED: the small-abscissa classification is fully machine-checked

`BohrCoefficientUniqueness.lean` now also contains `conductor_datum_pairing` and
`conductor_datum_pairing_coeff` (verified: standalone compile clean, umbrella build, axioms
[propext, Classical.choice, Quot.sound], lint green, index regenerated): under σ₀ < 1/2, absolute
convergence at σ₀, and the finite-datum reflection identity on the overlap strip,
`aₘ·m^{−½} = Σ_{j∈J} (if m ∣ Qⱼ² then cⱼ·a_{Qⱼ²/m}·(Qⱼ²/m)^{−½} else 0)` for every m ≥ 1 — the
Kaczorowski–Perelli pairing with the order axiom removed. Together with
`conductor_datum_finite_support` (the vanishing case of the same identity), the order-free
degree-0 classification on the small-abscissa stratum is machine-checked in BOTH halves and full
conductor-datum generality. Remaining Lean target for this card: `QuietCrossingRigidity.lean`
(in progress) — the σ_a ≥ 1/2 stratum under quiet crossings.

## Lean status — smoothed-Perron engine LANDED; rigidity shift remains the open Lean target

`QuietCrossingRigidity.lean` verified and integrated (all five public theorems
[propext, Classical.choice, Quot.sound]; umbrella; lint green): `perronKernel_mellin`
(`mellin (max(1−u,0)) s = 1/(s(s+1))` on `Re s > 0`), `perronKernel_mellinConvergent`,
`perronKernel_verticalIntegrable`, `perronKernel_inversion` (the kernel identity
`(1/2π)∫ y^{c+it}/((c+it)(c+it+1)) dt = max(1−1/y, 0)`, via Mellin inversion), and
`smoothed_perron_sum` (`Σ' aₙ·max(x−n,0) = (1/2π)∫ L(c+it)·x^{(c+it)+1}/((c+it)(c+it+1)) dt` for
any carrier absolutely convergent at `c > 0`, `x > 0`). This machine-checks deliverables A and B
of the wave-1 proof — the full analytic engine. Deliverable C (rectangle contour shift with quiet
crossings, residues at 0 and −1, M → ∞, and the piecewise-linear kink extraction) is proven on
paper (wave 1) and remains the module's outstanding Lean target; it is a self-contained
consumer of A + B.

## Wave 1 refinement — the residue-free form of quiet-crossing rigidity

The contour-shift proof simplifies structurally: instead of shifting the smoothed count `A₁(x)`
(whose integrand `F(s)x^{s+1}/(s(s+1))` has poles at `s = 0, −1` contributing the affine part
`F(0)x − F(−1)`), shift the SECOND DIFFERENCE directly. With `N(s) = (x+δ)^{s+1} + (x−δ)^{s+1}
− 2x^{s+1}`, the numerator vanishes at both poles — `N(0) = 0` (first differences of x cancel)
and `N(−1) = 0` (constants cancel) — so `F(s)·N(s)/(s(s+1))` is ENTIRE and the rectangle shift
needs no residue calculus at all: the second difference of `A₁` at every `x − δ > 1` equals the
left-line limit, which vanishes as `M → ∞`, giving `aₙ·δ = 0` directly. The observation with
content: the kernel's two poles and the two affine degrees of freedom of the shifted count are
the SAME two dimensions, and second-differencing quotients both out simultaneously. The residues
`F(0), F(−1)` — hence the values of the continuation at the pair {0,−1} = the s(s+1) divisor —
never enter the rigidity mechanism. (This is also the tractable Lean route; module target
updated accordingly.)

## Non-vacuity remark — dzo instantiates the order-free classification

The in-tree witness `dzo(s) = (1 − 2·8^{−s})(1 − 4·8^{−s}) = 1 − 6·8^{−s} + 8·64^{−s}`
(`DegreeZeroOffline.lean`) satisfies the exact conductor-8 identity `dzo(s) = 8^{1−2s}·dzo(1−s)`
and instantiates both halves of the machine-checked classification nontrivially: support
`{1, 8, 64} ⊆ div(8²)` (`conductor_datum_finite_support`), and in normalized coefficients
`b_m = a_m m^{−½}`: `b_1 = 1 = c·b_64` (with `b_64 = 8·64^{−½} = 1`, `c = 1`) and `b_8 = −6·8^{−½}`
self-paired (`conductor_datum_pairing`). The classified class contains genuine off-line-divisor
members; the theorems are not vacuously scoped. Relation to the in-tree everywhere-rep results:
`IntegralFEPolynomial`/`CocycleKernelTrivial` close the everywhere-valid-representation cells via
the integrality growth dichotomy; the new modules close the half-plane σ₀ < 1/2 cells via Bohr
orthogonality with NO integrality or multiplicativity — the two mechanisms cover disjoint strata
of the C-COC cell map and neither subsumes the other.

## Lean status — quiet-crossing rigidity LANDED in full (h = 1 form + constancy)

`QuietCrossingRigidity.lean` (1032 lines) now contains deliverable C, verified independently
(standalone compile clean; umbrella build; `perronKink_second_difference`,
`perronSecondDiff_integral`, `perronE_differentiable`, `quiet_crossing_rigidity`,
`quiet_crossing_rigidity_constant` all [propext, Classical.choice, Quot.sound]; lint green; index
regenerated). `quiet_crossing_rigidity`: entire `F`, equal to an absolutely convergent Dirichlet
series on `Re s ≥ c ≥ ½`, exactly symmetric, with ONE height sequence `T_k → ∞` where
`sup_strip ‖F‖ ≤ q_k`, `q_k/T_k² → 0` ⟹ `aₙ = 0` for all `n ≥ 2`;
`quiet_crossing_rigidity_constant` upgrades to `F ≡ a₁` on all of ℂ. Proof as in the wave-1
refinement: residue-free (the second-difference numerator has roots at both kernel poles, so the
integrand is entire and the rectangle shift needs no residue calculus). Remaining paper-only
forms: conductor-datum quiet-crossing (support for x > Q²) and kernel escalation to finite-order
quiet rates.

## Wave 2 addendum — quiet-crossing rigidity is frequency-blind (general Dirichlet form)

**[PROVED HERE — paper].** The quiet-crossing theorem holds verbatim for GENERAL Dirichlet series
`F(s) = Σ aₖ e^{−λₖ s}` with any discrete frequency sequence `0 ≤ λ₁ < λ₂ < ⋯ → ∞` and finite
abscissa of absolute convergence: entire + `F(s) = F(1−s)` + one quiet height sequence ⟹ `F`
constant. Every ingredient is frequency-blind: the smoothed count becomes
`Σ aₖ·max(x − e^{λₖ}, 0)` (kernel identity applied at `y = x·e^{−λₖ}`), the flank bounds come
from absolute convergence alone, the rectangle shift and edge estimates never see the
frequencies, and the kink extraction reads the second difference at the knot `e^{λₖ}` with any
`δ` smaller than the (positive, by discreteness) gap to the neighboring knots. Consequence for
the discriminating-invariant conjecture (wave 4): rigidity-under-quietness is already a theorem
of the WELD for every discrete one-sided spectrum — the open cell, for every such Λ, is exactly
the loud regime, and the pure-point/continuous divide is the full residual content. The ordinary
lattice `log ℕ` plays no role until arithmetic (integrality, INT-QUIET) is invoked against the
loud cell.

## Lean status — conductor-datum quiet-crossing LANDED

`QuietCrossingConductor.lean` verified and integrated (both theorems
[propext, Classical.choice, Quot.sound]; umbrella build; lint green; index regenerated):
`quiet_crossing_conductor_support` — under the conductor functional equation
`F(s) = (Σ_{j∈J} c_j Q_j^{1−2s})·F(1−s)` with `1 ≤ Q_j ≤ Q₀`, a quiet carrier has `aₙ = 0` for
every `n > Q₀²` — and `quiet_crossing_conductor_polynomial` (support ⊆ {0} ∪ [1, Q₀²]). The
left-flank transport carries the polynomially amplified constant `CJ·Q₀^{1+2M}·B`, and the
endgame closes by the ratio test `(Q₀²/(n−½))^M → 0` exactly when `n > Q₀²`. The quiet-crossing
K–P support theorem on the `σ_a ≥ 1/2` stratum is machine-checked. In flight: Gaussian kernel
escalation (`QuietCrossingEscalation.lean`) and path-quiet rigidity (`QuietPathRigidity.lean`,
two-stage primitive-telescoping design; the min-cut duality reading remains paper-only — planar
unicoherence is not in mathlib).

## Wave 2 precision note + Lean status — kernel escalation LANDED (corrected quantifier)

**Quantifier correction (caught during formalization).** Wave 2's per-(m, λ) phrasing overstated:
a quiet sequence at `o(e^{T²/λ})` for ONE fixed λ does NOT suffice by this route. At fixed λ the
left-edge weight cost `e^{M²/λ}` beats `(n−½)^{1−M}` as `M → ∞` (the parabola wins); optimizing
`M(λ) = λ·log(n−½)/2` yields only the nonzero bound `4πB(n−½)·e^{−λ log²(n−½)/4}`, and the
`λ → ∞` recovery of the sharp kink requires the shift's validity at arbitrarily LARGE λ. The
correct hypothesis is the ∀λ budget: `q_k · e^{−T_k²/λ} → 0` for every `λ > 0`, i.e.
`log q_k = o(T_k²)` (with the `s^{2m}` kernel: `log q_k = o(T_k^{2m})`). The wave-2 HEADLINE is
unaffected: a quiet sequence at any finite-order rate `q_k = O(e^{T_k^A})` satisfies the ∀λ
budget once `2m > A`, so "one finite-order-quiet height sequence ⟹ constant/polynomial" stands —
with the corrected route through the ∀λ form.

**LANDED — Lean.** `QuietCrossingEscalation.lean` verified and integrated (standalone clean;
umbrella build; `gaussian_weighted_contour_bound` and `quiet_crossing_rigidity_gaussian` both
[propext, Classical.choice, Quot.sound]; lint green; index regenerated). The Gaussian case
(m = 1): entire symmetric carrier with one height sequence satisfying the ∀λ budget
(`log q_k = o(T_k²)` — e.g. loudness up to `e^{T^{1.9}}`) has `aₙ = 0` for all `n ≥ 2`. Mechanism:
per-λ rectangle shift of the still-entire `F·E·e^{s²/λ}` (weight has no poles; edges die under
the λ-budget), then dominated convergence `W_λ → 1` on the fixed lines at fixed depth M, then
`M → ∞`. General `m` (rates `e^{T^A}`, `A ≥ 2`) remains paper-only with the corrected quantifier.
