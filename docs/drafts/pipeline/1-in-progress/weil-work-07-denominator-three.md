# Denominator-three rigidity: research log

- **ID:** weil-work-07-denominator-three
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/weil-work/07-higher-denominator-rigidity.md
- **Statement:** Every full-positive real coefficient sequence with third-integral canonical interval masses equals von Mangoldt on n ≥ 2.

## Goal and exact scope

Prove the assigned implication without additional mathematical assumptions, or refute it with an exact checked counterexample. No producer is assumed or constructed by this assignment. No computations, full builds, commits, or pushes. New Lean scope: `WeilWorkHigherDenominator*.lean`.

## Plan

1. Audit exact correspondence, current corpus, and current primary literature.
2. State and attack an exact new conjecture beyond existing exclusions.
3. Complete dependency-closed paper proof before Lean; reject or refine failed conjectures.
4. Verify new modules with targeted foreground Lean checks, audit axioms, wire umbrella, run lint.
5. Repeat until exact target closes; keep limitations explicit.

`update_plan` is unavailable in this tool inventory; this file records the working plan.

Checkpoint: central exclusion, the exact multiplicity-deficit dichotomy, and the finite boundary-packet receiver are paper-proved, Lean-checked, axiom-audited, and wired. All audited results use only `[propext, Classical.choice, Quot.sound]`. Latest global lint reports ten unrelated unreachable modules (listed in EVIDENCE.md). Goal stays active. No scientific-novelty or full-rigidity claim.

## Exact correspondence (read from Lean)

Third-integral full-positive interval counting is equivalent to:

- real λ with ∑ |λ(n)| / n^σ summable for every σ > 1;
- g : ℕ → ℂ, g(1)=1, absolutely convergent L(g,s) for Re(s)>1;
- E : ℂ → ℂ entire and of finite order;
- E(s) = (s(s−1)Γℝ(s))³ L(g,s) on Re(s)>1;
- E(1−s)=E(s) everywhere OR E(1−s)=−E(s) everywhere;
- E(1) ≠ 0;
- EVERY zero of E has real part 1/2;
- (L(g))′(s) = −3 L(lamC λ,s)L(g,s) on Re(s)>1.

`lamC` discards n=0,1. No Euler product, multiplicativity, coefficient nonnegativity, zero simplicity, or RH for ζ is included.

## Gates

- [x] 0 → 1: exact target and scope read.
- [ ] 1 → 2: full assigned implication proved on paper.
- [ ] 2 → 3: exact target checked in Lean.

## Current conjecture under attack

Central exclusion is closed in paper and Lean: every third-quantized full-positive system has a uniform empty neighborhood of ordinate zero; every corresponding degree-three completion is nonzero at 1/2 and has positive functional-equation sign. Both new modules compile and are wired into `RHTower.lean`. Full positive-sign classification remains the OPEN CORE.

The second conjecture is now Lean-checked: every nontrivial complete degree-three datum has a zeta-zero multiplicity deficit, ordρ(E)<ordρ(ξ). The proof subtracts one zeta spectral measure from three producer measures and applies half-integer rigidity to the positive remainder. Positivity, measure normalization, integer counting of μΛ, and the exact identity 3μλ{t}=ord(E,1/2+it) are all proved. It adds no simplicity, Euler-product, or RH premise to the final dichotomy.

2026-10-07 continuation: `WeilWorkHigherDenominatorSpectralSubtraction.lean` and `WeilWorkHigherDenominatorMultiplicity.lean` compile (exit 0, no diagnostics), using `lake --old env lean -o ...` in the foreground, one process at a time. Both imports are wired. Previous goal turn classified PROGRESS (central exclusion); this cycle adds the corrected multiplicity boundary.

Next conjecture: every nontrivial datum has infinitely many deficits below ord(ξ). Located finite-pole degree-two converses require an Euler product or twisted functional equations and coefficient bounds, absent from the exact datum. Do not apply them. A weaker alternative is infinitely many deficits below 2ord(ξ), via the degree-one quotient G/ζ²; the finite-growth and finite-pole Hamburger transport are not yet paid. Source search found theta-defect/radial-residue tools, not a verified complete receiver. No Lean code for either infinite-deficit conjecture.

Anti-theatre: the new result is a formally verified bridge/correction to L223, not a novel-science claim or full rigidity. Anti-laziness: no analytic quotient-growth lemma with zero-free hypotheses was misapplied; no remainder positivity was assumed. Positive survivor of the failed finite-pole import is the exact all-points spectral-domination theorem, already formalized.

Next-turn entry point: `HamburgerStabilityCriticalLine.coeff_eq_of_critical_line_even_sublinear_defect` (source line 736) and `HamburgerThetaDefect.coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect` (line 473). Finite Gamma principal-part corrections may convert G/ζ² to this receiver; arbitrary-order cancellation, quotient growth, boundary regularity and decaying Gamma ratios are all OPEN obligations. Common-height Gamma ratio bounds were inspected and are insufficient alone. Full target remains open; continue the conjecture loop.

## Log

- 2026-10-07, finite-boundary checkpoint: `WeilWorkHigherDenominator{PeriodDefect,PoleModes,FiniteBoundary}.lean` each compiled with exit 0 and no diagnostics under targeted foreground `lake --old env lean -o ...`; all imports wired. The capstone eliminates every finite logarithmic boundary packet with distinct positive-real-part exponents satisfying both modular identities. It derives decay/regularity and retains arbitrary polynomial orders. Classification: BRIDGE / REDISCOVERED, not WP07 closure. All fifteen exported theorems passed the scratch axiom audit with only standard axioms. Latest lint fails on ten out-of-scope unreachable modules, no WP07 error.
- Next core attack has a concrete paper construction: `Uρ(x+iy)=sqrt(y)∫ |t|^(−ρ)/sqrt((x−t)²+y²) dt`, normalized by `Cρ=Γ((1−ρ)/2)Γ(ρ/2)/Γ(1/2)`. Axis value is `y^(1/2−ρ)`; leading log-boundary factor is `−2/Cρ`, nonzero for `0<Re ρ<1`. Parameter derivatives retain every pole order. PROOF.md records the local uniform error estimates and the exact `MaassAxisContinuation.eq_zero_of_axis` receiver. Formalize this exact positive survivor, then pay quotient growth and the finite-pole Mellin-axis identity. Do not substitute the finished boundary receiver for those missing steps.

- 2026-10-07, finite-pole attack: selected the Maass boundary defect of `G/ζ`. A dependency-closed paper proof now gives an elementary three-term/inversion telescoping bound, recorded in PROOF.md. Lewis–Zagier already imply stronger bounds: this is a BRIDGE, not a scientific advance. Current implementation scope is the exact algebraic identities and telescoping receiver; actual quotient-to-boundary transport and arbitrary-order pole injectivity remain OPEN. The finite-deficit conjecture and WP07 remain unproved.

- 2026-10-07, continuation audit: no new Lean theorem this cycle. Exact target remains open. The weighted sampling representation behind `GammaRCubeFunctionalEquationAbundance` retains enough square summability to suggest absolute convergence for every Re(s)>1; the exported capstone currently states Re(s)>3. This refinement is a BRIDGE, not a counterexample: critical-line zeros, the normalized logarithmic-derivative data, and the required global finite-order statement still need separate proofs. Do not spend the next cycle polishing this easier side result.
- Booker's `L-functions as distributions`, Definition 1.3 and §§3.2–3.3, was inspected. Classification assumes almost all spectral masses integral; third-integrality does not discharge that condition. Correction to an intermediate chat statement: the mean-square part of (A1) is already supplied by the corpus's primitive-set estimate and dyadic summation, giving a log-cubed prefix bound for `Σ λ(n)^2/n`. The pointwise rapid logarithmic decay in (A1) is a separate condition. Do not conflate either condition with integrality or claim the mean-square bound is a new conjecture.
- Stronger competing conjectures for the next cycle are recorded in PROOF.md: positive linear lower growth of the deficit below one copy of the ξ divisor versus a nontrivial datum with sublinear such deficit. The finite-deficit case remains the first OPEN CORE. Existing full-deficit counting controls the threshold `3 ord(ξ)`, not this threshold `ord(ξ)`. Do not import the wrong deficit receiver.
- Anti-theatre: this cycle audited failed imports and rediscovered a known mean-square consequence; it did not move the scientific frontier. Anti-laziness: no proof was declined on effort grounds, but route scanning displaced proof construction. Next cycle must attack the finite signed degree-two remainder directly, retaining its exact pole data and cubic parent, before another broad literature sweep.

- 2026-10-07: Read hgtl7, project instructions, WP07/shared contract, exact correspondence, half-integer theorem, relevant frontier entries, C329 card and L222–L224 notes. No new theorem claimed. Existing working-tree changes left intact.
- 2026-10-07: Lexical `ZetaPowerDatum` search: seven declarations/two modules. `C329` lexical search: no declaration matches; rg locates paper notes. Deep corpus query running, output pending.
- 2026-10-07: Primary literature located: Kaczorowski–Perelli arXiv:2009.12329 and 2503.02492 (degree two); Cogdell's converse-theorem account (finite-pole Hamburger); degree-three conductor-one landscape (automorphic restrictions must not be imported into our larger class).
- 2026-10-07: Audit warning: L223's deduction “pole order >2m implies G(ρ)≠0” is unjustified for multiple zeta zeros. It gives ordρ(G)<m; no omission follows unless m=1. Record correction in owned outputs, not shared ledgers.
- 2026-10-07: Local-pencil proposal overlaps L273/L301/L387: REDISCOVERED as research direction; do not count it as a frontier result.
- 2026-10-07: Deep query completed, partial=false, but broad semantic hits mostly irrelevant. Coverage snapshot 68,280 files; compiler metadata mostly pending/source-only; refresh incomplete because background indexer running. Exact lexical/rg searches and source reading used instead of assuming absence.
- 2026-10-07: Central exclusion survives initial attack. Complete paper proof gives universal weighted mass <1/4, then third-quantized central gap and exclusion of negative sign. Main target remains open.
