# Every moment profile is dense in recovery-history space

- **ID:** weil-logshift-recovery-domain-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus: recovery homeomorphism, adaptive prefix, arithmetic potential-domain realizations.
- **Statement:** Any finite prescribed recovery history can be realized while retaining the signed, excess, and deficit summability domains of any chosen baseline. Every such moment-profile class is dense in the product topology on histories.

## Mission and scope
Extract verified mathematical structure from the local Lean corpus. No external papers or web sources. Previous increment proved bounded ±1 recovery samples compatible with divergent moments. This increment asks what finite history data can determine about entire moment domains. It does not settle boundedness at all real cutoffs.

## Corpus audit
Direct lexical research searches for recovery/innovation/weighted summability and finite-prefix/dense potential domains found the triangular reconstruction, all symmetric interval realizations, and inward-transfer lemmas. Exhaustive relevant Lean-source searches found no existing recovery-domain-density or innovation criterion. Existing results establish exact product-topology recovery but not density of moment-profile fibers.

## Dependency-closed paper proof
[PROVED HERE] Given baseline b, desired history h, and N, let λ_N use the existing inverse of h below index N+2 and b at all later indices. Every recovery sample k<N depends only on coefficients through k+2, so its value is exactly h(k). Each of the signed, excess, and deficit weighted series differs from the corresponding baseline series at only finitely many indices, for every real shift simultaneously. Their summability domains therefore coincide exactly.

For fixed h, the histories of λ_N are eventually equal to h in each coordinate, hence converge to h in the product topology. Each lies in the baseline's moment-profile class, proving density. Applying this to existing zero-excess minorants realizing arbitrary open or closed symmetric intervals shows that any finite observed prefix admits every such domain, with all excess moments still finite. A von Mangoldt baseline similarly supplies whole-line convergence, and the radius-zero open-domain baseline supplies nowhere convergence.

The interval realizations also have finite total excess: their excess is zero outside the finitely modified head. This stronger conclusion follows from the same finite-tail argument and introduces no analytic assumption.

## Plan
1. Verify finite-tail and topology APIs in a scratch Lean file.
2. Formalize splicing, all three moment invariances, coordinatewise convergence, and moment-class density.
3. Formalize arbitrary finite-prefix open/closed domain realizations and the whole-line/empty-domain distinction.
4. Compile the leaf, audit all public axioms, wire imports, refresh index, run lint, update memory, remove owned scratch.

## Gates
- [x] Source-pure corpus audit and closed paper proof.
- [x] Exact Lean results compiled and axiom-audited.
- [x] Imports, index, scoped checks, and global lint recorded.

## Formal results

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryDomainDensity.lean`.
Two definitions and nine public theorems:

- `weilLogShiftRecoverySplice`: inverse-history head joined to a chosen baseline tail.
- `weilLogShiftRecoverySplice_tail`: exact baseline agreement after N+2.
- `weilLogShiftRecoverySplice_history`: exact matching for every history coordinate k<N.
- `summable_weilLogShiftRecoverySplice_terms_iff`: summability of any coefficientwise real series is unchanged.
- `WeilLogShiftMomentEquivalent`: all three weighted convergence domains agree at every real shift.
- `weilLogShiftRecoverySplice_momentEquivalent`: splicing retains this complete profile.
- `tendsto_weilLogShiftRecoverySplice_history`: the spliced histories converge coordinatewise to any prescribed history.
- `dense_weilLogShiftRecoveryHistory_momentClass`: every realized three-domain profile is dense in the product topology on histories.
- `exists_weilLogShiftRecoveryPrefix_open_domain`: arbitrary finite histories coexist with any radius-|R| open domain, finite total excess, and all finite local excess moments. R=0 gives the empty domain.
- `exists_weilLogShiftRecoveryPrefix_closed_domain`: the same for closed domains; R=0 gives the singleton origin.
- `exists_weilLogShiftRecoveryPrefix_entire_domain`: arbitrary finite histories also coexist with whole-line convergence.

## Verification

- Final leaf compile/export: exit 0, no diagnostics, on the first leaf compilation.
- All eleven public declarations audited via scratch `#print axioms`: exactly `[propext, Classical.choice, Quot.sound]`, compiler exit 0.
- Umbrella wired; index refresh exited 0; all eleven API rows checked for unique name and correct module.
- Scoped whitespace/conflict-marker checks and `git diff --check` passed.
- Global lint exited 1 only for two unrelated unwired modules: `RHTower.PaperSuzukiCarrierNullSets` and `RHTower.PaperSuzukiCayleySynthesis`. Neither was changed. This is the current snapshot, replacing earlier unrelated-module lists.
- No new analytic hypotheses/axioms, proof gaps, numerical experiments, heartbeat/recursion increases, web or external-paper sources, umbrella builds, commits, or subagents.

## Interpretation and limits

Exact finite data determine a coefficient head but cannot determine the convergence radius, endpoint inclusion, or even whether any shift converges. The positive result is constructive, simultaneous preservation of all three moment domains and density of every realized profile. These statements concern arbitrary real coefficient systems; they do not add arithmetic constraints or assert RH. Boundedness at every positive real cutoff remains unresolved.

## Follow-up proved: residual nowhere summability

[Generic moment divergence](weil-logshift-generic-moment-divergence.md) now proves this conjecture. A dense residual set has arbitrarily large origin-weighted excursions of both signs in every tail, which forces all three moment domains to be empty. The histories admitting even one summable moment at any real shift form a meagre set. The proof uses open dense excursion sets and the corpus countable-intersection theorem; inward transfer handles all real shifts. All twelve follow-up declarations compile and have standard-axiom audits. The bounded-history cube remains a separate question.

## Log
- 2026-10-09 — prior turn classified verified progress; derived finite-tail moment-profile invariance and dense history realizations from existing Lean results.
- 2026-10-09 — eleven public declarations written in `WeilLogShiftRecoveryDomainDensity.lean`; exact toolchain API checks passed. Leaf compile/export pending.
- 2026-10-09 — all eleven declarations compiled, axiom-audited, indexed, and wired. Density and arbitrary finite-prefix domain realization verified; next conjecture recorded without claiming it.
