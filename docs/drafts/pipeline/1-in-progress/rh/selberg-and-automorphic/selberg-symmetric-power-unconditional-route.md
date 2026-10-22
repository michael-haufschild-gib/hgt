# Selberg quarter conjecture through symmetric-power amplification

- **ID:** SELBERG-SYMMETRIC-POWER-UNCONDITIONAL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User-requested proof search, 2026-09-07; existing `selberg-quarter-conjecture-corpus-audit.md`.
- **Statement:** Prove the quarter bound for nonzero weight-zero congruence Maass cusp eigenfunctions by constructing compatible generic unitary symmetric-power lifts in unbounded degree and applying their archimedean exponent bounds.

**Status:** Requested Selberg proof not obtained. Autonomous proof search is blocked after three consecutive goal turns encountering the same missing global lift construction. The exact scalar degree-family classification below is proved and formalized; compatible Maass lifts remain unconstructed. The mathematical route is not retired or disproved.

## Goal

A closed Lean proof of the actual spectral assertion. A scalar strip identity, a theorem with a lift-existence premise, or an artificial positive packet is not this result. No extra mathematical axioms, admitted proofs, numerical experiments, or computational certificates.

## Plan

- [x] Read prior Selberg research and current local representation status.
- [x] Search the whole declaration index for lift constructions and alternative mechanisms: converse theorems, tensor/character identities, descent, positivity, and limiting arguments.
- [x] Inspect exact definitions and hypotheses of every candidate retained for the route; verify current primary sources.
- [x] Derive a dependency-closed paper proof before formalizing any new assertion.
- [x] Check resulting Lean work in foreground, one Lean process at a time; perform targeted final build, umbrella wiring, lint, and scratch axiom audit. Global lint has unrelated errors listed below.
- [x] Record exact progress and remaining mathematical obligations without marking the conjecture proved.

## Initial evidence

The existing source already proves the exact positive-degree scalar strip locus, all-degree and all-even-degree amplification, invariant forms on explicit spherical complementary-series models, and corresponding product-packet statements. None of their definitions constructs an automorphic symmetric-power lift. The generic GL(n,R) bridge and the global Maass lift construction require separate proofs.

There are concurrent changes in the principal-series derivative modules and the RHTower umbrella. Preserve those changes; inspect current contents before any narrowly scoped umbrella edit.

## Dependency-closed scalar extension: paper proof

For a set `D` of natural degrees, let `L(D)` be the real parameters whose symmetric-power exponent packets lie in the open half-strip at every degree in `D`. The exponent formula already proved in the corpus gives

`ν ∈ genericUnitarySymPowerLocus d ↔ d |ν| < 1/2`,

including degree zero: the endpoint `j=0` proves necessity, and `|d-2j| ≤ d` proves sufficiency.

**[PROVED HERE] Exact degree-set classification:** `L(D) = {0}` if and only if `D` is infinite. Equivalently, for each nonzero real `ν`, only finitely many natural degrees pass the strip test.

Proof: if `ν ≠ 0`, every passing degree satisfies `d < 1/(2|ν|)`, hence belongs to a finite initial segment of the naturals. An infinite `D` cannot be contained in that segment. Zero passes every test. Conversely, if `D` is finite, choose a natural upper bound `N` for it and set `ν = (1/2)/(N+2)`. Then `0 < ν < 1/2`, and for every `d ≤ N`, `dν < (N+2)ν = 1/2`. Thus `ν ∈ L(D)` and `ν ≠ 0`.

The converse also supplies positive scalar eigenvalues `1/4−ν² < 1/4` passing every bounded-degree strip test. These are scalar parameters, not asserted congruence Maass eigenvalues. Arbitrarily sparse unbounded degree sets suffice; a theorem constructing only bounded degrees cannot close the scalar amplification argument by itself.

This is an elementary extension of the existing all-degree/all-even-degree calculation, not a new functoriality theorem or a proof of Selberg. The route is not retired.

## Corpus-driven attempts and their exact limits

Twenty-seven distinct declaration-index queries searched all theorem areas, supplemented by `rg` over owned Lean, mathlib, and prior Selberg research. The index was refreshed initially; follow-up discovery used `--no-refresh`, no module restriction, and no per-module cap. Broad discovery is not an exhaustive proof-body audit of the entire corpus. Searches with large results were saved in temporary JSON files and refined by mathematical mechanism.

| Query | Declarations | Modules |
|---|---:|---:|
| `"symmetric power"` | 48 | 13 |
| `automorphic lift` | 2 | 2 |
| `functoriality` | 150 | 40 |
| `"converse theorem"` | 0 | 0 |
| `"langlands"` | 0 | 0 |
| `"maass" "hecke"` | 0 | 0 |
| `"automorphic" "tensor"` | 1 | 1 |
| `"rankin" "selberg"` | 8 | 4 |
| `"whittaker"` | 159 | 18 |
| `"satake"` | 56 | 15 |
| `"automorphy"` | 28 | 12 |
| `"tannaka"` | 0 | 0 |
| `"tempered"` | 238 | 39 |
| `"symmetric" "unbounded"` | 8 | 6 |
| `"tensor" "unitary"` | 30 | 20 |
| `"amplification"` | 733 | 135 |
| `"unbounded" "exponent"` | 15 | 15 |
| `"generic" "unitary"` | 44 | 6 |
| `"converse" "modular"` | 0 | 0 |
| `"galois" "maass"` | 228 | 17 |
| `"holomorphic" "maass"` | 0 | 0 |
| `"isobaric"` | 9 | 4 |
| `"automorphic representation"` | 8 | 1 |
| `"adelic"` | 2005 | 144 |
| `"symmetric" "finite" "degree"` | 9 | 7 |
| `"amplification" "sublinear"` | 5 | 2 |
| `symmetricPower degree finite` | 0 | 0 |

Counts are discovery evidence only. For example, the `galois` term matches the project namespace and supplies no evidence of a Galois representation attached to a Maass form.

1. **Character recursion / tensor operations.** Read `SatakeSymPower.lean`, `SatakeTensor.lean`, and `AdamsOperations.lean`. Their inputs are finite lists of complex numbers. They prove symmetric characters, tensor Euler-factor identities, and nonnegative second moments. They do not construct global representations, continue the corresponding global products, or propagate automorphy in the degree. The character norm bound explicitly assumes `‖z‖=1`; importing it as Ramanujan would assume the parameter bound.
2. **Actual Maass representation.** Read `MaassCyclicAutomorphicRepresentation.lean`. Its result is a cyclic representation of `SL(2,R)` on an algebraic subspace of invariant functions. Its own docstring separates Hilbert completion, irreducible decomposition, adelization, and local factorization. It cannot yet instantiate a cuspidal adelic `π` in a functoriality theorem.
3. **Local invariant forms.** Read `GenericUnitaryExponentBounds.lean` and `SelbergExceptionalSphericalModel.lean`, plus the scalar exponent module. The packet criterion concerns explicitly defined rank-one blocks; it is not a classification of arbitrary generic unitary `GL(n,R)` representations. The exceptional scalar subtype does not assert occurrence in a congruence cusp spectrum. Neither point can be bypassed by renaming a type or a theorem.
4. **Cofinal amplification / small finite perturbations.** Inspected the cofinal-action and sublinear-growth declarations in `HTGeometry/RegularInertiaAmplification.lean` and the finite-matrix perturbation statements in `RHTower/FiniteDegreeReciprocalPerturbation.lean`. These suggested separating the finite-degree and unbounded-degree cases explicitly. Their objects are integer-charge cyclic models and finite matrices, respectively; neither supplies Maass lifts. The useful transferred mechanism is precisely the scalar classification proved above.
5. **Converse theorems / isobaric closure.** Source search found discussions in `selberg-orthogonality-working-log.md`, including sections 180 and 202. The matching Lean results are finite Satake identities, not analytic converse theorems or automorphic closure. Claims in those draft discussions were not used as established theorems. No retained candidate supplies compatible unbounded-degree lifts.

Serena symbol lookup rejected the Lean path as ignored by its active configuration. Source inspection therefore used `rg` and direct file reads; no Serena configuration was changed.

## Current primary-source check

- [Sarnak, Section 1, especially (13) and the discussion following (18)](https://publications.ias.edu/sites/default/files/FieldNotesCurrent.pdf): the archimedean half-strip bound uses genericity and unitarity. Symmetric-power functoriality supplies the global route to Ramanujan. Unitarity without genericity permits a bound growing with rank, which would not give the required fixed half-strip. This source supports the chain, not the missing general Maass lift theorem.
- [Newton–Thorne, Annals of Mathematics 203 (2026)](https://annals.math.princeton.edu/2026/203-1/p04): all symmetric-power lifts for representations associated to Hilbert modular forms of regular weight. This still does not cover the weight-zero Maass input.
- [Ng–Wang, August 2026, Theorem 1.1](https://arxiv.org/html/2608.10378v1): a sign-change result for coefficients of symmetric-power Euler products of Hecke–Maass forms. Its displayed conclusion is not automorphy or an archimedean quarter bound.
- [Sharma–Sankaranarayanan, Filomat 40:6 (2026), Remark 2.1](https://www.pmf.ni.ac.rs/filomat-content/2026/40-6/40-6-8-25651.pdf): discusses analytic properties in bounded degrees. This was checked to distinguish an apparent search-result lead from unbounded-degree automorphic lifts; none of its assertions is imported into Lean here.

## Remaining proof obligations

The requested theorem is not proved. A continuation must construct, for each relevant Maass representation, lifts for an unbounded set of degrees with the required infinity parameters, and prove the generic unitary bounds for their actual local representations. If a lift is noncuspidal, its isobaric constituents and real twists must be controlled so the exponent bound survives. The existing real cyclic representation must also be connected to the appropriate cuspidal adelic representation.

The new scalar theorem does not discharge any of these representation-theoretic or global arithmetic obligations. Further equivalent positivity predicates would not do so either. No route retirement or claim of impossibility is made.

## Lean results and audit

New module: `formal/GaloisForLFunctions/RHTower/SymmetricPowerDegreeFamilies.lean`.

- `mem_genericUnitarySymPowerLocus_iff_mul_abs`
- `finite_genericUnitarySymPower_degrees_iff`
- `exists_positive_exponent_in_genericUnitarySymPower_initial_segment`
- `genericUnitarySymPower_degree_family_eq_singleton_iff`
- `exists_exceptional_scalar_in_finite_genericUnitarySymPower_family`

All five statements are closed universal theorems about the existing exponent packet, with no lift-existence, positivity, or spectral-bound assumptions. They are auxiliary theorems, not Selberg's conjecture. The module is wired into `GaloisForLFunctions.RHTower`; the umbrella is not built.

Verification on 2026-09-07:

- `lake env lean /tmp/selberg_degree_names.lean`: passed after removing an unnecessary unavailable import; verified the installed mathlib names.
- `lake env lean /tmp/selberg_degree_family.lean`: passed after fixing a real-cast annotation and removing a redundant tactic.
- `lake env lean GaloisForLFunctions/RHTower/SymmetricPowerDegreeFamilies.lean`: passed, no warnings.
- `lake build GaloisForLFunctions.RHTower.SymmetricPowerDegreeFamilies`: passed; only the new module was reported rebuilt. No full or umbrella build.
- `lake env lean /tmp/selberg_degree_family_axioms.lean`: passed; checked all five theorem signatures and printed their axioms. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, additional mathematical axiom, or native evaluation axiom.
- Exact forbidden-token / computational-command scan of the new module: empty.
- `python3 scripts/formal_tools.py index`: completed.
- `git diff --check`: passed.
- `python3 scripts/formal_tools.py lint`: **failed**, with existing large-file warnings and three unrelated missing umbrella imports: `GaloisForLFunctions.RHTower.DivisorSmoothBlockOrientation`, `GaloisForLFunctions.RHTower.MontgomeryPairCorrelationLeadingOrder`, and `GaloisForLFunctions.RHTower.SymmetricSqrtClockBounds`. These concurrently edited modules were not modified here. The new Selberg module was not among the failures.
- Final `pgrep` for Lean/Lake processes: empty. No background proof processes were started.

Concurrent repository activity committed the new module and its umbrella import during this audit (`HEAD` observed as `2dca80eea`, subject `research`). This task did not run commit or push. The research card remains the durable continuation record.

## Continuation: global lift construction

Previous goal turn classified as **progress**: added and verified the exact degree-family theorem, without proving Selberg. This continuation targets the missing global construction, not further scalar reformulations.

- [x] Inspect the corpus's multiple-twist continuation machinery for actual symmetric-power coefficient input and analytic continuation output.
- [x] Check weak all-degree Maass functoriality results and newly located 2026 claims against the required infinity compatibility and degree quantifiers.
- [x] Audit whether tensor recursion, analytic quotients, or converse theorems can produce the needed unbounded-degree construction without unproved hypotheses.
- [x] Record whether a genuine new construction or a continuing impasse has been established.

**Outcome: no global lift construction obtained.** No additional Lean module was added in this continuation. The original unconditional Selberg objective remains unachieved; the scalar results above are auxiliary. This is a failure to close these proposed constructions, not a theorem that the symmetric-power route is impossible.

### Further corpus search

The refreshed `"symmetric power"` search returned 53 declarations in 14 modules, now including the five auxiliary theorems above. Seventeen further corpus searches explored analytic construction, representation realization, and algebraic recursion:

| Query | Declarations / modules |
|---|---:|
| `"tensor" "continuation"` | 4 / 4 |
| `"symmetric" "continuation"` | 26 / 7 |
| `"twist" "entire"` | 23 / 11 |
| `"rankin"` | 43 / 21 |
| `"converse" "L-function"` | 0 / 0 |
| `"hecke"` | 3 / 1 |
| `"local" "global" "representation"` | 3 / 3 |
| `"positive" "dirichlet" "pole"` | 6 / 4 |
| `"braverman"` | 0 / 0 |
| `"vinberg"` | 0 / 0 |
| `"poisson" "automorphic"` | 0 / 0 |
| `"symPower" "recurrence"` | 0 / 0 |
| `"chebyshev" "product"` | 17 / 9 |
| `"meromorphic" "quotient" "order"` | 12 / 11 |
| `"spherical" "tensor"` | 0 / 0 |
| `"whittaker"` | 159 / 18 |
| `"symPower" "tensor"` | 0 / 0 |

The installed dependency sources were also searched for Langlands, symmetric-power automorphic lifts, converse theorems, and Maass eigenform terms. No applicable construction was located. Search coverage has the indexing limits stated above; these counts do not prove nonexistence of a theorem. Located Whittaker candidates include explicit Eisenstein expansions; no construction of arbitrary Maass symmetric-power lifts was verified among them.

### Audit of the analytic construction candidates

All paths in this subsection are relative to `formal/`.

1. **Multiple twists do not supply functorial tensor products.** In `GaloisForLFunctions/SelbergClass/MultipleStandardTwistTensor.lean`, `multipleStandardTwistTerm` multiplies independently indexed Dirichlet coefficients and a nonlinear phase. Its type is not an automorphic representation. `MultipleStandardTwistData` requires a family of `RHTower.ExtendedSelbergClass` inputs, positive degrees and weights, and a weighted-degree identity. No theorem identifying this series with the requested symmetric-power L-function was found.
2. **Removing damping does not yet continue across the boundary.** `MultipleStandardTwistData.differentiable_damped` proves entire differentiability for positive damping. `tendsto_damped_atTop` assumes every coordinate has real part greater than one. In `MultipleStandardTwistInitialUndamping.lean`, the uniform limit theorem requires `1 < (s₀ i - ↑(2 * r)).re` for every coordinate. Thus its certified balls stay inside the initial convergence domain. Passing to the undamped limit elsewhere requires a new convergence theorem.
3. **Uniqueness does not construct the continuation.** `MultipleStandardTwistData.eq_of_analyticOnNhd_eqOn_initial` in `MultipleStandardTwistContinuationUniqueness.lean` requires both candidate functions to be entire and to agree with the initial series. In `MultipleStandardTwistGammaClearing.lean`, `gammaClearedPresentation` requires an entire numerator `G` as input. Neither supplies that numerator from general Maass symmetric-power coefficients.
4. **A quotient requires zero cancellation.** Mathlib's `meromorphicOrderAt_div` identifies quotient order with numerator order minus denominator order. Consequently, an Euler-factor identity solved by division supplies no missing zero-order inequality by itself. `GaloisForLFunctions/HTGeometry/MinimalTypeNevanlinnaAperiodicity.lean` locates possible quotient poles at denominator zeros; it does not remove those poles. Even a successful scalar meromorphic continuation would still need the global representation, infinity compatibility, and constituent control required by this route.
5. **Bundling the desired analytic properties would assume the missing input.** `GaloisForLFunctions/RHTower/SelbergClass/Basic.lean` defines `RHTower.ExtendedSelbergClass` with continuation, agreement with the Dirichlet series, and functional equation as fields. Assigning symmetric-power coefficients to a constructor is not a proof of these fields.

### Current primary-source leads checked

- [Booker, Theorem 1.1](https://link.springer.com/article/10.1007/s00209-018-2157-3): special Galois-conjugate Maass pairs with coefficients in `ℤ[φ]` have weak lifts in every degree, matching specified finite places. The theorem does not give the required infinity compatibility. Its quarter-eigenvalue conclusion requires a further condition: finitely many non-tempered primes or automorphy of the fifth symmetric power. These restrictions prevent applying it to general Maass forms.
- [Hsu–Yao, revised 13 August 2026](https://arxiv.org/html/2607.28507v2): Theorem 1.4 develops local zeta integrals; §7.2.2 treats every even symmetric power using the local monoid `det A = z^(2n)`. This provides a concrete local construction to study, but no global automorphic lift or real-place compatibility theorem. The paper also retains locality as Conjecture 1.5. The full HTML was read directly after browser fetching timed out.
- [Getz et al., revised 20 May 2026](https://arxiv.org/html/2512.00182v3): Theorems 1.3 and 1.6 construct local Fourier theory, with the stated identities tested on tempered representations. They do not construct the global Maass lift. Applying a tempered-input statement directly to an exceptional Maass parameter would assume the point at issue.
- [Arias-de-Reyna–Dieulefait–Pérez, revised September 2025](https://arxiv.org/abs/1611.06918v4): the arbitrary-rank tensor theorem uses a level-one classical modular form and regular algebraic polarized automorphic Galois data, with regularity and irreducibility conditions. It does not provide the missing general Maass input for an induction. The related [April 2026 Feng seminar](https://www.maths.ox.ac.uk/node/80971) announces further cases, but no theorem covering general Maass forms was located on the author's research page.
- An [SSRN claim posted August 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7178938) was located through its indexed abstract. Full text could not be accessed. Its claims remain unverified and are not used as proof input.

### Continuation verification and remaining obstacle

`lake env lean /tmp/selberg_global_lift_audit.lean` passed in one foreground process using existing dependencies. It checked the exact signatures of the continuation fields, damping and undamping theorems, uniqueness theorem, gamma-clearing construction, and quotient-order formula. The two audited continuation/undamping theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. This verifies their actual hypotheses, not the missing Maass construction. No new build was needed.

The remaining obstacle is unchanged: construct compatible global generic unitary lifts in an unbounded set of degrees for general Maass input, including the noncuspidal cases, without assuming the lift or its required analytic properties. The searched corpus and checked current papers have not supplied that construction. No Lean proof of Selberg is claimed, and the route remains in progress rather than retired.

## Third-turn revalidation and blocked audit

The preceding turn is classified as **progress in the evidence audit**: exact Lean signatures and newly checked papers eliminated concrete proposed constructions and determined the next check. It did not advance the formal Selberg theorem.

Current-state revalidation on 2026-09-07:

- Serena's Selberg memory inventory has no new entry. The scalar module, exponent module, cyclic Maass representation, continuation uniqueness, and initial undamping sources have no changes relative to the tracked versions audited above. The scalar module remains imported by `RHTower.lean`.
- A refreshing corpus query `"automorphic" "lift"` returned no indexed declarations. `"minuscule"` likewise returned none. A full source text search for symmetric lift/functoriality, Maass adelization, Langlands, and isobaric terms located no new applicable construction. This remains discovery evidence, not a nonexistence theorem.
- The remaining SSRN lead still had no accessible full text. Its indexed abstract restricts its advertised functoriality conclusion to irreducible minuscule representations. That scope does not directly cover the higher symmetric powers required here. [Kisin–Pappas, §1.2.9](https://people.math.harvard.edu/~kisin/dvifiles/parahoric.pdf) states that the irreducible minuscule representations of `SL₂` are standard and trivial. Equivalently, using the [symmetric-power weight formula](https://people.math.harvard.edu/~elkies/M222.23/index.html), for `m ≥ 2` the weight `m−2` is outside the Weyl orbit `{m,−m}` of the highest weight. This is an applicability check; the SSRN proof itself remains unverified. Realizing a higher symmetric power by first transferring to a larger group would require a new transfer construction, which has not been supplied.
- No Lean source was edited or new Lean process started in this turn. Process inspection found no running Lean/Lake build processes. Passed checks above were not repeated without a source change.

| Required conclusion or bridge | Evidence status |
|---|---|
| Quarter bound for every nonzero weight-zero congruence Maass cusp eigenfunction | Missing: no theorem of this scope obtained |
| Maass input to the required cuspidal adelic representation | Existing cyclic real representation does not supply the full bridge |
| Compatible global lifts in an unbounded set of degrees | Missing: no construction or closed proof obtained |
| Infinity compatibility and generic unitary bounds for the actual lifts | Missing: explicit model-packet bounds alone do not establish these |
| Noncuspidal constituent and real-twist control | Missing |
| Closed proofs without assumed functoriality or new axioms | Achieved for the auxiliary scalar theorems only |
| Foreground targeted verification, umbrella wiring, process cleanup | Recorded above for work actually performed; no full builds |

The same central obstacle was present in the original goal turn, the global-construction continuation, and this revalidation. No audited source or newly derived argument closes it. Adding another conditional wrapper or scalar consequence would not make the requested theorem true. At this point there is no concrete proof construction I can carry forward under the unconditional requirement. The task is therefore marked **blocked**, not complete. Resuming the same objective requires a substantive new argument or proof input resolving the global construction; this is not a claim that such an argument cannot exist.

## Log

- 2026-09-07 — Opened before substantive proof search. `docs/architecture.md` and `docs/testing.md` absent. Serena Selberg memory and formal project entrypoints read. The `update_plan` tool is unavailable; this card carries the plan.
- 2026-09-07 — Completed 27 corpus queries and current-source checks. Formalized five auxiliary scalar theorems, including the exact infinite-degree criterion and finite-degree exceptional-scalar survivor. Targeted build and all axiom checks passed; global lint exposed unrelated concurrent wiring gaps. The Selberg goal remains unachieved.
- 2026-09-07 — Continuation audited multiple-twist analytic construction, quotient recursion, weak Maass lifts, and 2025–2026 local Fourier/tensor results. Seventeen further corpus searches and a foreground Lean signature audit found no closed global lift construction. No further theorem was added or substituted for Selberg.
- 2026-09-07 — Third goal turn revalidated current sources and umbrella wiring, refreshed lift searches, and checked the minuscule restriction on the remaining unverified literature lead. The same global construction gap persists. Blocked audit threshold reached; unconditional Selberg proof remains unachieved.
