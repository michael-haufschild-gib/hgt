# RW: arithmetic Markov form and the pole direction

- **ID:** RW-SIGN-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Read-only `docs/reports/rh-current-frontier-map.md`, RW.
- **Statement:** Derive a source law controlling the full restricted Weil energy, retaining the signed creation potential and both pole directions.
- **Contribution credit:** None yet. A stronger estimate, another capacity receiver, or an assumed positive background form does not qualify.

## Goal and plan

1. Inspect the exact Markov/pole decomposition and local-corpus source mechanisms.
2. Test independent arithmetic mechanisms for the remaining sign. Pay every prime cross-term, creation potential, and polar contribution.
3. Formalize only a dependency-closed positive theorem that removes a hard obstruction. Run direct Lean module and axiom audits, wire any finished modules, refresh indexes, and clean owned scratch.

No numerical experiments, external search, historical research Markdown, added analytic premises, or full/umbrella builds. Preserve other sessions' changes.

## Source facts inspected

`WeilMarkovPoleCapacity.lean` gives

`W(g) = M_N(g) + C(g)^2/2 - S(g)^2/2`,

where `C(g)=integral 2 cosh(u/2) g(u)`, `S(g)=integral 2 sinh(u/2) g(u)`, and

`M_N(g) = [Omega(0)-2 sum_(2<=n<=N) Lambda(n)/sqrt(n)] integral g^2 + J_arch(g) + J_prime,N(g)`.

Both jump measures are positive. Their positivity does not control the negative creation term. Taking absolute values lowers `M_N` but raises the pole term; the two inequalities do not order `W`.

`WeilArchimedeanExactForm.lean` retains the exact Gamma constant and full autocorrelation cosh moment. `WeilMarkovOneBoundState.lean` proves that `M` has a negative direction unconditionally, while excluding a negative definite plane is RH-equivalent.

## Initial conjecture ledger

- **R1: positive jump measures make the background form positive. Rejected as an inference.** The signed creation potential remains. On even tests `S=0`, so `Q=M+C^2/2` is already the original Weil form; positivity of `Q` cannot be supplied merely by a positive-definite matrix inverse formula.
- **R2: absolute-value contraction selects a positive ground state for the complete form. Unsupported.** Markov and pole pieces move in opposite directions. Need an exact accounting law, not separate monotonicity assertions.
- **R3: the even theta ground cancels the negative source. Rejected as a new sign proof.** `theta_harmonic_identity` and `phiDoob_markovEnergy_groundState_cancellation` already give exact cancellation. The result is positive archimedean/prime jumps minus `phiDoobCoshMass(v^2)`. This is the remaining Poincare inequality, not its proof.
- **R4: an odd theta ground absorbs every negative collar. Local absorption rejected.** `oddProfile_harmonic_identity` gives the favorable sinh source; `absorbedArchIntegrand_nonneg` absorbs the archimedean collar. Reflected prime measures remain singular to the positive jump measure (`CHMDReflectedPrimeSingularPart.positive_negative_mutuallySingular`). Strictly positive scalar reweighting cannot remove the first-prime obstruction. This does not exclude nonlocal factorizations or assert negativity of the full form.
- **R5: restore the collar diagonal and discard the obstruction. Insufficient.** The exact compensation is strictly positive for every nonzero odd compact test and has a finite-divisor cut expansion (`compensated_source_pos`, `compensated_source_hasSum_cuts`). The full formula `doob_source_eq_reflected_compensation` still subtracts the cosh mass. This positive survivor is already formalized; no new contribution credited.
- **R6: Perron selection or pure parity forces an admissible one-signed ground. Unsupported.** Nonnegative/unimodal cone bounds apply only to those cones; general ground selection has not supplied these hypotheses. Current concurrent `CHMDOddBoundStateSignObstructionAndParityQuarterBound.lean` gives an orthogonality law excluding one-signed odd bound states above the critical threshold, not positivity preservation. Its source was inspected read-only, without treating its untracked state as a completed new contribution.
- **R7: first-contact regularity eliminates a zero ground. Open and not established by existing results.** The physical null vector exists in the completed form domain. `CCMFirstContactSourceKernel` puts it in the exact operator kernel, while `SuzukiFirstContactBoundaryRoughness` excludes its membership in the strict smooth interior core. Dense approximants can all have positive energy while converging to a null vector.
- **R8: real-rooted ground transforms force the source sign. Not established.** `CCMRestrictedWeilFullFormRealRootedGround.exists_realRooted_fullGround` already holds at every aperture. Convergence, mass overlap, second-moment, or strip-growth hypotheses in the downstream RH receivers remain substantive. Polar ground multiplicity is exactly a parity crossing (`two_le_finrank_iff_both_parities`); no unconditional parity-selection law was found.

- **R9: strict aperture monotonicity prevents first contact. Rejected.** Translation independence and compactness already prove `strictAnti_ccmRestrictedWeilPolarGroundEnergy`. The positive survivor is an exact classification: RH gives strict positivity at every finite aperture; otherwise there is exactly one zero, positive energies below, negative energies above. Strict decrease permits this second branch. No new theorem is needed for this observation.
- **R10: a dilation/commutator conservation law forces a sign barrier. Unproved.** `ccmPrimePolarWeightedWindow_clockCommutator` is an exact integration-by-parts identity with signed cumulative source. `suzukiFiniteWeilPrimeTorque_eq` retains signed even/odd lag overlaps; its proved nonnegative specialization is the free cosh/sinh pair, not arbitrary actual ground responses. A barrier for the original ground remains to be derived.

## Positive-survivor audit

The local-collar obstruction retains a nontrivial exact positive survivor: original collar diagonal minus twice the reflected difference is positive crossing energy; its complete sum equals the finite-divisor cut expansion and is strictly positive on every nonzero compact odd test. Paper argument and Lean implementation already exist in `CHMDPrimeDivisorCuts.lean` and `CHMDReflectedPrimeSingularPart.lean`. Retain the negative cosh mass in the full source formula. Repackaging this existing result does not earn contribution credit.

Ground existence, finite-dimensional ground spaces, real-rooted transform selection, pure parity selection, and strict constrained aperture monotonicity are also existing positive results. The missing step is a nonlocal arithmetic sign law controlling the full form, or a justified selection/compactness law supplying the substantive premises in an existing ground-state receiver.

## Remaining source obligation

The full actual-head producer is already admitted for arbitrary aperture L2 heads: the exact translation-defect quadrature retains prime atoms, polar continuum, and endpoint (`CCMRestrictedWeilActualHeadCompletedErrorProducer`). The signed higher-Gamma/error producer equals the original source minus its scalar Gamma term and converges on canonical heads (`CCMActualHeadSignedCompletedErrorGammaProducer`). Its required scalar-shifted lower threshold is equivalent to nonnegative actual ground energy. An unsigned reciprocal-Gamma chi-square envelope is already proved divergent. Neither regularity repair nor a new producer name supplies the missing sign.

**Current outcome:** RW remains open; no significant positive contribution credited. The local absorptions, ground-selection proposals, and contact arguments above have not removed the nonlocal arithmetic sign obligation. No route retirement and no new analytic premise.

## Gates

- [x] Exact current split and its sign obligations inspected.
- [ ] Independent positive source mechanism.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean theorem and final direct verification.
- [ ] Significant-contribution audit.

## Log

- 2026-10-17 — Selected previously unworked RW. Started documented deep search `Weil Markov sinh capacity positive ground energy arithmetic pole direction`, budget 300 seconds.

- 2026-10-17 — First deep search completed (`partial=false`, no errors): 73,150 inventoried files; compiler coverage predominantly pending/stale; refresh incomplete because background indexer was running. Inspected candidate lemmas, source arguments, and ingredient sets. Proposed ingredient set assumes the unknown positivity and supplies no producer. Verified relevant statements against local Lean source.
- 2026-10-17 — Started second deep search `restricted Weil ground state source positivity real rooted division boundary unique continuation prime reflected singular Dirichlet`, budget 300 seconds. Audited exact ground-state identities, reflected-prime compensation, constrained parity/derivative structure, and first-contact source kernel. No numerical work or repository Lean edits.

- 2026-10-17 — Second deep search returned partial results: 73,152 inventoried files; `filter_and_judge` reported malformed/incomplete local-model JSON. Used available candidate/source statements; no completeness claim. Both result sections inspected. The proposed positivity-transfer ingredient set does not produce source positivity.
- 2026-10-17 — Started third documented deep search `restricted Weil ground dilation virial commutator prime polar Ward first contact`, budget 300 seconds. Started a single direct Lean scratch audit of 20 existing results; no repository Lean edits.

- 2026-10-17 — Third deep search completed (`partial=false`, no errors), 73,152 inventoried files. Candidate/source/ingredient sections inspected. Suggested commutator assembly leaves the real-part bound as an explicit unproved obligation. Local source inspection confirms the completed-error producer already has full L2 admission and exact signed cancellation; its unknown threshold is the original ground-energy sign.

## Verification and handoff

- `lake --old env lean /tmp/hgt_rw_audit.lean` exited 0. All 20 requested existing declarations produced axiom reports using only `propext`, `Classical.choice`, and `Quot.sound`; no errors or warnings. This was an import/name/axiom audit, not a new proof or a full rebuild. All ten directly imported compiled modules were no older than their source files.
- No repository Lean declaration added or changed by this turn. No umbrella/index update needed. Concurrent work preserved.
- Own card passed trailing-whitespace and final-newline checks. All five owned search/audit scratch files removed; absence verified after process exit.
- Qualifying-contribution gate remains **unsatisfied**. Full cross-route goal remains active and incomplete. RW is audited, not retired or solved.
