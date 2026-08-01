# RH Current-Frontier Corpus Audit

- **ID:** rh-current-frontier-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** user-requested exhaustive audit of `HTGeometry`, `HilbertMetric`, and `RHTower`
- **Statement:** Produce a declaration-grounded, literature-checked map of every identified RH proof/disproof route, dead route, obstacle, and unresolved leap hypothesis in the current corpus.

## Goal

Write a review paper whose route claims are traceable to exact Lean declarations and whose dead-end and open-core claims are reconciled against pipeline records and current primary literature.

## Gates

- [x] 0 → 1 in-progress: scope fixed; corpus-first method fixed; read-only area audits assigned; audit log opened
- [ ] Corpus inventory: all three umbrella import closures accounted for
- [ ] Declaration audit: every RH-facing endpoint classified as unconditional, equivalence, conditional reduction, obstruction, or interface
- [ ] Route audit: chains, endpoints, open cores, and circularity risks reconciled across areas
- [ ] Failed-route audit: all route-relevant failed cards checked for exact obstruction and positive survivor
- [ ] Literature audit: unresolved leap claims checked against primary sources
- [ ] Completeness audit: hostile reread finds no omitted or misclassified route
- [ ] Paper complete: standalone review with theorem-level traceability and explicit limitations

## Audit invariants

- Lean declarations and their explicit hypotheses determine corpus truth.
- Names, docstrings, pipeline stage, and narrative prose never override theorem signatures.
- Explicit hypotheses are not counted as established analytic inputs.
- Equivalences to RH are route endpoints, not RH proofs.
- Formal obstruction theorems kill only statements matching their exact quantifiers and hypotheses.
- Existing dirty worktree changes remain untouched.
- Read-only agents may inspect but not edit repository files.

## Log

- 2026-08-01 — Session initialized: read project instructions, `docs/meta/scientific-method.md`, formal guide, Serena project memories, `hgt-fields-medalist`, and `scientific-writing` workflows.
- 2026-08-01 — Git audit found pre-existing modified, deleted, and untracked research/Lean files. Scope restricted to new audit artifacts; working tree will not be normalized.
- 2026-08-01 — Initial inventory found three very large theorem areas. Full audit method fixed: umbrella import closure → generated declaration index → exact source signatures → pipeline and literature reconciliation.
- 2026-08-01 — Transitive import-graph audit (source, not generated prose) found complete area closure: HTGeometry 3,408/3,408 leaves; HilbertMetric 52/52; RHTower 4,029/4,029. Direct umbrella imports are smaller because many leaves enter transitively. Source volume: 679,119 + 19,737 + 1,000,910 leaf lines.
- 2026-08-01 — Generated indexes are not fully synchronized with current source: `LEAN_OVERVIEW.md` reports HTGeometry 3,404 and RHTower 4,027 modules, versus source closure 3,408 and 4,029. Treat indexes as discovery aids only; exact source remains authoritative.
- 2026-08-01 — Missing mandated `docs/support-extraction-log.md`; only a historical validation card refers to it. This is a corpus-completeness limitation requiring explicit paper disclosure.
- 2026-08-01 — Verified architecture exception: `HilbertMetric/FourthCurvatureMixture.lean:1` imports `HTGeometry.HalfLineSteinRobertson`, contrary to formal guide's source-independence rule. Mathematical use must be classified by actual hypotheses, not advertised area boundary.
- 2026-08-01 — Corpus is moving during audit: new untracked HTGeometry modules and umbrella imports appeared after initial census. Completeness claim must be snapshot-qualified and final pass must recompute file/import/declaration hashes after a quiescence interval.
- 2026-08-01 — Exact `RiemannTower.lean` audit confirms foundational capstones are unconditional equivalences only: RH ↔ right-half nonvanishing ↔ coherent dyadic Kummer tower ↔ every multiplicity ladder rung. No direction constructs tower/roots from source data without assuming an RH-equivalent condition.
- 2026-08-01 — `RHCharacterizations.rh_tfae` packages fifteen equivalent mirrors (zeros, tower, ladders, height locus, valuation profile, census jumps, box zeros, variation sets, `u`-descent, deck charge, holography, window certificates, modulus slopes). These are atlas coordinates, not independent proof inputs.
- 2026-08-01 — First authoritative lint snapshot failed, not on proof debt but on source/index synchronization: unreachable `RHTower.SoninShellCutCouplingEnergy`, unreachable `HTGeometry.BooleanHypercubeTranspositionLaw` and `HTGeometry.CharacteristicEquilibriumDefect`, plus stale `LEAN_API.md`, `LEAN_GAPS.md`, and `LEAN_OVERVIEW.md`. Large-file warnings are nonfatal. This invalidates any completeness claim based solely on current umbrellas or generated inventories.
- 2026-08-01 — Current HilbertMetric source census: 52 leaves, 1,079 declaration heads, all imported; 28 direct external consumers (3 HTGeometry, 25 RHTower) through 30 import statements. Prior `WHOLE_CORPUS_*` artifacts exclude HilbertMetric and cannot establish Hilbert-to-RH dependency chains.
- 2026-08-01 — Prior publication census and manifest are useful historical route taxonomies but stale relative to the live tree. Every final count, endpoint, and first open premise will be regenerated from source at the frozen audit snapshot.
- 2026-08-01 — HilbertMetric read-only audit closed at 13:19 CEST: 52 leaves, 19,737 leaf lines, 1,079 public declarations, no `RiemannHypothesis` occurrence. Exact contribution is source-independent finite Hilbert/Fock/CCR/reconstruction machinery. Only direct RH handoff is `PrimeArchHankelDeterminantCriterion`, an equivalence whose all-degree source PSD/reconstruction phase remains open. Formal no-gos include finite full CCR, unrestricted quasi-free positivity, universal Gaussian log-concavity, dense closable unbounded scalar rigging, and character-mismatched invertible interfaces; each has a recorded positive survivor.
- 2026-08-01 — RHTower read-only audit froze at 13:22:32 CEST: 4,036 leaves, 1,005,498 lines, 50,070 regex declaration heads, 559 RH-containing files and 1,819 literal RH occurrences. Umbrella reached 4,035 leaves; sole then-unreachable leaf was untracked `DeningerHilbertKummer.lean`. Generated overview/API disagreed (46,802 versus 46,805 indexed declarations). No unconditional theorem of bare RH or bare `¬RH` exists.
- 2026-08-01 — RHTower route quotient stabilized into independent families: first-clock tail/Bohr; fixed-width rectangular Weil; complete Weil/Hedenmalm; prime–arch Hankel; Möbius/Mertens; Sonin transfer; Suzuki/Hermite–Biehler/Ward; Xi Taylor current; dyadic sharp prime window; quadratic spectral; Deninger/Hodge; Gamma–Jacobi singular reader; Hedenmalm prime-normal; Connes/prolate; completed-seam Thorin/Markov; moving-polynomial parity (retired); and secondary coordinate mirrors. Typed disproof interfaces exist, but none has an unconditional negative witness.
- 2026-08-01 — Literature audit against current primary preprints confirms external advances stop at the same kinds of source walls: Connes finite spectra need rigorous convergence; Suzuki finite self-adjoint models need the infinite/full-frequency identification; Hedenmalm supplies a formal theta spectral pair but not the all-order positive/self-adjoint realization; recent Möbius, Hardy, Colombeau, Salem, theta-infinity, and Thorin papers give conditional or equivalent criteria rather than a proof or disproof.
- 2026-08-01 — Post-snapshot RHT delta audit compiled four changed files individually. `DeningerHilbertKummer` closes real Hilbert-completion packaging but not arithmetic operator/spectrum construction. `SoninDilatedBandTransport` kills physical-band error and supplies a square-root norm floor, leaving frequency aggregate rate. `SuzukiVolterraCartesianPhaseDefect` splits the Volterra response into self-adjoint reflection-even symmetric and reflection-odd phase coordinates, proving symmetric positivity cannot recover phase; actual phase source-germ weld remains open. `ThetaCuspCalibratedPowerReciprocalMomentLaw` formally proves unique `alpha > 1` matching moments zero and one and quantitatively kills fixed `alpha = 1`; degree two onward remains open.
- 2026-08-01 — Tree mutation remains material: RHTower physical leaf count later dropped from 4,036 to 4,017 while a new unreachable `SoninShellCutBandPacketTerms.lean` appeared. Final paper must preserve dated counts and explicitly refuse a timeless zero-omission claim.
- 2026-08-01 — User-directed form correction applied: review paper contains present research state only; process chronology, census details, and mutation evidence remain confined to this audit log.
- 2026-08-01 — Final route reconciliation added exact fixed-width positive quadrature, grouped Mangoldt transport walls, sharp Sonin gap-tail/floor schedule, Suzuki light-cone and wall-field completions, Julia coherent-energy handoff, Deninger Hilbert/Kronecker infrastructure, and HT germ/centered-field results. Hostile read-only review reported no remaining route omission at its snapshot.
- 2026-08-01 — Live source subsequently closed additional intermediate layers: monotone cofinal Möbius--Plücker finite-prime/Euler-boundary diagonal on `Re(s)>1`, Gamma completion and negative reciprocal-square projectivization; unique least commuting Suzuki negative-part completion; explicit sharp Sonin band/high slack identities and weighted-tail vanishing; Deninger residual Hilbert nondegeneracy; arbitrary-measure nonlinear Herglotz compact-patch density; line-flat digamma-germ elimination; centered radical degree and full monodromy. Paper was updated to leave only their actual arithmetic continuation/source handoffs open.
- 2026-08-01 — July 23/29 Suzuki finite-element follow-up `arXiv:2607.24830v2` added to literature boundary: analytic archimedean head coefficient plus numerical/universal observations, no unconditional arithmetic finite-to-Xi limit.
- 2026-08-01 — Two `--require-stable` zero-omission census attempts failed to produce artifacts because new Lean modules landed during both passes. No census files were written; orphaned census readers were checked and no longer running. Final verification remains gated on quiescence and foreground Lean availability.
- 2026-08-01 — Further live reconciliation incorporated: analytic Sonin product-then-cut schedule existence, finite-torus Weyl/Kronecker density and integrated Deninger affine leaves, Gamma transcendence over finite digamma-jet germ fields, rectangular completed-lag strict lower carrier, and the singular literal/good/bad Julia Gram boundary. Their remaining open cores were narrowed accordingly.
- 2026-08-01 — Newly promoted reverse-Bessel theorem added to the retired-map quotient: normalized growing-order radial jets cancel Euler damping at every fixed prime, so least-prime and fixed finite-prime localization are impossible; exact positive integral carrier survives and forces a moving prime-window comparison.
- 2026-08-01 — Shared-machine load audit found concurrent external Lean/index jobs. This task launched no overlapping compiler, kept no background process, and deferred umbrella/final builds until a quiescent foreground window.
- 2026-08-01 — Sonin live delta closed two more premises: the ideal discount is exactly scale free, and one fixed product/start cut yields an admissible sequence with coupling energy bounded below linearly in annulus count and scale. The frontier is now the concrete linear-versus-logarithmic completion shortfall plus literal all-prime source handoff, not schedule or coupling-rate construction.
