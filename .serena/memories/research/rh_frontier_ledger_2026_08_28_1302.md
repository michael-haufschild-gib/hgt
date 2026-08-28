# RH frontier ledger audit — 2026-08-28 13:02 CEST

Target updated: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.

Evidence rule: Lean corpus only, queried with `scripts/formal_tools.py research`; no cards, papers, literature, builds, or Lean edits.

Freshness cutoff: all substantive HTGeometry/HilbertMetric/RHTower `.lean` files through mtime `2026-08-28 13:01:01` were audited. Final `find -newermt` after that cutoff returned empty.

Current ledger: 861 lines, 26 live rows, 30 candidate rows, `git diff --check` clean.

Material topology changes:
- LI promoted candidate -> live. Exact finite Chebyshev prime–Gamma landing and source-only all-degree RH criterion are Lean-proved. Open core: unconditional nonnegativity of every `liPrimeArchShiftedMomentSource d`.
- HCF added as candidate: thin-strip source contour extracts critical-line multiplicity; corrected pole–Gamma–von-Mangoldt lattice budget is source-defined. Named `4/25` ceiling gives three-quarters-line result, not RH; RH needs zero budget/additional bootstrap.
- NDS retired as independent producer. Arbitrary reduced-conductor regulator exists iff RH; nodal arithmetic/Picard–Lefschetz naturality is globally iff RH. Oriented cut-two holonomy gives unconditional defect-preserving regulator and survives only as R/JAS/WBF completion carrier.
- SC advanced: infinite all-prime bounded reflection-odd rigged Krein form exists; exact radical and global index-one classification modulo radical closed. Open: Xi landing/determinant and global polarization. Finite-port Stokes landing terminal.
- HC advanced: continuous confluent counterterm, summable literal Gamma-six collision current/loss, and nonzero `log 2 / m^2` residue closed. Open: coefficient-faithful comparison with multiplicity-sensitive Gauss–Hodge current.
- EGC advanced: entire Gaussian horizontal-edge path terminal; fixed-pole rational kernel avoids real-axis amplification, deletes diagonal, saturates distinct pairs. Source multiplicity extractor and finite contraction exist. Open: pole-safe nested source contour and cofinal vanishing.
- HB narrowed: arbitrary-kernel Ward classification; line-conjugate pairing is source-covariant but QNM-local iff RH; physical identity pairing is QNM-local but source-covariant iff RH; source-fixed gauge/clock coherence iff RH. Finite-radiation deck jump faithfully transports clock defect and conservation cannot cancel it. Open only nonlinear/singular pre-divisor extinction law.
- CLG/TTF narrowed: rank-four odd wall equals Ptolemy; mixed failure descends to one literal source fibre. Each fibre is positive near center and infinity; failure forces an interior stationary negative fibre satisfying exact three-scale decay-flux balance. Open: rule out that stationary fibre, then higher packets/cofinal no-escape.
- T2 gained exact infinite adjacent-prime log-mesh current, sharp transport norm, coefficient probes, Hardy/Fourier landing; shell defect remains open.
- WBF gained exact positive Wold response/current/reflected-work transmutation.
- Route-neutral response-work polarization added; noncommutative qubit has exact positive BKM response and quantum Jeffreys integral but no Xi landing.

No builds run; documentation-only task.