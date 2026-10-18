# Second- and third-band renormalized defect calculus

Module: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SecondAndThirdBandRenormalizedDefectCalculus.lean` (26 public theorems, 2 private helpers), wired exactly once into the field umbrella, reachable from MainTheorems. Card: `docs/drafts/pipeline/3-formalized/thim-second-third-band-defect-calculus.md`. Ledger: `logs/thim-band-defect-knowledge.md`; audit: `logs/thim-band-audit.json`.

For cε(n)=μ(n)n^(-ε), ε≥0, every endpoint 2≤k≤3N has |s_N(cε,k)|≤1, with no parity restriction. Through 4N the envelope holds when either 2 or 3 does not divide k. Polarization gives 2D_N(M)≤-Σ(s_N(k+1)-s_N(k))²≤0 for M≥1 in those endpoint ranges k=M+1. Thus all checkpoints through 3N-1 are nonpositive; all even checkpoints extend through 4N-1. Zero damping specializes to literal Möbius weights.

Key new contraction: for prime p, τ(pu)-c(pu)-c(u)=F_p(u)(τ(u)-c(u)), where F=1 if p divides u and F=1-p^(-ε) otherwise. F∈[0,1] for ε≥0. Reuses `AllHorizonRadicalSawtoothAndDefectReduction.pmPowerDampedDivisorCoeff_add_abs_weight_le_one`; do not duplicate this mass bound. The old requested prime-or-envelope condition is unnecessary.

Correction: the unsplit identity s_N(μ,k)=-μ(k) is FALSE below the horizon. For odd endpoints through 3N or six-coprime endpoints through 4N, the exact value is zero at 2≤k≤N, and -μ(k) at k>N. For every prime p>3 and N≥p, p is six-coprime, s_N(μ,p)=0, -μ(p)=1. This symbolic counterfamily and the piecewise positive survivor are formalized; full defect nonpositivity survives. No numerical experiments used.

Third-band endpoints divisible by both 2 and 3 remain outside the proved envelope. A simultaneous two-prime deletion identity is an open follow-up; do not claim the whole third band.

Verification: original source compiled via `lake --old env lean -o ... -i ...` exit 0, empty diagnostics. All 28 declarations passed scratch #print axioms using only propext/Classical.choice/Quot.sound. All 26 public declarations indexed uniquely, both private helpers searchable. Source and artifact hashes verified. Scratch files removed, all owned handles terminal. Global lint --check-generated is NOT clean: eight unrelated unreachable leaves, existing TransHorizon field-umbrella registration, stale LEAN_OVERVIEW amid concurrent edits. Exact errors in logs/thim-band-lint-final.txt. No target-leaf or prohibited-declaration lint error. No full build, added axioms, heartbeats, README edits, commits, or push. External novelty not asserted.

Scratch axiom audit detail: private Lean names contain a numeric Name component; textual `.0.` cannot be parsed as an identifier. Construct the exact Name with Lean.Name.num / Lean.Name.str, use Lean.mkIdent, and invoke generated #print axioms through Lean.Elab.Command.elabCommand. This successfully audited both private helpers.
