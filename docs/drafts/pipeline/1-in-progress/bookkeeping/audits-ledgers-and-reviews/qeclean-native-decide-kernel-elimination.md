# Kernel-only elimination of QECLean native decision axioms

- **ID:** qeclean-native-decide-kernel-elimination
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `formal/GaloisForLFunctions/QECLean/PROVENANCE.md` trust audit
- **Statement:** Every QECLean declaration imported by `GaloisForLFunctions.QECLean` can be proved with no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

## Goal

Remove all `Lean.ofReduceBool` dependencies introduced by `native_decide` without weakening a
statement or hiding a tainted module from the umbrella.  Completion is measured by
`scripts/lean/audit_extra_axioms.lean`, not by the line-based lint gate.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete proof plan for every finite certificate family, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: all 59 modules kernel-only, `lake build GaloisForLFunctions.QECLean` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone trust-migration note with certificate architecture and Lean audit

## Approach

1. Inventory every executable `native_decide` occurrence separately from documentation mentions and
   group by the finite predicate being certified.
2. Replace small leaves by kernel `decide`, with declaration-scoped recursion/heartbeat budgets.
3. For large Cartesian searches, replace brute-force decision with explicit structural certificates:
   decomposition tables, spanning/boundary witnesses, or a proof-producing reflection theorem whose
   checker is kernel-reduced.
4. Build each affected module once after a batched conversion, then run the QEC umbrella build and
   complete axiom audit.

Initial feasibility evidence:

- two concatenation-independence leaves in `SteaneFourQubit.lean` pass with kernel `decide` after
  raising `maxRecDepth`;
- the `bb_90` weight-four base-floor leaf does not fail but exceeds twenty minutes under direct
  kernel reduction and must be treated as a structural-certificate target;
- `bv_decide` is not a drop-in route because preprocessing cannot reify the custom group-algebra
  predicates.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `bv_decide` preprocessing reports that no hypothesis lies in
  its supported `BitVec` fragment for the `bb_90` obligations.
- **Strongest positive survivor:** kernel `decide` proves the small QEC leaves; large leaves isolate
  exactly where compressed structural certificates are required.
- **New insight:** trust migration is not one global tactic substitution.  It is a two-tier proof
  architecture: kernel reduction for small finite predicates, theorem-level certificates for large
  searches.
- **Status:** internal audit complete; small tier Lean-tested; large tier open and explicitly named.

## Log

- 2026-08-05 — created in stage 1 after fresh corpus axiom audit and representative conversion tests.
