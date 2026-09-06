# Arithmetic unit-phase factorization: exact classification and scoped no-go

- **Stage:** 3-formalized
- **Modules:** `ArithmeticUnitPhaseRigidity`, `ArithmeticUnitPhaseNoGo`
- **Namespace:** `RHTower.DeletionMixedRefinement`
- **Type:** unconditional classification and refutation of two frozen proposals; not RH

For the literal normalized remainder, `g_s(1)=conj(G(s))`, where

`G(s)=-1/[2*s*(1-s)]-zeta(s)/[s*(s+1)]`.

The proposed identity is `Im(g_s(1))=Im(zeta(s)*H(s))` throughout an open strip domain. The source identity and all analytic hypotheses are linked to the existing arithmetic remainder. No chosen substitute source is used.

## Closed results

1. **Connected-domain classification.** For holomorphic H on a connected open strip domain, the identity holds iff `G+zeta*H=c` for one real c. This follows from open mapping applied to the actual source sum.
2. **Exact rational fibres.** For `B(s)=-1/[2*s*(1-s)]`, `B(s)=B(t)` iff `s=t` or `s+t=1`. Hence a chart contains at most one positive-height zero.
3. **Zero-free solutions.** Each real c gives the analytic multiplier `(c-G)/zeta`; on connected open zero-free domains these exhaust all solutions.
4. **Tangent identity.** At any zero rho admitting a phase germ,

   `zeta'(rho)*(H(rho)-1/[rho*(rho+1)])=-(1-2*rho)/[2*(rho*(1-rho))^2]`.

5. **Exact local existence.** At a positive-height strip zero, a holomorphic phase germ exists iff `Re(rho)=1/2` and `zeta'(rho)!=0`. Necessity uses the real boundary and tangent identity. Sufficiency constructs the removable quotient from analytic divided differences, including its value at rho.
6. **Global and finite-cover no-go.** No such H exists on the whole strip. No finite family of connected open charts, even allowing empty charts, covers every positive-height strip zero. The proof uses the corpus's analytic Hardy theorem to produce a zero above the bounded heights of any finite chart cover.

The local existence theorem is a classification, not an assumption inserted into an RH proof. An all-zero construction of these germs would also prove simplicity. U1 and U2 are retired; EDQ itself and other head-orientation identities remain open.

## Verification

The combined scratch proof `/tmp/edq_unit_all.lean` passes. The published rigidity leaf passes `LEAN_NUM_THREADS=1 lake env lean` without warnings. The finite-cover leaf passes source checking; its strengthened empty-chart statement passes `/tmp/edq_unit_nogo_empty.lean` before identical publication. Serialized final audits `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticUnitPhaseRigidity` and `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticUnitPhaseNoGo` both pass, rebuilding only the respective leaf. The latter replays existing dependency diagnostics; neither new leaf emits a warning.

All 28 public declarations are audited by `/tmp/edq_unit_final_axioms.lean` against the built leaves. Each uses only `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or placeholder occurs. Output: `/tmp/edq_unit_axioms.log`.

The index refresh succeeds and research retrieves `unitPhaseGerm_iff_simple_critical_zero`. Global `python3 scripts/formal_tools.py lint --check-generated` fails on two pre-existing, unrelated missing umbrella imports: `RHTower.ThetaCuspModularCompactTube` and `HTGeometry.PolynomialODEJetRankThreeCompactExpansion`. Existing large-file warnings remain. Output: `/tmp/edq_unit_lint.log`; global lint is not claimed to pass. Scoped whitespace and documentation-link checks pass. All owned Lean processes completed.

Both leaves are wired into `RHTower.lean`; no full or umbrella build is used. No numerical zero evaluation or computational certificate occurs in the proof.

See [the frozen proposals, dependency-closed paper proof, and positive salvage](../5-failed/arithmetic-unit-phase-factorization.md), [current EDQ frontier](../1-in-progress/rh-current-frontier-map.md), and [remaining exceptional-head problem](../1-in-progress/edq-quartic-remainder-phase-cutoff.md).
