# Compact-source nodal mass coercivity and strict modulus contraction

- **ID:** compact-nodal-mass-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Quantify the exact modulus energy loss by the product of positive
  and negative weighted source masses, and classify when contraction is strict.

## Proven result

For the compact source ψ and actual state f(x)=c+primitive q(exp x), define

    P=∫ψ(x)² max(f(x),0)dx,    N=∫ψ(x)² max(−f(x),0)dx.

All quantities are constructed and finite. Proved

    4 P N ≤ sinh(2B) * nodalEnergy(compactMixture ψ weights,q,c).

Together with the actual modulus decomposition, this proves strict graph
energy decrease precisely when both signs occur at nonzero source points:

    J(modulusVelocity q c)=J(q)
      iff f≥0 on {ψ≠0} or f≤0 on {ψ≠0}.

Also proved the exact unweighted variance defect
`Vψ(f)−Vψ(|f|)=4PN`. Distinguish this loss classification from zero jump
energy: a nonconstant one-sign state may have positive jump energy but zero
modulus loss. No connected-support or nonzero-mass assumption is needed.

## Mechanism and audit boundary

The opposite-sign pair integrand is symmetric. Its full pair integral is 2PN,
so its positive-lag integral is PN. The actual nodalCost includes factor 4.
Compare the positive diffuse kernel on h≤2B with 1/sinh(2B); retain all
nonnegative atoms. Zero weighted lobe mass, continuity and full support
identify absence of that sign wherever ψ≠0. The zero-source case must remain
covered without division by total mass.

Focused corpus search `nodal positive negative source mass graph modulus coercivity`
found the current nodal upper bounds, compact admission and variance coercivity,
but no matching positive/negative mass floor or strict-contraction classification.
All 20 candidate-lemma and 20 source-argument entries were inspected. No execution
errors or partial results; semantic coverage is unavailable and the coverage
snapshot is older than the current index. Repeat focused source and parent-theory
audits before implementation; no exhaustive novelty claim. Classical positive
kernel and modulus-contraction ingredients are not externally new.

## Plan and proof gate

1. Prove the finite source-lobe moments, exact variance loss and its positive-lag integral.
2. Compare the nonnegative nodal integrand directly with the actual diffuse density.
3. Classify zero lobe mass and zero nodal energy; derive strict modulus contraction.
4. Audit both direct leaves, every public declaration's axioms, wiring, index and lint.

Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/CompactNodalMassCoercivity.md`.
Fresh query `nodal positive negative mass strict modulus contraction pair variance`
completed with no errors or partial stages. All 20 candidates and 20 source arguments
were inspected. Coverage snapshot is stale; semantic coverage unmeasured; background
indexer prevented synchronous refresh. No matching lower bound or classifier found.
Paper proved. `CompactSourceNodalVariance.lean` passed its final direct leaf check
without diagnostics (13 theorems, 4 definitions). `CompactNodalMassCoercivity.lean`
also passed its final direct leaf check without diagnostics (9 theorems).
All 26 public declarations passed axiom audit with only `propext`,
`Classical.choice`, `Quot.sound`; seven main signatures have no extra analytic
premises. Both imports and all 22 public theorem names are present in the
generated API. Global lint reports five unrelated concurrent unreachable modules,
listed in the fact ledger; neither new leaf has an error. All owned processes
are terminal. This is one connected contribution, certified package **7/100**.

Follow-on result: `rough-markov-clamp-domain.md`, now formalized as package 8.
