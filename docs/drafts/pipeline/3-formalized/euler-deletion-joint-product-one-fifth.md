# Literal joint deletion product above one fifth

**Stage:** 3-formalized for actual moduli two and three. **RH implication:** none.
**Novelty:** not certified. General coprime moduli remain a separate obligation;
[fixed-target sharpness](euler-deletion-joint-product-sharpness.md) is now Lean-closed.

For `a_p(n)=1-p[p divides n]`, arbitrary `X,Y` in any complete complex normed unital
algebra, and every complex `s` with `Re(s)>1/5`, Lean proves that

`prod_{n=1}^N exp(n^(-s)*(a_2(n)X+a_3(n)Y))`

converges to a unit as `N` tends to infinity. No zero, commutation, or cancellation premise
is supplied. The theorem covers the actual weights and every partial prefix.

The proof combines the verified fifth-order remainder with summable Dirichlet-weight
variation. Local Lipschitz continuity of the finite block map makes the freezing error
summable. Reversed negated exponentials supply inverse blocks; both products converge and
their two-sided inverse identities pass to the limit. Exact source periodicity and six
residue limits complete the all-prefix argument.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointProductOneFifth.lean`.
Namespace: `RHTower.DeletionJointProduct`.
Capstone: `sourceProduct_converges_to_unit`.
Other audited results: `summable_weight_fifth`, `summable_actual_block_error`,
`variableBlock_inverse_pair`, `actual_blocks_converge_to_unit`, `sourceProduct_six_mul`.

`lake env lean /tmp/hgt-joint-polygon-17TZsg/ProductAudit.lean` passed. All six axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`. Production matches the
audited scratch body. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionJointProductOneFifth` passed.
The module is wired into its umbrella; no umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` passed. No numerical computation or external certificate was used.

Convergence on a region crossing the critical line is not a critical-line selector. The
[paper theorem](../2-fully-proven/euler-deletion-joint-product-one-fifth.md) also gives the now-formalized
fixed sharpness witness and a general coprime-modulus extension. Only the latter remains paper-only.
