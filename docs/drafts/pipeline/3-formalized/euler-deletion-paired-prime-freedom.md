# Complete multiplicativity leaves exact finite observation freedom

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionPairedPrimeFreedom.lean`.
Namespace: `RHTower.DeletionPairedPrimes`.

`paired_observation` classifies every scalar observation on a pair of opposite large-prime
perturbations. With matched cofactor cutoff `M`, baseline coefficient sum `S`, and shorter
coefficient sum `T`, it proves

`sum f(n)F(w(n)) = F(1)*S + (F(1+t)+F(1-t)-2F(1))*T`.

The weight is the actual global function
`w(n)=(1+t)^v_p(n)*(1-t)^v_q(n)` for positive `n`, extended by zero at zero.
`weight_mul` proves complete multiplicativity for all natural arguments; `weight_pos`
proves strict positivity for positive inputs when `|t|<1`. Prime-square and product bounds
justify the three possible weights in the finite interval; divisor reindexing proves the
observation formula. It requires no regularity of `F`.

`paired_endpoints` and `paired_curvature` specialize this mechanism to literal deletion
coefficients. The premise-free capstone
`completely_multiplicative_closed_endpoints_opposite_curvatures` constructs two weights
through cutoff 930 with every divisor-of-thirty endpoint zero and exact curvature `-72`
and `3`. The prime pairs are `(59,61)` and `(251,257)`, both at `t=1/2`.

`lake env lean /tmp/hgt-paired-prime-fGCfQq/Audit.lean` passed. The general observation
law and unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`.
Earlier audits also checked multiplicativity, paired moments and curvature. The production
body matches the final scratch source. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionPairedPrimeFreedom` passed; its umbrella
import is wired. No umbrella or full build ran.

Repository-wide `scripts/formal_tools.py lint` was run and failed on concurrent work outside
this module. After the other file changed, the gate was rerun: its sole remaining error was
`HTGeometry/OneDimBrascampLieb.lean` being unreachable from its theorem-area umbrella.
No lint error named the new paired-prime module. Historical output:
`/tmp/hgt-paired-prime-fGCfQq/lint-final.log`. The subsequent compatible-curvature
audit passed repository-wide lint; output `/tmp/hgt-compatible-curvature-Pe4gsu/lint.log`.

The [paper proof](../2-fully-proven/euler-deletion-paired-prime-freedom.md) is independent
of the [exploratory Runpod calculation](../2-fully-proven/computations/deletion-multiplicativity-tangent/REPORT.md).
The latter guided the construction; no computed output enters a Lean proof.

This closes the finite
[failed sign gate](../5-failed/euler-deletion-complete-multiplicativity-gate.md), together with
its stronger positive survivor. It establishes no additional relation for the literal
infinite Mellin weights, no off-line zero exclusion, and no new RH architecture.
