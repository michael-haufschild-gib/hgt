# A measurable fundamental domain for the cubic kernel

- **ID:** cubic-kernel-measurable-fundamental-domain
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The level-three Eisenstein group acts freely on hyperbolic three-space; every subgroup has an explicit measurable fundamental selector, including the actual cubic kernel.

For a level-three matrix, `tr(M)−2` is divisible by nine. If it fixes a
hyperbolic point, a conjugate is unitary, giving `|tr(M)−2|≤4`. Every nonzero
Eisenstein integer has modulus at least one, so `tr(M)=2`. A unitary
matrix with trace two is the identity. Thus the action is free.

Integral orbit sublevels of the Frobenius norm are finite. Order points
lexicographically by Frobenius norm and the eight real Gram-matrix entries.
The Gram matrix determines the point. Each orbit has a unique minimum, and
the minimum predicate is measurable because the group is countable and all
key coordinates are continuous. Freeness yields a fundamental domain for
every Borel measure; no invariance or volume estimate is assumed.

Source: external OpenAI `Eisenstein/FundamentalDomain.lean` and
`QuadraticSieve/GlobalBinLoss.lean`. Lean: `TheCubicKernelHasAMeasurableFundamentalDomain.lean`, namespace
`CubicEisenstein`: `levelThree_action_free`, `integral_frobenius_sublevel_finite`,
`hyperbolicFundamentalSet_measurable`, `hyperbolicFundamentalSet_unique`,
`globalKubotaKernel_isFundamentalDomain`. Direct source audit passed; all five
transitive axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.
Invariant hyperbolic volume and finite quotient mass remain separate obligations.
