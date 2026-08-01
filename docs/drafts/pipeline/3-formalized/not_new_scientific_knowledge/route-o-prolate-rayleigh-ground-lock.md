# Route O prolate Rayleigh--ground lock

- **ID:** `route-o-prolate-rayleigh-ground-lock`
- **Stage:** 3-formalized
- **Type:** THEOREM / DETERMINANT-SUBMECHANISM CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]
  [NOT AN RH PROOF]`
- **Route:** O — Connes/CCM restricted-Weil and prolate limit
- **Primary sources:** Connes--Consani--Moscovici, *Zeta Spectral Triples*
  (arXiv:2511.22755); Connes--van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the
  Spectral Action* (arXiv:2511.23257).

## Exact theorem

Let `epsilon_n` be a cofinal nested sequence of true restricted-Weil spectral floors and let
`r_n` be the Rayleigh energy of the normalized constrained-prolate seed at the same apertures.
Assume the literal source facts

```text
epsilon_(n+1) <= epsilon_n,
epsilon_n <= r_n,
r_n -> 0,
RH <-> forall n, 0 <= epsilon_n.                               (O1)
```

Write `Delta_n=r_n-epsilon_n`. Then

```text
RH <-> Delta_n -> 0.                                           (O2)
```

More sharply, if RH is false, there are `delta>0` and `n_0` such that

```text
Delta_n >= delta  for every n>=n_0.                            (O3)
```

The theorem is unconditional: `(O1)` is data in a universally quantified source-typed structure,
not an axiom or assumed RH. Instantiating its `r_n -> 0` field with the analytic constrained-prolate
source theorem is a separate formula-level obligation. Paper cards claim that source asymptotic,
but its concrete PSWF graph-domain realization is not yet dependency-closed in Lean and is not
silently imported here.

## Proof

Under RH, `0<=epsilon_n<=r_n`; hence

```text
0 <= Delta_n = r_n-epsilon_n <= r_n -> 0.
```

If RH is false, the cofinal Weil criterion gives one `n_0` with `epsilon_(n_0)<0`. Antitonicity
then gives `epsilon_n<=epsilon_(n_0)` for every `n>=n_0`. Since `r_n->0`, eventually
`r_n>epsilon_(n_0)/2`, so

```text
Delta_n >= -epsilon_(n_0)/2 > 0.
```

This proves `(O3)` and contradicts `Delta_n->0`, proving `(O2)`.

## Why this is source-specific

Proof uses three literal restricted-Weil facts:

1. aperture nesting makes the true floors antitone;
2. Rayleigh--Ritz puts the actual normalized prolate seed above the true floor;
3. nonnegativity of every cofinal restricted-Weil floor is Weil's RH criterion.

Arbitrary real-zero entire approximants have none of this variational structure. Constant
Xi-based approximants under RH cannot witness the source-typed structure.

## Hostile audit

| Attack | Result |
|---|---|
| Constant-Xi theatre | blocked by actual nested floors and Rayleigh--Ritz field |
| Pointwise/zero-set convergence loophole | absent; proof uses no zero convergence |
| Non-nested finite cutoffs | continuous/nested floor is explicit data; arbitrary Galerkin towers do not qualify |
| Unnormalized seed | excluded by the Rayleigh inequality field |
| Negative spectrum evacuation | impossible by antitonicity; one witness persists forever |
| Determinant estimate presented as easier | any estimate forcing `Delta_n->0` proves RH already |
| Hidden proof of seed asymptotic | rejected; `r_n->0` remains an explicit source field until concrete instantiation |

## Finite published CCM infrastructure closed during audit

`formal/GaloisForLFunctions/RHTower/CCMPublishedRestrictedWeilMatrix.lean` now defines, for physical
`a>0` (with a totalized algebraic extension), the literal one-sided functional

```text
Psi# = W_(0,2)# - W_R# - sum_p W_p#
```

with the exact finite archimedean endpoint correction. It proves:

- the sine test equals the existing published CCM source coefficient;
- diagonal entries are the exact tent--cosine Weil values;
- off-diagonal entries are the exact divided differences `(b_i-b_j)/(i-j)`;
- centered clock/source are odd and diagonal is even;
- real symmetry, reflection commutation, and rank-two clock displacement;
- unconditional radical-preserving boundary completion for every scalar shift;
- automatic selection of a finite spectral-floor shift;
- positive semidefiniteness and a nonzero radical at that shift;
- a source/response completion whose full characteristic polynomial has only real zeros.

This removes the finite simple-even hypothesis as a prerequisite for existence of a real-rooted
**source-or-response** completion. It does not identify that branch with the original CCM
eta-channel ground-vector determinant, and does not prove convergence of finite floors, ground
vectors, or determinants to Xi.

## Relation to prior work and novelty verdict

`ccm-rayleigh-transfer-collapses-to-spectral-floor.md` already proves that the stronger normalized
Rayleigh-excess/gap estimate collapses to the cofinal floor criterion. The present theorem records
the sharp unnormalized equivalence and persistent false-RH gap and formalizes it. This is an
elementary consequence of prior variational facts, so it is route infrastructure, not new
scientific knowledge.

`constrained-prolate-continuous-polar-charge-law.md` gives the paper candidate for `r_n->0`, while
`constrained-prolate-exterior-weil-leading-law.md` records the formula-level graph-domain debt.
Neither supplies the true-floor comparison. Once seed energy tends to zero, that comparison is
exactly `(O2)` and therefore exactly RH.

## Lean realization

`formal/GaloisForLFunctions/RHTower/CCMProlateRayleighGroundLock.lean` defines
`CCMProlateRayleighGroundData` and proves, without project axioms:

```text
CCMProlateRayleighGroundData.rayleighExcess_nonneg
CCMProlateRayleighGroundData.rayleighExcess_tendsto_zero_of_riemannHypothesis
CCMProlateRayleighGroundData.eventually_rayleighExcess_ge_of_not_riemannHypothesis
CCMProlateRayleighGroundData.riemannHypothesis_iff_rayleighExcess_tendsto_zero
```

## Scope verdict

This theorem retires only the claim that determinant transfer is an independent last mile after a
prolate-to-ground comparison. It does **not** terminalize Route O or Connes's program as a whole.
Finite arithmetic matrix, completion, and real-zero algebra are closed; at least three source
problems remain live:

```text
prove the literal constrained-prolate seed lies in the required graph domain and r_n -> 0;
prove the original simple-even eta-channel branch is the selected ground branch;
prove epsilon_n -> 0 on one literal cofinal restricted-Weil family.       (O4)
```

Any prolate ground comparison strong enough to justify determinant convergence already proves
`(O4)` and RH before determinants are used. This is a cost classification, not a no-go theorem:
Connes's source geometry could still prove that comparison or prove `(O4)` directly. A new
approximant normalization, determinant wrapper, or ground-state name alone supplies no progress.

## Gates

- [x] internal corpus audit
- [x] primary external collision audit
- [x] exact theorem frozen
- [x] hostile paper-proof audit
- [x] unconditional Lean formalization
- [x] literal finite published matrix formalized
- [x] finite ground shift and real-rooted completion closed
- [x] novelty downgraded to not-new route infrastructure
- [x] determinant-after-comparison submechanism classified
- [ ] Route O whole-program closure
