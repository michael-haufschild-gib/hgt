# Prime Ising trees as a positive FK cluster expansion

- **ID:** `prime-ising-tree-fk-deletion-contraction`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [DIRECT CORPUS SIMPLIFICATION]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeIsingTreeCavity.lean`,
  `formal/GaloisForLFunctions/RHTower/IsingCavityRapidityAudioCascade.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordSynchronizedCluster.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeLeeYangPolydisk.lean`

## Claim

For a normalized ferromagnetic edge with disagreement weight `c in [0,1]`, its two spin factors
split exactly as

```text
(a + c b, c a + b)
  = c (a+b, a+b) + (1-c) (a,b).                 (1)
```

This is the local Fortuin--Kasteleyn deletion--contraction identity.  The `c` term cuts the edge
and contributes the full child partition independently of the parent spin.  The `1-c` term opens
the bond and forces the child root to equal the parent spin.  Iterating (1) on a tree expresses its
partition as a positive sum over bond subsets; each summand is a product of synchronized connected
cluster partitions.

After prime-field substitution, the synchronized components are precisely the existing
`synchronizedPrimeClusterPartition` basis.  Thus the arbitrary finite Ising-tree class is not a
new opaque approximant family: it is a source-positive mixture of already formalized prime-word
cluster functions.  At `c=0` only the fully synchronized term survives; at `c=1` only the fully
cut independent-spin term survives.

## Candidate competition

1. **Positive-real/scattering Cayley equivalence.** Rejected: its scalar content is already in
   `CayleySchur`, `PrimeCayleyHalfPlane`, and the passive-response modules.
2. **All-pass group-delay/Poisson positivity.** Rejected for now: the corpus already has the
   Poisson kernel and passive diagonal Pick signs, while no source-specific phase-orientation
   hypothesis is discharged by another generic boundary sign.
3. **Passive two-port Schur-complement energy.** Rejected as a standalone transfer: the dyadic
   passive-network route needs the sign of the actual prime--polar--critical-defect coupling.
   Generic Schur-complement passivity would only rename that open premise.
4. **FK deletion--contraction.** Selected: it directly rewrites the new arbitrary tree model into
   the existing synchronized-cluster basis and gives nonnegative source coordinates for the open
   inverse-ferromagnet problem.

## Formalization target

- prove (1) for arbitrary child conditional weights;
- prove the corresponding one-edge two-field partition identity
  `Z_c(u,v) = c(1+u)(1+v) + (1-c)(1+uv)`;
- specialize the endpoints to the existing independent and synchronized prime partitions;
- formalize recursive bond configurations for arbitrary rooted trees;
- prove the exact positive FK expansion and nonnegativity of every coefficient;
- expose a theorem usable by the active locally-uniform Ising route without adding a wrapper-only
  API.

## RH value and exact limit

The expansion does not prove the completed source comparison.  It strengthens Open Core A by
replacing an unconstrained finite tree search with a specific nonnegative cluster-basis
factorization.  A completed source packet outside that cone retires tree Ising realization; a
packet inside it provides explicit edge couplings and therefore inherits the already-proved
finite zero localization and locally-uniform RH capstone.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/PrimeIsingTreeFKExpansion.lean` proves:

- `isingEdgeFactors_eq_cut_add_synchronized` and
  `treePartition_singleEdge_fields_eq_fkMixture`;
- `treeBondCoefficient_nonneg` and `forestBondCoefficient_nonneg`;
- `sum_treeBondCoefficient_treeBondConfigurations`, so the bond weights form a probability
  vector rather than only a positive cone;
- `bondTreeConditionalWeights_eq_clusterData` and
  `bondTreePartition_eq_clusterProduct`, the exact connected-component factorization;
- `treeConditionalWeights_eq_sum_bondConfigurations` and
  `treePartition_eq_sum_bondConfigurations`, the arbitrary-tree FK identity; and
- `primeIsingTreePartition_singleEdge_eq_fkMixture`, which composes directly with the existing
  independent prime partition and synchronized prime-cluster partition for distinct labels.

The module is exported by `RHTower.lean`.  Its target build and the 10,096-job `RHTower` umbrella
build pass.  The axiom audit of the principal theorems reports only `propext`, `Classical.choice`,
and `Quot.sound`; the formal lint and `git diff --check` pass.

## Primary physics sources

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model. I. Introduction and relation
  to other models*, Physica 57 (1972), 536--564,
  <https://doi.org/10.1016/0031-8914(72)90045-6>.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin--Kasteleyn--Swendsen--Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988), 2009--2012,
  <https://doi.org/10.1103/PhysRevD.38.2009>.

## Gates

- [x] candidate has a direct consumer in the live Lean corpus
- [x] local deletion--contraction identity derived on paper
- [x] local identity formalized
- [x] arbitrary-tree FK expansion formalized
- [x] synchronized-cluster and independent-spin consumers composed
- [x] target build, axiom audit, lint, and diff check pass
