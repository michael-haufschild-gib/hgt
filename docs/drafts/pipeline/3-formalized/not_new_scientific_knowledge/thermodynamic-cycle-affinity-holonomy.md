# Thermodynamic cycle affinity as scalar clock holonomy

- **ID:** `thermodynamic-cycle-affinity-holonomy`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, chemical/gauge cycle value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ThermodynamicCycleAffinity`

## Additive/multiplicative value law

For a positive directed rate field, define the walk affinity by summing the local logarithmic
affinities in walk order:

```text
A(p) = sum_(u -> v in p) log(rate(u,v) / rate(v,u)).
```

The existing clock transport multiplies the same rate ratios.  The new exact identity is

```text
exp(A(p)) = clockWalkTransport(rateRatioCalibration, p),
A(p) = log(clockWalkTransport(rateRatioCalibration, p)).       (1)
```

Walk affinity is additive under concatenation.  Equation `(1)` converts the existing
group-valued holonomy interface into a scalar observable without losing information:

```text
A(p) = 0  iff  clockWalkTransport(..., p) = 1.                 (2)
```

## Scalar Wegscheider criterion

On a connected observable graph, the positive rate-ratio calibration comes from one global
detailed-balance potential exactly when every closed-walk affinity vanishes.  This is the scalar
Kolmogorov/Wegscheider form of the existing clock exactness/flatness theorem.

Unlike an abstract nonunit holonomy, `A(p)` is a real value that can be estimated, bounded,
summed, and compared directly with response or entropy quantities.

## Positive residue after the no-go

A nonzero cycle affinity discharges the hypotheses of the existing thermodynamic-holonomy and
Fisher-coercivity theorems.  Therefore it exposes an observed edge with

```text
entropyProductionValue > 0,
pseudoEntropyProductionValue > 0.                              (3)
```

Thus failure of global detailed balance produces both a logarithmic entropy witness and a
rational quadratic-current/Fisher witness.  Equation `(3)` is the significant positive statement
paired with the obstruction.

## Gibbs/KMS specialization

For the finite Gibbs population calibration,

```text
A(p : a -> b) = -beta * (energy(a) - energy(b)).                (4)
```

Every closed Gibbs population walk therefore has zero cycle affinity.  This cleanly separates
equilibrium endpoint calibration from genuinely nonequilibrium cycle holonomy, while using no
temporal-evolution premise.

## Physics and chemistry provenance

- T. Schmiedl and U. Seifert, *Stochastic thermodynamics of chemical reaction networks*,
  arXiv:cond-mat/0605080.
- M. Polettini and M. Esposito, *Irreversible thermodynamics of open chemical networks I*,
  arXiv:1404.1181.
- M. Polettini, G. Falasco, and M. Esposito, *Tight uncertainty relations for cycle currents*,
  arXiv:2106.00425.

The same formal law applies to biochemical and genetic reaction networks, stochastic transport,
electromagnetic or gauge calibration loops with positive abelian readout, and finite KMS
transition graphs.

## Lean surface

- `thermodynamicWalkAffinity`
- `thermodynamicWalkAffinity_append`
- `exp_thermodynamicWalkAffinity_eq_clockWalkTransport_val`
- `thermodynamicWalkAffinity_eq_log_clockWalkTransport`
- `thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one`
- `rateRatioCalibration_exact_iff_closedWalkAffinity_zero`
- `thermodynamicWalkAffinity_vertexPopulation`
- `thermodynamicWalkAffinity_finiteGibbsStateWeight`
- `thermodynamicWalkAffinity_finiteGibbsStateWeight_closed`
- `exists_adjacent_entropyProductionValue_pos_of_walkAffinity_ne_zero`
- `exists_adjacent_pseudoEntropyProductionValue_pos_of_walkAffinity_ne_zero`

## RH impact and boundary

The scalar affinity interface can replace a group-valued holonomy hypothesis in any
prime-incidence or KMS response construction and immediately supplies a positive quadratic
current edge.  It is therefore easier to couple to real inequalities and limiting response
values than the original unit-valued proposition.

It does not construct a nonzero prime--archimedean cycle affinity or identify the normalized
prime--Gamma source with a cycle response.  Those remain producer steps, so this theorem does not
prove RH.

## Verification

- [x] exact module target built and cached
- [x] touched Lean file checks directly
- [x] selected capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`
- [x] no full or concurrent build used
- [x] no numerical computation used
