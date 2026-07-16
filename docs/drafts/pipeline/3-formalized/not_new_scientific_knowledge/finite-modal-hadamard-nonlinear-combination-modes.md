# Finite modal Hadamard algebra and nonlinear combination modes

- **ID:** `finite-modal-hadamard-nonlinear-combination-modes`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, nonlinear observation closure and resonance criterion
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FiniteModalHadamardAlgebra`

## Statement

For two finite modal observations

```text
x_n = sum_(i<d) a_i z_i^n,
y_n = sum_(j<e) b_j q_j^n,
```

their pointwise product is

```text
x_n y_n = sum_(i<d,j<e) (a_i b_j) (z_i q_j)^n.           (1)
```

Hence the width-bounded modal class is closed under pointwise multiplication:

```text
width(x) <= d and width(y) <= e
  implies width(x*y) <= d*e.                             (2)
```

Its first oversized Hankel determinant therefore vanishes:

```text
det H_(d*e+1)(x*y) = 0.                                 (3)
```

If every input amplitude is nonzero, then the maximal product determinant is nonzero exactly
when the pairwise combination-node map is injective:

```text
det H_(d*e)(x*y) != 0
  iff (i,j) |-> z_i q_j is injective.                    (4)
```

Under `(4)`, the product has exact noiseless Hankel mode count `d*e`.

## Positive statement after the resonance no-go

Node collision is not merely a reason the naive `d*e` count can fail.  Equation `(4)` identifies
the complete positive criterion: absence of multiplicative resonances is sufficient and necessary
for all quadratic combination modes to remain separately observable.  This converts a mode-count
no-go into an exact observability theorem.

## Physics connection

For sampled complex exponentials, `z_i=exp(w_i)` and `q_j=exp(v_j)`, so product nodes are
`exp(w_i+v_j)`.  Equation `(1)` is therefore the value-level skeleton of summed complex frequencies
in second-order response.  Black-hole perturbation theory predicts and observes quadratic
quasinormal modes; the full-rank condition is precisely that the sampled summed frequencies do not
alias.  The same law applies to nonlinear gravitational-wave readout, neutron-star mode coupling,
nonlinear optics, and weakly anharmonic quantum circuits.

Primary sources motivating the nonlinear observation interface:

- H. Nakano and K. Ioka, *Second Order Quasi-Normal Mode of the Schwarzschild Black Hole*,
  arXiv:0708.0450.
- H. Zhu et al., *Nonlinear Effects In Black Hole Ringdown From Scattering Experiments I: spin and
  initial data dependence of quadratic mode coupling*, arXiv:2401.00805.
- S. Yi et al., *Nonlinear quasinormal mode detectability with next-generation gravitational wave
  detectors*, arXiv:2403.09767.

## General HTGeometry significance

The theorem enlarges the finite modal surface from a representation class to a nonlinear
observation algebra.  It does not treat the label as time: the same product law holds for repeated
clock reports, spatial samples, detector bins, or arithmetic moments.  Thus polynomial sensors do
not create arbitrary finite complexity; their new observable nodes are constrained multiplicative
combinations of the original node palette.

## Lean surface

- `finiteModalProductWeight`
- `finiteModalProductNode`
- `finiteModalSequence_mul`
- `FiniteModalWidthAtMost.mul`
- `det_algebraicHankelMatrix_mul_eq_zero_of_finiteModalWidthAtMost`
- `det_algebraicHankelMatrix_finiteModalSequence_mul_ne_zero_iff`
- `finiteModalSequence_mul_exact_hankel_mode_count`

## RH impact and boundary

This result strengthens the modal obstruction used by completed prime--Gamma moment models:
finite nonlinear products remain in an explicitly bounded modal class.  Therefore replacing a
linear finite-mode explanation by a finite quadratic mixing explanation does not escape the Hankel
boundary; it only raises the bound from `d,e` to `d*e` and makes resonances visible as node
collisions.

It does not produce a nonzero completed-source Hankel determinant and therefore is not an RH source
producer.  Its value is to close a model-class escape route and supply an exact positive
nonresonance certificate for any future source determinant.

## Verification

- [x] exact module target builds and is cached
- [x] touched file checks directly
- [x] no numerical computation used
