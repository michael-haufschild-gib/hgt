# Ultrametric thermal Mahler constraint

- **ID:** `ultrametric-thermal-mahler-constraint`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PHYSICAL-SPECTRAL ALGEBRAIC CORE
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [PARENT-DERIVED]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/UltrametricThermalMahler.lean`
- **Paper theorem:** `../../2-fully-proven/not_new_scientific_knowledge/ultrametric-thermal-mahler-hypertranscendence.md`
- **Statement:** The formal reduced heat trace of the exact ultrametric shell spectrum is the
  unique solution of a finite-boundary-defect Mahler constraint.

## Exact theorem surface

For every integer `p >= 2`, Lean constructs the weighted shell series

```text
Theta_p(X) = sum_(k>=0) p^k X^(p^k)
```

and proves

```text
Theta_p(X) = X + p Theta_p(X^p).                          (1)
```

It then constructs

```text
K_p(X) = (-1/p) X + ((p-1)^2/p) Theta_p(X),               (2)
```

whose coefficients are `p-2` at `X`, `(p-1)^2 p^(k-1)` at `X^(p^k)` for `k>=1`, and zero away
from the geometric shell tower.  Coefficientwise algebra proves the exact affine constraint

```text
K_p(X) = (p-2) X + X^p + p K_p(X^p).                     (3)
```

If a formal series `Y` satisfies the homogeneous difference equation

```text
Y(X) = p Y(X^p),                                          (4)
```

then its constant coefficient vanishes because `p != 1`; every positive coefficient either
vanishes immediately or descends to a smaller index.  Lean therefore proves `Y=0`.  Equations
`(1)` and `(3)` each have a unique formal solution, without a separately supplied initial datum.

## Exact boundary

The coefficient spectrum is identified with the Neumann-to-Dirichlet spectrum on the `p`-adic
unit circle in the paper card, not inside Lean.  The Lean module does not claim convergence,
operator positivity, reflection positivity, a Lorentzian theory, or the external
rational-or-hypertranscendental Mahler theorem.

The mathematics formalized here is an exact parent-derived bridge.  It is not labelled new
scientific knowledge.  Its scientific use is to replace a chosen geometric tower by a
source-derived quantum spectrum and to isolate interaction-preserving scale rigidity as the open
physical core.

Finite prefixes and the exact identity equating their same-resolution constraint defect with the
next omitted shell are formalized separately in
`ultrametric-thermal-finite-resolution-residual.md`.

## Lean surface

- `branchingThermalSignal`
- `branchingThermalCoefficient_recursion`
- `branchingThermalSignal_constraint`
- `branchingThermalInvariant_eq_zero`
- `branchingThermalSignal_unique`
- `ultrametricThermalSignal`
- `ultrametricThermalCoefficient_recursion`
- `ultrametricThermalSignal_constraint`
- `ultrametricThermalSignal_unique`

## Verification

- [x] direct touched-file Lean check passed
- [x] exact cached module build passed in one foreground process
- [x] axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation used
- [x] imported by the HTGeometry umbrella
