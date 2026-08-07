# Burnol co-Poisson bilateral dilation source covariance — formalized

- **ID:** `burnol-copoisson-bilateral-dilation-source-covariance-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-copoisson-bilateral-dilation-source-covariance.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSourceDilation.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonQuotientDilationCollapse.lean
```

## Formal theorem chain

```text
1  dilateSeed, burnolCoPoissonRightSum_dilateSeed      seed dilation intertwines the sum
2  BurnolCoPoissonSource.dilate                        the dilated source at the shrunk aperture
3  evenDilation_mem_coPoissonSourceSpace               U_r C_a <= C_(a/r)                   (1)
4  evenInverseDilation_mem_coPoissonSourceSpace        U_r^* C_a <= C_(a/r)                 (1)
5  evenDilation_mem_coPoissonSourceOrthogonal          U_r y in C_a^perp                    (2)
6  evenInverseDilation_mem_coPoissonSourceOrthogonal   U_r^* y in C_a^perp                  (2)
7  burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal   E_a = P_a (3)
8  burnolCoPoissonQuotientProjection_bilateralDilation_eq_soninProjection         both sides
9  coPoissonQuotientForward_eq_soninProjection_of_mem_next    forward bonding map            (3)
10 coPoissonQuotientInverse_eq_soninProjection_of_mem_next    inverse bonding map            (3)
```

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolCoPoissonSourceDilation.lean          -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolCoPoissonQuotientDilationCollapse.lean -- clean
```

Both headline endpoints report `[propext, Classical.choice, Quot.sound]` under `#print axioms`
and use no divisor, zero, critical-line, completeness, growth, or dagger hypothesis.
Both modules are wired into `GaloisForLFunctions.RHTower`.
