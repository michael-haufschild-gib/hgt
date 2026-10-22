# Deninger Gamma tensor-square mate identification

- **ID:** `deninger-gamma-tensor-square-mate-identification`
- **Status:** formalized in Lean 4; unconditional; Route L remains open
- **Paper proof:**
  `new_scientific_knowledge/deninger/deninger-gamma-tensor-square-mate-identification.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittGammaTensorSquareMateIdentification`

## Formal result

For the Deninger half-density character

```text
lambda_n(s) = n^(1/2-s),
```

the module defines tensor-square radial source-inverse/analytic-dagger mate
curvature

```text
K_n(s) = norm(lambda_n(s))^(-2) - norm(lambda_n(s))^2
```

and proves unconditionally

```text
K_n(s) = 2 sinh((2 Re(s)-1) log n).
```

For every `n >= 2`, its zero set is exactly `Re(s)=1/2`.  At the actual
ordered `(2,3)` Gamma/co-Poisson Calderon--Witt witness, the two depth-zero
modular rates sum to `-log 6`.  With

```text
c_23 = -A_23/2 > 0,
```

the actual boundary coefficient satisfies the exact comparison

```text
b_Gamma(q) = c_23 * K_6(rho_q).
```

The comparison preserves the critical zero set.

## Novelty boundary

Neither half-density norm formula, scalar hyperbolic-sine curvature, nor
Gamma reflection-odd formula is claimed new.  New content is equality of the
independently constructed actual Gamma reporter and Deninger tensor-square
mate curvature, including forced composite degree `6`, sign, and strictly
positive calibration.

This closes radial associated-grade part of
`FINITE_EPG_FAILURE_NERVE_MATE_COMPARISON`.  It does not construct filtered
prime/depth source mate or strict cofinal Xi Cartier landing.

## Verification

- symbolic scratch proof using repository toolchain: passed;
- direct `lake env lean` on module: passed;
- targeted module build: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- umbrella import: `GaloisForLFunctions.RHTower`.
