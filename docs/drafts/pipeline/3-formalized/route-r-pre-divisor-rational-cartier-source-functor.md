# Route R pre-divisor rational Cartier source functor

- **ID:** `route-r-pre-divisor-rational-cartier-source-functor`
- **Stage:** 3 — formalized in Lean 4
- **Source card:**
  `../1-in-progress/route-r-rational-cartier-prime-dilation-landing.md`
- **Module:**
  `GaloisForLFunctions.RHTower.RouteRPreDivisorRationalCartierSourceFunctor`
- **Status:** `[UNCONDITIONAL SOURCE CONSTRUCTION] [EXACT DEFECT COMPARISON] [NOT RH]`

## Formalized theorem

For independent jet grade `k`, spectral parameter `w`, and literal degree-one rational-adelic
cyclic source chain `x`, Lean defines

```text
h(k,w,x) = iteratedDeriv k XiC w * epsilon0DegreeOne(x)
```

as a linear map in `x`, and constructs the constant polynomial presentation

```text
A(z) = h(k,w,x),  B(z) = 1,  H(z) = A(z)/B(z).
```

This source presentation is coefficient-faithful, invariant under genuine cyclic rotation, and
fixed by every geometric dilation. At the ordinary-prime atom and first nonzero Xi jet, its value
is exactly the nonzero multiplicity-leading coefficient `c_rho` in both Gamma orientations.

Its failure to intertwine physical prime dilation is formalized as

```text
sourceCartierPhysicalDilationDefect p rho
  = (1 - deningerHalfDensityMateGain p rho) * c_rho.
```

The main comparison theorem proves the nondivisive identity

```text
sourceCartierPhysicalDilationDefect p rho
  = - cofinalCentralBocksteinReadout p rho m.
```

Consequently, scalar defect vanishing, constant rational-function defect vanishing, explicit
cofinal source-null-homology, physical rational Cartier landing, critical-line placement, and
Route-R Hodge-mate coefficient vanishing are equivalent.

## Main declarations

- `ccmRationalAdelicPreDivisorCartierCoefficient`
- `ccmRationalAdelicPreDivisorCartierCoefficient_rotate`
- `ccmRationalAdelicPreDivisorRationalCartierPresentation`
- `ccmRationalAdelicPreDivisorRationalCartierPresentation_primeAtom_ne_zero`
- `ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi_reflection`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect_eq`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_neg_cofinalReadout`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_sourceNull`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_landing`
- `ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_hodgeMateCoefficient`

## Exact remaining frontier

Source rational presentation now exists unconditionally. It has source dilation gain one.
Identifying it with physical gain is not automatic: exact mismatch is retained cofinal central
Bockstein class. No theorem in this module asserts that class vanishes. Remaining scientific
theorem is singular pre-divisor Cartier/Stokes annihilation preserving period-one generator; its
universal form is RH-equivalent.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/RouteRPreDivisorRationalCartierSourceFunctor.lean`:
  pass.
- `lake build GaloisForLFunctions.RHTower.RouteRPreDivisorRationalCartierSourceFunctor`: pass.
- `scripts/formal_tools.py lint`: pass.
- Axiom audit of construction, non-erasure, reflection, Bockstein comparison, null-homology
  equivalence, and landing equivalence: only `propext`, `Classical.choice`, `Quot.sound`.
- Module imported by `GaloisForLFunctions/RHTower.lean` umbrella.
