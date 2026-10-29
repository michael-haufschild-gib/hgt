# The dual averaged Mellin transform is the inverse class series

- **ID:** hecke-dual-averaged-mellin-is-the-inverse-class-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](../1-in-progress/hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** For a finite-primitive Hecke character, the actual dual unit average has an absolutely convergent Mellin transform throughout `Re(s)>1`. It equals the inverse-character ideal-class series with the exact Gauss, fractional-norm, torsion, and Gamma/Jacobian factors, and agrees with the symmetric actual theta continuation.

## Proof

The proved joint density for each actual dual class generator is
absolutely integrable on `Re(s)>0`. Its exact norm mass separates into
the inverse ideal-term norm times a common archimedean factor. Absolute
ideal-series convergence makes these masses summable on `Re(s)>1`.

Fubini gives integrability of every radial class density. The integral
triangle inequality bounds its absolute mass by the joint absolute
mass, so the radial masses remain summable. This justifies the infinite
Mellin exchange after the exact logarithmic substitution `t=exp(2q)`.

The proved fixed-parameter unit unfolding identifies this sum with the
actual dual average minus its regulator-scaled zero mode. Integrating
the exact individual Gamma formula gives

```
Mellin(dualAverage - regulator*dualZeroMode)(MArgψ(s))
  = torsionOrder * inverseCharacterClassSeries(s)
      * Cψ ψ(b) Norm(dual(mb))^(-s)
      * Γψ(s)/(degree * 2^unitRank).
```

For zero parity, `Re(s)>1` implies the symmetric weak-pair Mellin
inequality. For nonzero parity, both actual zero modes vanish, so the
symmetric pair is strong and supplies its Mellin identity at every
argument. This proves equality with the symmetric continuation on the
entire half-plane `Re(s)>1`. Inversion invariance identifies its Gamma
factor with the inverse character's Gamma factor.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeDualAveragedMellinIsTheInverseClassSeries`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualClassL`, `heckeDualClassRadialMellinKernel`
- `integrable_heckeDualClassRadialMellinKernel`
- `integral_norm_heckeDualClassRadialMellinKernel_le`
- `summable_integral_norm_heckeDualClassRadialMellinKernel`
- `integrable_tsum_heckeDualClassRadialMellinKernel`
- `heckeUnitAveragedDualTheta_logMellin_eq`
- `mellinConvergent_heckeUnitAveragedDualTheta_classSeries`
- `integral_heckeDualClassRadialMellinKernel`
- `mellin_heckeUnitAveragedDualTheta_eq_dualClassL`
- `heckeUnitThetaMellinPair_symm_eq_dualClassL`

Both main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeDualAveragedMellinIsTheInverseClassSeries.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
Finite dual class recombination, completed removable values, and the
normalized global functional equation remain separate obligations.
