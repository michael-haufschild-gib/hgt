# Burnol first-wall Cartier residue and Gamma cancellation law — formalized

- **ID:** `burnol-first-wall-cartier-residue-cancellation-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-first-wall-cartier-residue-cancellation-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolDyadicCoboundaryContraction.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallResiduePolarization.lean
formal/GaloisForLFunctions/RHTower/BurnolGammaSteinCollarKernel.lean
formal/GaloisForLFunctions/RHTower/BurnolGammaSteinMoments.lean
formal/GaloisForLFunctions/RHTower/BurnolCollarKernelSeries.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallZeroDividedSource.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallSourceDecay.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallSourceMass.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallExteriorMass.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallCrossingCorrelation.lean
formal/GaloisForLFunctions/RHTower/BurnolReflectedRawSource.lean
formal/GaloisForLFunctions/RHTower/BurnolReflectedDividedShift.lean
formal/GaloisForLFunctions/RHTower/BurnolReflectedPotential.lean
formal/GaloisForLFunctions/RHTower/BurnolBocksteinLimit.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallCenteredPrimitive.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallTailMass.lean
formal/GaloisForLFunctions/RHTower/BurnolFirstWallCollarDepthDecay.lean
```

The last three are the modules built for the two auxiliary sharpenings `(12)` and `(31)`; the
declaration-to-equation map for everything else is the table inside the paper card.

## Formal theorem chain for `(12)`

```text
 1  burnolPrimitiveMean                                 m = ∫_0^1 P                          (14)
 2  abs_burnolPrimitiveMean_le_one                      |m| ≤ 1
 3  burnolCenteredPrimitive                             P_0 = P − m                          (14)
 4  burnolCenteredPrimitive_periodic                    one-periodic
 5  integral_burnolCenteredPrimitive_unit               mean zero over a cell
 6  abs_burnolCenteredPrimitive_le_two                  |P_0| ≤ 2
 7  hasDerivWithinAt_burnolCenteredPrimitive            right derivative p, everywhere
 8  burnolSecondPrimitive                               P_1 = ∫_0^t P_0
 9  burnolSecondPrimitive_periodic                      one-periodic
10  abs_burnolSecondPrimitive_le_two                    |P_1| ≤ 2
11  hasDerivAt_burnolSecondPrimitive                    C^1
12  integral_burnolFractPairKernel_centered_byParts     first by-parts, finite window
13  integral_burnolFractPairKernel_Ioi_centered         first by-parts, in the limit
14  integral_burnolCenteredPrimitiveKernel_byParts      second by-parts, finite window
15  integral_burnolCenteredPrimitiveKernel_Ioi_eq       second by-parts, in the limit
16  norm_integral_burnolCenteredPrimitiveKernel_Ioi_le  tail moment of P_0 is O(t^{-σ-2})
17  burnolZeroDividedSource_eq_centered                 the mean already cancelled            (15)
18  integral_burnolFractPairKernel_Ioi_eq_sub           tail = total moment − head
19  continuousOn_burnolZeroDividedSource_pos            continuity on (0,∞), divisor-free
20  integrableOn_burnolZeroDividedSource_Ioi            integrability past every cut
21  burnolTailMassConstant                              ‖ρ+1‖(1+‖ρ+2‖/(Re ρ+2)) + 4
22  norm_integral_burnolZeroDividedSource_Ioi_le        ∫_T^∞ g_ρ = O(T^{-2})                 (12)
```

`(12)` is proved for **every** `ρ` in the critical strip and every cut `T > 0`; the divisor
condition `ξ(ρ) = 0` is not used.  No Fubini step occurs: the divided shift is split into the
`ρ = 0` tail moment of `P_0` and a remainder that the second by-parts already makes `O(t^{-3})`,
and each piece is bounded by an explicit integrable majorant on `(T,∞)`.

## Formal theorem chain for `(31)`

```text
 1  abs_burnolCollarKernel_mul_mode_le_cubic  |κ_*(u) e^{-u/2}| ≤ 4000 e^{-3|u|}
 2  burnolCollarModeFive_le                   |κ_*(r)| e^{-5r/2} ≤ 4000 e^{-|r|}
 3  burnolIntegrable_collarModeFive           the 5/2-mode majorant is integrable
 4  burnolCollarModeFiveMass                  its total mass
 5  burnolCrossingCorrelation_residue_error   e^{s/2} W(s) − R = a · conj(∫_{e^s/2}^∞ g)      (21)
 6  BurnolQuadraticExteriorMass               the interface used from (12)
 7  norm_burnolDepthProfileError_le           ‖D_n(r)‖ ≤ K 4^{-n} e^{-5r/2}, all n and r
 8  burnolCollarDepthConstant                 the assembled constant
 9  norm_burnolCollarDepthReading_le          normalised reading is O(4^{-n})
10  burnolCollarDepthReading_eq               reading = 2^{n/2} · raw pairing integral
11  norm_burnolDepthPairing_le                Q_n = O(8^{-n}), abstract form                  (31)
12  xiDivisor_burnolQuadraticExteriorMass     (12) as an instance of the interface
13  xiDivisor_norm_burnolCollarDepthReading_le  the actual source, O(4^{-n})
14  xiDivisor_norm_burnolDepthPairing_le        the actual source, O(8^{-n})                  (31)
```

Step 7 is the point of the argument.  Subtracting the `A`-null limit profile `R e^{-r/2}`, whose
collar pairing vanishes by `(28)` (`integral_burnolCollarKernel_mul_mode`), turns the reading into a
pairing against the depth-profile error.  Where the shifted lag `nL + r` is positive, `(12)` bounds
that error by `4‖a‖C · 4^{-n} e^{-5r/2}`; where it is not, the constraint `r ≤ −nL` gives
`e^{2r} ≤ 4^{-n}` and converts the crude bound `O(e^{-r/2})` into the same majorant.  One integrable
majorant therefore covers the whole line and no region has to be treated by a separate limit.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolFirstWallCenteredPrimitive.lean   -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolFirstWallTailMass.lean            -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolFirstWallCollarDepthDecay.lean    -- clean
lake build GaloisForLFunctions.RHTower.BurnolFirstWallCollarDepthDecay            -- success
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
`norm_integral_burnolZeroDividedSource_Ioi_le`, `burnolZeroDividedSource_eq_centered`,
`norm_integral_burnolCenteredPrimitiveKernel_Ioi_le`, `abs_burnolCollarKernel_mul_mode_le_cubic`,
`norm_burnolCollarDepthReading_le`, `xiDivisor_norm_burnolCollarDepthReading_le`, and
`xiDivisor_norm_burnolDepthPairing_le`.
All three new modules are wired into `GaloisForLFunctions.RHTower`.

## What this certificate does not cover

The card's section 7 states `(34)`, the pre-completion singular orientation law
`Re(r_ρ − r_ρ^∨) ≤ 0`, as the remaining RH-bearing target.  It is explicitly not claimed as proved
on the card and carries no Lean obligation here.
