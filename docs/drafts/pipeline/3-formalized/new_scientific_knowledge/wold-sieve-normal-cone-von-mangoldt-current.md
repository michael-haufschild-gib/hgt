# Wold-sieve normal cone / von Mangoldt current — formalization certificate

- **ID:** `wold-sieve-normal-cone-von-mangoldt-current`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/wold-sieve-normal-cone-von-mangoldt-current.md`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH]`

## Formalized theorem

The first common-normal derivative of the finite Wold prime-incidence sieve converges
coefficientwise to the von Mangoldt current.  At coordinate `n`, every normal jet below
`n.primeFactors.card` vanishes and the first nonzero jet equals that factorial times the product
of the incident prime logarithms.  Reciprocal weighting gives literal diagonal operators on
`ℓ²(ℕ)` which converge in Hilbert--Schmidt norm exactly above `σ = 1/2`; the limit is compact, the
wall is sharp, and its absolutely convergent trace is `-ζ'/ζ`.

## Source modules and capstones

```text
formal/GaloisForLFunctions/RHTower/WoldSieveNormalConeVonMangoldt.lean
formal/GaloisForLFunctions/RHTower/WoldSieveNormalConeVonMangoldtCompletion.lean

hasDerivAt_woldIncidenceNormalFactor
iteratedDeriv_woldIncidenceNormalFactor_zero_of_lt_omega
iteratedDeriv_woldIncidenceNormalFactor_omega
tendsto_woldFiniteNormalCoefficient_atTop
tendsto_hsNorm_woldFiniteWeightedOperator_sub_atTop
isHS_woldVonMangoldtWeightedKernel_iff
not_isHS_woldVonMangoldtCriticalKernel
opTrace_woldJetTraceOperator_eq_zeta_logDeriv
```

## Verification and boundary

Both modules are registered in the `RHTower` umbrella.  Direct `lake env lean` verification and
targeted `lake build GaloisForLFunctions.RHTower.WoldSieveNormalConeVonMangoldtCompletion` pass.
Scratch `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.

This certificate covers the dependency-closed source theorem, equations `(1)`--`(16)` in the
paper card.  It does not claim the explicitly open critical Gamma/co-Poisson weld, bilateral
temperedness of the completed Xi conormal, or RH.
