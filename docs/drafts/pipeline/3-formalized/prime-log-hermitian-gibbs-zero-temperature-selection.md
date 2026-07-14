# Prime-log Hermitian Gibbs zero-temperature selection

- **ID:** prime-log-hermitian-gibbs-zero-temperature-selection
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` PHYSICS VALUE RELATION / LEAN / DIRECT CORPUS CORRECTION
- **Physics source:** unsymmetrized Gibbs/Lehmann transition weights, KMS detailed balance, and the low-temperature spectral limit
- **Lean consumers:** `PrimeLogKMSRealization`, `PrimeLogKMSHermitianCompletion`, and the universal prime-orientation limit

## Goal

Recover the existing one-sided prime-log carrier as the zero-temperature limit of honest Hermitian finite quantum systems.  The symmetric Wightman half-density forces a mirror-odd response, but the physical unsymmetrized Gibbs spectrum weights the reverse transition by its Boltzmann factor.  Formalize that distinction and connect it directly to the existing directed carrier.

## Physics value relation

For the vacuum/prime Hamiltonian with gap `omega_p = log p`, normalize a Hermitian amplitude so that its Gibbs transition intensity from the vacuum to the prime level is `w_p`.  Detailed balance then fixes the reverse intensity:

```text
I_beta(p,0) = w_p,
I_beta(0,p) = exp(-beta*omega_p) w_p.
```

Therefore the exact negative passive response is

```text
-R_(P,beta)^G(z)
  = sum_(p in P) w_p *
      ((omega_p-z)^(-1) - exp(-beta*omega_p)*(omega_p+z)^(-1)).
```

At `beta=0` this is the mirror-odd Hermitian Wightman carrier.  Since every `omega_p>0`, the reverse Boltzmann term tends to zero as `beta -> +infinity`, leaving the existing one-sided carrier `H_P(z)`.

## Attack and status

- `[SEARCH]` The Gibbs/Lehmann detailed-balance factor is standard equilibrium quantum statistical mechanics.
- `[BRIDGE]` The exact prime-log normalization and response identity are project-specific specializations with direct corpus utility.
- The result does not prove an RH sign.  It removes the apparent physical obstruction to the directed orientation selector by identifying it as a vacuum, rather than symmetric-half-density, limit.
- No numerical evidence is used.

## Gates

- [x] existing directed and Hermitian prime-log realizations audited
- [x] primary KMS/detailed-balance mechanism checked
- [x] exact finite response and zero-temperature limit derived on paper
- [x] Gibbs-normalized Hermitian amplitude and transition intensities formalized
- [x] exact finite thermal carrier identity formalized
- [x] zero-temperature convergence to the directed carrier formalized
- [x] universal prime-gauge and orientation consumers formalized
- [x] targeted build, axiom audit, formal lint, and index refresh
- [ ] RH

## Primary physics sources

- L. Accardi and K. Imafuku, *Dynamical detailed balance and local KMS condition for non-equilibrium states*, arXiv:quant-ph/0209088.
- S. R. Jain and P. Gaspard, *Dynamical response and time correlation functions in random quantum systems*, arXiv:2408.09419.
- F. H. L. Essler and R. M. Konik, *Finite-temperature dynamical correlations in massive integrable quantum field theories*, arXiv:0907.0779.

## Formalized result

`PrimeLogGibbsZeroTemperature.lean` proves the exact forward and reverse Gibbs transition values, the thermal carrier response identity, the infinite-temperature midpoint at `beta=0`, the zero-temperature convergence to every existing finite directed carrier, and the universal-gauge specialization.  It packages the iterated cold/thermodynamic limit as `UniversalPrimeOrientationHermitianGibbsColdLimit` and proves that this property selects exactly the all-positive prime orientation.  The existing canonical constraint-orientation limit consumes the same theorem directly.

## Open core

The physics obstruction to the directed carrier is discharged: it is a vacuum-limit Hermitian Gibbs response, although it is not a symmetric half-density response at finite temperature.  This does not determine the arithmetic orientation by itself; the next useful physics relation must constrain the order of the cold and thermodynamic limits, or couple the resulting vacuum susceptibility to a named prime--archimedean/RH sign consumer.
