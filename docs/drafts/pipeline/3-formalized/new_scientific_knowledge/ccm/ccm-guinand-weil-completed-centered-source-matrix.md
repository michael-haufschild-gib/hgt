# CCM Guinand--Weil completed centered source matrix

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / whole mixed-order source dictionary
- **Novelty scope:** corpus-new channel-faithful reconstruction of every published centered matrix
  entry; published restricted-Weil matrix formula is external input
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilCompletedCenteredSourceMatrix.lean`

## Polar--prime diagonal action

For every continuous real test, Lean first proves the real interval expansion of the critical
Mellin Stieltjes pairing. Applying it to the transported diagonal test gives

```text
2 (L_pole+L_prime)(omega cos(2*pi*n*omega))
  = Re criticalMellinStieltjesPairing(a,F_(a,n)).               (1)
```

This closes the prime cutoff, affine reflection, factor-two, and weighted-cosine normalization on
the diagonal.

## Mixed-order completion

The Gamma diagonal is defined at its correct order by the restricted-Weil endpoint-subtracted
action, justified locally by the first-jet theorem. Adding it to `(1)` yields

```text
completedDiagonal(a,n)
  = ccmPublishedRestrictedWeilPairing(a,F_(a,n)).               (2)
```

Separately, the odd-source construction is extended from natural to all integer modes. Its
polar--prime part and endpoint-cancelled Gamma part satisfy

```text
completedOdd(a,n)
  = ccmPublishedSourceSineCoefficient(a,pi*n/a).                (3)
```

## Whole-matrix weld

Restrict `(2)` and `(3)` to centered modes `{-N,...,N}` and use them as diagonal and source data
of the divided-difference packet. Lean proves the matrix identity

```text
ccmGuinandWeilCompletedCenteredSourceMatrix(a,N)
  = ccmPublishedRestrictedWeilMatrix(a,N)                       (4)
```

for every `a>0` and every `N`. Equation `(4)` is entrywise whole-matrix equality while retaining
pole, prime, odd-Gamma, and diagonal-Gamma provenance before addition.

## CCM-FU consequence

Endpoint-renormalized weighted-cosine diagonal is no longer an open normalization problem. The
remaining route obstruction is dynamical: construct the global aperture/event connection of this
mixed-order source and identify its oriented incidence with the already-formal continued Xi Ward
column.

## Lean declarations

- `ccmCriticalMellinStieltjesPairing_real_re_interval`
- `ccmGuinandWeilPolarPrimeContinuousDiagonal_eq_critical`
- `ccmGuinandWeilArchimedeanDiagonalValue`
- `ccmGuinandWeilCompletedDiagonalValue_eq_restrictedWeil`
- `ccmGuinandWeilPolarPrimeIntegerOddSourceValue_eq_published`
- `ccmGuinandWeilArchimedeanIntegerOddSourceValue_eq_published`
- `ccmGuinandWeilCompletedIntegerOddSourceValue_eq_published`
- `ccmGuinandWeilCompletedCenteredSource_eq_published`
- `ccmGuinandWeilCompletedCenteredDiagonal_eq_published`
- `ccmGuinandWeilCompletedCenteredSourceMatrix_eq_published`

Targeted direct Lean check and `lake build
GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilCompletedCenteredSourceMatrix` pass. Principal
`#print axioms` reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
