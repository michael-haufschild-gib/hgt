# CCM Guinand--Weil endpoint-renormalized archimedean first jet

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / mixed-order source dictionary
- **Novelty scope:** corpus-new universal endpoint-jet law and mode-independent diagonal
  counterterm; published restricted-Weil Gamma expression is external input
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilArchimedeanFirstJet.lean`

## Universal first-jet law

For every differentiable real logarithmic test `F`, Lean proves

```text
(exp(h/2) F(h)-F(0))/(exp(h)-exp(-h))
  -> F'(0)/2+F(0)/4 as h -> 0+.                              (1)
```

Thus restricted-Weil endpoint subtraction is not an ad hoc finite part. It is the canonical
order-one source reader on the first jet `(F(0),F'(0))`.

## Physical diagonal specialization

For integer mode `n`, define

```text
xi_n=pi*n/a,
F_(a,n)(h)=2(1-h/(2a)) cos(xi_n h).                            (2)
```

Exact affine transport identifies `(2)` with twice the weighted-cosine horizon coordinate.
Despite the mode-dependent oscillation, every mode has the same endpoint jet

```text
F_(a,n)(0)=2,
F'_(a,n)(0)=-1/a.                                              (3)
```

Combining `(1)` and `(3)` gives

```text
(exp(h/2) F_(a,n)(h)-F_(a,n)(0))/(exp(h)-exp(-h))
  -> 1/2-1/(2a).                                               (4)
```

The singular Gamma diagonal therefore contributes one universal aperture counterterm, not one
independent endpoint datum per Fourier mode.

## CCM-FU consequence

Odd sine tests lower Gamma distributional order because they vanish at the endpoint. Diagonal
tent--cosine tests retain endpoint value and are read by a first-jet functional. C60's odd
cancellation and `(1)` are the two degrees of one graded source complex.

## Lean declarations

- `ccmGuinandWeilArchimedeanFirstJet_limit`
- `ccmGuinandWeilPhysicalFrequencyInt`
- `ccmGuinandWeilSineCoordinate_logToHorizon_int`
- `ccmGuinandWeilDiagonalLogTest`
- `ccmGuinandWeilWeightedCosineCoordinate_logToHorizon`
- `hasDerivAt_ccmGuinandWeilDiagonalLogTest_zero`
- `ccmGuinandWeilArchimedeanDiagonalFirstJet_limit`

Targeted direct Lean check and `lake build
GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilArchimedeanFirstJet` pass. Principal `#print axioms`
reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
