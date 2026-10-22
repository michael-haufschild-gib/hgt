# Even prolate double-Fourier eigenline universality law

## Status

Lean-formalized; exact file audit passed on 2026-07-22. Literature novelty audit pending.

## Corpus sources

- `RHTower/SlepianKernelFubini.lean`
- `RHTower/ProlateDiagonalization.lean`
- `RHTower/SlepianBandCommutation.lean`

## Theorem-first derivation

`SlepianKernelFubini` identifies the composed finite-band Fourier integral with the Slepian sinc
kernel on even inputs. `ProlateDiagonalization` proves that the sinc-kernel band transform is
scalar on a nonvanishing compact segment of any prolate eigenfunction. Converting the set integral
to the interval-integral definition joins the two exact operators.

## Universal law

Every even `C²` prolate eigenfunction at bandwidth `2π` is an eigenfunction of the actual composed
unit-aperture double Fourier operator on every compact interior interval where it is nonzero. The
same real scalar works throughout the interval.

## Lean status

- Module: `GaloisForLFunctions.RHTower.EvenProlateDoubleFourierEigenlineUniversalityLaw`
- Capstone: `RHTower.evenProlateEigenfunction_doubleBandFourier_smul_on`
- Exact command passed: `lake env lean GaloisForLFunctions/RHTower/EvenProlateDoubleFourierEigenlineUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
