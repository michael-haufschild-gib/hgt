import GaloisForLFunctions.LogarithmicChowla.LogarithmicAverages
import GaloisForLFunctions.LogarithmicChowla.LimitFunctional
import GaloisForLFunctions.LogarithmicChowla.FiniteEntropy
import GaloisForLFunctions.LogarithmicChowla.ResidueHoeffding
import GaloisForLFunctions.LogarithmicChowla.EntropyDecrement
import GaloisForLFunctions.LogarithmicChowla.ShiftDeviation
import GaloisForLFunctions.LogarithmicChowla.PrimeShiftReduction
import GaloisForLFunctions.LogarithmicChowla.DiscreteFourier
import GaloisForLFunctions.LogarithmicChowla.ArcMass
import GaloisForLFunctions.LogarithmicChowla.CircleMethod
import GaloisForLFunctions.LogarithmicChowla.CircleBound
import GaloisForLFunctions.LogarithmicChowla.PrimeKernelBound
import GaloisForLFunctions.LogarithmicChowla.DilatedWindows
import GaloisForLFunctions.LogarithmicChowla.TwistTransfer
import GaloisForLFunctions.LogarithmicChowla.TwistVarVanishes
import GaloisForLFunctions.LogarithmicChowla.TwistVarLimit
import GaloisForLFunctions.LogarithmicChowla.LogarithmicChowlaTheorem

/-!
# Logarithmic two-point Chowla

`(1/log x) Σ_{n ≤ x} λ(n)λ(n+h)/n → 0` for every `h ≥ 1` (`tendsto_logAvg_liouville_shift`). Correlations are read through limit functionals
`L_U` of logarithmic averages along ultrafilters (`LimitFunctional`), which are exactly shift
invariant and dilation covariant.

* **Entropy decrement** (`EntropyDecrement`, `ShiftDeviation`, `PrimeShiftReduction`): for every `ε`
  there are arbitrarily large scales `k` with `|c(h) − avg_{p ∈ (2^k, 2^{k+1}]} c(ph)| ≤ 6ε`, from
  the decrement of `H(X_H | n mod Q)/H` along doubling scales, Hoeffding on residues mod the primes of a
  scale, and the event inequality (`FiniteEntropy`, `ResidueHoeffding`).
* **Circle method** (`DiscreteFourier`, `ArcMass`, `CircleMethod`, `CircleBound`): over `ℤ/R`,
  `|avg_p c(ph)|` is at most the minor-arc size `η` of the prime kernel plus `4 Σ V(b/s, T)` over the
  fractions `b/s`, `s ≤ hQ₀`, where `V` is the twisted short mean square of `λ`.
* **(PRIME)** (`PrimeKernelBound`): the prime kernel is small off the major arcs
  (`PrimeExponentialSums.exists_off_major_arcs`), so `|avg_p c(ph)| ≤ η + 4 Σ V(b/s, T)` for all large
  scales `k` and `T ≤ 2^k/(4W)`.
* **(MR)** (`DilatedWindows`, `TwistTransfer`, `TwistVarVanishes`, `TwistVarLimit`): `V(b/s, T) → 0`.
  The twist `e(mb/s)` splits into residue classes, each class into characters mod `s/(r, s)` acting
  on dilated windows; non-principal characters use Matomäki–Radziwiłł for `λχ`, the principal ones
  reduce through Möbius to dilated windows of `λ` (`MatomakiRadziwill`); dyadic short-window bounds
  give logarithmic-average bounds.
* **Assembly** (`LogarithmicChowlaTheorem`): `c(h) = 0` for every `U`.
-/
