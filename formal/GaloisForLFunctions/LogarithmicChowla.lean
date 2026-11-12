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

/-!
# Logarithmic two-point Chowla

Toward `(1/log x) Σ_{n ≤ x} λ(n)λ(n+h)/n → 0`. Correlations are read through limit functionals
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
-/
