import GaloisForLFunctions.MatomakiRadziwill.ShiftedVinogradov
import GaloisForLFunctions.MatomakiRadziwill.ShiftedPhaseBlocks
import GaloisForLFunctions.MatomakiRadziwill.HurwitzGrowth
import GaloisForLFunctions.MatomakiRadziwill.LFunctionGrowth
import GaloisForLFunctions.MatomakiRadziwill.LFunctionThreeFourOne
import GaloisForLFunctions.MatomakiRadziwill.LFunctionDLVP
import GaloisForLFunctions.MatomakiRadziwill.LFunctionZeroFree

/-!
# Matomäki–Radziwiłł for twisted Liouville functions

Toward the mean square of short sums of `λχ`, `χ` a Dirichlet character of fixed modulus.

* **Zero-free region** (`ShiftedVinogradov`, `ShiftedPhaseBlocks`, `HurwitzGrowth`,
  `LFunctionGrowth`, `LFunctionThreeFourOne`, `LFunctionDLVP`, `LFunctionZeroFree`): Vinogradov's
  estimate and the `k`-th derivative test hold for shifted phases `(n+α)^{it}`, so Hurwitz partial
  sums and `L(s, χ)` grow like `log τ` across the Vinogradov–Korobov width, and the de la Vallée
  Poussin argument gives `L(β + iγ, χ) ≠ 0` for `β > 1 − (log γ)^{-2/3}(log log γ)^{-5/3}/10⁸`.
-/
