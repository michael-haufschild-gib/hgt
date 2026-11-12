import GaloisForLFunctions.MatomakiRadziwill.ShiftedVinogradov
import GaloisForLFunctions.MatomakiRadziwill.ShiftedPhaseBlocks
import GaloisForLFunctions.MatomakiRadziwill.HurwitzGrowth
import GaloisForLFunctions.MatomakiRadziwill.LFunctionGrowth
import GaloisForLFunctions.MatomakiRadziwill.LFunctionThreeFourOne
import GaloisForLFunctions.MatomakiRadziwill.LFunctionDLVP
import GaloisForLFunctions.MatomakiRadziwill.LFunctionZeroFree
import GaloisForLFunctions.MatomakiRadziwill.LFunctionConj
import GaloisForLFunctions.MatomakiRadziwill.LFunctionLogDerivStrip
import GaloisForLFunctions.MatomakiRadziwill.TwistedChebyshevContour
import GaloisForLFunctions.MatomakiRadziwill.TwistedChebyshevBound
import GaloisForLFunctions.MatomakiRadziwill.PrimeBlockRouteT
import GaloisForLFunctions.MatomakiRadziwill.LadderMeanValue
import GaloisForLFunctions.MatomakiRadziwill.RamareDecomposition
import GaloisForLFunctions.MatomakiRadziwill.RamareBlocks
import GaloisForLFunctions.MatomakiRadziwill.RamareBlockError
import GaloisForLFunctions.MatomakiRadziwill.RamareBlockMVT
import GaloisForLFunctions.MatomakiRadziwill.LadderBlocks
import GaloisForLFunctions.MatomakiRadziwill.LadderMoment
import GaloisForLFunctions.MatomakiRadziwill.LadderScaleBounds
import GaloisForLFunctions.MatomakiRadziwill.LadderExceptional
import GaloisForLFunctions.MatomakiRadziwill.LadderHM
import GaloisForLFunctions.MatomakiRadziwill.LadderRouteT
import GaloisForLFunctions.MatomakiRadziwill.LadderCover
import GaloisForLFunctions.MatomakiRadziwill.LadderRough
import GaloisForLFunctions.MatomakiRadziwill.LadderMaster
import GaloisForLFunctions.MatomakiRadziwill.LadderNumerics
import GaloisForLFunctions.MatomakiRadziwill.LadderNumericsMoment
import GaloisForLFunctions.MatomakiRadziwill.LadderNumericsExceptional
import GaloisForLFunctions.MatomakiRadziwill.LadderNonRough
import GaloisForLFunctions.MatomakiRadziwill.LadderDensity
import GaloisForLFunctions.MatomakiRadziwill.LadderSequence
import GaloisForLFunctions.MatomakiRadziwill.LadderConfig
import GaloisForLFunctions.MatomakiRadziwill.LadderHBounds
import GaloisForLFunctions.MatomakiRadziwill.LadderStepTerm

/-!
# Matomäki–Radziwiłł for twisted Liouville functions

Toward the mean square of short sums of `λχ`, `χ` a Dirichlet character of fixed modulus.

* **Zero-free region** (`ShiftedVinogradov`, `ShiftedPhaseBlocks`, `HurwitzGrowth`,
  `LFunctionGrowth`, `LFunctionThreeFourOne`, `LFunctionDLVP`, `LFunctionZeroFree`): Vinogradov's
  estimate and the `k`-th derivative test hold for shifted phases `(n+α)^{it}`, so Hurwitz partial
  sums and `L(s, χ)` grow like `log τ` across the Vinogradov–Korobov width, and the de la Vallée
  Poussin argument gives `L(β + iγ, χ) ≠ 0` for `β > 1 − (log γ)^{-2/3}(log log γ)^{-5/3}/10⁸`.
* **Route T for `χ`** (`LFunctionConj`, `LFunctionLogDerivStrip`, `TwistedChebyshevContour`,
  `TwistedChebyshevBound`, `PrimeBlockRouteT`): reflection `L(s, χ⁻¹) = conj L(conj s, χ)` covers
  negative heights; Landau's lemma bounds `L'/L ≪ log Y/ε(Y)` in the strip of half the
  Vinogradov–Korobov width at heights `≤ Y`; truncated Perron and Cauchy's theorem on the rectangle
  give `Σ_{n ≤ N} χ(n)Λ(n)n^{-iτ} ≤ N/(log X)^A` for `|τ| ≤ X`, `log N ≥ (log X)^θ`, `θ > 2/3`, and
  hence `Σ_{P < p ≤ 2P} χ(p)p^{-1-iτ} ≤ (log X)^{-A}`.
* **Ladder** (`LadderMeanValue`, `RamareDecomposition`, `RamareBlocks`, `RamareBlockError`,
  `RamareBlockMVT`, `LadderBlocks`, `LadderMoment`, `LadderScaleBounds`, `LadderExceptional`, `LadderHM`,
  `LadderRouteT`, `LadderCover`, `LadderRough`, `LadderMaster`, `LadderNumerics`,
  `LadderNumericsMoment`, `LadderNumericsExceptional`, `LadderNonRough`,
  `LadderDensity`, `LadderSequence`, `LadderConfig`, `LadderHBounds`,
  `LadderStepTerm`):
  the moment computation for powers of prime blocks with arbitrary bounded
  coefficients; Ramaré's identity at one scale and its block decomposition
  `Σ_{n ∈ S} f(n)n^{-1-it} ≈ Σ_v Q_v R_v`, with mean-square error `≪ (W/X + 1)(1/H + 1/P)`; the
  first step (mean value theorem where every block is small), the later steps (moment trick against
  the previous scale), and the exceptional set (Markov for its measure, a pointwise bound for the top
  scale), assembled into the master inequality `LadderScales.ladder_master`.
-/
