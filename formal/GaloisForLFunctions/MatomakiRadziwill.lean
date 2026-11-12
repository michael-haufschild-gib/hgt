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
import GaloisForLFunctions.MatomakiRadziwill.LadderFirstTerm
import GaloisForLFunctions.MatomakiRadziwill.LadderLastScale
import GaloisForLFunctions.MatomakiRadziwill.LadderTopTerms
import GaloisForLFunctions.MatomakiRadziwill.LadderBound
import GaloisForLFunctions.MatomakiRadziwill.LadderMeanSquare
import GaloisForLFunctions.MatomakiRadziwill.ParsevalWindows
import GaloisForLFunctions.MatomakiRadziwill.ParsevalMeanSquare

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
  `LadderStepTerm`, `LadderFirstTerm`, `LadderLastScale`, `LadderTopTerms`, `LadderBound`,
  `LadderMeanSquare`):
  the moment computation for powers of prime blocks with arbitrary bounded
  coefficients; Ramaré's identity at one scale and its block decomposition
  `Σ_{n ∈ S} f(n)n^{-1-it} ≈ Σ_v Q_v R_v`, with mean-square error `≪ (W/X + 1)(1/H + 1/P)`; the
  first step (mean value theorem where every block is small), the later steps (moment trick against
  the previous scale), and the exceptional set (Markov for its measure, a pointwise bound for the top
  scale), assembled into the master inequality `LadderScales.ladder_master`; the concrete ladder
  `a_0 = 200 log L`, `b_0 = L/2`, `a_{j+1} = 2b_j²`, `b_{j+1} = a_{j+1}²` below `(log X)^{0.93}` and the
  Route T scale above it give, for `χ ≠ 1` (`exists_mean_square_twLiouville_le`):
  `∫_{|w| ≤ W} |Σ_{X<n≤4X} λχ(n)/n · n^{2πiw}|² ≤ ε` for `L ≥ L₀(ε)`, `X ≥ X₀(L)`, `W ≤ X e^{-L/2}`.
* **Parseval** (`ParsevalWindows`, `ParsevalMeanSquare`): Plancherel for logarithmic windows with the
  dyadic frequency tail, the passage from `f(n)/n` to `f(n)`, and the corpus block transfer give
  `Σ_{X ≤ m < 2X} |Σ_{m<n≤m+h} λχ(n)|² ≤ ε h² X` for `h ≥ h₀(ε)`, `X ≥ X₀(h)`
  (`exists_short_sum_mean_square_twLiouville_le`).
-/
