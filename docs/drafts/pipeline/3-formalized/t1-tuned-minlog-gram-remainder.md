# T1 tuned minimum-log Gram remainder

## Route and proof-chain burden

Route T1: smooth-AFE/Barban--Vehov arithmetic producer -> signed long detector control -> fixed critical half-density Weil-source bound -> RH.

Exact burden attacked: preserve cancellation in the included detector polynomial at `L = N^100`, `M = N^49` and `lambda = 1 / log L`, without separately estimating the six moving minimum-log Selberg monomials.

## Corpus basis

`DifferentiatedBarbanVehovIncludedMinLogForms` gives the three exact included boundaries. `SelbergMinLogMonomial` gives symmetry and the omitted minimum-log forms. `DifferentiatedBarbanVehovIncludedEnergy` identifies the actual long energy with the included polynomial up to the closed quantitative error. Corpus search found no tuned cancellation or positivity theorem for the surviving minimum-log combination.

## Literature audit

Graham's classical Barban--Vehov asymptotic and modern explicit/generalized treatments control ordinary logarithmic quadratic sieve weights. The checked primary sources do not state the detector-coupled `A^i B^j min(A,B)^k` cancellation or its cubic Gram kernel: Zuniga Alterman, *On a logarithmic sum related to the Selberg sieve* (arXiv:2005.04280); An, *A Generalization of Graham's Estimate on the Barban--Vehov Problem* (arXiv:2206.10104); Ramare--Zuniga Alterman, *An L2-bound for the Barban--Vehov weights* (arXiv:2405.12662).

## Conjecture loop

1. **C1 (failed):** `lambda * ell = 1` cancels every minimum-log term. Expansion leaves a degree-five cubic remainder, so total boundary cancellation is false.
2. **C2 (live):** it cancels all five lower channels and leaves exactly
   `R(M) = (1/3) Min(1,1,3;M) - Min(2,1,2;M) + Min(2,2,1;M)`.
3. **C3 (live strengthening):** `R(M)` is nonnegative because its symmetric kernel is
   `A B integral_0^min(A,B) (A-t)(B-t) dt`, and the gcd coefficient is a totient-weighted Gram kernel. Thus six signed moving objects collapse to one nonnegative square-energy remainder.

## Hostile checks

- Endpoint logs are nonnegative only on `1 <= m,n <= M`; proofs must carry this support.
- `Min(2,1,2)` must be symmetrized before claiming a Gram kernel.
- Pointwise kernel positivity alone is insufficient because Mobius signs occur in `selbergOriginalCoeff`; proof must use gcd/totient Gram factorization.
- This theorem does not claim the remaining scalar asymptotic or RH. It discharges the exact cancellation/sign-preservation premise and isolates the sole analytic remainder.

## Status

Fully formalized. The paper proof and Lean module establish:

- `selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder`: reciprocal tuning `lambda * ell = 1` cancels every lower minimum-log channel and leaves exactly `R(M)`.
- `selbergOriginalTunedMinLogRemainder_eq_integral_totient_sq`: `R(M)` is exactly an integral of totient-weighted squares.
- `selbergOriginalTunedMinLogRemainder_nonneg`: the survivor is nonnegative for `0 < M`.
- `barbanVehovIncludedLongEnergyPolynomialMain_eq_ordinary_add_tunedRemainder`: the actual included long-detector polynomial is ordinary energy plus this single Gram remainder.
- `selbergOriginalIncludedOrdinaryEnergy_div_log_sq_le_polynomialMain_of_tuned`: tuned included polynomial coercively dominates its ordinary Selberg sector after the detector normalization.

Formal artifact: `formal/GaloisForLFunctions/RHTower/Sieve/DifferentiatedBarbanVehovTunedMinLogGram.lean`. Direct `lake env lean` and targeted `lake build GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogGram` pass. Representative `#print axioms` audits report only `propext`, `Classical.choice`, and `Quot.sound`. Module-local forbidden-token scan is empty.

Route consequence: T1 no longer needs six independent moving minimum-log asymptotics or an external sign hypothesis. Remaining hard burden is a coefficient-faithful estimate/asymptotic for the single positive Gram remainder and its landing into the critical half-density carrier. This result does not claim that remaining estimate or RH.

Repository-wide lint remains red because unrelated owned modules are currently unreachable from their umbrellas; this module is wired into `GaloisForLFunctions.RHTower`.
