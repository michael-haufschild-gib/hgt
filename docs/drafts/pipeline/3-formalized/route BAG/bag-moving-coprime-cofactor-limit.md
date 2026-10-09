# BAG growing coprime cofactor limit

- **Stage:** 3-formalized

For primes up to N and L=log N, put s=1-u/L, with nonzero complex
parameter u. The actual coprime principal-character cofactor satisfies

C_N(s) -> -exp(-gamma-P(u))/u,
P(u)=integral_0^1 (exp(u*t)-1)/t dt.

The integrand is extended continuously with value u at zero, using
u*dslope(exp,0,u*t). This is an actual growing-cutoff law; no RH premise.
The nonzero parameter is represented by the domain Complex units.

Proof. Complex prime-window weak convergence follows from the corpus real
weak limit applied to real and imaginary parts. Thus sum_(p<=N)
(exp(u*log(p)/L)-1)/p tends to P(u). For q=p^(-1+u/L), the logarithmic
error log(1-q)+q has norm at most 2|q|^2 once |q|<=3/4. The corpus radial
bounds give |q|^2<=p^(-3/2) eventually, uniformly in p. The difference
from the balanced error vanishes termwise and is dominated by 4*p^(-3/2).
Dominated convergence therefore proves the full logarithmic ratio limit.
Exponentiating the finite sum, with each factor nonzero, proves
product_(p<=N)(1-p^(-1+u/L))/(1-1/p) -> exp(-P(u)). No logarithm of a
product or unstated branch identity is used. The zeta residue gives
(-u/L)*zeta(1-u/L)->1. The exact corpus cofactor identity and Mertens'
product law A_N*L->exp(-gamma) finish the displayed limit.

Corpus dependencies: MertensPrimeWindowWeakConvergence,
MertensThirdTheorem, SquarefreeCriticalNormalCone,
ChiRamanujanCofactorPole. All proof steps now have Lean proofs in
ChiRamanujanMovingCofactorLimit. The complete two-variable labelled
source and physical pole/near-cone/tail cancellation remain open.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole` | `criticalCofactorTerm_eq`, `criticalCofactor_hasSum`, `criticalCofactor_eq`, `criticalCofactor_residue`, `criticalWeightedCone_hasSum`, `criticalWeightedConeEuler_balanced`, `criticalWeightedConeEuler_continuousAt`, `criticalCompletedCone_hasSum`, `criticalCompletedCone_double_residue` |
| `GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit` | `criticalComplexPrimeWindow_tendsto`, `criticalEulerProfile_continuous`, `criticalEulerProfile_mul`, `criticalMovingEulerRatio_tendsto`, `criticalEulerProfile_zero`, `criticalCofactor_logScale_limit`, `criticalPrimeNormalization_logScale_tendsto`, `criticalCofactor_moving_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
