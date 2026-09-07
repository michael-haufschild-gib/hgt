# EDQ finite-source contour transport

- **ID:** EDQ-FCT
- **Stage:** 3-formalized; paper proof and Lean verified
- **Sources:** ArithmeticFiniteCutoffZeroBudget, ArithmeticCenteredTailPhase, RiemannXiSuzukiPositiveCriticalStripEtaFiniteRouche, FiniteToEntireLocalDivisor.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. This component supplies quantitative approximation and exact local contour transport for the literal finite arithmetic head. A separating comparison of its contour data remains open.

## Dependency-closed paper proof

For integer N>=1, let G_N be the existing entire pole-cleared finite Bernoulli residual, and let F_N(s)=G_N(s)/(s-1). Work on U={Re(s)>0, s!=1}. The exact retained-tail identity gives

F_N(s)-zeta(s)=s*(s+1)*integral_N^infinity P(x)*x^(-s-2) dx,

where P(x)=({x}^2-{x})/2+1/12. No tail term is discarded. If norm(s)<=M<=N, the existing complete signed-frequency estimate bounds the tail norm by N^(-Re(s)-2)/15. Since N>=1 and Re(s)>0, this is at most 1/(15*N^2), and norm(s*(s+1))<=(M+1)^2. Consequently

norm(F_N(s)-zeta(s)) <= (M+1)^2/(15*N^2).

This proves uniform convergence on every bounded subset of U, hence locally uniform convergence on U. Both functions are analytic on U. On any circle in U where zeta is nonzero, compactness provides a positive minimum of norm(zeta). The explicit error eventually lies below that minimum. The corpus's local Rouche theorem then gives nonvanishing of F_N on the circle and exact equality of their logarithmic-derivative integrals.

At any actual nontrivial zeta zero rho, choose an isolating circle of radius less than any requested positive r and less than both Re(rho)/2 and (1-Re(rho))/2. Its closed disk lies in U. The local analytic-order argument principle computes the zeta contour integral as its positive analytic multiplicity times 2*pi*i. All sufficiently large finite approximants have that same nonzero integral. If one had no zero in the open disk, boundary nonvanishing would make its logarithmic derivative analytic on the entire closed disk; Cauchy's theorem would give integral zero, a contradiction. Finally the complete-tail phase cone proves G_N(rho)!=0 for N>=2*norm(rho+3), so the nearby finite zero differs from rho itself.

This establishes actual displaced finite zeros and contour multiplicity transport for every nontrivial zeta zero, without simplicity or RH assumptions. It does not force their real parts to equal 1/2. Approximation and contour stability coexist with the impossibility of exhaustive exact matching at original critical zeros.

## Gates

- [x] Corpus comparison and dependency-closed paper proof.
- [x] Lean exact error, uniform convergence, contour transport, displaced-zero existence.
- [x] Leaf audit, new-only axioms, umbrella wiring.
- [x] Index, ledgers, cleanup; repository lint executed and reports the unrelated wiring failures detailed below.
- [ ] Arithmetic contour separation; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticFiniteSourceContour.lean` (232 lines, 9 theorems, 1 definition); namespace `RHTower.DeletionMixedRefinement`.
- Exact retained error: `finiteCutoffZeta_sub_zeta`; quantitative estimate: `norm_finiteCutoffZeta_sub_zeta_le`.
- Uniform and local uniform convergence: `tendstoUniformlyOn_finiteCutoffZeta`, `tendstoLocallyUniformlyOn_finiteCutoffZeta`.
- Exact circle transport: `eventually_finiteCutoffZeta_circle_nonzero_and_logDeriv_eq`.
- Full local winding and displaced actual finite-head zero: `exists_lt_eventually_finiteCutoffZeta_displaced_zero_and_winding`.
- Arbitrarily close, distinct zeros of all sufficiently long literal entire heads: `eventually_exists_finiteCutoffResidual_zero_near`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_contour.lean`, exit 0, no diagnostics.
- Final audit from `formal`: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticFiniteSourceContour`, exit 0. New leaf built in 7.5 seconds. Lake also refreshed two required dependency modules, `XiCenteredOrderTwentyOneSourceBudgetClosure` (110 seconds) and `HedenmalmThetaEigenODE` (3.4 seconds); other dependency jobs were cached. The initially missing Hedenmalm olean had been restored separately with `lake env lean ... -o ...`. No full or umbrella target was built. Umbrella import appended.
- New-only axiom audit: `lake env lean /tmp/edq_contour_axioms.lean`, exit 0. All 10 new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; no added axioms, admissions, or computational certificates.
- Repository lint: exit 1 solely for unrelated concurrent modules `ThetaCuspDeepTailCalibration` and `ThetaCuspDeepTailCooling` being unreachable from their umbrella. The new EDQ leaf is wired. File-size warnings also present. Those concurrent files were not modified by this task.
- Index: exit 0; refreshed API/GAPS/OVERVIEW and search database once (4 changed, 0 removed, including concurrent changes).
- Cleanup: all owned check, dependency, build, axiom, lint, and index sessions reached terminal states. Both owned scratch Lean sources were removed; logs retained. No owned Lean/lake process remains.
- Logs: `/tmp/edq_contour.check.log`, `.build.log`, `.axioms.log`, `.dependency.log`, `.lint.log`, `.index.log`.

RH remains unproved and unfalsified. Local contour transport preserves any hypothetical off-line zero's multiplicity as well; a new arithmetic location-separating estimate is still required.
