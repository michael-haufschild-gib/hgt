# EDQ finite-zero displacement law

- **ID:** EDQ-FZD
- **Stage:** 3-formalized; paper proof and Lean verified
- **Sources:** ArithmeticCenteredTailPhase, ArithmeticFiniteSourceContour, PrimeZeroSusceptibility, Mathlib analytic-order factorization and real-power asymptotics.

## Full chain

Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH. The finite-source contour theorem produces displaced zeros but does not determine their direction. This component extracts the actual leading complex displacement from the complete arithmetic tail, retaining every multiplicity and the cutoff phase.

## Dependency-closed paper proof

Write F_N=G_N/(s-1), B(s)=s*(s+1)*(s+2)/720, and C_N for the complete normalized tail. Existing exact identities imply

N^(s+3)*(F_N(s)-zeta(s))=B(s)*C_N(s).

For N>=1 and abs(Im(s))<=N, norm(C_N(s)-1)<=4*norm(s+3)/(5*N), so C_N(z_j) tends to 1 whenever N_j tends to infinity and z_j tends to a point of Re(s)>0. Thus the scaled error tends to B(rho) along every such varying spectral sequence.

At any nontrivial zeta zero rho, let m be its positive finite analytic multiplicity. Analytic-order factorization supplies an analytic g, nonzero at rho, with zeta(z)=(z-rho)^m*g(z) near rho. Along any cofinal integer cutoff sequence N_j and actual finite-head zeros z_j tending to rho, the exact zero equation gives

N_j^(z_j+3)*(z_j-rho)^m = -B(z_j)*C_(N_j)(z_j)/g(z_j)
  → -B(rho)/g(rho) != 0.

The moving exponent must also be controlled. The scaled displacement is bounded. Since Re(z_j)>0 eventually and N_j>=1, its norm implies N_j^2*norm(z_j-rho)^m is bounded. Therefore

(norm(z_j-rho)*log N_j)^m <= constant*(log N_j)^m/N_j^2 → 0.

Taking the positive m-th root gives (z_j-rho)*log N_j → 0. Hence N_j^(rho-z_j)=exp((rho-z_j)*log N_j) → 1, and the fixed-center complex displacement law is

N_j^(rho+3)*(z_j-rho)^m → -rho*(rho+1)*(rho+2)/(720*g(rho)).

Taking norms and the positive m-th root also proves that N_j^((Re(rho)+3)/m)*dist(z_j,rho) tends to the strictly positive constant norm(B(rho)/g(rho))^(1/m).

This is an exact nonzero complex limit, not a norm-only approximation. It retains the logarithmic cutoff phase exp(i*Im(rho)*log N_j). Cofinal sequences of actual finite-head zeros tending to every rho exist by the preceding contour theorem: choose a cutoff at least j and a distinct zero within 1/(j+1). Thus the asymptotic law has actual witnesses and no simplicity or RH premise. It determines displacement relative to the original zero, not the original zero's real part. A separate location-separating arithmetic comparison remains open.

## Gates

- [x] Corpus comparison and dependency-closed paper proof.
- [x] Lean normalized error, multiplicity displacement, fixed-center phase, actual witnesses and exact distance scale.
- [x] Leaf audit, new-only axioms, wiring; repository lint executed with unrelated concurrent wiring failures.
- [x] Index, ledgers, cleanup.
- [ ] Signed location separation; RH.

## Formal certificate

- Leaf: `formal/GaloisForLFunctions/RHTower/ArithmeticFiniteZeroDisplacement.lean` (262 lines, 11 theorems, 1 definition); namespace `RHTower.DeletionMixedRefinement`.
- Exact source coefficient: `finiteTailLeadingCoefficient`, `scaled_finiteCutoffZeta_error`.
- Complete varying-point error: `tendsto_centeredTailPhase_of_tendsto`, `tendsto_scaled_finiteCutoffZeta_error`.
- Moving-power splitting: `tendsto_moving_scaled_finite_zero`.
- Phase-drift control and fixed-center correction: `tendsto_finite_zero_log_drift`, `tendsto_finite_zero_power_correction`.
- Full complex asymptotic: `tendsto_fixed_scaled_finite_zero`; unconditional actual-zero assembly: `exists_finite_zero_displacement_coefficient`.
- Actual cofinal finite-head zero sequences with nonzero limit: `exists_cofinal_finite_zero_displacement_limit`.
- Exact distance scale: `tendsto_finite_zero_distance_scale`.
- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_displacement.lean`, exit 0, no diagnostics.
- Final audit from `formal`: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticFiniteZeroDisplacement`, exit 0. Only this leaf built (6.8 seconds); dependencies cached. Umbrella import appended; no full or umbrella build.
- New-only axioms: `lake env lean /tmp/edq_displacement_axioms.lean`, exit 0. All 12 declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; no added axioms, admissions, or computational certificates.
- Repository lint: exit 1; unrelated concurrent modules remain unreachable from their umbrella: `ThetaCuspDeepTailCalibration`, `ThetaCuspDeepTailCooling`, `ThetaCuspTwoAtomReflectedApproximation`, `ThetaCuspTwoAtomReflectedBounds`, `ThetaCuspTwoAtomScalePolynomials`, `ThetaCuspTwoAtomSourceApproximation`. The new EDQ leaf is wired. These concurrent modules were not modified by this task. Existing file-size warnings also present.
- Index: exit 0; API/GAPS/OVERVIEW and search database refreshed once. refreshed formal/.lean_search-9925dbc05e32a559.db (3 changed, 0 removed).
- Cleanup: all owned scratch-check, leaf-build, axiom, lint, and index sessions reached terminal states. Both owned scratch Lean sources removed; logs retained. No owned Lean/lake process remains.
- Logs: `/tmp/edq_displacement.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, `.index.log`.

RH remains unproved and unfalsified. The limit preserves full multiplicity and complex cutoff phase but does not determine the limiting zero's real part.
