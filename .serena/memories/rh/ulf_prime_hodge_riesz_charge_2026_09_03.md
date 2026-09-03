# ULF prime-Hodge Riesz charge checkpoint (2026-09-03)

Constructed Lean core already exists:
- `RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect`
- `RHTower.PrimeHodgeHistoryFirstExitTransgression`
- `RHTower.PrimeHodgeHistorySurvivalFredholmColligation`

Paper theorem:
- `docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/prime-hodge-singular-gauge-riesz-charge.md` (ULF-PHSGRC-001)

Exact object: for H=l2(N), K=l2(primes), U unilateral, C weighted survival, Q=diag(sqrt(m_n)), D=I-C*C, A_d normalized positive prime Stokes operator:
`Phi=Q D Q=Q^2-U*Q^2U=diag(w_n)`,
`G_d=Q^2 tensor A_d`,
`T_d=Phi tensor A_d=G_d-(U tensor I)* G_d (U tensor I)`.
Signed family: T(0)=0, T(t)=sign(t)T_|t| for t!=0; exactly Lean's homotopy defect.

Lean-closed core facts: S1; trace=sign(t); trace norm=|sign(t)|; reflection odd; positive by chamber; every ordered cross-prime entry nonzero; diagonal theta Mellin-six flux times unsquared prime density; first-exit curvature reconstructs same T; Fredholm index/exit flux/Hodge flux/trace all unit.

Paper joint reconstruction:
- history partial trace of T_d recovers A_d (sum w=1);
- prime partial trace recovers diag(w);
- Riesz potential sum_j U*^j T_d U^j recovers G_d in S1 (sum m=7/4);
- from G recover m, survival r=m_{n+1}/m_n, curvature/exit w.

Hostile correction:
- T is a source Riesz charge/potential, not an RH selector.
- Observer horizon does not force harmonic lift; literal formation chooses first-exit finite-trace lift.
- Identifying strict-right Xi relation horizon with a harmonic component of this same Riesz equation remains missing and must be derived, not chosen.
- ULF-PHTH-002 moved to failed; STATUS FAIL-93/CANNOT-245, MUST-165/166.
- Abstract Riesz/Toeplitz decomposition is classical; novelty only corpus-specific fusion.

Further promising but not promoted yet:
- For fixed primes, normalized A_d matrix entries should tend 0 as d->0+ (numerator 8d log p p^(-1-2d), denominator ->4; offdiagonal Schur bound). Positivity/norm<=1 then gives A_d ->0 SOT while trace=1. Hence T_d ->0 SOT but not S1: exact topology/index wall.
- Scalar Stokes jump charge j(t)=1_{t=0} complements ||T(t)||_1=1_{t!=0}; possible conserved carrier-switch compactification.
- Corpus already has exponential aperture-wall blow-up and proves naive wall determinant divisor differs from Xi; do not rediscover naive normal-cone solution.
