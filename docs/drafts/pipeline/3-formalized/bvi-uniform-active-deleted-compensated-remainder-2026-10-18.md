# Uniform active-deleted compensated remainder

- **ID:** BVI-UNIFORM-ACTIVE-DELETED-2026-10-18
- **Stage:** 3-formalized
- **Parent:** `bvi-uniform-renormalized-interior-energy-remainder-2026-10-18.md`
- **Full goal:** `../1-in-progress/bvi-interior-martingale-coercive-contraction-2026-10-18.md`

## Statement

For every epsilon > 0, there is C >= 0, independent of T, such that

    |pmActiveDeletedCovarianceDiagonal epsilon T
      - pmShiftedExponentCovariance epsilon * pmCompensatedHarmonicSum T|
      <= C.

All coefficient summability conditions are discharged for the actual
arithmetic functions. This improves the existing o(log T) statement for
the diagonal to a uniform O(1) bound. It does not bound the predecessor
remainder or prove strict interior contraction.

## Dependency-closed paper proof

Write F_e(n)=sum_{d|n} mu(d)*d^(-e), rho=rho_e, and eta=1+e.
The existing corpus provides the divisor expansion of F_e*F_eta, with
coefficient b_e satisfying |b_e(n)| <= d(n)*n^(-e). The ordinary damped
Mobius coefficient obeys the same bound.

For either coefficient a, its logarithmic weight is bounded by

    |a(n)|*(1+log n)/n
      <= d(n)^2*n^(-1-e)*(2+(log n)^2),  n>=1.

This follows from d(n)>=1 and 1+u<=2+u^2. Both majorant series are already
proved summable in `RHTower/FourthMomentDiagonal.lean`, at
sigma=(1+e)/2 > 1/2. The zero-index logarithmic weight is zero.

Apply the existing uniform divisor-harmonic remainder theorem to the
ordinary coefficient at e and eta and to b_e. Their densities are the
existing rho_e, rho_eta and `pmShiftedExponentSecondDensity e`; the ordinary
real density identification also follows from uniqueness of the two
already-proved Cesaro limits. Denote the resulting uniform constants by
C_e, C_eta and C_product.

The exact active-deleted coefficient is (F_e-rho)*(F_eta-rho). Expanding
its harmonic sum and subtracting the existing shifted covariance times
H_comp leaves the product remainder, minus rho times each single-field
remainder, plus rho^2*(H_T-H_comp(T)). The existing harmonic difference
bound is between 0 and 2.

Finally, the actual compensated diagonal is that harmonic sum minus
the coefficient prefix sum divided by T+1. Since 0<=F_e,F_eta<=1, the
coefficient has absolute value at most (1+|rho|)^2. Hence its terminal
average has the same bound. A valid total constant is

    C_product + |rho|*C_e + |rho|*C_eta
      + 2*rho^2 + (1+|rho|)^2.

The empty horizon is covered directly. No analytic budget is assumed.

## Corpus reuse and verification

Live corpus searches located the existing log-weight harmonic remainder,
shifted coefficient bound and divisor-square moment estimates. Relevant
candidate lemmas and source arguments were inspected, including partial
coverage and source-only statuses. Eight reused APIs passed a separate
Lean axiom audit (18588), all with only standard Lean axioms.

New source:
`formal/GaloisForLFunctions/BezoutValuationIncidence/UniformActiveDeletedCompensatedRemainder.lean`
(250 lines, five public theorems). Umbrella import added once. Original
source verification (21412) exited 0 with no diagnostics; both `.olean`
and `.ilean` were emitted. Output:
`logs/bvi-uniform-active-deleted-2026-10-18-source-pass1.txt`.
Final public audit (18267) exited 0: all five public theorems use only
`propext`, `Classical.choice`, and `Quot.sound`; thirty explicit mathlib
name probes also passed. The earlier scratch-only universe mismatch is
retained in the pass-one log; no source change was required.

Index refresh (11333) passed, and corpus search located the new capstone.
Formal lint (59443) returned 1 for the unrelated package-root placement
of `TransHorizonIncidenceMechanics.lean`, plus 381 existing warnings.
No finding names the owned leaf; no global lint pass is claimed.

Source SHA-256:
`3107e7af3a1b51c7d8ca18b4ec2b1f2d97e5e035aa4e188eb1ec8e9d5a551f02`.
The full certificate is
`logs/bvi-uniform-active-deleted-2026-10-18-manifest.json`.
Thirty completed proof/search scratch files were archived, hash-verified
and removed. Only the separately tracked adjacent-correlation work remains
active. No field README write, commit or push was performed by this task.

Twenty-three raw corpus results are archived and hash-verified in
`logs/bvi-uniform-active-deleted-2026-10-18-search.tar.gz`; coverage,
freshness, candidate/source names and interpretation are recorded in the
corresponding search manifest. The eight reused axiom closures are in
`logs/bvi-uniform-active-deleted-2026-10-18-reused-axioms.txt`.
The additional global log-weight query covered all 130 distinct hits.
The existing convolution closure requires the input log moments, so it
does not replace their arithmetic discharge in this leaf.
