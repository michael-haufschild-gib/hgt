# Mixed Euler-deletion refinement correction

Exploratory Runpod results. No computed value enters a Lean proof. This folder belongs under the requested computations location; it does not label the numerical conjectures as proved.

## Question and source

Set `u_n=n^(-s)`, `S_N=sum_(n<=N)u_n`, `c_p=p^(1-s)`,
`D_p=(1-c_p)zeta(s)`, and `X_p(k)=S_k-c_p S_floor(k/p)`.
At a zeta zero, `D_p=0`. We evaluated

`T_p(N)=sum_(0<=k<N)(X_p(k)-D_p)(k+1)^(-conj(s))`

and the full within-cell correction

`J_(p,q)(N)=c_p sum_(0<=k<N)(X_q(k)-D_q)[sum_(r=1..p)(pk+r)^(-conj(s))-p(pk+p)^(-conj(s))]`.

The matched finite identity is

`T_(pq)(pN)=T_p(pN)+|c_p|² T_q(N)+J_(p,q)(N)`.

This is now proved symbolically in `RHTower.DeletionMixedRefinement.mixedPrefix_mul`. The Lean identity allows any centering value, so it supplies no zero-specific vanishing. Equal finite cutoffs on every term would be a different assertion.

## Execution and checks

- Host: specified Runpod, Python 3.8.10, NumPy 1.24.4, mpmath 1.3.0.
- Eight worker processes; numerical array operations vectorized; BLAS/OpenMP restricted to one thread per worker.
- All 20 ordered distinct pairs from `2,3,5,7,11`.
- First eight critical-line zeros; six controls with real parts `0.65,0.85` at the first three zero heights; `1.25` and `0.5+17i` as additional controls.
- Cutoffs `36,960`, `147,840`, `591,360`, each divisible by all tested distinct modulus products.
- Zero heights and zeta values evaluated with 70 decimal digits; main arrays use complex128.
- Within-cell differences use `expm1` and `log1p` to avoid subtracting nearly equal powers.
- Independent 50-digit scalar calculation at the first zero, `p=2,q=3,N=4096`, verifies the matched finite identity with discrepancy `2.67e-49`.

Scripts: `scan.py`, `analyze.py`, `refine.py`. Raw and derived results: `results.json`, `analysis.json`, `refinement.json`. Reproduce in that order on the Runpod; `scan.py --workers 8 --output results.json`.

## Outcomes

**Blanket correction vanishing fails numerically.** At the first zero,

`J_(2,3) ≈ 1.7585255899100045 - 0.4651528457584624 i`.

Its real part also changes sign across the tested zeros. Across all pairs, maximum magnitudes at the eight zeros range from `13.05` to `46.56`; the largest change from the middle to final cutoff is below `5.6e-8`. These are numerical observations with convergence diagnostics, not interval-certified inequalities.

**One scalar per dilation does not absorb the correction.** Fitting `J_(p,q)=kappa_p T_q` across all four other moduli gives relative residuals of approximately `1.8%–43%` at the tested zeros. These exceed the cutoff sensitivity. The residuals are stored per modulus and point.

**The first residue correction is shared by zero and nonzero controls.** The equal-cutoff insertion discrepancy at critical-line points has leading maximum `440/N`, nearly independent of height. The predicted individual correction is

`T_p(N)-T_p(infinity) ~ (p²-1)/(12 N^(2 Re(s)))`

at complete cells. Subtracting it reduces maximum insertion discrepancies at the eight zeros from about `7.44e-4` to `9.5e-9–3.0e-8` at the final cutoff. The same improvement occurs at nonzero controls. This asymptotic prediction is numerical here; the coefficient is suggested by the first moment of the centered residue sequence. It is not evidence for zero selection.

**The tested two-coordinate repairs also fail.** After the cutoff correction, fitting `J_(p,q)` in the span of `T_q` and respectively `q-1`, `q²-1`, or `c_q-1` leaves substantial residuals. For `p=2` at the first zero the residuals are `9.71%`, `9.79%`, and `15.57%`. All fits and condition numbers are retained. This tests precisely these spaces, not every finite-dimensional or nonlinear repair.

## Consequence for the proof attempt

The mixed ordinary-sum construction exposes a real arithmetic correction, not an automatic identification of dilation with replication. Neither dropping that correction nor absorbing it in any of the tested scalar/two-coordinate forms is supported. Its exact finite weighted cocycle survives in Lean (`cellCorrection_cocycle`). An identity valid only at hypothetical strict-right zeros remains untested by actual critical-line zeros and unproved. No RH conclusion or claim of literature novelty follows.
