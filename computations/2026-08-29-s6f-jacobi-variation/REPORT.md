# S6F scale-velocity Jacobi/Loewner test

Date: 2026-08-29
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Route question

Can native D1 scale monotonicity be explained by matrix order rather than direct expansion? Let
`H(X,w,y)` be the signed even-jet `3 x 3` Hankel matrix whose determinant is D1. On the Lean-proved
refined cone, test whether its scale velocity `H_X` is strictly positive definite. If true, D1
scale increase follows conceptually from Loewner/Jacobi monotonicity once `H` is positive definite;
one negative principal minor kills this mechanism while leaving direct D1 alive.

## Outcome

- All three diagonal entries of `H_X` have strictly positive exact half-prism Bernstein
  certificates.
- All three rank-two principal minors do too.
- The rank-three determinant has degree `(9,45,24)` in scale slack, normalized clock square, and
  wall interpolation. All 10,375 exact half-prism Bernstein coefficients are strictly positive.
- Independent face reconstructions also give strict positivity on seam (10 coefficients) and the
  dangerous outer scale-floor/upper-clock face (25 coefficients).

Thus the computation opens a new S6F mechanism:

```text
on refined cone: H_X is positive definite
therefore H increases strictly in Loewner order with scale slack
therefore det(H) increases once base-scale H is positive definite.
```

This converts the old scalar derivative burden into one matrix-velocity theorem and aligns the
rank-three route with its natural Hankel geometry. It does not prove D1, clock concavity, outer-face
positivity, finite-order-5 positive definiteness, or cofinal landing.

## Proof boundary

No Bernstein coefficient, digest, or sign count may enter Lean. Next research task is a compact
source-derived Gram/SOS or Schur-complement decomposition of `H_X`; only an independently proved
analytic decomposition can discharge scale variation. Raw 10,375-term formalization is excluded.

## Reproduction

RunPod reconstructed the five signed reflected jets from the exact three-state modular Lie
recursion, transformed them to intrinsic `(X,w,y)` coordinates, differentiated before cone
localization, and tested every principal minor using exact rational arithmetic. `run_experiments.py`
contains both rank-two and determinant modes. Artifacts include exact results, face audits, logs,
verifier, environment metadata, and checksums.
