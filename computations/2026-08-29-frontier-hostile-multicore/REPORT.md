# Frontier hostile multicore computation

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Verdict

**S6F/TCD survives and is sharply strengthened.** The exact physical rank-three reflected eighth
determinant is positive on every one of 13,700 Arb interval boxes covering
`0 <= x <= 137/2000`. The weakest computed lower enclosure is
`1.9293714407994698e10`. A separate 1,000,001-point scan and 100-digit checks found minimum value
`2.0043635926393831e10` at the seam `x=0`; no negative value occurred. Thus the missing compact
physical chamber did not kill S6F/TCD. The computationally selected next conjecture is exact
physical-orbit positivity on this interval, followed by the already-open cofinal/all-order landing.

**C5 survives a much broader hostile scan.** The exact C5 action/barrier expression was positive at
all 361,200 tested points on `0 <= u <= 20`, `1e-6 <= t <= 100`. The minimum is the expected
`t -> 0` seam degeneration. The minimum sampled seam-normalized value `C5/A^2/t^4` was
`633.4927717822768`; no non-seam negative pocket was found. This is evidence, not a global result,
because the physical `(u,t)` domain is noncompact.

No route was killed by this batch. It removes the main numerical doubt from the compact S6F/TCD
interval and strengthens the C5 conjecture without changing either statement's proof status.

## Exact objects computed

The S6F/TCD job transcribes the literal source

```text
Phi(x) = sum_(n>=1) [4 pi^2 n^4 exp(9x/2-pi n^2 exp(2x))
                     -6 pi n^2 exp(5x/2-pi n^2 exp(2x))]
```

from `ThetaCuspFinitePrimeSource.lean`. Derivatives through order eight use the exact recurrence

```text
P_(m+1)(c) = (a-2c) P_m(c) + 2c P'_m(c),   c=pi n^2 exp(2x).
```

Those jets are inserted into the exact reflected products and determinant appearing in
`modularThetaReflectedEighthGeneralPolynomial` and
`thetaCuspFullSource_reflectedEighthHankel_eq_generalModular`.

The Arb pass used 256-bit balls, 13,700 equal boxes, source terms `n<=20`, and an explicit absolute
tail radius for each derivative order. The largest omitted-tail radius, at order eight, was below
`4.58e-567`. Every box had strictly positive lower endpoint. The recorded minimum box is an
interval-arithmetic enclosure minimum, not the location of the true function minimum.

The C5 job evaluates the corpus identities

```text
C5 = 24 A^2 - 9 t A D + t^2 (5 A J - 4 D^2)
C5/P^2 = 24 r^2 - 9 t r q1 + t^2 (5 r (q2-q1^2) - 4 q1^2)
```

at 60 decimal digits, checking both presentations pointwise.

## Consequences and boundaries

- `[CONJECTURE]` S6F/TCD physical-orbit positivity on `0 < x < 137/2000` survives a compact
  interval attack with a large margin. Next work should seek an interval-free analytic
  factorization or monotonic/chamber proof. Computed boxes must not be imported as Lean premises,
  certificates, tactics, or decision procedures.
- `[CONJECTURE]` C5 physical-trajectory nonnegativity survives the expanded scan. A proof still
  needs asymptotic control of the noncompact ends plus a compact analytic argument.
- F2 was not numerically evaluated. Its exact source moment uses the infinite-dimensional Sonin
  projection and an abstract Hilbert basis. Corpus contains no convergent numerical realization of
  that operator. A naive finite Fourier/Galerkin model changes the aperture fibre and cannot kill
  F2. The earlier recommendation to treat F2 as an immediately executable root-isolation problem
  was premature; a validated Sonin projection discretization is a prerequisite.
- O was not numerically evaluated. Its finite head is source-selected by the peripheral spectral
  subspace of an infinite-dimensional Gamma--Slepian Gram. Corpus proves finite dimensionality but
  does not expose a concrete matrix or certified Galerkin convergence. An arbitrary truncation
  would not test the stated O inequality.
- T2's direct shell computation was already completed and killed in
  `../2026-08-29-t2-common-mode-exponent-triage/REPORT.md`. Its surviving selected-cell computation
  awaits a literal all-shell arithmetic selection law; no such object is currently defined, so no
  generic packet proxy was rerun.
- U's raw covariance/null-current computations already have exact Lean answers. Remaining issue is
  a fixed-carrier diagonal source law. Optimizing a carrier independently at each finite scale
  would be adaptive and scientifically invalid; no such computation was run.
- E's existing sublinear factor-replacement relation is already rigorously falsified. Remaining
  route asks for a new source-predeclared relation. None is specified, so a data-selected matching
  tournament would be circular and was not run.

These are definition/readiness obstructions, not negative computational outcomes for F2, O, T2,
U, or E.

## Reproduction

Runpod: 128 CPUs, Python 3.12.3, NumPy 2.5.2, mpmath 1.4.1, python-flint 0.9.0. BLAS/OpenMP thread
counts were pinned to one per worker. Wall time was 248 seconds.

```bash
/root/frontier-venv/bin/python run_experiments.py \
  --output results --workers 128 \
  --s6f-points 1000001 --arb-boxes 13700 --arb-bits 256 \
  --c5-u-points 241 --c5-t-points 900

python3 verify_results.py .
```

- `results.json`: compact parameters and extrema
- `s6f_arb_boxes.jsonl`: all interval enclosures
- `run_experiments.py`: complete multicore source transcription
- `verify_results.py`: independent artifact consistency checks
- `run-output.txt`, `verify-output.txt`, `environment.txt`, `SHA256SUMS`: audit metadata

No Lean source, theorem, proof, or umbrella was changed or built. No computation result may be used
in a Lean proof.
