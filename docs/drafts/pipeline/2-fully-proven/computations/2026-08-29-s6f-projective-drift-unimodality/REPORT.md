# S6F projective-drift and raw-unimodality hostile follow-up

**Date:** 2026-08-29  
**Scope:** diagnostic route selection only; no output is admissible in a Lean proof

## Computed objects

For the actual completed theta source on `0 <= x <= 137/2000`, the run evaluated source jets
through order ten and derived:

- raw reflected rank-three D1 and its first two derivatives;
- projective D1 derivative numerator `N = Q L(P) - 6 P L(Q)`;
- normalized derivative `N / Q^7`;
- Arb interval enclosures with explicit Gaussian-tail radii.

RunPod command used 128 foreground workers, 2,000,001 dense points, 27,400 Arb boxes, and
256-bit precision. Runtime was 12.17 seconds under Python 3.12.3, NumPy 2.5.2, and python-flint.

## Outcome

- Dense scan found no negative projective numerator and no sign change.
- Arb certified the projective numerator positive on every box from `0.00211` through
  `137/2000`; 26,556 boxes were positive, none negative. The 844 boxes from `0` through
  `0.00211` were unresolved.
- Dense raw derivative had one sign-change bracket:
  `[0.0544456495, 0.05444568375]`.
- Dense raw second derivative had one sign-change bracket:
  `[0.03041766475, 0.030417699]`.
- Arb certified raw derivative positive on most of `[0.0193, 0.0383925]` and negative on
  `[0.0637375, 0.0685]`; dependency inflation left the intervening root region unresolved.
- Arb certified raw second derivative negative on `[0.037685, 0.0685]`.
- All Arb source boxes were positive. Order-zero through order-ten tail radii ranged from
  approximately `4.27e-595` to `4.68e-560`.

The floating-point projective value reported at `x = 0` is cancellation noise, not a positive
seam value. A computation-free corpus audit subsequently proved that projective D1 is even,
`Q` is even, the projective numerator is odd, and therefore `N(0) = 0` exactly.

## Interpretation

1. **Raw monotonicity is a bad target.** Raw D1 rises and then falls. The surviving competing
   raw route is a one-critical-point/unimodality theorem plus endpoint positivity.
2. **Projective monotonicity survives this attack.** No counterexample was found, and Arb proves
   its sign away from the seam. This remains evidence, not proof.
3. **Correct seam target is desingularized.** Because `N` is exactly odd, direct interval
   evaluation of `N` near zero suffers forced cancellation. Future work should factor the exact
   zero and attack `N(x)/x`, with its seam value supplied by exact second variation.
4. **Next useful computation is certificate discovery.** Express `N/x` in parity-adapted modular
   coordinates and search for an exact polynomial shear, Bernstein/SOS decomposition, or invariant
   cone. Any discovered identity must be rederived symbolically before Lean formalization.

These results neither prove positivity on the unresolved seam range nor establish uniqueness of
either sampled sign change.

## Reproduction and verification

Run on a host with python-flint:

```bash
/root/frontier-venv/bin/python run_experiments.py \
  --workers 128 --points 2000001 --boxes 27400 --bits 256 --output results
```

`verify_results.py` independently checks parameters, summary counts, box ordering, coverage, and
reported signs. `SHA256SUMS` authenticates downloaded artifacts.

## Artifacts

- `run_experiments.py` — multicore dense/Arb driver
- `results.json` — compact summary
- `arb_boxes.jsonl` — all interval-box records
- `run-output.txt` — captured summary output
- `verify_results.py` — independent structural verifier
- `SHA256SUMS` — artifact hashes
