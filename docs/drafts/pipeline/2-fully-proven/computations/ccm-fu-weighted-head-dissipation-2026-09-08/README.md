# Fixed head weights: complete paths versus arbitrary-state extension

RunPod diagnostic only; no numerical result enters Lean.
[Frozen protocol](../../../1-in-progress/ccm-fu-weighted-head-dissipation.md).

For actual retained energy Q, head H and V=Q-H², test the fixed potential
`L_alpha=V+alpha H²` for every weight in [0,1], without a sampled grid.

## Result

Across all 8,860 stored subset states at cutoffs 1..32, some complete
monotone path exists at each cutoff for every weight in the common
interval from zero to approximately 0.20099786271898004. Its successive
restrictions occur at cutoffs 7, 11 and 19. The relaxed and tightened
upper endpoints are respectively 0.20099786272276013 and
0.20099786271521156. Positive weights in this range retain head control;
zero does not. These are finite diagnostic results, not uniform bounds.

In contrast, no fixed weight provides a nonincreasing next operation at
every proper state. The first incompatible cutoff is 25, which already
has no such weight by itself. Two of its literal states expose the cause:

| Processed core | Remaining primes | Diagnostic weight requirement |
| --- | --- | --- |
| {2,3,5,11,13,17,19,23} | {7} | Small head weight: its same-sign scalar absorption grows H² |
| {2,7,11,13,17,19,23} | {3,5} | Larger head weight: H² must pay for forced V growth |

At the first state H is approximately -0.5241055663503245 and the
remaining leaf is -0.01860694309553673. At the second, the four
coordinates are H=-0.7388053478086111, a=0.008181375865577394,
b=0.01386478194178246 and c=0.1740466805553899.
Full interval certificates, all restrictive states and their affine
transition coefficients are retained in summary.json.

The complete-path claim survives this screen. The arbitrary-state
extension rule does not. A failure of the latter is not a falsification
of the former: an ordering can avoid states from which it cannot continue.

## Method and independent audit

The primary screen reads the existing subset-states.csv and reconstructs
heads from isolated late-prime energy differences, checking every late
anchor. It regenerates no arithmetic channels. Each edge imposes
`Delta V+alpha Delta(H²)≤0`. Exact fractions of the recovered binary
floating-point values represent its interval endpoints. Dynamic
programming propagates interval unions through every subset state.
Separate intersections test complete paths and universal local descent.

The two tolerance runs use right sides ±1e-12 max(1,Q(empty)). Exact
fraction operations eliminate additional interval-algebra roundoff;
they do not turn floating-point source data into mathematical proof.

Independent 80-digit reconstruction evaluates the defining divisor
defects and signed Abel channels at every restrictive cutoff:
5,7,8,9,10,11,17,18,19,20,25. It reconstructs every retained field at
those cutoffs and repeats both graph tests with tolerance
1e-60 max(1,Q(empty)). It confirms the incompatibility at 25 and the
reported complete-path endpoint. No range or assertion was changed.

## Execution and provenance

- Supplied RunPod; eight workers; one-thread numeric libraries.
- Screen plus independent audits: 0.8151 seconds.
- Internal deadline 50 seconds; external timeout 60 seconds.
- One mathematical run; no range extension or rerun.
- Downloaded result and script hashes match remote copies.
- Removed the three owned files and remote directory
  /tmp/ccm-weighted-head-1EPN3TcE. Foreground job exited; no owned worker
  remained. Remote process inspection used grep after rg proved absent.

| Artifact | SHA-256 |
| --- | --- |
| screen.py | 34dfbe18a2a740ef50e935bea8e6efe2c629af27a0cfba4b1cfc011c0dcb4f69 |
| summary.json | 8e8925d63f802e8251fbddff75c6b130ada578f909db4ad1a39ca91ecb9ec841 |
| Input subset-states.csv | ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9 |

The [analytic Lean certificate](../../../3-formalized/ccm-fu-weighted-head-state-selection.md)
now proves the two-state incompatibility and BOTH exact positive completion
intervals, with `0<beta<1/20<sigma<1/5`. Seven new theorem audits use
only standard Lean axioms; no numerical value supplies a proof premise.
