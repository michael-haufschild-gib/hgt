# Gamma three-grade delay and root-port observability, formalized

- **ID:** `suzuki-gamma-three-grade-delay-root-observability`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-gamma-three-grade-delay-root-observability.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootPortFirstGradeObservability.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRootPortObservationGram.lean`
  - carrier: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiSupportPrunedSelfAdjointSeamCarrier.lean`,
    `SuzukiSupportPrunedSeamCarrierBounds.lean`, `SuzukiPrimeValuationSeam.lean`

## Formal content

| Card | Lean |
|---|---|
| `(8)` endpoint root trace | `suzukiRootTraceVector`, `suzukiRootTraceVector_apply` |
| `(9)` full prime adjacency | `suzukiFinitePrimeAdjacency` at `suzukiPrimePowerStep`, `suzukiPrimePowerWeight` |
| `(24)` admissibility count | `suzukiLeftRoot_step_admissible`, `suzukiRightRoot_step_admissible`, `suzukiLeftRoot_negStep_not_admissible`, `suzukiRightRoot_negStep_not_admissible` |
| `(25)` exact survivor coordinates | `suzukiRootPortObservation_left_coordinate`, `suzukiRootPortObservation_right_coordinate`, `suzukiRootPortObservation_eq_zero` |
| `(11)` exact observation Gram | `suzukiRootPortObservation_norm_sq` (general injective visible alphabet), `suzukiRootPortObservation_primePower_norm_sq` (Suzuki's alphabet, `c_a² = ∑ (log p)²/p^j`) |
| `(10)` the Gram constant | `suzukiPrimePowerWeight_sq`, `suzukiRootPort_gram_pos` |
| `(14)` visibility threshold | `two_visible_of_gt_half_log_two` |
| no dark trace at first grade | `suzukiRootPortObservation_ne_zero`, `suzukiFirstGrade_rootTrace_injective` |
| same-end collision exclusion | `primeSeamCoordinate_injective`, `primePowerStep_injOn` |

## What the card actually closes

The oriented root-retained carrier hides no endpoint half-log trace: one strictly visible prime
step separates both root coefficients (`suzukiFirstGrade_rootTrace_injective`), and the full
first-grade observation is an exact scaled isometry

```text
‖P T β‖² = c_a² (‖β₋‖² + ‖β₊‖²),   c_a² = ∑_{p^j visible} (log p)²/p^j > 0  for a > (log 2)/2,
```

with the admissibility count proved literally: from each root exactly one arm of each symmetric
step survives strict-aperture compression, and the survivors are pairwise orthogonal because
distinct visible prime powers have distinct valuation labels and the two root sectors stay
orthogonal even at coinciding physical positions.

## Hypotheses

Everything is object data: the aperture, the finite visible alphabet with `j ≥ 1` and strict
visibility `p^j < e^{2a}`, and the trace coefficients.  No completed-domain carrier map is
assumed; no RH, no numerical certificate.  No `sorry`, `axiom`, `opaque`, or `unsafe`.  Every
theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The analytic sharp asymptotic `(4)`–`(7)` (Watson–dyadic nonstationary phase for the literal
Gamma multiplier) rests on the Hilbert-valued oscillatory Gamma theorem, which the card names as
shared analytic infrastructure still absent from Lean and deliberately not introduced as an axiom;
it is a stated scope decision, not a silent gap.  The open gates are research: the
completed-source normal-family intertwining, the trace-zero weighted source gate, and RH.
