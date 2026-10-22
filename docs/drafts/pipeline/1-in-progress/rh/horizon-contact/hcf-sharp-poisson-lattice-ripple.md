# HCF sharp Poisson lattice ripple

- **ID:** HCF-SHARP-POISSON-LATTICE-RIPPLE
- **Stage:** 1-in-progress (analytic component formalized; producer ceiling open)
- **Type:** THEOREM (Lean) + falsified producer shortcut
- **Source:** HCF source-Plemelj / canonical lattice-summed displacement route
- **Statement:** The periodized HCF profile has exact zero mode `2π`, nonzero Fourier charge at most `37/200`, and total finite-lattice charge at most `9`.

## Goal

Replace the old quartic majorant in the fused HCF source gate by the exact Poisson envelope and test
whether uniform lattice control alone can force the source-only covariance ceiling needed for the
`75%` endpoint.

## Gates

- [x] 0 → 1: source-independent profile, exact Fourier attack, existing HCF gate identified
- [x] Paper proof: transform, Poisson identity, geometric envelope, rational tail estimate
- [x] Lean component: `HedenmalmCriticalFeatureSharpLatticeCharge.lean`; targeted build and axiom audit pass
- [ ] Producer gate: signed pole--Gamma covariance bounded by `21 N / 100 + o(N)`
- [ ] Endpoint transfer: unconditional lower density at least `3/4`

## Corpus audit

Whole-corpus `formal_tools.py research` searches covered HCF Fourier/Poisson profiles, source-only
Plemelj covariance, positive-shift pole--Gamma density, finite-displacement fusion, Gamma vertical
line bounds, and von-Mangoldt lattice cancellation. No prior exact HCF Fourier envelope or uniform
periodization-ripple theorem was present. Existing source results already identify corrected budget
with pole--Gamma Plemelj covariance plus an `o(N)` von-Mangoldt channel; they do not control the
signed covariance at the required constant.

## Proved component

In `HedenmalmCriticalFeatureSharpLatticeCharge.lean`:

- `fourier_criticalFeatureRealBoundaryWeight_zero` proves
  `F[4/(1+x²)²](ξ) = 2π(1+2π|ξ|) exp(-2π|ξ|)` under the corpus Fourier convention.
- `criticalFeatureFourierLatticeEnvelope_eq` evaluates the full absolute Fourier envelope as a
  geometric-series expression.
- `criticalFeatureFourierLatticeEnvelope_sub_two_pi_le_thirtySeven_twoHundred` proves all nonzero
  modes together cost at most `37/200`.
- `abs_tsum_criticalFeatureRealBoundaryWeight_sub_two_pi_le_thirtySeven_twoHundred` proves the
  physical periodization differs from its exact zero mode `2π` by at most `37/200`, uniformly in
  height.
- `criticalFeatureLatticeBoundaryCutoffWeight_le_nine` proves every fused finite center/cutoff
  weight is at most `9`, replacing `1024 * intNatAbsPowTotal 4`.

## No-go closure

- **Exact killing mechanism:** The conjecture that the pointwise lattice ceiling alone yields the
  `21/100` source covariance ceiling fails. After Poisson separation, the zero Fourier mode is the
  total-mass channel. In the corrected HCF identity that channel is precisely where off-line mass
  remains; bounding it independently would assume the quantity being estimated. Moreover the
  subcritical positive-shift pole--Gamma density is signed, so absolute-value domination discards
  the cancellation needed for `21/100` or `4/25`.
- **Strongest positive survivor:** Nonzero height aliases are uniformly at most `37/200`, already
  below `21/100`. Thus any excess over the target must enter through the zero mode or through a
  failure to preserve signed Fourier cancellation in the source scalarization.
- **New insight:** Remaining producer can be narrowed to a source-side zero-mode cancellation plus
  a signed nonzero-mode estimate for the fused pole--Gamma/von-Mangoldt observable. Better windows,
  larger center sets, and unsigned `L¹` estimates cannot close this gate.
- **Status:** Positive survivor is dependency-closed and formalized. Quantitative source covariance
  ceiling remains open; no `75%` theorem is claimed.

## Verification

- `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSharpLatticeCharge`: PASS
  (`13734/13734`).
- `#print axioms` for all 21 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- Global `scripts/formal_tools.py lint`: umbrella reachability currently blocked by concurrent,
  intentionally frozen imports; no change to the frontier map or umbrella was made here.

## Log

- 2026-08-30 — exact transform, Poisson envelope, `37/200` ripple, and finite-cutoff `≤ 9`
  formalized; unsigned producer shortcut retired with positive survivor.
