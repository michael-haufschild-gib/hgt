# JAS Half-Density Double-Log Boundary Residue

- **ID:** JAS-W2-LOGLOG
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE CAPSTONE
- **Source:** `HedenmalmThetaMobiusPrimeNormalHalfDensityDixmierTraceNoGo.lean` · `HedenmalmThetaPhysicalEndpointLogarithmicBoundaryLaw.lean` · `PrimeDiagonalSingularValues.lean`
- **Lean:** `GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue.lean`
- **Statement:** Ordered physical half-density energy has double-logarithmic residue zero on neutral Xi copies and exactly one on every nonneutral copy; global zero residue is equivalent to RH.

## Goal and exact RH chain

Extract strongest positive invariant surviving ordinary Dixmier-trace blindness. Full intended chain:

`Gamma--theta source/grade identity forces double-log residue zero`
→ `theta boundary flux vanishes on every Xi copy`
→ `thetaXiReciprocalEigenvalue² is positive real / internal-only divisor syndrome`
→ `XiPrimePoissonReflectionSewing ρ`
→ `Re ρ = 1/2`
→ RH.

This card constructs and classifies invariant. Remaining hard burden is first arrow: derive zero residue
from actual source-defined Gamma--theta creator/transport, without assuming boundary neutrality.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, leaf `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus derivation

Physical amplitude is signed universal-minus-twisted Gamma channel gap. On a nonneutral copy with
centered-rate magnitude `a > 0`, its square is `p⁻¹(1-p⁻ᵃ)²`. Difference from `1/p` is nonnegative
and bounded above by `2 p^{-(1+a)}`, hence summable. Corpus theorem
`tendsto_primeDiagonalSum_div_logLog` gives residue one for reciprocal-prime reference. On a neutral
copy every physical amplitude vanishes. Corpus search found pointwise logarithmic endpoint laws but
no double-logarithmic partial-energy residue for this literal half-density.

## Paper proof `[PROVED HERE]`

For Xi copy `q`, define

`E_q(N) = ∑_{n≤N} a_{p_n}(q)^2`

and correction

`c_q(p) = 1/p - a_p(q)^2`.

Universal amplitude bounds imply `c_q(p) ≥ 0`. Expanding channel gap at centered rate `t` gives

`c_q(p) ≤ 2 p^{-(1+|t|)}`.

If boundary flux is nonzero, corpus rate/flux identity gives `t ≠ 0`; prime-power summability then
gives `∑_p c_q(p) < ∞`. Exact finite identity

`E_q(N) = ∑_{n≤N} 1/p_n - ∑_{n≤N} c_q(p_n)`

and `∑_{n≤N} 1/p_n / log log N → 1` therefore yield `E_q(N) / log log N → 1`. If flux is zero,
same-copy physical amplitude vanishes at every prime, so `E_q(N)=0` and normalized limit is zero.
Uniqueness of limits gives both converses. Quantifying zero residue over all Xi copies and applying
`thetaGreenBoundaryNeutral_iff_riemannHypothesis` gives RH equivalence.

## Lean certificate

Main declarations:

- `thetaMobiusPrimeNormalHalfDensityEnergyPrefix`
- `thetaMobiusPrimeNormalHalfDensityEnergyCorrection`
- `thetaMobiusPrimeNormalHalfDensityEnergyCorrection_nonneg`
- `thetaMobiusPrimeNormalHalfDensityEnergyCorrection_le`
- `summable_thetaMobiusPrimeNormalHalfDensityEnergyCorrection_of_rate_ne_zero`
- `thetaMobiusPrimeNormalHalfDensityEnergyPrefix_eq_primeDiagonalSum_sub_correction`
- `tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_of_boundaryFlux_ne_zero`
- `tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_of_boundaryFlux_zero`
- `tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_boundaryFlux_zero`
- `tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_iff_boundaryFlux_ne_zero`
- `all_tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_riemannHypothesis`

Verification on 2026-08-29:

- direct `lake env lean` PASS
- leaf `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue` PASS (`12796/12796`)
- axiom audit PASS: only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions.RHTower`
- formal lint found no forbidden declaration here; global lint remains red only on unrelated existing umbrella-reachability errors

## Novelty audit

Search through 2026-08-29 found general singular-trace and prime spectral literature, but no exact
Gamma channel-gap double-log residue or RH classification. Status: `[NOVELTY UNVERIFIED]` pending
expert review.

## Route consequence

Ordinary `log N` Schatten normalization is provably blind, while prime-natural `log log N`
normalization is exactly quantized: zero on neutral copies, one on all nonneutral copies. Any valid
Gamma--theta identity proving universal zero residue therefore closes RH through existing corpus
equivalences. Research now targets that source identity, not further bound optimization.

## Log

- 2026-08-29 — created directly in 1-in-progress from proved ordinary-residue blindness.
- 2026-08-29 — paper proof closed and formalized; leaf build and axiom audit passed; promoted to stage 3.
