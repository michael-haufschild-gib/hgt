# Logarithmic Möbius approximation at the weighted endpoint

- **ID:** pm-log-mobius-weighted-endpoint
- **Stage:** 3-formalized
- **Type:** PROVED UNCONDITIONAL WEIGHTED SOURCE
- **Source:** Route PM; exact logarithmic Fermi head; PNT Chebyshev-error integrability; linear Barban–Vehov mass
- **Formalized statement:** For some `C≥0` and every `N≥2`, the literal logarithmic Fermi error satisfies
  `∫_(0,1] t |h-A_N^log|² dt ≤ (N+1)^(-2)+(C+9)/(log N)²`, hence tends to zero.
- **Scope:** Weighted norm `t dt`. The canonical PM target uses `dt`; no transfer to it is asserted.
- **Novelty:** No exact weighted construction/rate in the reviewed deep-search hits; exhaustive source audit remains.

## Why this candidate

The canonical log-smoothed head is exactly the dyadic Chebyshev discrepancy divided
by `log N`. The available unconditional PNT estimate supplies one additional power
of the reciprocal variable. Rather than silently discard that weight, retain it and
identify precisely what the source currently proves. This also connects to the
previously formalized singular zero-weight witness domain.

## Dependency-closed paper argument to audit

Write `e(x)=ψ(x)-x`, `Q(x)=ψ(x)-2ψ(x/2)=e(x)-2e(x/2)`.
The global Chebyshev bound gives `|e(x)|≤Kx` for `x>0`, with `K≥1`.
The PNT input gives absolute integrability of `e(x)/x²` on `(1,∞)`.
Local boundedness extends it to `(1/2,∞)`. Let

`J=∫_(1/2)^∞ |e(x)|/x² dx`, a finite nonnegative constant.

For `x≥1`,

`Q(x)² ≤ 2e(x)²+8e(x/2)² ≤ 2Kx|e(x)|+4Kx|e(x/2)|`.

Divide by `x³`, integrate, and substitute `u=x/2` in the second term.
This gives `∫_1^∞ Q(x)²/x³ dx ≤ 4KJ`. Set `C=4KJ`.
The substitution `x=1/t` gives

`∫_(0,1] t [2ψ(1/(2t))-ψ(1/t)]² dt ≤ C`.

Now fix `N≥2`, `c_N=1/(N+1)`. The exact Fermi head formula yields

`∫_(c_N,1] t |h-A_N^log|² dt ≤ C/(log N)²`.

The source coefficient mass is bounded independently of a logarithmic loss:
`Σ_(d≤N) |μ(d)log(N/d)| ≤ N`. Since `|φ_d|≤3` and `|h|=1`,

`|h-A_N^log| ≤ 1+3N/log N`.

Thus the unchanged small-`t` tail is at most

`(c_N²/2)(1+3N/log N)² ≤ c_N²+9/(log N)²`.

Add the two nonnegative pieces. Both terms of the resulting upper bound tend to
zero. There is no exchange of an infinite Möbius series with an integral and no
zero-location or zero-simplicity premise.

The reciprocal substitution and absolute integrability must be formalized before
using these improper integrals. The proof controls `Q²/x³`, whereas the canonical
head requires `Q²/x²`; the missing power is an unresolved arithmetic estimate.

## Inspected source inputs

- `FermiNymanLogMobiusHead.dyadicHaar_sub_logMobiusFermiApprox`: actual logarithmic
  Fermi head identity; targeted build, final actual-leaf and all 13 axiom audits passed.
- `Sieve/BarbanVehovLinearL1.sum_abs_barbanVehovWeight_le_linear`: exact coefficient
  absolute mass at most `N`; full 77-line module inspected.
- `MertensVonMangoldtEulerConstant.chebyshevError`: literally `Chebyshev.psi x-x`.
- `MertensVonMangoldtEulerConstant.integrableOn_chebyshevError_div_sq`: unconditional
  absolute integrability on `(1,∞)`; statement and tail proof inspected.
- `ChebyshevPsiErrorInputs`: unconditional PNT error and discrete weighted summability;
  the continuous integral theorem above avoids replacing the integral by samples.
- Prior Mellin/Plancherel search was partial because local model returned malformed JSON.
  All 20 available candidate and 20 source-argument statements were reviewed. Its
  stronger Chebyshev power bounds assume RH or a half-plane bound. Available hits
  nevertheless identified the unconditional error-integrability input used here.

## Gates and log

- [x] Literal source and precise weighted target specified.
- [x] Audit paper proof, exact constants, interval endpoints, and novelty.
- [x] Scratch-check every reused API; formalize bound and convergence.
- [x] Targeted build, final actual-leaf, axiom, wiring, index and lint audits (global lint has unrelated failures).
- 2026-10-01 — candidate recorded before new weighted-endpoint Lean code. Current
  research query targets prior weighted Nyman/Fermi approximation. The canonical
  log-smoothed card remains open; RH remains unproved.
- Deep weighted-approximation search completed with `partial=false`, no errors and
  complete source inventory; compiler metadata mostly pending/stale. All 20 candidate
  and 20 source-argument statements reviewed. It returned the new raw norm bounds,
  generic logarithmic integrals and unrelated Möbius action identities; no matching
  weighted convergence/rate theorem. The suggested ingredient set does not supply
  the required reciprocal-variable square estimate and was not accepted as a proof.

- Paper audit: constants and the split at `1/(N+1)` check out. The Lean proof may
  take `C` to be the actual nonnegative dyadic integral instead of `4KJ`; the
  latter is only needed to prove finiteness. Reciprocal transport uses `Ici 1`
  as the exact image of `Ioc 0 1`, with its singleton removed by atomlessness.
  Exhaustive relevant source search found no earlier weighted rate.

- Scratch formalization passed with empty diagnostics. New source leaf
  `ChebyshevDyadicWeightedEnergy` has 12 declarations / 148 lines; approximation
  leaf `FermiNymanLogMobiusWeightedEndpoint` has 11 declarations / 177 lines.
  Exact integrability, the reciprocal integral identity, coefficient bound,
  head/tail rate and unconditional weighted convergence are proved. All 23 names
  are unique; both leaves wired. Targeted build and final audits in progress.
- Next-mechanism search (dyadic Chebyshev energy, logarithmic approximation,
  multiple zeros, Mellin lower bound): `partial=false`, no errors, full 63,545-file
  inventory; compiler metadata predominantly pending/stale. All 20 candidate and
  20 source-argument statements reviewed. Returned power bounds have explicit
  error-spectrum/half-plane premises; the proposed ingredient set does not prove
  a multiplicity obstruction or canonical decay. A focused logarithmic-harmonic
  tail search follows; no additional mathematical conclusion accepted yet.

## Final formalization certificate — 2026-10-01

- `ChebyshevDyadicWeightedEnergy`: 12 declarations, 148 lines. Unconditional
  `Q²/x³` integrability, exact reciprocal transport, and `t Q(1/t)²` integrability.
- `FermiNymanLogMobiusWeightedEndpoint`: 11 declarations, 177 lines. Literal
  coefficient bound, head/tail estimates, rate and weighted error convergence.
- Main results: `weightedLogMobiusFermiErrorEnergy_le` and
  `tendsto_weightedLogMobiusFermiErrorEnergy_zero`. The convergence theorem has
  no hypothesis. The rate has only its literal cutoff restriction `2≤N`.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanLogMobiusWeightedEndpoint:olean`
  passed, building source leaf in 76s and approximation leaf in 147s.
- Final direct `lake env lean` checks of both actual leaves passed, exit 0 with
  empty diagnostics. All 23 separate `#print axioms` checks passed using only
  `propext`, `Classical.choice`, `Quot.sound`; both main types checked.
- All names unique in the owned Lean tree, one umbrella import per leaf, all 23
  API entries present once, scoped whitespace clean. Index generation passed.
- `scripts/formal_tools.py lint --check-generated` exits 1 only for the 11 unrelated
  unwired modules listed below; no generated drift or finding in the new leaves.

Unrelated lint findings at this snapshot: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
`ZetaNotchTwistPolynomialEnvelope`, `ZetaZeroDensityPowerSaving` (all in `RHTower`).

The result does not establish the canonical PM norm estimate. The exact remaining
weight gap is retained in both leaf documentation and the frontier map. No full or
umbrella build, numerical experiment, added axiom, proof hole, heartbeat increase,
commit or push occurred. The successor is now formalized in
`3-formalized/pm-log-mobius-auxiliary-variance.md`; RH goal remains active.

Cleanup: all owned search, build, direct-leaf and axiom jobs completed; all 19
owned temporary files from this iteration removed after their results were recorded.
