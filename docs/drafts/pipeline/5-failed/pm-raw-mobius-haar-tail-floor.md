# Raw Möbius Fermi approximation: exact head, forced tail floor

- **ID:** pm-raw-mobius-haar-tail-floor
- **Stage:** 5-failed — exact raw-coefficient sequence retired; positive survivor formalized
- **Type:** NO-GO WITH FORMAL POSITIVE SURVIVOR
- **Source:** Route PM; literal Fermi generators; Möbius floor inversion; corpus critical harmonic-energy obstruction
- **Statement:** The raw coefficients `-μ(d)` reproduce dyadic Haar on `1/(N+1)<t≤1`, but their full `L²(0,1)` error has a cofinal positive lower bound.
- **Novelty:** Exact PM transfer not found in returned source hits or exhaustive Möbius/Fermi/Nyman name co-occurrence search. Global novelty unverified.

## Goal

Test a concrete source approximation, rather than another index receiver. The tempting
conjecture is that an exact expanding head leaves a vanishing tail. Current corpus evidence
suggests this is false even after the Fermi subtraction cancels the harmonic head defect.
A no-go is not closed until the exact head identity, quantitative tail lower bound, and
cofinal positive survivor are formalized.

## Gates

- [x] 0 → 1: literal approximation and proposed obstruction specified
- [x] 1 → 2: audit every continuous/discrete transfer and integrability claim
- [x] 2 → 3: formalize exact head and positive tail floor; actual-leaf and axiom audits
- [ ] 3 → 4: publication and novelty review

## Definitions to use

`φ_d(t)={1/(dt)}-2{1/(2dt)}`, the actual `fermiNymanGen d t`.
`A_N(t)=-sum_{1≤d≤N} μ(d) φ_d(t)`.
`H_N=sum_{1≤d≤N} μ(d)/d`, the existing `deningerHarmonicPartial N`.
On `t>0`, set `E_N(t)=1_(0,1](t)+sum_{d≤N} μ(d){1/(dt)}`.
The literal Haar error is `E_N(t)-2E_N(2t)`; it vanishes for `t>1`.

## Paper mechanism to audit

1. Möbius floor inversion gives `E_N(t)=H_N/t` for every `t>1/(N+1)`.
   This uses the integer floor of `1/t`, not an unsupported extension from integer samples.
   For `t>1`, the target vanishes and every fractional part is its argument.
2. Therefore `A_N(t)=dyadicHaar(t)` whenever `1/(N+1)<t≤1`.
   The harmonic term cancels exactly in the difference.
3. Each `E_N` is square-integrable on the whole positive half-line: it is bounded near zero,
   and equals `H_N/t` beyond one. No infinite-series exchange is required.
4. For any such `E`, set `D(t)=E(t)-2E(2t)`. The pointwise weighted Young inequality
   `4|E(2t)|²≤(3/2)|E(t)|²+3|D(t)|²` and the exact dilation identity
   `integral_0^∞ |E(2t)|²=(1/2) integral_0^∞ |E(t)|²` yield
   `integral_0^∞ |D|²≥(1/6) integral_0^∞ |E|²`.
   The constant is convenient and certified by algebra; no numerical experiment is needed.
5. Step 1 supplies the exact tail contribution
   `integral_(1/(N+1))^∞ |E_N|²=(N+1)H_N²`. Consequently the entire Haar error,
   supported in `(0,1/(N+1)]`, is at least `(N+1)H_N²/6`.
6. Existing `frequent_harmonic_energy_floor` gives `N H_N²≥ε>0` cofinally often,
   unconditionally. Hence the raw Fermi Haar error has a cofinal positive floor and cannot
   tend to zero. This is stronger than merely failing to prove convergence.

The numerical constants and the cutoff endpoint must survive the exact Lean identities.
Do not transfer the discrete Báez–Duarte norm directly to the continuous Fermi norm.
The half-line coercivity and explicit harmonic tail are the proposed bridge.

## Prior research and inspected evidence

- Deep Möbius/Haar source search and critical-line `1+ζD_N` mean-square search each completed
  without partial stages or errors, with complete source inventory but mostly pending/stale
  compiler metadata. Every returned candidate and source statement was reviewed. Neither
  returned an independent approximation producer. Mean-value upper bounds alone do not
  supply convergence to zero; a reported mollified polynomial has nonzero limiting mean square.
- The hybrid finite Möbius/Nyman/head-tail search was partial (text/source retrieval interrupted).
  Its available hits include chronological finite-tail obstructions and divisor-floor residues.
- Exhaustive source text search found `PNTPlus/Consequences.sum_mobius_floor`,
  `MoebiusApproximantResidual.moebius_floor_summatory_le`, and
  `BaezDuarteMobiusCriticalTailObstruction.frequent_harmonic_energy_floor`.
- Inspected the latter module's mechanism and cofinal-floor proof. Its raw modular approximation
  already fails because `N H_N²` cannot tend to zero; the proposed PM transfer must retain that
  positive survivor after the dyadic subtraction. No new source code for this candidate yet.

## Log

- 2026-09-30 — created while the zero-weight endpoint undergoes final audits. Exact arithmetic
  head and half-line coercivity are the next proof obligations. RH remains unproved.
- Additional lexical coercivity search reviewed all 20 returned declarations and their documentation. It found generic operator coercivity, normalized full-line/half-line dilation transport, and `RoutePPrimitiveHankelDepthSquareIntertwiner.integral_normSq_half_dyadic_dilation`, but no exact raw-Fermi tail estimate. Local mathlib source supplies `integral_comp_mul_left_Ioi` and `integrableOn_Ioi_comp_mul_left_iff`; scratch probes remain required. The operator here is `E(t)-2E(2t)` on the full positive half-line. Its coercivity is not positivity of the compressed PM witness form and must not be used as such.
- 2026-10-01 — paper audit closed: finite floor inversion applies at the real argument `1/t`; the strict cutoff makes `floor(1/t)≤N`, including `N=0`. The bounded head and reciprocal tail give square-integrability before the dilation estimate is used. Tail monotonicity and exact support transfer connect the full-half-line estimate to the literal PM norm without a discrete/continuous norm identification. Scratch Lean has verified truncated floor inversion and the generic constant-6 coercivity; arithmetic and analytic bridge scripts are undergoing checks. Existing `frequent_harmonic_energy_floor` was separately axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`.

## Formal certificate and positive survivor

`formal/GaloisForLFunctions/RHTower/FermiNymanRawMobiusTailFloor.lean`
contains 24 declarations in 339 lines. The failed claim is convergence of this exact raw
Möbius sequence, not existence of any Haar approximation.

- `rawMobiusFermiApprox_eq_dyadicHaar`: exact equality on `1/(N+1)<t≤1`.
- `rawMobiusFermiErrorEnergy_eq_tail`: all error energy lies in `(0,1/(N+1)]`.
- `integral_normSq_rawMobiusNymanError_tail`: exact auxiliary tail energy `(N+1)H_N²`.
- `rawMobiusFermiErrorEnergy_lower_bound`: literal error is at least `(N+1)H_N²/6`.
- `frequent_rawMobiusFermiErrorEnergy_floor`: one strictly positive floor recurs cofinally.
- `not_tendsto_rawMobiusFermiErrorEnergy_zero`: unconditional failure of norm approximation.

The positive insight is quantitative energy concentration: exact pointwise reproduction on
an expanding head coexists with unavoidable energy on its shrinking complement. The
half-line difference is coercive, so cancellation of the reciprocal harmonic head cannot
erase that obstruction. The paper proof and this exact positive survivor are formalized.

Validation, 2026-10-01:

- Targeted `lake --old build +GaloisForLFunctions.RHTower.FermiNymanRawMobiusTailFloor:olean`
  passed; own leaf built in 266s. Other jobs reported by Lake were dependency replays.
- Final `lake env lean GaloisForLFunctions/RHTower/FermiNymanRawMobiusTailFloor.lean`
  passed, exit 0 with empty diagnostics.
- Separate `#print axioms` audit passed for all 24 declarations; only `propext`,
  `Classical.choice`, `Quot.sound`. The cofinal-floor and no-convergence types were checked.
- All 24 declaration names have no outside duplicate; leaf wired into `RHTower.lean`.
- Generated indexes refreshed. `scripts/formal_tools.py lint --check-generated` exits 1
  solely for 12 unrelated unwired modules; no own-leaf finding or stale generated index.
  Exceptions: `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
  `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
  `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
  `HamburgerStabilityCriticalLine`, `MoebiusMollifiedCriticalMoment`,
  `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
  `ZetaZeroDensityPowerSaving`, `HTGeometry.HamburgerCriticalLineEvenDefect`.

No full/umbrella build, numerical experiment, new axiom, proof hole, heartbeat increase,
commit or push. RH remains unproved. Next: `1-in-progress/pm-log-smoothed-mobius-haar.md`.
