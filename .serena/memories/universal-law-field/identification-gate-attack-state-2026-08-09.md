# Identification-gate attack state — 2026-08-09 (Claude)

Card: `1-in-progress/universal-law-field/identification-gate-reduction-attack.md` (§§1-11).

## Where it stands

ULF-INV-9 asked whether the Weil-polarization lane's last gate (identifying the Hermitian
extension with tests' own prime sums) is wall-grade. Answer emerging: NO for the decisive class,
YES at most for the broad algebra. Chain of source-verified facts:

1. Every test evaluation lies in the closed Cauchy core (`XiWeilCauchyCoreMultiplicity.lean:425`)
   — the mean-zero complement carries NO tests (refuted my §6 candidate class).
2. Rectangular family already has the full sharp identity
   (`rectangularCorrectedXiWeilValue_eq_primePolarSource`).
3. Eigen-evaluations are FIBER DELTAS (from `(alpha+z)F = -XiC z`) — explains antidiagonal Gram;
   decisive class = delta family.
4. Eigen-pair prime side is ABSOLUTELY convergent (decay e^{-|x|} at zeros — rate 1 > 1/2);
   strip hypothesis |Im| < 1 unconditional for all zeros. No summability obstruction.
5. Delta approximation needs NO simplicity: eigen-delta is fiber-constant; single-anchor
   normalized packets converge to fiber-constant directions (simplicity governs core density,
   not the delta family).
6. The hard two-variable limit exchange is BYPASSED by the corpus's own device: integrate the
   ODE (D+alpha)u = -k against the distribution (no Fubini); boundary terms vanish by rate-1
   decay at zeros.
7. All ingredients located in source: transform identities (HedenmalmThetaEigenTransform),
   packet-limit theorem (XiQuotientRealDecay:354), kernel form (XiRelativeResolventFlux:84),
   theta-source identity k_N = R_N(1/2)a + summability (ThetaCuspFinitePrimeSource).

## Remaining work (bounded, next major cycle)

The derivation itself: two integrations by parts (boundary terms die by rate-1 decay), reduce
cross pairings to the theta-source n^{-1/2} log-translate series, archimedean normalization
(logDeriv archFactor against removable quotients, (18a) substrip decay). Output on completion:
- ULF-INV-9 wall suspicion: recorded DEATH on the decisive class.
- Positive survivor: "eigen-span positivity <=> RH + simplicity" in genuine prime-sum form —
  a new exact group-3 producer with the interchange closed; the lane's last analytic gate done
  at paper level. Lean certification in a Lean-enabled session afterward.

## Cap landing (kept for the broad-algebra half)

`sq_le_prime_mass_of_uniform` (`Sieve/UniformDistanceAverage.lean:247`) hypothesis shape:
uniform pretentious-distance lower bound vs charFn over |t| <= T, f bounded by 1. Bridge =
corpus Halász dictionary (`multiplicative_euler_bound_distance_form`). Only relevant if the
broad-algebra no-go is pursued after the decisive-class positive result.

## Session discipline notes

Three candidate objects refuted by one-grep reads this session (Hadamard/Schur; mean-zero
class; wall suspicion on decisive class trending false). Read before conjecturing, always.
