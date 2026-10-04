# SZ supported modulation phase recovery

- **ID:** sz-supported-modulation-phase-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route SZ; `../1-in-progress/sz-first-contact-multiplier-identity.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilModulationPhaseRecovery.lean`

## Exact new result

Let Q_a be the literal complete restricted Weil quadratic, P_a its finite prime operator, and M_t physical modulation exp(2*pi*i*t*x). Every actual form vector u has an exact same-aperture modulated lift u_t. For each fixed h,

    Q_a(u_(t+h)) - Q_a(u_t)
      + Re<P_a M_(t+h) Ju,M_(t+h) Ju>
      - Re<P_a M_t Ju,M_t Ju> -> 0.

There exists one clock k_j -> infinity for each aperture, valid for every fixed source u and shift h, such that

    Q_a(u_(k_j+h)) - Q_a(u_(k_j))
      -> Re<P_a Ju,Ju> - Re<P_a M_h Ju,M_h Ju>.

Both Gamma energy and the two polar charges are retained and discharged. No RH, phase-independence, or unknown-source regularity premise is assumed. This is a supported quadratic comparison.

For the actual pole source u=ccmPolarFormVector(a,1/2)+ccmPolarFormVector(a,-1/2), the recovered prime difference is exactly the full Schur phase energy. If log 2 < 2a, its value at h=1/(2*log 2) is strictly positive. For every real R, some t>=R has Q_a(u_(t+h))>Q_a(u_t), and another has Q_a(u_(t+h))<Q_a(u_t).

## Dependency-closed paper proof

1. The corpus Gamma derivative is continuous, bounded on a compact central interval, and O(1/|t|) outside it. The full derivative is bounded. Existing logarithmic asymptotics give vanishing fixed additive increments.
2. The resulting carrier-independent increment bound is integrable against every L2 Fourier mass. Dominated convergence gives the Gamma increment law. The same bound admits every translated Fourier vector into the exact weighted form space; Fourier modulation and the existing reconstruction preserve physical aperture.
3. Riemann--Lebesgue sends each actual fixed pole charge to zero under modulation. The scalar norm term cancels. The complete source formula therefore gives the prime-compensated increment law.
4. Simultaneous recurrence of the finitely many literal prime phases chooses one clock independent of u and h. Translation-modulation intertwining recovers the full prime quadratic, retaining all complex correlations.
5. Modulation preserves every Schur row density. The unmodulated positive pole has zero edge energy, so its prime loss is exactly its modulated edge energy.
6. Prime two has phase -1 at h=1/(2*log 2). Its overlap row integral is positive whenever log 2<2a, and every other edge is nonnegative. Comparing the recurrent zero phase and the opposite starting phase proves both increment signs.

## What remains open

The aperture and source are fixed before the carrier limit. No uniform statement about moving sources or growing apertures follows. The result excludes eventual frequency monotonicity and supplies an exact phase-recovery law. It does not prove a negative energy, canonical-head positivity, ground-specific first-contact cancellation, eventual primitive sign, near-floor control, or RH.

## Verification

- Full scratch: exit 0, no diagnostics (11443).
- Final leaf: `lake --old env lean GaloisForLFunctions/RHTower/CCMRestrictedWeilModulationPhaseRecovery.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMRestrictedWeilModulationPhaseRecovery.olean`; exit 0, no diagnostics (73301).
- Eight public axiom queries: passed (69365, exit 0); every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
- One umbrella import; no umbrella or full build. No numerical experiment, heartbeat change, or added axiom.
- Global `scripts/formal_tools.py lint`: exit 1, fourteen unrelated unreachable modules; no new-leaf or prohibited-declaration diagnostic. Exact remaining errors:

```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureChainProfile
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureTranslationChains
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MertensProductDiamondPintz
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaDiagonalWardCrossing
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaDiagonalWardForcing
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
```
