# Vacuum-differentiable nonlinear HB evolution cannot repair linear FE--Schwarz defect

- **ID:** HB-VAC-DIFF-NONLINEAR-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB live core (read-only)
- **Statement:** Any nonlinear finite-time packet evolution whose coefficientwise vacuum first variation is the centered Birmingham--Mokhtari QNM clock and which is exactly covariant under literal anti-linear source-FE transport forces covariance of that linear clock; at any nonzero source-predeclared time, existence of such evolution is equivalent to RH.

## Goal

Kill perturbatively regular, genuinely time-dependent nonlinear Einstein--Teukolsky dynamics as a mechanism for repairing the HB source-FE clock defect. Exact proof chain:

`nonlinear Einstein--Teukolsky FE covariance near vacuum`
`→ first-variation FE covariance`
`→ HB centered-QNM finite-clock covariance`
`→ Re(q)=1/2 on every Xi copy`
`→ RH`.

This materially reduces remaining HB burden: nonlinear perturbative corrections cannot create the missing symmetry. A survivor must already change linearized PDE/clock, change literal source-FE transport, be singular/non-differentiable at vacuum, or assert only isolated finite-amplitude coincidences with no accumulating vacuum family.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4HBVacuumDifferentiableNonlinearEvolutionRouteKilled`, targeted `lake build` green, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

All conjecturing used `scripts/formal_tools.py research`. Relevant dependency chain:

- `ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity.lean`: one nonzero physical clock step commutes with literal source-FE transport iff RH.
- `ThetaCuspHawkingBMVacuumRegularNonlinearSourceGaugeNoGo.lean`: arbitrary static vacuum-regular nonlinear source gauges cannot exchange the reflected sources while commuting with fixed clock; it explicitly leaves genuinely time-dependent dynamics open.
- `ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence.lean`: distinguishes literal anti-linear FE transport from its complex-linear surrogate.
- `ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint.lean`: Peierls incidence is unconditional; branch covariance is exact remaining endpoint.
- `ThetaCuspHawkingTeukolskyDelayedPumpProbe.lean` and `ThetaCuspHawkingAIMEPeripheralSpectrumZeroModeRigidity.lean`: finite local, finite-energy continuum, and ordinary peripheral corrections already fail.

No declaration returned for differentiation of a nonlinear FE-covariant evolution at vacuum or for the exact existence classification below.

## Literature audit through 2026-08-31

Primary-source searches covered second-order Teukolsky formulations, nonlinear QNM excitation, AIME, QNM bilinear forms, and rigorous meromorphic resolvents. The literature constructs nonlinear response perturbatively from a fixed linearized equation but does not state this HB/Xi first-variation obstruction or an RH consequence. Key comparisons:

- Spiers--Pound--Moxon, arXiv:2305.19332, explicit second-order Kerr Teukolsky nonlinear source.
- Spiers--Pound--Wardell, arXiv:2306.17847, covariant/gauge-invariant second-order Schwarzschild equations.
- Ma--Yang, arXiv:2401.15516, quadratic QNM excitation from frequency-domain second-order Teukolsky equation.
- Bourg et al., arXiv:2503.07432, linear and quadratic QNMs in second-order Schwarzschild perturbation theory.
- Sberna et al., arXiv:2112.11168, absorption-induced third-order mode excitation.
- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, conserved QNM bilinear form and nonlinear-coupling framework.
- Stucker, arXiv:2407.04612, Kerr QNMs as poles of meromorphically continued cutoff resolvent.

## Conjecture loop

- **C1 (failed/pivoted):** finite-channel holomorphic operator corrections cannot realize horizontal optical-cancellation susceptibility. True-looking but weaker: actual Einstein sources are Hermitian and naturally antiholomorphic.
- **C2 (survives hostile audit):** exact nonlinear FE covariance plus vacuum first variation equal to physical BM clock forces linear FE covariance. This attacks actual perturbative time dependence and is independent of locality, channel count, perturbative order, memory, continuum, positivity, and invertibility.

## Paper proof `[PROVED HERE]`

Let `R` be literal anti-linear source-FE packet transport, `U_t` centered-QNM physical clock step, and `Phi_t` arbitrary nonlinear packet evolution. Define coefficientwise vacuum first variation by

`epsilon⁻¹ Phi_t(epsilon x)(r) → U_t(x)(r)`

for every finite packet `x`, output coordinate `r`, and real nonzero `epsilon → 0`. Assume `R(Phi_t(x)) = Phi_t(R(x))` for all `x`.

Fix `x,r`. Apply first variation at reflected coordinate `Rr`. Since `epsilon` is real, anti-linearity gives

`epsilon⁻¹ R(Phi_t(epsilon x))(r)`
`= kappa(Rr) conjugate(epsilon⁻¹ Phi_t(epsilon x)(Rr))`
`→ kappa(Rr) conjugate(U_t(x)(Rr))`
`= R(U_t(x))(r)`.

Covariance and real homogeneity of `R` identify the same quotient with

`epsilon⁻¹ Phi_t(epsilon R(x))(r) → U_t(R(x))(r)`.

Uniqueness of limits gives `R(U_t(x))(r)=U_t(R(x))(r)` for all `x,r`, hence full linear finite-clock covariance. Existing exact classification gives `t=0 ∨ RH`; for `t≠0`, RH.

Conversely, under RH take `Phi_t=U_t`. Complex linearity makes its vacuum first variation itself, and existing finite-clock theorem gives FE covariance. Therefore existence is equivalent to RH.

## Hostile scope audit

- Does not assume locality, finite-dimensionality, analyticity, invertibility, positivity, energy bounds, spectral completeness, or a finite perturbation order.
- Uses only coefficientwise directional first variation along real amplitudes; conjugate/Hermitian nonlinearities remain included.
- Does not cover a map singular at vacuum, a changed linearized clock, changed source transport, or covariance asserted at one isolated nonzero amplitude only.
- Those exceptions are exact positive survivor, not proof gaps.

## No-go closure

- **Exact killing theorem/mechanism:** equivariance differentiates; nonlinear terms vanish from first variation and cannot repair a non-equivariant linear clock.
- **Strongest positive survivor:** any successful time-dependent HB producer must be nonperturbative at vacuum, change the linearized Einstein--Teukolsky clock/source law, or supply a source-specific isolated-amplitude identity not arising from an amplitude-neighborhood symmetry.
- **New insight:** genuinely time-dependent perturbative dynamics is not a remaining escape from static nonlinear no-go; it collapses to already-classified finite-clock covariance at first order.
- **Status:** dependency-closed and formalized in `ThetaCuspHawkingBMVacuumDifferentiableNonlinearEvolutionNoGo.lean`. Direct `lake env lean` and targeted module build pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`. Repository lint reaches this module but is presently blocked by unrelated unwired `Sieve.MatomakiTeravainenLemma35ThirdDerivative`.

## Log

- 2026-08-31 — created in 1-in-progress after corpus-first C1→C2 pivot and external novelty audit.
- 2026-08-31 — dependency-closed hostile paper proof promoted to 2-fully-proven.
- 2026-08-31 — formalized exact first-variation reduction, nonlinear-existence iff RH classification, unit-time specialization, and premise-free route-kill certificate; targeted build passed.
