# HB AIME peripheral-spectrum zero-mode rigidity

- **ID:** HB-PERIPH-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB producer burden; corpus escape theorem `d4BMCausalSpectralPersistentCounterterm_forces_not_ae_strictlyDamped`
- **Statement:** A finite-variation strictly damped response plus an `L¹` real-axis continuum converges to zero, so an asymptotically persistent AIME counterterm is carried exactly by its zero-frequency atom.

## Goal

Kill the remaining ordinary spectral-completion escape after the arbitrary strictly damped-spectrum no-go.  Full HB chain is

`Einstein--Teukolsky source -> nonzero chiral return determinant -> positive-total FE--Schwarz Ward identity -> RH`.

The proposed theorem does not assume any incidence or RH receiver.  It proves that QNM/redshift modes and an ordinary absolutely continuous branch cut cannot erase the already-derived nonzero AIME numerator at late time.  Any surviving cancellation must contain a source-tuned zero-frequency atom or leave finite variation/`L¹` continuum regularity.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 -> 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Write total return as `z0 + D(t) + B(t)`, where `z0` is the zero mode, `D` is an arbitrary finite-variation superposition with frequencies almost everywhere in the open lower half-plane, and `B` is the Fourier transform of an `L¹(ℝ,ℂ)` boundary density.  Dominated convergence gives `D(t) -> 0`; Riemann--Lebesgue gives `B(t) -> 0`; hence total return tends to `z0`.  Uniqueness of limits classifies every proposed persistent counterterm exactly.  Adding passive stationary mass leaves the AIME numerator nonzero, so zero-free asymptotic cancellation is impossible.

Hostile audit retains three genuine escapes rather than hiding them: a literal zero-frequency atom, singular/non-Rajchman boundary spectrum outside the `L¹` class, or infinite variation.  These become the exact remaining PDE alternatives.

## Novelty audit

- Internal corpus contains arbitrary strictly damped finite-variation extinction and separately contains Riemann--Lebesgue infrastructure, but no mixed AIME/QNM/real-axis-continuum/zero-mode classification.
- Rosato--De Amicis--Pani, arXiv:2603.20490, identify the Schwarzschild low-frequency branch cut with decaying Price-law/logarithmic tails and redshift terms with decaying modes; they do not classify nonlinear AIME cancellation or isolate a necessary zero-frequency atom.
- Arnaudo--Carballo--Withers, arXiv:2510.18956, give convergent QNM/Matsubara representations and the Schwarzschild branch-cut confluence; they do not prove the source-specific AIME rigidity statement.
- Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, establish AIME as a third-order effect but do not give this continuum/zero-mode cancellation classification.

## Paper proof

**[PROVED HERE]** Let `R(t)=z0+D(t)+B(t)`.  For `D`, strict lower-half-plane support gives pointwise character decay, modulus at most one for `t >= 0`, and the finite-variation density is an integrable majorant; dominated convergence yields `D(t) -> 0`.  For `B`, its `L¹` real-axis density has Fourier transform tending to zero by Riemann--Lebesgue.  Therefore `R(t) -> z0`.  Since `ℂ` is Hausdorff, `R(t) -> c` iff `z0=c`; eventual equality with `c` is a special case.

For one Xi copy, add stationary numerator
`A(q,m)=AIME(q)+passiveMass(q,m)`.  Existing source algebra proves `A(q,m) != 0`.  Hence the full numerator tends to `A(q,m)+z0`, so asymptotic cancellation occurs iff `z0=-A(q,m)`.  In particular `z0=0` gives eventual nonvanishing.  Existing simple-pole order classification then gives meromorphic order `-1` at the negative-branch fundamental QNM for all sufficiently late times.

No hidden analytic premise remains: both convergence inputs and stationary nonvanishing are already unconditional corpus theorems.  The hostile exceptions are exactly those stated in Approach.

## No-go closure

- **Exact killing theorem/mechanism:** Mixed damped/absolutely-continuous peripheral response converges to its zero atom; without that atom, nonzero AIME survives.
- **Strongest positive survivor:** Persistent cancellation forces the exact source-dependent zero-mode coefficient; absent that atom, the AIME pole survives.
- **New insight:** The continuum escape is not generic peripheral spectrum.  It is concentrated at the threshold atom; ordinary branch-cut density dephases.
- **Status:** Formalized in `ThetaCuspHawkingAIMEPeripheralSpectrumZeroModeRigidity.lean`.  Exact survivor theorem `d4BMPassivePeripheralSpectralFullPoleNumerator_tendsto_zero_iff_zeroMode`; route-kill certificate `d4BMPassivePeripheralSpectralNoZeroModeCancellationRouteKilled`.  Direct Lean and targeted module build pass.  Axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-31 — Created directly in Stage 1 after corpus and current-primary-literature audit; conjecture `HB-PERIPH-1` selected.
- 2026-08-31 — `[PROVED HERE]` Exact zero-mode classification and no-zero-mode AIME pole survival paper proof closed; promoted to Stage 2.
- 2026-08-31 — Formalized, wired into `GaloisForLFunctions.RHTower`, targeted build green, standard-axiom audit green; promoted to Stage 3.  Global lint reaches this module and remains red only on unrelated concurrently owned unreachable modules.
