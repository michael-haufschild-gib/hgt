# HB bulk-holomorphic Hermitian optical no-go

- **ID:** hb-bulk-holomorphic-hermitian-optical-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED / ROUTE-CLASS NO-GO
- **Source:** `rh-current-frontier-map.md` HB route; open core in
  `ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint`
- **Statement:** No fixed-phase, same-variable Hermitian anomaly represents the actual balanced
  theta-Hawking Born channel on any nonempty open complex-frequency domain.

## Goal

Kill the live one-complex-frequency bulk-local interpretation of the missing phase-sensitive
optical Ward producer. Exact RH chain tested:

```text
same-variable complex-frequency Hermitian optical identity
  -> opposite sign for complete HB causal orbit
  -> total-cokernel extinction
  -> source-FE unit clock gain
  -> shared HB/FZZ-P/PW-B/RBH Ward cancellation
  -> Re(s)=1/2 on every Xi fibre
  -> RH.
```

The theorem is non-circular: it uses holomorphic/Schwarz rigidity and unconditional source values,
never a premise about Xi zero placement.

## Gates

- [x] 0 -> 1: corpus-derived exact open core and RH chain identified
- [x] 1 -> 2: dependency-closed paper proof and hostile falsification complete
- [x] 2 -> 3: premise-free Lean certificate, umbrella wiring, targeted build and axiom audit
- [ ] 3 -> 4: publication-ready exposition and independent priority review

## Internal frontier

- `[CORPUS]` `ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint` isolates a phase-sensitive
  complex-frequency optical identity as the surviving HB open core.
- `[CORPUS]` `thetaCuspBalancedHawkingBornAmplitude_eq_XiC` identifies the actual balanced Hawking
  channel.
- `[CORPUS]` `differentiable_thetaCuspFourierLaplace_all` makes this channel entire.
- `[CORPUS]` `XiC_ne_zero_of_norm_le_one` supplies the unconditional nonzero anchor at `z=1`.
- `[CORPUS]` `analyticOnNhd_eqOn_of_eqOn_isOpen` propagates agreement from an interior ball.
- `[CORPUS]` `HolomorphicSchwarzPolarization` gives the exact two-variable positive replacement.
- Corpus search found no local-open route classification for the actual Hawking Born channel.

## External frontier

Moving-mirror literature derives real-time noise, nonlocal dissipation, and fluctuation-dissipation
relations from pair emission; see Butera, *Noise and dissipation on a moving mirror induced by the
dynamical Casimir emission*, J. Phys. Photonics 5 (2023), arXiv:2306.03813. Targeted primary-source
search through 2026-08-31 found no same-variable complex-frequency Hermitian landing for this
theta-Hawking channel and no corresponding local-open impossibility classification. Generic facts
about real-valued holomorphic functions and Schwarz polarization are classical; novelty is claimed
only for the exact source-pure route kill and survivor classification, pending independent priority
review.

## Conjecture loop

`[C-HB.1]` A fixed nonzero phase and arbitrary scalar channels `B,C` can satisfy

```text
F(z) = phase * (conj(B(z))*C(z) + conj(C(z))*B(z))
```

throughout some nonempty open complex-frequency domain, where `F` is the actual balanced
theta-Hawking Born amplitude.

Hostile relaxations built into the statement:

1. the open domain may be disconnected;
2. `B,C` are arbitrary functions, with no continuity or analyticity required;
3. phase and normalization are arbitrary, except the phase is nonzero;
4. only local equality on one nonempty open domain is assumed.

**Verdict: FALSE.** The right side is fixed by conjugation after division by `phase`, so the rescaled
entire `F` is real-valued on an interior ball. It is constant on that ball and therefore everywhere.
But `F(0)=0` and `F(1) != 0`.

## Complete paper proof

Let

```text
H(B,C;z) = conj(B(z))*C(z) + conj(C(z))*B(z).
```

Commutativity shows `conj(H(B,C;z))=H(B,C;z)` for every `z`; no regularity of `B,C` is involved.
Assume `F(z)=a H(B,C;z)` on a nonempty open set `Omega`, with `a != 0`, and set
`G(z)=a^(-1)F(z)`. The corpus source theorem makes `F`, hence `G`, entire. Choose
`s0 in Omega` and an open ball `D(s0,r) subset Omega`. On that ball `G=H`, so `Im G=0`.

A holomorphic function with constant imaginary part on the connected ball is constant there.
Both `G` and that constant function are entire and agree on a nonempty open set, so analytic
continuation gives equality on all of `C`. Therefore `G(1)=G(0)`. Since `a != 0`, this implies
`F(1)=F(0)`. The exact source formula gives `F(0)=0`, while
`F(1)=(-i/(4*pi))*XiC(1) != 0`; contradiction.

## No-go closure

- **Exact killing theorem:**
  `not_thetaCuspHawkingSameVariableLocalHermitianOpticalLanding`.
- **Strongest positive survivor:** the separately holomorphic two-variable anomaly
  `thetaCuspHawkingSchwarzPolarizedAnomaly B C z w`, with exact diagonal recovery at
  `w=conj(z)` and proved holomorphy in each independent variable.
- **New insight:** analytic continuation and Hermitian diagonalization do not commute in one
  variable. Complex-frequency HB must keep the Schwarz partner independent until physical-diagonal
  restriction, or leave bulk-local holomorphy through boundary values, distributions, or nonlocal
  kernels.
- **Status:** `[LEAN-PROVED]`; route class killed, positive survivor formalized; exact application
  novelty pending independent priority review.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBulkHolomorphicHermitianOpticalNoGo`

- `star_thetaCuspHawkingLocalHermitianAnomaly`
- `thetaCuspBalancedHawkingBornAmplitude_zero`
- `thetaCuspBalancedHawkingBornAmplitude_one_ne_zero`
- `not_thetaCuspHawkingSameVariableLocalHermitianOpticalLanding`
- `thetaCuspHawkingSchwarzPolarizedAnomaly_diagonal`
- `differentiable_thetaCuspHawkingSchwarzPolarizedAnomaly_left`
- `differentiable_thetaCuspHawkingSchwarzPolarizedAnomaly_right`
- `thetaCuspHawkingBulkHermitianOpticalNoGoCertificate`

Audit: direct `lake env lean` passed; targeted module build passed; declared theorems use only
`propext`, `Classical.choice`, and `Quot.sound`, with no project axiom or hypothesis.

## Log

- 2026-08-31 — C-HB.1 frozen from corpus endpoint and source-to-clock chain.
- 2026-08-31 — global obstruction strengthened to arbitrary nonempty local-open domains; exact
  Schwarz-polarized survivor proved; module wired, built, and axiom-audited.
