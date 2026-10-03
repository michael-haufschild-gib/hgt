# RN: global confluent coordinate residual

Status: formalized and directly audited on 2026-10-02. RH remains open.

For the actual source k, actual full-tail kernel H, K=k(0), and
β=2∫₀∞t k'(t)²dt−K²>0, the literal residual satisfies

    B_*(y)=y k(y)−K H_x(0,y)/β > 0       for every y>0.

Moreover, for every fixed y>0, every sufficiently small z>0 satisfies
z<y and both actual inverse-Gram source and coordinate residuals are
strictly positive. The z threshold may depend on y. This removes the
previous restriction that y itself be sufficiently close to zero.

Exact Lean results in `ThetaTailConfluentCoordinateGlobal.lean`:

- `centerMixedRow_eq_rawMoment`: the raw canonical moment equals the actual
  mixed row, with its zero boundary correction retained.
- `normalizedMixedRow_hasDerivAt`: the negative transport integral is the
  derivative of N(y)=H_x(0,y)/(yKk(y)).
- `normalizedMixedRow_strictAnti`, `normalizedMixedRow_limit`, and
  `normalizedMixedRow_lt_center`: N strictly decreases from β/K².
- `confluentCoordinateResidual_pos` and `eventually_actual_ports_pos_at`:
  the actual residual and actual finite-pair chamber consequences.

The analytic producer is `ThetaCoordinateCanonicalFlux.lean`. It proves
0≤λ<1 on the integration ray, decay of the literal raw Schwartz flux,
and F_t=M_y−Jw. The finite primitive ∫₀ᵇM_y−F(b) strictly decreases from
zero and tends to ∫M_y. Its limit is strictly negative. No integrability
of the logarithmic quotient current is assumed.

Both leaves passed targeted `lake --old build` and final direct
`lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` checks without
own diagnostics. All 19 public theorems were audited from a /tmp file;
only propext, Classical.choice and Quot.sound occur. Together with the
global-current chain, this session directly audited six leaves and 43
public theorems. All five new leaves are wired into RHTower. No full or
umbrella build, numerical experiment, added axiom or heartbeat increase.

`scripts/formal_tools.py lint` reports 11 unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SuzukiTaV2PrescribedEnergySource, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No violation names an owned leaf.

Next hard problem: the actual finite-pair coordinate-row forcing, recorded
in P1 `rn-center-schur-coordinate-row-flow.md`. Finite-pair compensation
and propagation, general anchors, arbitrary rank and the retained
arithmetic RH transfer remain open. This theorem does not identify
off-diagonal kernels from their common diagonal.
