# TG C9.11c — rigidity of the retained Sonin dilation channel

- **ID:** TG-C9.11c
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG C9.11b, `tg-balanced-ward-cubic-survivor.md`
- **Successor:** `tg-coherent-dilation-support-rigidity.md`
- **Statement:** For `0 < a ≤ b ≤ c ≤ r*a`, `r > 1`, the map `Q_c D_r` is injective on `range (Q_a-Q_b)`.

## Goal

Eliminate the unproved retained/lost decoupling case in the exact balanced Ward cubic law. For one scale, `Z†W=0` should imply `Z=0`. This concerns actual Sonin source operators; no Xi, divisor, RH, or continuation-budget premise is admitted. The joint prime–Gamma completion, Hardy-index comparison, and sub-unit budget remain open.

## Corpus basis and novelty audit

Two deep corpus searches (source rigidity; dilation support recovery) completed with `partial=false`, inventory complete, but mostly source-only compiler coverage. Applicable existing inputs are the closed physical/Fourier forbidden sum (`SoninBandCodimensionTwo`), normalized dilation covariance (`SoninEulerCalkinPartialIsometry`), and qualitative Fourier uncertainty. Existing annular injectivity only handles `D_r v=0`; the needed conclusion recovers support from bounded support of `D_r v`.

## Paper attack

Write `v=f+g` using `v ∈ K_bᗮ`, with `f` physically supported at radius `b` and `g` Fourier-supported there. From `Q_c D_r v=0`, also write `D_r v=h+k` in the two radius-`c` bands. Then `D_r f-h=k-D_r g` is both physically and Fourier compactly supported; uncertainty forces zero. Thus each polarized image lies in its radius-`c` band separately.

Recover support exactly: if `f` is physically supported at `t` and `D_r f` at `c`, the identity `U_(r^-1) f=D_r f-U_r f` and covariance improve support to `max(c/r,t/r²)`. Finite iteration gives `max(c/r,b/r^(2n))`; choose `n` making the second entry at most the first. Fourier covariance gives the same recovery in the Fourier band. Therefore `v` belongs to the radius-`c/r` forbidden sum, hence to `K_aᗮ` when `c≤ra`. Since `v∈K_a`, it vanishes.

The exact support endpoint and both polarization transports were subsequently checked in Lean; see verification below. No numerical experiment is involved.

## Log

- 2026-10-02 — Candidate formulated from actual corpus source decompositions; beginning support-recovery formalization. No theorem claimed verified yet.

## Exact proved statements

Let `A_t` and `B_t` be the physical and Fourier forbidden bands, `T_t=A_t+B_t`, and `Q_t` the actual Sonin projection. For **any** `b,c>0`, `r>1`, and `v∈T_b`, Lean proves

`D_r v ∈ T_c ↔ v ∈ T_(c/r)`.

Equivalently, if `Q_b v=0`, then `Q_c D_r v=0 ↔ Q_(c/r) v=0`. This is stronger than the proposed crossing-chamber injectivity. For `v∈K_a`, `c≤ra` forces the right side to imply `v=0` by orthogonality. The theorem holds on full ambient L² and is then restricted to the actual even carrier.

For `0<a≤b≤c≤ra`, put `E=Q_a-Q_b`, `Z=E D_r(Q_b-Q_c)`, and `W=E D_r Q_c`. The adjoint `W†` is injective on `range E`. Hence, for every operator `T` with `ET=T`, `W†T=0 ↔ T=0`. Applying this to `Z`, and taking the adjoint of `Z†W=0`, gives

`Z†W=0 ↔ Z=0`.

For the existing actual singleton balanced Ward completion `B`, this proves

`Re Tr(B³)=0 ↔ Z=0`, and `Re Tr(B³)<0 ↔ Z≠0`.

No unconditional nonvanishing of `Z` at every strict aperture is asserted. No mixed-scale/cofinal claim is inferred from this single-scale statement.

## Completed proof and verification

The finite support descent was implemented without limit estimates: choose `n` with `b<(r²)^n(c/r)` by the Archimedean power theorem, then descend one power at a time. Each step uses exact band membership and the inverse dilation identity. Fourier covariance and bounded-support uncertainty complete the two-polarization classification. Closedness of the forbidden sum is the previously formalized input converting projection kernels into actual decompositions.

Two new leaves, twelve public declarations:

- `formal/GaloisForLFunctions/RHTower/SoninDilationSourceSupportRecovery.lean`
- `formal/GaloisForLFunctions/RHTower/SoninSingleScaleWardRigidity.lean`

Both final foreground leaf audits passed with `lake --old env lean <module>.lean -o <matching .olean>`; no umbrella/full build. Both are wired into `RHTower.lean`. A separate `/tmp` audit printed axioms for all twelve declarations: exactly `propext`, `Classical.choice`, `Quot.sound`. Default heartbeat limits; no holes, added axioms, numerical experiments, or retained scratch declarations.

Global `scripts/formal_tools.py lint` still reports ten unrelated pre-existing unwired modules: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. Neither new leaf is implicated.

## Frontier assessment

This resolves the actual single-scale cubic decoupling problem rather than adding a density hypothesis. The surviving cubic detects every nonzero transition at that scale. The coherent finite-scale inverse-support law and complete cubic rigidity are now proved in C9.11d, retaining all coefficients and phases. Joint prime–Gamma completion, source-to-Hardy index, and the sub-unit law remain unsolved. RH goal remains active and unmet.

- 2026-10-02 — Exact support classification and single-scale cubic rigidity fully formalized and axiom-audited.

- 2026-10-02 — C9.11d exposes three existing support helpers for reuse (current support leaf: ten public declarations). The four-leaf, 33-declaration audit passed after this change.
