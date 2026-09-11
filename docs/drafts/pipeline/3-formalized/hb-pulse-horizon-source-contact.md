# HB: normalized pulse horizon and original radial contact

Status: twelve source/contact theorems formalized in two leaves; both exact leaf audits passed. Complete radiative extinction remains open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → original common Hawking-clock extinction → RH.

## Exact source result

Write `s=physicalRate(q,true)`, `t=physicalRate(q,false)=-s-3`, `alpha_i=(2i+1)(2i+2)`, `d_i=i(i-1)/4`, `u=1/r=-tanh x`, and `A_i(u)=amp_i²(1+u)^(2i)`. Let `H_i` be the actual full angular response, `Q` the literal half-square, `U_i=coexact H_i` and `W=coexact Q`. All coefficients below use the original source and clock.

The proved scalar pulse factorization is

    P_i=2 alpha_i A_i(u)(1-u)
      [-((2i+1)u+1)H_i+d_i u²((2i+3)u+3)Q] chi'(v)exp(2iv).

The original master-source normalization is

    S_i=-r³ coexact(P_i)/(f alpha_i),  f=r²-1.

The exterior identities `0<u<1` and `alpha_i≠0` are proved for each actual Xi occurrence. Cancel the source's radial zero before taking a limit:

    S_i=2 A_i(u)/[u(1+u)]
      [((2i+1)u+1)U_i-d_i u²((2i+3)u+3)W] chi'(v)exp(2iv).

This regular expression has the actual limit

    S_i|H=2 A_i(1)(T_i-N_i) chi'(v)exp(2iv),
    T_i=U_i-d_i W,
    N_i=-i U_i+d_i(i+2)W.

Proof ingredients: literal angular smoothness; differentiation of its linear combination with Q; the actual pulse factorization; exterior denominator nonvanishing; `u→1` at the original tortoise horizon; continuity of the complex power on positive real bases. No covariance or extinction hypothesis is used.

## Original radial contact

The source-contact orientation is the one in [the complete mixed-current calculation](../1-in-progress/hb-mixed-complete-current.md). Before taking its limit,

    C_r=f/r² sum_j[Psi_static,s,r,j S_t,j-Psi_static,t,r,j S_s,j]
       =r^(-2) sum_j[(f Psi_s,r,j+Psi_s,v,j)S_t,j
                       -(f Psi_t,r,j+Psi_t,v,j)S_s,j].

The second expression retains both differentiated incoming jets. Their actual radial profiles and first derivatives are continuous at r=1. Thus the radial term vanishes only after its regular limit is justified, leaving

    C_H=sum_j[Psi_s,v,j S_t,j-Psi_t,v,j S_s,j].

Put `c=a²b²/64`, `TT=T_s dot T_t`, `X=T_t dot N_s`, `Y=T_s dot N_t`. The branch relation gives `A_s(1)A_t(1)=c` and the unchanged common temporal exponent -6. Exact bilinear expansion gives

    C_H(v)=exp(-6v){4c[(s-t)TT+tX-sY] chi chi'
                        +2c(X-Y)chi'^2}.

For every fixed h>=0,

    integral_{-h}^1 exp(6v)[C_H(v+h)-exp(-6h)C_H(v)]dv=0.

This uses the established endpoint identity for the two compact contact profiles. It neither sets C_H pointwise to zero nor identifies this temporal moment with the physical left-QNM functional.

## Contact law before the horizon limit

At every exterior radius write `Psi_i=A_i(r) chi exp(2iv)`, `D_i=partial_r A_i` and `S_i=P_i(r) chi' exp(2iv)`, where these are the actual covector coefficients. Expansion of the regular contact gives

    C_r(v)=exp(-6v)[B(r) chi chi'+E(r)chi'^2],
    B(r)=r^(-2) sum_j[((f D_s+2s A_s)_j P_t,j)
                         -((f D_t+2t A_t)_j P_s,j)],
    E(r)=r^(-2) sum_j[A_s,j P_t,j-A_t,j P_s,j].

Thus its unchanged-clock translation moment is zero for every original exterior radius. No interchange of an integral and a horizon limit is needed. This stronger law is proved in `ThetaCuspHawkingBMPulseContactClock.lean` by `compactPulseContact_profile`, `compactPulseContact_clockMoment` and `originalPulseContact_clockMoment`.

## Scope and open producer

These theorems concern the literal normalized pulse and its source contact with the explicit incoming SV–SV field. They do not evaluate the causal pulse response, its cross current, the other eight SS/SV/VV pairings, the complete tensor quadratic corrections, changing metric weights or all remaining faces.

The actual finite retarded action retains a history strip under a fixed time translation; see C13 in [the active source-translation investigation](../1-in-progress/hb-fixed-clock-source-translation.md). The next mathematical obligation is the completed physical pairing of the propagated source defect and that history, with every correction and boundary term. No source-derived sign or vanishing of that full pairing has been proved.

## Lean

Source: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPulseHorizonSource.lean`, namespace `RHTower.D4BMPulseHorizonSource`.

- `normalizedPulseSource_eq_compact`, `normalizedPulseSource_original_radius`: actual exterior cancellation and original normalization.
- `compactPulseSource_horizon`, `normalizedPulseSource_horizon_limit`: retained horizon drive and original exterior limit.
- `horizonPulseContact_profile`, `horizonPulseContact_clockMoment`: exact horizon contact and its translation moment.
- `originalPulseContact_eq_compact`, `compactPulseContact_horizon`, `originalPulseContact_horizon_limit`: original radial contact, regular trace and justified limit.

Scratch proofs checked with `lake env lean`. Final exact leaf builds passed with no warnings: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPulseHorizonSource` (202 seconds) and `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPulseContactClock` (40 seconds). Each used twelve existing cache roots and compiled only its leaf. Both modules are wired into `RHTower.lean`; no umbrella or full build was run. Static index refreshed and formal lint passed, with existing large-file warnings. No new axioms or incomplete proofs were added.

Audited source SHA-256 values: `4a70aba6a727f6fc6559a0915fb4d9a1d574e4d3dd3ad24397a4f56f7e5d8624` (horizon/source leaf), `9d52996da090334e0feb52c03a4d9a49ee3ee5b538fa6b38979fa13603f9307c` (finite-clock leaf).
