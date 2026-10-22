# HB two-source clock: exact cap balance and retained spin-two bulk

Status: paper proof and exact Lean leaf audit complete. HB extinction and RH remain open.

## Original source and proof chain

The target chain is literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal/left-QNM action → extinction at the original common Hawking clock → RH. This result evaluates one of the actual two-source factors entering the causal action. It does not prove a law for the complete nonlinear action.

Fix an actual Xi occurrence q and its original branch rate s=physicalRate(q,branch). Its FE partner has rate t=−s−3. Keep the original smooth onset chi and radial coordinates u,w. Put

    alpha=(2s+1)(2s+2), gamma=(2t+1)(2t+2),
    b_r(z)=r(r−1)z[3+(2r+3)z]/[2(1+z)],
    g_r(z,v)=exp(2rv)[(2r+1)(2r+2)chi(v)−b_r(z)chi'(v)].

These are the established `clockProfile` functions. The established source identity `clockProfile_original` identifies them with the reduced coefficient of the original wave-image source, including its radial prefactor. The original finite clock is

    W_V(h)=integral_0^(V−h) g_s(u,v+h)g_t(w,v) dv.

No frequency, source, onset, measure or endpoint is changed.

## Complete observation-cap identity

For every real V and h, including both onset regions,

    partial_V W_V(h)=g_s(u,V)g_t(w,V−h).

Proof: the literal profiles are continuous, since the original smooth transition and its first derivative are continuous. Apply the fundamental theorem of calculus to the original finite integral and the derivative of V−h. This establishes the cap identity without extending an asymptotic expression across a transition layer.

## Exact late evaluation and finite translation

For 1<h<V−1 define

    a=alpha[gamma−6b_t(w)] tailClock,
    b_V=alpha gamma exp(−6V)/6,
    tailClock=integral_0^1 exp(−6v)chi(v)dv+exp(−6)/6.

Then

    W_V(h)=a exp(2sh)−b_V exp((2s+6)h).

The later onset is identically one throughout the integral and its derivative is zero. The original FE relation combines the two v-exponentials into exp(−6v). For c=V−h>1, the original finite contact and tail identities give

    integral_0^c exp(−6v)chi(v)dv=tailClock−exp(−6c)/6,
    integral_0^c exp(−6v)chi'(v)dv=6 tailClock.

Substitution proves the formula. The finite tail correction remains even though the earlier onset derivative has compact support.

Differentiating this exact expression on its open interval gives both actual delay derivatives and

    (partial_h−2s)W_V(h)=−6b_V exp((2s+6)h),
    partial_V W_V(h)=6b_V exp((2s+6)h).

For any fixed positive physical time H, with h>1 and V>h+1,

    W_(V+H)(h)−W_V(h)=b_V[1−exp(−6H)]exp((2s+6)h) ≠ 0.

The nonvanishing is source-derived: the actual Xi occurrence has nonzero imaginary part, so s and t are nonreal and all four linear factors in alpha gamma are nonzero. Complex exponentials never vanish, and 0<exp(−6H)<1. This result compares observation caps for the same source. It does not identify that operation with translating every field, boundary and measure in the complete nonlinear action.

## Actual retained spin-two bulk

Let Z be the original direct or image causal invariant, A=partial_h Z and B=partial_h A. The established full native angular primitive is

    F=(Z²−1)² partial_Z² M,

where M is the actual circular mean of the full theta half-square. Its derivative satisfies F''=Delta(Delta−2)M. No angular eigenfunction or scalar substitute is used for the retained spin-two field.

The exact twice-transposed coefficient in the original delay measure is

    T[W]=W''/A²−3BW'/A³+(3B²−A²)W/A⁴
        =A partial_Z²(W/A).

Define

    E_r=r²/A²−3Br/A³+(3B²−A²)/A⁴.

Substituting the proved original clock and both proved derivatives into the existing `delayBulk` gives

    delayBulk=F[a exp(2sh)E_(2s)−b_V exp((2s+6)h)E_(2s+6)].

The public bulk theorem uses the actual exterior radial domain and delays satisfying max(1,causalDelayStart)<h<V−1, for either causal image. In particular, the physical slope is away from its characteristic degeneracy there. The existing finite transfer theorems still supply the characteristic and terminal currents. They are not replaced by the late formula, and no endpoint contribution is discarded.

## What this resolves and what remains

A proposed cancellation by an unweighted fourth derivative is invalid: the actual Rodrigues operator is weighted. A clock-only annihilation of the twice-transposed coefficient would require W/A to be affine in Z. The new theorem evaluates the precise coefficient to be tested; it does not prove that the direct and image integrals, the reversed branch, or the complete tensor channels cancel.

The full extinction target still requires a source-derived identity or sharp estimate for the actual completed physical action, including the solved quadratic corrections, independent SS/SV/VV channels, changing metric weights, and temporal, horizon, exterior, cusp, characteristic and source-contact contributions. After physical-action identification with the established transduction C_phys=−Sigma |D|², Sigma>0, a source-derived Re(C_phys)>=0 (or a strict deficit estimate with constant less than one) would force D=0. No such sign or estimate is assumed or proved by this clock calculation.

The positive result is an exact, nonzero finite-cap compensation and its attachment to the original retained spin-two bulk. It supplies a term that any proposed complete extinction law must account for. No RH route is retired here.

## Formalization

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLateSourceClock`.
Namespace: `RHTower.D4BMLateSourceClock`.

Public source theorems:

- `clockDensity_late` and `clockDensity_late_derivatives`;
- `clockDensity_cap_balance`;
- `terminalCoefficient_ne_zero` and `clockDensity_late_terminal_law`;
- `delayBulk_late`;
- `clockDensity_terminal_flux` and `clockDensity_terminal_flux_ne_zero`;
- `clockDensity_finite_cap_translation` and `clockDensity_finite_cap_translation_ne_zero`.

The public statements use the literal Xi occurrence and source definitions. Their only domains are the stated geometric/time subtypes; no covariance, extinction, physical sign or RH premise is added.

Research transfers and their applicability limits are recorded in [the active source-translation card](../1-in-progress/hb-fixed-clock-source-translation.md), C20–C21.

Scratch checking passed without warnings. The exact cached leaf audit passed in 98 seconds without warnings, compiling only this leaf against twelve existing cache roots. The leaf is wired once into `RHTower.lean`; no umbrella build was run. The source has 352 lines, ten public theorems and three public definitions.

Source SHA-256: `e3e2e9f17106759afcf185d9995cd9af35f3533ab80642c6189e2e88d4967f7d`. Canonical audited `.olean` and `.ilean` are retained.

Static API index refreshed and all thirteen public entries verified. Formal lint passed with existing large-file warnings. Owned scratch, search, audit and log files were cleaned; no owned Lean process remains.
