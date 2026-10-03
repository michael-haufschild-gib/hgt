# Route PM: the actual norm-null profile remainder has zero Abel mass

- **ID:** pm-ramanujan-band-profile-remainder
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, fully audited)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Statement and dependency-closed paper proof

For a measurable complex function f bounded on (0,infinity) and tending to0 at infinity,

    delta * integral_(u>0) exp(-delta*u)*f(u) du -> 0

as delta decreases to0. The positive dilation v=delta*u identifies this expression exactly with integral_(v>0) exp(-v)*f(v/delta) dv. For every v>0, v/delta tends to infinity, so the integrand tends to0. Its norm is bounded by B*exp(-v), an integrable majorant independent of positive delta. Filter dominated convergence proves the limit.

For the actual PM family, suppose inside the proposed contradiction that normalized complete-band vectors F_X tend strongly to F. Define

    b(u)=exp(-i*gamma*u) *
      (q_h(exp u)-<h,U_(u/(2*pi)) F>).

The actual tested-scale measurability and continuity of the fixed phase pairing make b measurable. The difference in parentheses is exactly <h,U_(u/(2*pi))(F_(exp u)-F)>. The phase isometry and the norm inequality for inner products bound |b(u)| by ||h||*||F_(exp u)-F||, which tends to0. The already derived global moving-source bound C also gives |b(u)|<=||h||*(C+||F||) on u>0. Applying the bounded-null Abel theorem proves zero Abel mass for this literal source remainder; no unknown regularity or source bound is assumed separately.

The exact substitution X=exp u in the actual scale integral at rho+delta, with Re(rho)=1/2, gives

    integral_(X>=1) X^(-rho-delta-1/2)*q_h(X) dX
      = integral_(u>0) exp(-(delta+i*Im(rho))*u)*q_h(exp u) du.

The derivative exp u cancels the real exponent1 from the original kernel. This identity retains the full actual source and uses the same change-of-variables theorem already audited in the finite-band Hilbert realization.

## Scope and verification

These results apply inside the convergence contradiction. The separate fixed-profile Abel term was already audited in `PMRamanujanBandAbel`. The two Abel terms combine by actual integrability and linearity, yielding delta times the actual tested scale integral tending to zero whenever the test stays a positive frequency distance from Im(rho). Invoking the positive complete residue test and instantiating an actual positive critical zero are still required for spectral escape. No small-damping energy ceiling or RH conclusion follows from the remainder lemma alone.

`PMRamanujanBandProfileRemainder.lean` contains all seven public declarations. Targeted old-mode leaf build passed (73 seconds), mandatory final actual-file `lake env lean` passed with no diagnostics, and every export has only propext, Classical.choice and Quot.sound. Umbrella wired once. Lint has eleven unrelated unreachable modules, none own. Completed scratch and audit artifacts cleaned after verification.
