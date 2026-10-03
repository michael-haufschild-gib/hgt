# Route PM: actual moving-band critical Mellin vector

- **ID:** pm-ramanujan-band-moving-mellin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean audited)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact source and result

For X>=1 and real epsilon, let V_X be the audited critical Mellin L2 vector of the complete natural denominator band floor(X)<q<=floor(2X). Normalize by X^epsilon and apply the corpus frequency-phase unitary with parameter log(X)/(2*pi). The resulting moving vector W_X has the literal almost-everywhere representative

    W_X(tau)=X^(epsilon+i*tau)*T_X(tau)

and squared norm

    ||W_X||^2=2*pi*X^(2*epsilon)
      * sum_(n>=0)|S_X(n+1)|^2/[(n+1)(n+2)].

For epsilon>0, Re(z)>1, s=1/2+i*tau and r=epsilon+s-z!=0, the literal scalar scale transform is integrable and satisfies

    zeta(z)*integral_(X>=1) X^(-z-1/2)*W_X(tau) dX
      =alpha*zeta(s)/s*(1-2^(-r))/r
        *[zeta(1+z-s)*H_epsilon(z,s)-zeta(z)].

The integrand uses the displayed literal representative, so no exchange of separate almost-everywhere exceptional sets is assumed.

## Dependency-closed paper proof — [PROVED HERE]

The phase unitary multiplies the normalized critical vector by exp(i*tau*log X). For positive X this equals X^(epsilon+i*tau) after absorbing the real normalization. Almost-everywhere equality follows from the two Lp representative laws. The phase action is isometric; scalar normalization and the audited exact complete-energy norm give the stated norm identity.

Multiply the representative by X^(-z-1/2). The positive-real complex-power addition law gives exponent epsilon+s-z-1. The remaining factor zeta(s)/s is constant in X. The audited full cutoff-integrand admission therefore proves actual integrability. Pull the constant outside the integral and apply the complete cleared cutoff identity, retaining the literal q=1 subtraction.

## Contribution and remaining hard problem

The actual moving Hilbert carrier and the arithmetic cutoff transform now refer to the same complete source, with exact normalization and energy. This does not continue the transform across Re(z)=1 or establish a cutoff-uniform norm bound. Compact tested continuation, residue positivity and the profile-remainder Abel argument remain open. The global small-damping energy ceiling sufficient for RH remains open.

## Verification status

`PMRamanujanBandMovingMellin.lean` passed the targeted old-mode build (only this leaf built, 261 seconds), mandatory final actual-file `lake env lean` with no diagnostics, and all nine separate public axiom queries. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella wired once. Global lint reports thirteen unrelated unreachable modules and no own finding. No full build, umbrella build, heartbeat increase or numerical experiment was used.
