# Anderson temporal-recurrence phase law

- **Status:** in progress; external priority audit active
- **Target modules:** existing finite/countable localized survival modules plus a thermodynamic-limit transfer module
- **Claim class:** `[CONJECTURE] [REINTERPRETATION] [PRIORITY UNRESOLVED]`

## Proposed law

Local spectral type defines a temporal phase for a local quantum observer.

### Localized side

For a normalized local state whose distinct-energy spectral weights admit,
uniformly in ambient volume,

\[
 p_K\le C e^{-2\mu r_K},\qquad
 |S_R|\le V(R+1)^d,
\]

with a summable shell certificate, the formalized quadratic recurrence law
at \(Q=2^N-1\) gives

\[
 n\le 2^{N(V(N+1)^d-1)}
\]

and

\[
 1-S_p(n)\le
 4\,\mathrm{GeometricTail}(N)
2\left(\frac{2\pi}{2^N}\right)^2.
\]

Thus error decays exponentially in \(N\) while the logarithm of the
certified local recurrence clock grows polynomially with degree \(d+1\).
Neither bound contains ambient Hilbert-space dimension.

### Atomless side

For every atomless probability local spectral measure, every positive
additive collision mass vanishes and the complete long-time distribution
of survival fidelity is the point mass at zero. This permits exceptional
returns but makes every continuous statistic supported away from zero have
zero symmetric-window mean.

For absolutely continuous spectral measures with an integrable density,
the stronger Riemann--Lebesgue conclusion would make survival fidelity tend
pointwise to zero. This stronger clause is not yet part of the formalized
claim.

### Thermodynamic transfer

Suppose finite-volume local histories converge at the finite sampled times
\(0,\ldots,N_{\max}\), and every volume has a recurrence within the same
finite clock and error. Then the limit history has a recurrence within the
same clock and error:

\[
 \min_{1\le n\le N_{\max}}
 |f_\infty(n)-f_\infty(0)|
 \le\varepsilon.
\]

The return index may vary with volume. No common return time is claimed.
Consequently, failure of local recurrence in the thermodynamic limit forces
failure of at least one uniform input: localized head size, tail control,
or finite-time convergence.

## Intended interpretation

The Anderson metal--insulator transition can be re-read as a transition in
local temporal recurrence class only in model regimes where established
spectral theory supplies the corresponding pure-point or atomless local
spectral measures and the uniform quantitative hypotheses above.

This is not the claim that localization generically makes recurrence fast.
The certified clock can remain enormous.

## Existing formal support

- `FiniteAndersonLocalizedSurvivalQuadraticLaw`
- `FiniteAndersonLocalizedResolutionScaleLaw`
- `SummableLocalizedSurvivalRecurrenceLaw`
- `ObserverRecurrenceDistributionLaw`

## Missing formal theorem

Formalize the finite-clock thermodynamic-limit transfer without choosing a
common return index. The clean finite formulation should use convergence of
the vector

\[
 (f_V(0),\ldots,f_V(N_{\max}))
\]

and continuity of finite minimum.

## Priority kill tests

- RAGE/Wiener/almost-periodic spectral theory already states the same
  temporal-phase equivalence.
- Published Anderson recurrence work already derives the
  \(d+1\) accuracy exponent.
- The quantitative law is only a restatement of effective-support
  recurrence with \(M(\varepsilon)=O(\log^d(1/\varepsilon))\).
- Standard Anderson localization does not supply the required uniform
  finite-head certificate.
- Finite-volume recurrence fails to transfer under the actual
  thermodynamic-limit topology used in physics.
- No observable experimental scaling window separates this law from
  finite-size revivals or boundary reflections.

## Claim boundary

No named Anderson ensemble, mobility edge, open-system device, many-body
localized phase, gravity, or cosmology claim is permitted until a separate
formal and priority audit closes its exact interface.
