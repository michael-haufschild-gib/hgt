# Actual degree compound-Poisson producer: false

- **ID:** LI-CLOCK-DEGREE-COMPOUND-POISSON
- **Stage:** 5-failed
- **Type:** FAILED CONJECTURE / positive salvage paper-proved, Lean-open
- **Parent:** [integrated actual-source sign](../1-in-progress/li-clock-integrated-source-sign.md)
- **Closure:** INCOMPLETE — positive survivor requires exact Lean formalization.

## Tested claim and exact obstruction

For the literal full-source degree probability pi_z(j)=nu_j*z^(2j)/((2j)!*Phi(z)), the proposed ordinary compound-Poisson representation with finite nonnegative intensities on positive integers is false for EVERY z>0. Its exact log-PGF coefficient at degree2 is -M1*z^4/4<0, using installed unconditional actual M1>0. An ordinary positive-jump compound-Poisson logarithm has nonnegative every nonconstant coefficient. This is an actual-source obstruction, not a substituted countermodel or a claim against every possible Ward argument.

The corpus predicate `IsCompoundPoissonMixture` permits arbitrary positive convolution weights. The actual degree law DOES satisfy that broader predicate using pi_z and delta1. The failed claim requires ordinary Poisson weights and must never be encoded as negation of the broader predicate. This discrete no-go does not imply failure of continuously Gamma-smoothed CP positivity and does not falsify RH.

## Strongest positive survivor and status

[Complete signed Gamma jump coupling](../2-fully-proven/li-clock-signed-gamma-jump-coupling.md), N10–N15:

- For p>1, exact finite signed density sigma_p(t)=exp(-pt)*P(t)/t admits quantitative absolute L1/TV tails and all fixed-order moments before exchange.
- Separate positive finite jump measures tau_plus/tau_minus satisfy mu_p*CP(tau_minus)=CP(tau_plus), preserving all actual source degrees and the origin atom.
- Every integer m>=1 gives CP(m*tau_plus)=CP(m*tau_minus)*mu_p^{*m}, hence genuine stochastic domination by an independent nonnegative summand. No fractional-time or pointwise intensity comparison follows.

Complete author475 and independent root N1–N17 paper audits PASS. New probability survivors and discrete no-go are Lean-OPEN. Existing final Primitive/Correction and raw-moment source facts are dependencies, not formalization of this new coupling. Formalization of the exact positive coupling remains required before closing this failed subroute. Parent integrated-source/RH sign route stays OPEN; actual sigma_p>=0 is still unproved.

## Evidence

Author SHA256 `8f9803dc0bb525c2fafb6d66079f8dbcffcd5b3466f5bc55d9d16e9e491a471f`; independent root review SHA256 `b8478ae8b04eb5567d16fa3384daccd7c387d1c01a6040bd90a95f1dffbd193c`. Full proof and partial-search coverage are preserved verbatim on the Stage2 survivor card. No computation, compiler claim, corpus-exhaustion or worldwide-novelty claim.
