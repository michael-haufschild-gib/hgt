# TG C9.21: literal Gamma clock source and Hardy phase

- **Stage:** 3-formalized
- **Route:** TG, completed source-to-Hardy compatibility
- **Target:** identify the compensated odd clock source with the actual Gamma Hardy phase, with normalization fixed by the source.
- **Arithmetic target remains open:** Summable soninPrimePolarGridEnergy; this card does not replace it.

## Corpus basis

SoninGammaClockSymbol proves the even full symbol is twice the normalized
quarter-line Gamma log modulus. DigammaIntegralRepresentation proves
Gauss's complex integral unconditionally on the right half-plane.
HardyZPhaseAsymptotic constructs gammaHardyTheta by integrating the actual
Gamma phase rate and identifies its exponential with gammaHardyPhase.
Fresh deep search tg-c921-phase-search is nonpartial, source snapshot,
compiler refresh incomplete. Candidate lemmas/source arguments inspected.
No matching literal odd clock identification appeared in these hits.

## Conjecture and dependency-closed paper argument

Write g(u)=ccmPublishedArchimedeanDensity u=e^(-u/2)/(1-e^(-2u)).
Define
 Q(t)= integral_(0,infinity) (t*u-sin(t*u))*g(u)/u du,
 Theta_src(t)=t*gammaHardyPhaseRate(0)+Q(t).
Claim: Theta_src(t)=gammaHardyTheta(t) for every real t. Consequently
 gammaHardyPhase(t)=exp(-i*Theta_src(t)).
All clock scales, conductor and linear normalization must be retained.

The first moment u*g(u) is integrable: e^(2u)>=1+2u implies
u*g(u)<=(u+1/2)e^(-u/2), hence an exponential majorant. The global elementary
bounds |x-sin x|<=2*x^2 and |1-cos x|<=|x| give absolute convergence and a
locally uniform integrable derivative envelope. Differentiation gives
Q'(t)=integral(1-cos(t*u))*g(u)du. Subtract the two actual Gauss integrands
at 1/4+i*t/2 and 1/4 and change variables v=2u. Their real difference is
(1-cos(t*u))*g(u), so Q'(t)=(Re digamma(1/4+i*t/2)-Re digamma(1/4))/2.
Restoring the fixed linear term gives precisely gammaHardyPhaseRate(t).
Both source phase and gammaHardyTheta vanish at zero; derivative uniqueness
proves equality. The existing phase ODE then gives the original unitary
Gamma Hardy phase, rather than a branch chosen from a principal logarithm.

## Scope and audit

This is the archimedean phase part of the source-to-Hardy gap, not full
prime-Gamma compatibility, an arithmetic estimate, sub-unit control or RH.
The original finite compensated phase converges under every countably generated
cofinal endpoint pair eps→0+, R→infinity. Its exponentials have modulus one and
define actual unitaries on spectral SoninL2. Pointwise phase convergence and the
common modulus-one bound give strong convergence to the existing literal CCM
scattering unitary. Its symbol is exp(2i*Theta_src), while the zeta reflection
symbol is exp(-2i*Theta_src). The literal Hardy decomposition is retained.

Production: `formal/GaloisForLFunctions/RHTower/SoninGammaClockHardyPhase.lean`.
2026-10-04: final foreground `lake --old env lean
GaloisForLFunctions/RHTower/SoninGammaClockHardyPhase.lean -o
.lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninGammaClockHardyPhase.olean`
exits 0, empty diagnostic log. All 17 public definitions/theorems pass the
separate `/tmp` axiom audit: exactly propext, Classical.choice, Quot.sound.
RHTower umbrella wired; no umbrella/full build. Index exits 0 and records all
17 declarations. Lint exits 1 on 16 unrelated unreachable modules, with no
finding in this leaf. Logs: `/tmp/tg-c921-{final,axioms,index,lint}.log`.
No added axioms, numerical experiments, assumed convergence or heartbeat increases.

Contribution: closes literal archimedean phase-source identification and original
cutoff strong unitary admission. It does not establish trace-norm convergence of
the tested varying commutator, the completed joint cubic comparison, native
prime–polar energy summability, strict contraction, or RH.
