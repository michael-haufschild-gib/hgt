# The pure-exponential critical endpoint diverges

Status: [FORMALIZED; GLOBAL LINT HAS THREE UNRELATED UMBRELLA ERRORS]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Objective and plan

Close the remaining equality case at the local rate r(y)=2*pi*exp(-|y|).
Strengthen the necessary coefficient moment at that rate and extend the
positive-exponential actual-probe divergence result to equality.

1. Audit the full-kernel central lower proof, exponential convexity, harmonic
   divergence, and the existing local rate/probe theorems. Done.
2. Prove a central lower estimate with variable radius d>0 for full K.
3. Choose d=exp(-z) and prove K(z)>=D*exp(-z)*exp(-2*pi*exp(z)), z>=0.
4. Transfer this to a paired-kernel critical harmonic envelope, derive the
   necessary critical damping moment divided by n, and prove exact pure-
   exponential summability iff rho<r(y).
5. Extend the actual majorant probe's plus-infinity result to rho>=2*pi/m.
6. Compile/export, audit all public declarations, wire/index/lint, promote,
   update predecessor endpoint notes, save memory, clean owned scratch.

## Dependency-closed paper proof

The corpus has Phi(t)>=2*pi^2*exp(-pi*exp(2|t|)). On
I=(z/2-d,z/2+d], z>=0 and d>0, both |t| and |t-z| are at most z/2+d.
Integrating the constant product lower bound over this interval yields

 K(z) >= 2*d*(2*pi^2)^2*exp(-2*pi*exp(z+2*d)).

Use d=exp(-z), so 0<d<=1. Convexity of exp on the chord from 0 to 2 gives
exp(2*d)<=1+(exp(2)-1)*d. Since exp(z)*d=1,

 exp(z+2*d)<=exp(z)+(exp(2)-1).

Thus with D=2*(2*pi^2)^2*exp(-2*pi*(exp(2)-1))>0,

 K(z)>=D*exp(-z)*exp(-2*pi*exp(z))  for every z>=0.

At fixed y, eventually z=log n-|y|>=0. Evenness of K makes K(z) one of
the two paired terms P_y(n). Its lower envelope becomes

 P_y(n)>=(D*exp|y|/n)*exp(-r(y)*n).

Multiplying by |v(n)| proves that potential summability forces summability of
|v(n)|*exp(-r(y)*n)/n. At v(n)=exp(r(y)*n), this is the divergent harmonic
series, so equality cannot converge. Combine with the already proved strict
subcritical convergence and supercritical divergence to obtain the exact iff.

For lam(n)=Lambda(n)+sqrt(n)*exp(rho*n), normalized deviation is exp(rho*n)
for n>=2 and zero below, and deficit is identically zero. Removing two terms
does not affect summability. For rho>=2*pi/m the signed sample therefore
diverges, so the already proved finite-local-deficit theorem forces the actual
real-cutoff probe to plus infinity, including equality.

No sharp polynomial prefactor or universal statement about arbitrary critical-
rate sequences is claimed. Additional polynomial damping requires separate
analysis. No new analytic hypothesis is introduced.

## Corpus audit

Direct lexical search: 2112 declarations, 579 modules, 929 eligible entries;
cached output has no partial/coverage fields. Existing full autocorrelation
lower envelopes require rate strictly above 2*pi; fixed-radius estimates lose
the critical constant. The shrinking interval removes that loss.
`convexOn_exp.2` is already used in GeometricCDDFiniteRealTBA and other corpus
modules. CCMRiemannKernelBartaLayerBounds' declaration inventory concerns Phi
and cutoff layers, not this full-autocorrelation endpoint; no import is needed.

## Verification

- Library names checked in scratch against the installed toolchain.
- `WeilLogShiftCriticalEndpoint.lean` compiled/exported directly with
  `lake --old env lean <leaf> -o <local olean>`; final exit 0, no diagnostics.
- Eight public theorems cover the variable-radius and critical kernel bounds,
  paired harmonic envelope, necessary moment, exact endpoint classification,
  and actual majorant probe divergence including equality.
- All eight public theorems passed scratch `#print axioms`; only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- Umbrella import added. Index refresh succeeded and all eight public API rows
  were inspected. Scoped `git diff --check` passed.
- Global formal lint exited 1 on three unrelated unreachable modules:
  `RHTower.CCMRiemannKernelBartaEdgeFormDomain`, `HTGeometry.CStarEnvelope`, and
  `HTGeometry.CompactKernelAlgebra`. Their sources/imports were not modified.
  The preceding BartaLayerBounds error no longer occurs.
- Endpoint outlook notes were updated on the subexponential-domain,
  local-decay-threshold, reflection-duality, and domain-boundaries proof cards.
- All owned jobs exited. Owned `/tmp/hgt-weil-critical-endpoint-*` scratch files
  were removed after recording evidence. No numerical experiments, new axioms,
  unproved analytic inputs, heartbeat increases, full/umbrella builds, commits,
  or subagents.

All scoped steps are formalized. The exact new insight is that a shrinking
integration window preserves the critical double-exponential constant while
losing only a harmonic factor at logarithmic integer coordinates. That factor
still diverges, so pure-exponential convergence is exactly strict subcriticality.
The previously open equality case is now closed; this does not classify arbitrary
additional polynomial damping.

## Further targets, not formalized here

The new endpoint theorem suggests a sharper all-probe obstruction with rate pi:
lam(n)=Lambda(n)+sqrt(n)*exp(pi*n) should have convergent origin potential while
every probe m>=2 tends to plus infinity and has divergent sampled potential.
More generally, lifting the already constructed reciprocal weights to arithmetic
coefficients should realize any chosen finite probe-convergence radius, with
finite limits inside and one-sided infinite limits outside. This could test
whether cofinality of the probe family is necessary, even for zero-excess
minorants. Audit realization and finite-head removal before implementation.
