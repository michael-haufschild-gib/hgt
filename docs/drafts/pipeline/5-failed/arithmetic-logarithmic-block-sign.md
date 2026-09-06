# Universal nonpositive complete logarithmic turns

- **Stage:** 5-failed
- **Type:** closed no-go with formal positive survivor
- **Frozen claim:** B1 in [the original phase-block card](../1-in-progress/arithmetic-log-phase-blocks.md).

## Refuted statement

For every `sigma>0`, `t>0`, integer `N>=1` with `t<2*pi*N`, and natural k, B1 claimed that the fixed-anchor imaginary Bernoulli remainder contribution over

`[N*exp(2*pi*k/t), N*exp(2*pi*(k+1)/t)]`

was nonpositive. The anchor is `N^(-s)`, where `s=sigma+i*t`. No zero-location assumption occurs in B1.

The Lean theorem `not_all_complete_logarithmic_turns_nonpos` disproves this universal law even for each fixed `sigma>=-1`. At `t=(4*pi/3)*N`, the second turn, k=1, is positive at arbitrarily large N. Its endpoints are `N*exp((3/2)/N)` and `N*exp(3/N)`. The height remains strictly below `2*pi*N`. The proof retains the actual periodic quadratic, power weight, complex conjugation, and original anchor.

This is now an analytic refutation, independent of the earlier numerical counterexamples. It is not restricted to a constant-speed model. It does not assert these heights are zeros or rule out a zero-specific theorem. The finite integral is well-defined also at `sigma=-1`; the original convergent-tail interpretation only needs the positive-sigma subcase used by B1.

## Strongest positive residue

The source has an exact scaling limit. For fixed `sigma>=-1`, fixed lambda, and `0<=a<=b`,

`N^(2*sigma+2)*Im[N^(-s)*integral_(N*exp(a/N)..N*exp(b/N))b(x)*x^(-conjugate(s)-2) dx]`

converges to `integral_(a..b)b(v)*sin(lambda*v) dv` as integer N tends to infinity with `s=sigma+i*lambda*N`. This limit, its change of variables, and the complex phase transport are proved in Lean.

For every fixed complete prefix ending at a noninteger constant-speed coordinate and with `0<lambda<2*pi`, the limiting prefix is strictly negative. The actual logarithmic prefix is therefore eventually strictly negative. This survivor is both paper-proved and formalized, including the source integral; it is not an unproved replacement hypothesis.

Positive complete turns and negative cumulative prefixes can coexist. B1's failure does not refute B2, C, the below-threshold whole-tail conjecture R, or RH. At integer endpoint coincidences the limiting prefix is zero, but the separately frozen [first variation is now proved](../3-formalized/arithmetic-clock-first-variation.md). Its exact coefficient is strictly negative, completing the positive survivor: every fixed positive complete prefix is eventually negative, including integer endpoints. This includes the literal source and is both paper-proved and formalized. The cutoff may depend on the prefix; no common cutoff for every turn number is supplied.

## Certificate and exact remaining gap

Module: `ArithmeticLogarithmicPhaseScaling`; [formal statements and audit status](../3-formalized/arithmetic-logarithmic-phase-scaling.md). Scratch, source, targeted leaf build, all sixteen public axiom checks, and repository lint passed. The umbrella import and corpus index are updated.

The route must use cumulative arithmetic cancellation if it proceeds. Neither this limit nor a possible proof of the tail conjectures supplies the missing independent constraint at the unit remainder of a zeta zero. No claim that all alternative arithmetic identities are impossible is made.
