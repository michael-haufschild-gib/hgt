# RP71: separate signed mixed payment fails

- **Stage:** 5-failed
- **Route:** RP, separate payment mechanism only
- **Positive survivor:** cofinal subcritical exponential escape, formalized

The proposed mechanism would pay the literal complete late-prime mixed
work by a bounded signed primitive Q on a late physical ray, even though
its absolute integral is infinite. It fails for every0<epsilon<1/2.

The strongest proved survivor is substantially stronger: for every
b<1/2-epsilon and real C,A, some t>A satisfies

    |Q(t)| > C*exp(b*t).

Here Q is the actual routePNativeLatePrimeMixedPrimitive; no surrogate
prime core, missing removal atom, or altered physical cutoff is used.
The exact corrected primitive absorbs the full Q-weighted reciprocal
jump sum. A hypothetical envelope would admit its two ordinary Laplace
terms and kill the terminal boundary. The exact weighted FTC identifies
the candidate far to the right. Adding the finite source head and
subtracting the actual decaying correction gives an analytic source
continuation across the Hardy axis, contradicting the unconditional
variable-width source obstruction.

Paper proof: dependency-closed. Lean proof:
RHTower.NativeMixedLaplace.nativeMixedPrimitive_exponential_escape,
RoutePNativeMixedGrowthBarrier.lean, final audit55535 exit0.
All four supporting new leaves are wired. Axiom audit78542 exited0:
all14 audited public theorems use only propext, Classical.choice and
Quot.sound. Global lint has12 unrelated unreachable-module errors and
none in these new leaves. Full construction and audit history:
[formalized card](../3-formalized/rp-native-signed-mixed-primitive-2026-10-04.md).

This does not rule out joint cancellation with the complete square.
It proves neither one-sided escape nor two-sided sign oscillation, and
does not decide RH. The positive-damping joint energy problem, signed
high-LCM payment and both physical history debts remain open.
