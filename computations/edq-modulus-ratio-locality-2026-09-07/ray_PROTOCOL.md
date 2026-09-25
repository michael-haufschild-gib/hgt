# Frozen follow-up: fixed reduced denominators in the distant bands

Freeze after reading the first diagnostic, before any new numerical evaluation.
The first run found that every ratio-(16,32] band is negative and every
ratio-(32,64] band positive, with similar sizes across the nine frozen cutoffs.
This new question is attribution of those bands, not an extension of the
rejected ratio-four localization test or evidence for an asymptotic ceiling.

For coprime a>b>=1, d=r*a,e=r*b, the exact identities are

```
K(r*a,r*b)=K(a,b)/r,
mu(r*a)*mu(r*b)=mu(a)*mu(b)*mu(r)^2*[gcd(r,a*b)=1].
```

Thus the contribution of this reduced pair to the complete complementary
flux at N is

```
-mu(a)*mu(b)*K(a,b)
 *sum_(N/a<r<=N/b, gcd(r,a*b)=1) mu(r)^2/r.
```

All terms in its r sum are nonnegative. These identities supply a reason to
test fixed reduced denominators as an explanation of scale-stable band signs;
they do not predict their aggregate numerical share.

Frozen [BRIDGE] prediction: reduced denominators b<=4 approximate each of the
two distant signed bands within one quarter of its magnitude, at every one of
N=32,48,64,96,128,192,256,384,512. Since b=1 has zero kernel and mu(4)=0,
the predicted contribution comes entirely from b=2,3. Report b cutoffs
2,4,8,16,32 as diagnostics, without changing the primary b=4 criterion.

Use the archived complete band intervals from results.json and the same
baseline_kernel_bounds.npz. Every selected reduced-pair contribution retains
the exact finite r range and the complete infinite j kernel. Form full omitted
reduced-denominator intervals by subtraction. Report all signed values.
SURVIVES_FINITE_TEST iff all 18 upper relative errors at b=4 are <=1/4;
REVERSED if any lower relative error exceeds 1/4; UNRESOLVED otherwise.
No subsequent cutoff is promoted to the primary criterion after results.

Validate the two homothety identities for every a<=64,b<=16,r<=16 with
gcd(a,b)=1; require kernel interval overlap and exact integer Möbius equality.
At N=32 and 96 reconstruct each entire band by all b<=N using an independent
literal d,e enumeration, and require overlap with its saved interval.
Numerical margin remains 1e-8. These are floating evaluations of analytic
intervals, not certified rounding bounds or Lean evidence.

Run on authorized RunPod only, eight cutoff workers, numerical threads one,
120-second external timeout. Freeze input hashes. Download ray_results.json,
ray_run.log, and hashes; verify them and clean owned remote files. Reuse the
first experiment's archived support script and inputs without changing them.

If the prediction survives, attempt a bound for the complete remainder after
subtracting the explicit b=2,3 arithmetic rays. If it fails, retain the wider
reduced-denominator source and do not substitute an empirically chosen cutoff.
