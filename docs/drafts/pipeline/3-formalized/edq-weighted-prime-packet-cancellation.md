# EDQ weighted prime-packet cancellation

Stage: 3-formalized. [BRIDGE] derived theorem; dependency-closed paper proof and Lean proof complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: isolate a growing, positive packet in the actual weighted carrier and prove the precise relative cancellation supplied by the remaining literal Möbius coefficients.

## Paper proof

Let U_N be the primes p with N/2<p<=N. In the existing carrier put
P_N=sum_(p in U_N) bdGen(1/p), F_N=bdMobiusModularApproximantVec N,
and R_N=F_N-P_N. Since mu(p)=-1, R_N is exactly the finite generator
combination with the U_N coefficients deleted, retaining every other coefficient.

For positive m,n and K<min(m,n), the first K terms of the genuine
discrete Gram series each satisfy
k^2/(m*n*k*(k+1)) >= 1/(2*m*n), 1<=k<=K.
All subsequent terms are nonnegative. Consequently
bdGram(1/m,1/n)>=K/(2*m*n). Summing over U_N twice gives
norm(P_N)^2 >= (K/2)*(sum_(p in U_N)1/p)^2.
Take K=floor(N/2). The existing theta-window theorem with exponent 3/4
gives card(U_N)>=N/(32768*log N) eventually. Since p<=N, the reciprocal
sum is at least card(U_N)/N; since K>=N/4 for N>=4,
norm(P_N)^2 >= N/(8*32768^2*(log N)^2) eventually.

The existing full Möbius norm saving gives, for every fixed q,
norm(F_N)^2*(log N)^q/norm(P_N)^2 -> 0.
Taking a square root gives norm(F_N)/norm(P_N)->0. The reverse triangle
inequality applied to R_N and -P_N gives norm(R_N)/norm(P_N)->1.
Finally inner(P_N,R_N)=inner(P_N,F_N)-norm(P_N)^2 and Cauchy–Schwarz give
Re inner(P_N,R_N)/norm(P_N)^2 -> -1. Dividing by the complementary norm ratio also gives
Re inner(P_N,R_N)/(norm(P_N)*norm(R_N)) -> -1.
These are actual weighted source identities and limits, with the entire tail retained.

## Meaning and remaining gap

Uniform-period orthogonality conceals large weighted destructive interference:
the isolated prime packet and its actual complement asymptotically oppose
each other. Relative cancellation is already unconditional, even with arbitrary
fixed logarithmic savings. It does not give a polynomial-log bound on the
absolute residual energy because the packet itself grows. The unresolved
EDQ producer remains an absolute cofinal logarithmic ceiling; RH remains open.

## Corpus basis and scientific method

BaezDuarteGramDiscrete supplies the genuine positive Gram series;
BaezDuarteGram its finite carrier quadratic form;
BaezDuarteMobiusPrefixApproximation the exact Möbius generator coefficients;
PrimeCountShell and Sieve.ShortIntervalThetaEveryWindow the prime count;
EulerDeletionMobiusGlobalLogSaving the complete residual upper saving.
EulerDeletionPeriodAveragingObstruction defines the same upper-half prime set.
HTGeometry.SignChoiceNormalizedDistance was inspected for normalization geometry;
here the sign is fixed by the literal source decomposition, so direct complex
Cauchy–Schwarz and the reverse triangle inequality suffice.

This is a visible deduction, classified [BRIDGE] under docs/meta/scientific-method.md.
No numerical experiment is run: its outcome is predicted by the paper proof.
It neither replaces the primary RH objective nor asserts the missing ceiling.

## Lean validation

`EulerDeletionWeightedPrimeCancellation.lean`, namespace `RHTower.DeletionPrimePacket`,
contains two definitions and eleven public theorems. `remainder_eq_remaining_sum`
identifies the actual surviving coefficients. `gram_lower_of_common_head` and
`packet_norm_sq_lower` give the full weighted finite-head lower bounds;
`upperPrime_card_eventually_lower`, `packet_norm_sq_eventually_lower`, and
`packet_norm_eventually_pos` provide arithmetic growth and valid normalization.
`source_relative_energy_log_pow_tendsto_zero` retains every fixed logarithmic
order. The final four limits give residual norm decay, complementary norm ratio,
energy-normalized signed inner product, and the normalized real inner product.

The complete scratch proof passed `lake env lean` without diagnostics. The targeted
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionWeightedPrimeCancellation`
built only this new leaf, in 22 seconds; no umbrella build was run. All thirteen
new public declarations were audited once through a temporary `lake env lean`
file. Their dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`;
there is no admission, added axiom, or numerical certificate. The leaf is wired into
`RHTower.lean`. Formal lint passed; the search index was refreshed. Scoped whitespace, declaration
coverage, umbrella, and documentation-link checks passed. All owned Lean processes
exited, and the temporary proof/API/audit source files were removed. No numerical
experiment was run.
