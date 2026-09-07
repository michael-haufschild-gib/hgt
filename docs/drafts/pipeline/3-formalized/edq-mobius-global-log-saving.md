# EDQ full-source logarithmic saving

Stage: 3-formalized. [BRIDGE] derived theorem; dependency-closed paper proof and Lean proof complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: derive an unconditional upper bound on the complete arithmetic energy and signed Gram cross sum, using actual Möbius cancellation with the entire tail retained.

## Paper proof

Let M(k)=sum_(d<=k) mu(d), H_N=sum_(d<=N) mu(d)/d, and A_N(n)
be the literal unweighted deletion primitive (negative modular approximant).
Suppose N,L>=1 and abs(M(k))<=epsilon*k for every k>=N.
For N<n<=N*L the omitted floor sum is
sum_(N<d<=n) mu(d)*floor(n/d).
Its coefficient prefixes M(N+j)-M(N) have absolute value at most
2*epsilon*n. Its nonnegative floor weight decreases, starting at no
more than L. Finite Abel summation bounds this whole signed sum by
2*epsilon*n*L. The exact global residual identity therefore gives,
for every 1<=n<=N*L,
abs(A_N(n))<=1+n*(abs(H_N)+2*epsilon*L).
The known exact initial identity covers n<=N.

Put b=abs(H_N)+2*epsilon*L. On the first T=N*L coordinates,
abs(A_N(n))^2/n^2 <=2/n^2+2*b^2. The full inverse-square sum is
at most 2. Beyond T use abs(A_N(n))<=N and the inverse-square tail
bound 1/T. Genuine fixed-cutoff summability then gives the full estimate
E_N <=4+2*N*L*b^2+N/L.
The modular carrier norm squared is at most E_N by termwise comparison
of 1/(n(n+1)) with 1/n^2. Together with the existing reverse estimate,
norm(rawVec_N)^2 <= E_N <= 2*norm(rawVec_N)^2. Its signed cross sum is
at most that norm squared because the complete diagonal is nonnegative;
in absolute value it is at most E_N plus that diagonal.

For any prescribed q, put r=q+1, P=(log N)^r and L=floor(P).
Eventually P>=2, P/2<=L<=P. The corpus gives a constant C>=0 such
that, for all k>=N, abs(M(k))<=C*k/(log N)^(2*r); it also gives
abs(H_N)<=1/(log N)^(2*r) eventually. Set epsilon=C/P^2.
Then b<=(1+2*C)/P, so the finite energy bound is at most
4+(2*(1+2*C)^2+2)*N/P. Eventually P<=N, hence E_N<=B*N/P
for one fixed B. The diagonal is eventually at most 4*log N, which is
absorbed by 4*N/P. This supplies arbitrary logarithmic savings relative
to N, unconditionally, for the full energy, full modular norm, and
absolute signed cross sum. Each of these quantities times (log N)^q/N
tends to zero for every natural q. The existing actual-zero current
transfer gives the same limit for abs(Re Q_N(rho)) at every actual zero.
No part of the infinite tail is dropped.

## Remaining gap

N divided by any fixed logarithmic power still grows faster than every
fixed logarithmic power. These source upper bounds therefore coexist
with the already proved superlogarithmic escape at hypothetical off-line
zeros. They are actual producer estimates, but do not supply the cofinal
polynomial-log ceiling required by the EDQ RH receiver. No RH conclusion
or off-line zero existence is asserted.

## Corpus basis

EulerDeletionMobiusPrimitiveEnergy: exact global primitive identification,
summability and current transfer. EulerDeletionMobiusGramCancellation:
full carrier Gram decomposition and nonnegative diagonal.
BaezDuarteMobiusPrefixApproximation: exact initial and omitted-floor
identities. Sieve.MoebiusHarmonicArbitraryLogRate: unconditional Mertens
and harmonic savings at every logarithmic order. Finite Abel summation,
inverse-square head/tail comparisons, and the logarithm-versus-power
bound supply the remaining analytic steps. No numerical experiment is
needed for these deductions.

## Scientific-method classification

This is a [BRIDGE], as required by docs/meta/scientific-method.md: its
statement follows from a visible derivation using existing corpus estimates.
It is not a new primary conjecture and does not replace the RH objective
or the missing cofinal logarithmic current ceiling. No experiment is run:
the proposed bounds are mathematical deductions, whose outcomes are already
predicted by the paper proof. Any future numerical experiment must have an
uncertain, discriminating outcome capable of changing the approach to an
open problem, follow the scientific-method document, run only on RunPod,
use multicore code where appropriate, finish within bounded time, and have
results downloaded and documented under the prescribed computations directory.

## Lean result

`EulerDeletionMobiusGlobalLogSaving.lean`, namespace `RHTower.DeletionMobiusGlobal`,
contains 12 public theorems. `floorResidual_le_of_mertens` and
`primitive_extended_prefix_le` retain the literal omitted floor sum.
`primitiveEnergy_le_of_extended_prefix` gives the complete finite-head/tail
bound for every positive integer T; `primitiveEnergy_le_of_mertens` specializes
it to T=N*L. `modular_norm_sq_le_primitiveEnergy` closes the reverse carrier
comparison. `primitiveEnergy_log_saving`, `modular_norm_log_saving`, and
`abs_cross_log_saving` give the unconditional eventual bounds. The four
`*_log_pow_div_tendsto_zero` theorems give the stated weighted limits, including
the full real current at every actual nontrivial zero.

Validation: the complete scratch file passed `lake env lean` without diagnostics.
The final targeted `lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusGlobalLogSaving`
compiled only this new leaf. All 12 new public declarations were audited once
via a temporary `lake env lean` file: dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`; no admission, added axiom, or numerical
certificate is used. The module is wired into `RHTower.lean`; no umbrella
build was run. The search index was refreshed. Repository-wide formal lint reported only three
unwired modules from concurrent work: `MobiusDivisorCoupledTwoSourceCone`,
`PartialSubsetEnergyOrder`, and `ThreePlaneSourceMargin`. The new EDQ leaf is
wired and has no lint error; the repository-wide gate is not claimed to pass.
Scoped whitespace, public-declaration coverage, umbrella, and documentation-link
checks passed. Temporary proof/API/audit source files were removed after all
owned Lean processes exited. No numerical experiment was run.
