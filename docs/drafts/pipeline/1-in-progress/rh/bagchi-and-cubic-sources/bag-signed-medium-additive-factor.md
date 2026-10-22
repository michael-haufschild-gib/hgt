# BAG signed medium additive factor

- **ID:** BAG-C28.56h
- **Stage:** 1-in-progress
- **Target:** C28.44 actual full signed Gaussian cubic at o(N/log²N)
- **Corpus basis:** ChiPrimeGaussianCubicPrimeOnlyVaughan; ChiPrimeVaughanIntegerAliases; Sieve/HeathBrownIdentity; Sieve/MenonHeathBrownSixFactorDichotomy; Sieve/MenonHeathBrownMediumMobiusFactor; Sieve/MenonHeathBrownMediumMobiusExclusion.

## Hard mathematical problem

Construct cancellation of the actual signed medium Möbius factor against the additive product phase, with the original shared prime q,r sums, incomplete integer interval, noncontraction masks and coupled Gaussian/W amplitudes retained. The finite compressed Heath–Brown identity is already proved below its exact support cutoff. Its medium/long dichotomy does not eliminate the medium Möbius alternative in this additive problem. No new identity wrapper or assumed analytic estimate constitutes closure.

## Failed steps and exact lessons

1. Real-fraction injectivity is insufficient even for exact integer-sampled collisions. C28.56d has a formal actual-prime-cofactor family with growing non-identical alias energy and coefficient -1. The same construction does not lower-bound the full signed cofactor sum.
2. Separating the residue zero mode and applying ordinary Farey large sieve after complete-period enlargement still loses a conductor power. This is a paper scale check of a proposed proof estimate, not a lower bound for the source.
3. Existing Kloosterman complete-period orthogonality leaves incomplete physical intervals in its remainder. An inverse-unit kernel is not automatically the product-frequency kernel.
4. The actual medium-factor theorem bounds logarithmic Dirichlet phases. A Mellin transfer must account for the transform norm and retain joint q,r cancellation; the word “medium” or a polynomial frequency horizon does not supply that transfer.

## Next conjecture and proof test

The actual short-factor expansion permits a signed joint estimate before Cauchy or completion discards the medium-cofactor and modulus correlations. Test the medium branch directly. If a proposed transform only recovers an N^(3/2) envelope or charges a missing cancellation as a premise, reject that estimate and retain the precise remaining signed carrier. Do not retire BAG or infer RH from an exact expansion.

## Status

No proof of the new additive estimate yet. C28.56d positive survivor is fully audited in its own failed-estimate card. Full cubic, growing moments, moving cofactors, positive self-target recurrence, MUST270 and RH remain open. No numerical experiments or subagents.

## C28.56i — finite prime dilation: paper argument and failed transfer

Corpus ingredients inspected: `Sieve/TuranKubilius.sum_omegaCount_variance_le`,
`Sieve/SharedPrimeTail.sum_inv_sq_bigPrimeSet_le`, actual Möbius multiplicativity,
and `Sieve/MertensSecond.le_mertensS`. These suggest the following finite
amplification, with no numerical experiment. This paragraph is a paper argument,
not a Lean theorem or a claimed cubic estimate.

Write e(x)=exp(2πix), P={primes ≤z}, H=Σ_{p∈P}1/p, J=|P|, and
S=Σ_{1≤n≤M}μ(n)e(αn). Turán–Kubilius and finite Cauchy give

    |H S − Σ_{n≤M} μ(n)e(αn)ω_P(n)| ≤ √(M(MH+J+2J²)).

Reindexing the divisor count gives Σ_p Σ_{m≤M/p} μ(pm)e(αpm).
For p∤m, μ(pm)=−μ(m); for p|m, μ(pm)=0. Thus its difference from
−T, where T=Σ_m μ(m)Σ_{p∈P,pm≤M}e(αpm), has norm at most
Σ_p⌊M/p²⌋≤M. The correction is μ(m) on p|m, not μ(pm), which vanishes.
Cauchy and the exact expansion of the inner square then give

    |T|² ≤ M [MH + Σ_{p≠q∈P}
                     |Σ_{1≤m≤min(M/p,M/q)}e(α(p−q)m)|].

For fixed irrational α, every off-diagonal geometric sum is bounded
independently of M. For fixed z, the resulting limsup of |S|/M is at most
2/√H+1/H; subsequently letting z grow gives a paper proof of cancellation at
each fixed irrational frequency. A finite uniform version excludes frequencies
with |e(α(p−q))−1| smaller than C/M. Uniform treatment of the excluded rational
arcs would additionally require fixed-progression Möbius cancellation and
partial summation; these inputs have not been constructed here.

**Transfer failure:** even uniform pointwise o(M) in this argument cannot be
inserted into the cubic followed by an absolute q,r sum and called closure.
It supplies no missing conductor-power saving. Do not spend a production leaf
on the fixed-irrational corollary as though it solved the actual medium branch.
The positive paper statement above is retained, not retired or falsely marked
formalized.

## C28.56j — joint incomplete correlation: current hard conjecture

Keep the actual joint row inside the amplified sum. Its cross terms then have
the phase

    e(m(ℓ₁q₁/r₁ − ℓ₂q₂/r₂)),

with the original Gaussian/window amplitudes, squarefree/coprimality masks,
cofactor weights and truncated m interval. These amplitudes depend on m;
the expression is not automatically an unweighted geometric sum. Any partial
summation must retain its boundary terms and variation costs.

For distinct prime r₁,r₂, prime q₁≠r₁, and 0<ℓ₁<r₁, exact integer frequency
collision is impossible. Indeed an integer equality, cleared by r₁r₂, forces
r₁|ℓ₁q₁r₂. Primality and the three exclusions contradict this. The statement
is a paper observation about exact collisions only, not a spacing estimate.
In particular it does not remove same-modulus aliases from C28.56d.

The near-resonance numerator is the signed integer

    Δ_k = ℓ₁q₁r₂ − ℓ₂q₂r₁ − k r₁r₂.

For an m interval of length M, |Δ_k| of order r₁r₂/M remains a coherent scale.
Excluding Δ_k=0 gives only spacing of order 1/(r₁r₂), too small to force
cancellation on the incomplete interval. The corpus four-dimensional double
large sieve uses nonnegative weighted near-energies; it does not retain the
signed cancellation of this determinant sum. No improvement at the required
contraction scale has been deduced from it.

There is also a pre-correlation cost which the scalar argument does not solve.
For a joint weight G(n), the Turán–Kubilius comparison error is bounded by

    (Σ_{n≤M}|G(n)|²)^(1/2) (MH+J+2J²)^(1/2),

not by √(M(MH+J+2J²)) unless |G|≤1. The actual q,r aggregate is not a unit
phase. Bounding G by the absolute q,r sum restores the lost conductor power;
assuming the needed joint energy would relocate the open problem. If G is
squarefree-restricted, the p|m reindexing error vanishes, but G(pm) retains the
resulting coprimality masks in every correlation. They cannot be discarded to
recover a plain geometric sum.

**Next proof obligation:** estimate this actual signed, amplitude-weighted
incomplete determinant correlation before any absolute cross-modulus bound.
Any prime-dilation proof must also control the weighted comparison error above,
or replace that comparison by a proved identity that preserves the source.
The required saving must be checked after every Heath–Brown/Vaughan factor and
modulus sum is restored. A correlation hypothesis, removal of its near-resonant
part, complete-period replacement, or another exact expansion is not a proof.

Turn evaluation: two transfer mechanisms were tested and their missing terms
identified; no hard analytic gap was closed and no new Lean result is claimed.
The full cubic remains the target. This card stays in progress.
