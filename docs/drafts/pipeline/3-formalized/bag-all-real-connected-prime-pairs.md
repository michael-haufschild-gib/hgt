# BAG all-real connected prime-pair trace

- **ID:** BAG-C28.56u
- **Stage:** 3-formalized
- **Type:** unconditional Lean theorem
- **Target:** remove the rational-denominator restriction from the actual Gaussian prime-pair estimate, with the entire prime diagonal subtracted.
- **Status:** direct production and all five public axiom audits pass. Only propext, Classical.choice and Quot.sound occur. C28.44 and RH remain open.

## Exact source basis

The growing-twist work in ChiPrimeGaussianGrowingTwists retains the literal
full-band coefficients, the complete Gaussian height integral, every pair and
the exact frequency log(A*p)-log(B*q). Its high-cutoff singular-product and
Gaussian integer-kernel proofs are the ingredients to extend, not an assumed
pair-correlation law.

Mathlib.NumberTheory.DiophantineApproximation.Basic, theorem
Real.exists_rat_abs_sub_le_and_den_le (line147), supplies for every real beta
a reduced a/b with b<=K and |beta-a/b|<=1/((K+1)*b). No irrationality or
distribution premise occurs.

Sieve.PrimeDilationFullSieve.card_primeAffinePair_full_mertens_le (line113)
counts the complete n in [1,M] with a*n+c and b*n+d prime. The anchor primes
c,d are arbitrary above the sieve height. Its denominator retains the full
discriminant and slope singular factors and its finite remainder. This is the
right source for a localized progression; the old global box bound P/B alone
does not exploit a short translated block.

## Exact complete connected average

Let P_N(t) be the actual primeGaussianChiField 1 N t and let

    E_N = sum_{p in the original prime band} |V(p/N)/sqrt(p)|^2.
    A_N(beta,t0) = integral_u exp(-pi*u^2)
      * exp(-i*log(beta)*(t0+2*pi*N*u)) * |P_N(t0+2*pi*N*u)|^2.
    D_N(beta,t0) = E_N * exp(-i*t0*log(beta))
      * exp(-pi*(N*log(beta))^2).

For N=K^2, the paper proof gives log(N)*|A_N-D_N| -> 0 uniformly in
beta in [1/2,2] and t0 in R. D_N is the EXACT p=q contribution, not merely
the value at beta=1. Near-identity twists with |log beta| of order 1/N retain
this whole Gaussian diagonal packet. Do not discard it by excluding beta=1.

## Dependency-closed proof

1. Choose the source Dirichlet approximant a/b to beta. For K large, a>0,
   a<=3b<=3K, b<=K and gcd(a,b)=1. Put delta=beta-a/b.
2. Partition the entire q band (N,2N] into consecutive integer blocks of
   width b*K, indexed by floor(q/(b*K)). Including the final partial block,
   block count times b is at most 3*K. No prime is omitted.
3. On a block starting at q0, set v=b*p-a*q and c0=b*delta*q0.
   The moving centre b*delta*q drifts by at most b across the block, since
   |delta|<=1/(b*K). The logarithmic gap estimate therefore bounds the exact
   Gaussian kernel by C*exp(-c*((v-c0)/b)^2), with absolute constants.
   More precisely, replacing c0 by floor(c0) gives the upper kernel
   exp(1)*exp(-(v-floor(c0))^2/(64*b^2)). Its complete integer v sum is
   O(b), uniformly in c0; both approximation drift and floor error remain.
4. For each nonempty fixed-v fibre inside that block, take its least prime
   anchor. Coprimality parametrizes p=p0+a*n, q=q0'+b*n. The block width gives
   0<=n<=K. Apply the literal full affine sieve to every n>=1 and retain the
   anchor as +1. The discriminant is v, independent of the anchor.
5. For p!=q, v=0 is impossible: a,b<both band primes, so prime divisibility
   would force a=b=1 and p=q. All surviving discriminants are nonzero, and
   |v|ab<=24*K^5 over the entire finite source. With lower cutoff ceil(16 log K)
   and sieveSift K, the surviving singular product is bounded below exactly
   as in C28.56t. Each fibre costs O(K*(log log K/log K)^2+K^(3/4)+1).
6. Multiply the O(b) determinant mass by the O(K/b) block count and divide by
   N=K^2 from the actual coefficient products. The complete connected average
   is O((log log K/log K)^2+K^(-1/4)). Its product with log N vanishes.

The formal proof constructs the localized affine-fibre transport, shifted
integer Gaussian estimate, and entire prime-band partition. None is an assumed
hypothesis. The block size follows from Dirichlet approximation and retains
the complete source.

## Lean theorem and audits

Production: formal/GaloisForLFunctions/RHTower/ChiPrimeGaussianGrowingTwists.lean,
namespace RHTower.GaussianPrimeTwist. New declarations realAverage,
diagonalPacket and exists_connected_negligible_error implement exactly the
average, diagonal and uniform vanishing envelope above. The old growing
rational-twist theorem remains. Shared sieve main/remainder helpers avoid
copying the original analytic proof; the leaf has 1351 lines.

- Scratch73415: exit0, no diagnostics, entire capstone.
- Production63415: exit0, no diagnostics, lake --old env lean leaf with output
  olean. Log /tmp/bag-connected-final-01a0.log.
- Axiom51041: exit0. All five public declarations depend exactly on propext,
  Classical.choice and Quot.sound. The printed capstone has no outside
  hypotheses. Log /tmp/bag-connected-axioms-01a0.log.
- Existing RHTower umbrella import verified, no umbrella or full build.
- Index22520: exit0, generated API/gaps/overview refreshed.
- Lint46914 (--check-generated): exit1, exactly 16 unrelated unreachable
  modules; no generated-index error and no finding for this leaf.
- No numerical experiments, extra axioms, heartbeat changes or subagents.

## What remains after this theorem

Even uniform control of every real connected twist does not sum the signed
BAG mode family without its actual coefficients and transfer costs. All modes
are demodulated: their surviving height-centre phase is exp(i*t0*lambda), with
lambda the residual pair frequency near zero. A large-sieve argument treating
the bare log(beta) as separated output frequencies would discard this residual
phase. Retain the signed aggregate, moving zero-trace weights, nearby distinct
zeros, finite exponent inversion and contraction subtraction.

## Log

- 2026-10-04 — Conjecture based on the source full affine sieve, Dirichlet
  approximation and C28.56t exact Gaussian trace.
- 2026-10-04 — Localized sieve, shifted kernel and full block sum checked in
  scratch91284. Entire height-average capstone checked in scratch73415.
  The final partial block requires (#blocks)*b<=3K and is retained.
- 2026-10-04 — Production63415 and axiom51041 passed. Card moved to formalized,
  frontier/main BAG/zero-form records updated. Superseded scratch and proof
  fragments removed; audit logs retained. RH goal remains ACTIVE.
