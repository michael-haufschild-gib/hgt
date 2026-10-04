# BAG growing rational twists at the critical height

- **ID:** BAG-C28.56t
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Result:** complete Gaussian prime-pair averages are o(1/log N), uniformly in every height centre and every nontrivial reduced rational twist A/B with A,B<=sqrt(N), along N=K^2.
- **Lean:** RHTower.GaussianPrimeTwist.exists_negligible_error in ChiPrimeGaussianGrowingTwists.
- **Scope:** a new growing-family critical pair estimate. The signed cubic/zero trace C28.44 and RH remain open.

## Exact statement and normalization

Write P_N(t)=primeGaussianChiField 1 N t. The public definition
RHTower.GaussianPrimeTwist.average is exactly

    integral_u exp(-pi*u^2)
      * exp(i*(log A-log B)*(t0+2*pi*N*u))
      * P_N(t0+2*pi*N*u) * conjugate(P_N(t0+2*pi*N*u)).

The unconditional capstone constructs error:Nat->Real tending to zero such
that, eventually in K, log(K^2)*norm(average(K^2,A,B,t0))<=error(K)
simultaneously for all positive coprime distinct A,B<=K and all real t0.
All original prime-band coefficients and all prime pairs remain. No prime
pair, distribution, stationary-phase or zero-correlation estimate is assumed.
The window is this normalized Gaussian height window; no unproved replacement
by the moving BAG zero-trace weights is asserted.

## Source-based proof

1. The exact Gaussian transform converts the complete height integral into
   the finite prime-pair sum with phase exp(i*t0*lambda) and weight
   exp(-pi*(N*lambda)^2), lambda=log(A*p)-log(B*q).
2. For A<=B<=K, determinant v=A*p-B*q is nonzero: v=0 forces B|p;
   B<p then forces B=1 and hence A=B=1. Also |v|AB<=4K^5.
3. The source logarithmic gap inequality bounds the kernel by
   exp(-v^2/(16B^2)). Its complete integer sum is <=(1+4sqrt(pi))*B.
   Integrability, summability and the entire Gaussian tail are proved.
4. Start the full affine sieve at L=ceil(16 log K), with h=sieveSift K.
   The source prime-divisor harmonic bound gives sum_{p|d,p>L}1/p<=1/2
   for d=|v|AB. Thus the singular product is >=1/2. Mertens supplies the
   denominator (log h/log L)^2. The exact progression length floor(2N/B),
   the anchor and the finite sieve remainder remain.
5. Each determinant fibre costs at most

       1 + C*(N/B)*(log L/log h)^2 + 2*K^(3/4).

   The O(B) Gaussian determinant mass cancels the reciprocal B in the
   main term. Original coefficient products have norm <=1/N. Consequently
   the entire normalized average is bounded by

       C*((log L/log h)^2 + K^(-1/4)).

6. The source sieve height has log h>=log K/288. The logarithm of L is
   O(1+log log K), so multiplication by log N tends to zero. Conjugation
   covers B<A. The height centre contributes only a unit phase throughout.

The essential advance is retaining the short progression length and starting
above a logarithmic cutoff, instead of paying a power of the discriminant.
This constructs a critical-scale estimate for a growing twist family.

## Audit

- Direct production audit33237: exit0, no diagnostics, using
  lake --old env lean GaloisForLFunctions/RHTower/ChiPrimeGaussianGrowingTwists.lean
  with its output olean. Log: /tmp/bag-growing-twists-final-01a0.log.
- Both public axiom queries80065: exit0, exactly propext, Classical.choice,
  Quot.sound. Log: /tmp/bag-growing-twists-axioms-01a0.log.
- Umbrella import wired; no umbrella or full build run.
- Index63106: exit0, regenerated formal metadata.
- Lint95490 with --check-generated: exit1, 16 unrelated unreachable modules
  and stale generated LEAN_OVERVIEW.md after regeneration. No error for this
  leaf. Log: /tmp/bag-growing-twists-lint-01a0.log.
- Leaf has 732 lines, no heartbeat changes, no numerical experiments and no
  added axioms. Temporary proof fragments and superseded scratch are removed.

## Evaluation and next hard conjecture

This advances the critical twisted-pair frontier beyond fixed rational slopes.
It does not estimate the full signed BAG mode aggregate or identify the
moving zero-trace kernel with this Gaussian average. Nearby distinct zeros,
finite exponent inversion, mixed terms, derivative costs, growing moments,
positive self-return and RH remain open.

The initial proposal for every fixed theta<1 is not separately formalized.
A stronger, structurally different continuation now proves the result for all real twists
in [1/2,2] after subtracting the EXACT prime diagonal Gaussian packet.
Dirichlet approximation and localized affine prime-pair sieving provide a
complete block proof. See bag-all-real-connected-prime-pairs.md
(C28.56u). Do not discard near-identity twists or try to obtain orthogonality
from their bare frequencies after demodulation.

C28.56u extends the same leaf to 1351 lines; the 732-line count above records
the original C28.56t audit. See the continuation card for the current audit.
