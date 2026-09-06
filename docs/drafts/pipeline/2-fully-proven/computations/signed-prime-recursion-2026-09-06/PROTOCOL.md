# Signed recursion: discovery protocol

Status: exploratory measurements, not an RH proof. Positivity is suspended as a proposed producer in this investigation. This is a research allocation, not a no-go theorem about all positivity methods.

## Source evidence and question

`Sieve/MultiplicativeLogRecursion.lean` preserves the exact signed prime recursion but bounds two remainders by O(N). `LiouvilleDirichletSeries.sum_divisors_liouvilleC` identifies the exact square-supported divisor convolution. The frontier and universal ledgers reject generic energy positivity as a substitute for source-specific cancellation. These three corpus observations motivate inspecting the discarded signed terms before replacing their bounds.

For a real completely multiplicative sign function f, put S(N)=sum(n<=N) f(n), and define

- Elog(N)=sum(n<=N) f(n) log(N/n);
- Eeven(N)=sum(p^k<=N, k>=2 even) log(p) f(p)^k S(floor(N/p^k));
- Eodd(N)=sum(p^k<=N, k>=3 odd) log(p) f(p)^k S(floor(N/p^k));
- P(N)=sum(p<=N) log(p) f(p) S(floor(N/p)).

The exact identity is S(N) log(N)=P(N)+Elog(N)+Eeven(N)+Eodd(N). No absolute value is taken before this addition.

Discovery question: are the two discarded errors individually small, or do they need cancellation against one another? Is their signed relationship specific to literal f(p)=-1, or also present in independent random completely multiplicative controls?

No primary conjecture is frozen before observing data. This is hypothesis-generating work. Any subsequent claim must be frozen separately and attacked on new cutoffs/seeds. In particular, bounded finite normalized values will not be called an asymptotic theorem.

## Design and falsifiers

Use the literal Liouville function, seven seeded random prime-sign controls, and f=1 as an implementation and degeneracy control. Every control preserves complete multiplicativity, so the exact recursion remains applicable. The all-one control is not an experiment on cancellation; its predictable behavior checks the measurement implementation.

Measure powers of two and three intervening cutoffs per octave from 4096 through 2097152. Record all signed terms, square-root and square-root-times-log normalizations, sign disagreements, the fraction of absolute remainder size retained after summing, and the exact-recursion residual. These are linear/signed diagnostics, not quadratic energies or PSD tests.

Reconstruct signs independently by smallest-prime-factor recursion on a short prefix. Validate the prime-power identity against the weighted sum. A failed identity check invalidates the batch. Do not infer RH from finite bounds or from random-control similarity.

Run only on the authorized Runpod, at most eight worker processes, one numerical-library thread per worker, and a 120-second command cap. Download scripts and results. No numerical output enters a Lean proof.

## Intended proof chain and open steps

Exact arithmetic recursion → a new deterministic cancellation law with all discarded terms retained → all strict half-power bounds for Möbius sums → the corpus's closed Mertens criterion → RH.

The deterministic law and its propagation to every cutoff and every exponent above one half are missing. Changing from an energy language to this recursion does not discharge either obligation. A square-root bound for Liouville would also require the exact square-dilation transfer to Möbius; that transfer must be checked before claiming the chain closes.

## Adaptive reversal, frozen before execution

The first batch at N=2097152 gives literal Elog/sqrt(N) approximately -1.34944 and Epp/sqrt(N) approximately -2.75630. They reinforce, as do most controls. Thus the hoped-for cancellation between those two remainders is not the observed mechanism.

Reverse the prime/cofactor summation for the literal source:

`P(N)=-N sum(m<=N) lambda(m)/m - sum(m<=N) lambda(m)(theta(N/m)-N/m)`.

Measure the two terms independently at five cutoffs through 2^23. Then cyclically shift the cofactor signs inside each dyadic block, independently in 64 seeded controls. Preserve every block's exact charge and sign count, and the smallest cofactors 1,2,3; keep the actual prime-counting error unchanged. This intervention destroys multiplicativity and is not a competing zeta source. It asks whether the literal alignment with the counting error is unusually small relative to those coarse-data-preserving rearrangements. Record signed ranks and absolute-value ranks, without fitting a model or choosing favorable cutoffs afterward. A middle rank rejects distinctiveness at that resolution; an extreme rank motivates a new hunch and an independent test, not a theorem.

## H1: withheld-cutoff amplification test

The reversed discovery batch has literal signed ranks 0,2,62,64,64 among 64 controls at N=2^15,2^17,2^19,2^21,2^23. All corresponding absolute ranks agree. Literal alignment therefore does not consistently suppress this error; the two largest cutoffs suggest amplification.

Freeze this empirical prediction before running more data: at each N in `{3*2^19,3*2^20,5*2^20,7*2^20,2^24}`, the literal signed counting-error pairing exceeds the 95th percentile of 128 new charge-preserving cyclic-shift controls, with seeds 86100 through 86227. A single failed cutoff rejects H1. This is a finite experimental hypothesis, not an all-scale mathematical conjecture. Its motivation is the observed late amplification, not an available proof strategy.

Record each dyadic cofactor block's exact contribution and its charge-times-mean-kernel term. Their difference identifies where literal alignment survives charge centering. This decomposition is descriptive and retains its sign; no energy or positive-definite form is introduced. At non-dyadic cutoffs, shift the final partial block only within its visible prefix, preserving that prefix's charge too. Reinitialize each seed at each cutoff so the discovery's complete-block controls remain reproducible.

## H2: hostile prime-dilation test

H1 failed at four of five withheld cutoffs. Exact charge centering at N=2^21,2^22,2^23,2^24 gives normalized excess approximately `5.9313,-5.5113,4.2893,-3.9993`. Most of each value comes from cofactors at least 64. This suggests coordinated signed dilation, but the selection of powers of two may be responsible.

Corpus input: `LiouvilleDyadicGramLaw.liouvilleC_two_mul` and `LiouvilleDirichletSeries.liouvilleC_mul`/`liouvilleC_prime_pow` give exact coefficient reversal under any prime dilation. They do not prove the same reversal of the counting-error pairing after cutoff and charge centering.

Freeze the risky empirical extension H2: the exact charge-centered counting-error excess C(N) satisfies `C(pN)*C(N)<0` for every p in `{2,3,5,7}` and N in `{2^19,2^20,2^21}`. Compute these twelve comparisons, retaining the full visible final block. One failure rejects H2; do not rescue it by restricting primes after seeing results. The response identity `R(pN)+R(N)=sum(p does not divide n, n<=pN) lambda(n)(theta(pN/n)-pN/n)` is an exact derived bridge, but controlling its right side is still open and may carry the original difficulty.
