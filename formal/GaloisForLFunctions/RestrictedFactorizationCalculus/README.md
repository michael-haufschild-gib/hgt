# Restricted factorization calculus

For a sharp interval \((L,U]\), each squarefree integer carries its Möbius sign. An exchange replaces one prime factor by two distinct primes, or reverses that operation, with both integers in the interval. Removing disjoint opposite-sign pairs preserves the signed sum exactly. The question is which exchanges unique factorization supplies, and how much signed mass survives at every cutoff. The target is
\[
  \left|\sum_{1\le n\le X}\mu(n)\right|\ll_\varepsilon X^{1/2+\varepsilon}
  \qquad(\varepsilon>0).
\]

## Where a change of fibre matters

Quantitative Factorization Matching partitions a dyadic block by deleting one or two largest primes according to parity. A negative source with ordered cofactor \(a\) cannot be matched in that fibre if \(aP^+(a)^2\ge 2X\). The witnesses include products of three primes in separated windows of size comparable to \(X^{1/3}\). Ordering the factors differently at the exchange changes which integer is held fixed. [Ordered fibres and debt](../QuantitativeFactorizationMatching/GlobalDyadicGraphAndCofactorFibres.lean)

Write a source as \(cqr\) with \(q<r\) its two largest primes. Try the reverse move \(cqr\mapsto cp\), keeping \(c\) and replacing the entire pair. Both endpoints belong to \((L,U]\) exactly when both variable factors belong to \((\lfloor L/c\rfloor,\lfloor U/c\rfloor]\). If \(p>P^+(c)\), deleting the largest prime from the target recovers \(c\). This permits simultaneous injections over different cofactors. Within one cofactor, the relevant quantities are the number of eligible pairs and the number of available primes in the same interval.

## Prime supply in a sharp cell

Fix \(K\ge1\) and nonnegative integers \(B,D\). For sufficiently large \(s\), take any
\[
 s^2\le u\le v\le2s^2,\qquad v-u\ge s^2/(\log s)^B .
\]
Let \(A\) consist of products \(qr\in(u,v]\) with both factors prime and \(s/K<q\le Ks\). Then
\[
 D\,|A|\le\pi(v)-\pi(u).
\]
The height at which this holds is independent of both cell endpoints. For each \(q\), the prime number theorem bounds the number of possible \(r\) in the exact interval \((u/q,v/q]\). Summing over the balanced primes \(q\) uses one more factor of \(1/\log s\) than counting the available primes in \((u,v]\). This supplies spare partners even inside partial octaves. [Prime supply for balanced products](PrimeSupplyForBalancedProducts.lean)

## What the calculus must prove

1. Transport a growing family from deficient ordered fibres, with a formula for losses at both sharp endpoints. A neighbour for each source leaves target collisions unresolved.
2. Combine exchanges over unboundedly many cofactors and factor counts. Count previously consumed targets and identify the remaining integers by arithmetic conditions.
3. Apply signed divisor inversion or a terminating recurrence to those remaining integers. A stopping rule must retain the terminal intervals and their signs. Fixed factor-count cutoffs, fixed-prime insertions and short moves have known obstructions. [Restricted matching obstructions](../QuantitativeFactorizationMatching/CompleteResolutionOfTheFactorizationMatchingQuestion.lean)
4. Bound the resulting signed sum at every cutoff. An absolute count of unmatched vertices suffices, but can be much larger. The Mertens estimate above gives RH by continuation of the reciprocal zeta series and reflection. [Dyadic transfer](../QuantitativeFactorizationMatching/DyadicMatchingStripAndRiemannEquivalence.lean)

Contributions must change the available range of arithmetic exchanges, determine the exact signed remainder of a growing construction, or prove a bound on that remainder. An unrestricted sign pairing measures the Mertens sum itself and supplies no arithmetic construction.
