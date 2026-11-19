# A prime shell beyond the square root at every midpoint

For integers \(n\ge1\), let \(P=\lfloor2\sqrt n\rfloor\), \(Q_*=\max(P,\lfloor n^{500/999}\rfloor)\), \(D(n)=2\theta(3n)-\theta(2n)-\theta(4n)\), and
\[
 k_n(p)=\lfloor4n/p\rfloor-2\lfloor3n/p\rfloor+\lfloor2n/p\rfloor,\qquad
 H^*(n,Q)=\sum_{Q<p\le2n}(\log p)k_n(p).
\]
For every integer \(P\le Q\le Q_*\), uniformly in both endpoints,
\[
 D(n)=H^*(n,Q)-\log\frac{(4n)!(2n)!}{(3n)!^2}+O(\sqrt n).
\]
The sum runs over ordinary primes. At \(Q_*\), every contributing product \(pv\) has \(2\le v<4n^{499/999}\).

**Proof.** Factor the factorial quotient into Mangoldt weights. Removing the unit cofactor gives the midpoint with the displayed sign. Each three-floor weight has absolute value at most one. The small factors and higher prime powers cost at most \(\psi(P)+\psi(4n)-\theta(4n)\ll\sqrt n\). On a partial dyadic block \([X,Y)\) beyond \(P\), write \(k_n(p)=2s(3n/p)-s(2n/p)-s(4n/p)\) with \(s(x)=\{x\}-1/2\). Up to \(Q_*\), the three frequencies lie between \(X^{999/500}\) and \(X^{1001/500}\). The sharp ordinary-prime reciprocal estimate costs \(O(X^{999/1000})\) on each block. Geometric summation through the last partial block gives \(O(\sqrt n)\). [Ordinary-prime input](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOfReciprocalPrimes.lean#L181)

Lean declarations `unrestricted_large_prime_factorial_error`, `midpoint_floor_prime_block_saving`, `prime_floor_shell_beyond_square_root`, and `midpoint_after_paid_prime_shell` passed the kernel audit with `propext`, `Classical.choice`, and `Quot.sound`. [Formal proof](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeFloorRowBeyondTheSquareRoot.lean#L281)
