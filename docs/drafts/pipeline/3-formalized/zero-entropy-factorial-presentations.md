# Zero-entropy factorial presentations

Can the exact section generator be recovered from a balanced factorial product whose Stirling entropy vanishes identically? For integer exponents $c_j$, let $q=\prod(j!)^{c_j}$, $E=\prod j^{j c_j}$ and impose $\sum j c_j=0$.

For $a,b>0$ the quotient
$$Q(a,b)=(ab)!/((a!)^b(b!)^a)$$
has entropy zero in logarithmic units, after adding $ab$ copies of $1!$. Write $Q_4=Q(2,2)$, $Q_6=Q(2,3)$, $Q_9=Q(3,3)$ and $Q_{10}=Q(2,5)$. Cancellation of factorials gives
$$2=Q_9Q_4^4/(Q_{10}Q_6).$$
Now assume all positive integers below $n$ admit such presentations. For $n=2k\ge4$ multiply presentations of $2$ and $k$. For $n=2k-1\ge3$, expand
$$Q(2,k)=\frac{2k\,n\,(n-1)!}{(2!)^k(k!)^2}.$$
Every factor other than $n$ is a product of integers below $n$. This supplies $n$ at horizon at most $\max(10,n+1)$. Division supplies every positive rational. In particular every rational section generator admits a balanced, exactly zero-entropy presentation.

At horizon at least six, two balanced products of value one have rationally independent entropies. Consequently the entropy at any fixed representable value is dense in the real line. The infimum of $\max(|S|,|\log q-S|)$ equals $|\log q|/2$.

Lean declarations are `log_nat_mem_zeroEntropyPrices`, `zeroEntropy_factorial_ratio`, `factorial_entropy_dense_at_fixed_value` and `factorial_entropy_remainder_minimax`. For the exact ordinary prime generator, `ordinaryPrimeGenerator_zeroEntropy_factorials` gives horizon $\max(10,3\,\mathrm{windowEnd}(N)+1)$, including all flooring errors. [Factorial identities](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/EntropyAndValueOfBalancedFactorials.lean) · [Prime generator](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ZeroEntropyFactorialsForThePrimeGenerator.lean)
