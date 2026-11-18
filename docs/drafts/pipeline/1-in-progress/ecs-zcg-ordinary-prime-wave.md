# Ordinary prime counts and isolated zero waves

- **Stage:** 1-in-progress
- **Target:** Decide RH through the ECS confined state and the ZCG finite-top prime wave, or prove an obstruction to the full route for ordinary primes.

## Arithmetic question

For a right zero ρ, can the prescribed conjugate-pair wave exhaust ψ(x)−x up to O(√x log²x)? Excluding every finite separated top gives AAL. A proof of RH by that argument also needs ZAL.

Write $b_V=\delta-\mathbf{1}*\mu_{\le V}$ and $D_{V,W}(s)=\sum_{n\le W}b_V(n)n^{-s}$. At a zero ρ with β = Re ρ > ½, the short cofactor has two possible contributions. The unit coefficient gives 1. Summing the divisibility contribution by its divisor gives the continuum term −W^{1−ρ} Σ_{d≤V} μ(d)/[d(1−ρ)] with error Oρ(V W⁻ᵝ).

Put r = 2^{1−ρ}. Subtracting r times the width-W polynomial from the width-2W polynomial cancels the continuum term. The difference tends to 1−r for W ≥ V². Since |r| > 1, at least one cutoff detects the zero. The long-prime cutoff removes a finite Dirichlet polynomial from −ζ′/ζ and leaves its residue unchanged.

## Remaining estimate

Write $E(N)=\psi(N)-N$. For each $1/2<b<1$, prove that arbitrarily large $V$ satisfy
$$\left|\sum_{d\le\min(N,W)} b_V(d) E(\lfloor N/d\rfloor)\right|
\le K_{b,V,W}N^b \qquad (N\ge1)$$
at both $W=V^2$ and $W=2V^2$. Equivalence to RH is formalized. Even a bound for $b<\Re\rho$ derived under the single-quartet hypothesis would exclude that quartet. [Proof and Lean declarations](../3-formalized/paired-vaughan-cofactors-at-strip-zeros.md)

For ordinary primes counted once, put $A(N)=\pi(N)-\sum_{2\le n\le N}1/\log n$. RH is equivalent to power bounds for any one fixed nonzero finite sum $\sum_d f(d)A(\lfloor N/d\rfloor)$. Even a cofactor that vanishes at a right zero detects that zero, since dividing the continued series by the cofactor would give a meromorphic primitive for a derivative with nonzero residue. [Proof and Lean declarations](../3-formalized/every-finite-cofactor-detects-the-ordinary-prime-count.md)

A zero with real part $\beta>1/2$ forces each sign of $E$ to have harmonic mass $\gg_\rho N^\beta$ on every sufficiently large interval $(\sqrt N,N]$. This also holds when the zero abscissa is unattained. RH is equivalent to a bound $O_b(N^b)$ for either sign on arbitrarily distant such intervals, for every $1/2<b<1$. An independent arithmetic upper bound for one sign remains open. [Local mean and sign criterion](alternating-divisor-kernel-at-an-arbitrary-right-zero.md)

Intersecting divisibility conditions from successive central binomial coefficients gives a gcd whose large prime divisors select a single residue class of the quotient. RH is equivalent to cumulative error $O(N^{1+b})$ about a linear slope at cofinally many depths for every $1/2<b<1$. An independent arithmetic estimate remains open. [First-mean criterion](../3-formalized/the-first-means-of-dyadic-binomial-gcds.md) · [Dyadic binomial common divisors](dyadic-binomial-common-prime-divisors.md)

Under one quartet, what is the size of the surviving wave when the cofactor symbol vanishes at $\rho$ to order $k$? In log coordinates the derivative of the filtered logarithmic-integral mode is $e^{\rho t}\sum_d f(d)d^{-\rho}/(t-\log d)$. Its first nonzero inverse-power coefficient is $(-1)^kD^{(k)}(\rho)$. This predicts oscillation of order $x^{\Re\rho}/\log^{k+1}x$ in the actual count.

The largest prime factor $P(n)$ alone recovers the ordinary prime-error exponent. For $1/2\le b<1$, the bound $\sum_{n\le N}P(n)\log P(n)=\pi^2N^2/12+O(N^{1+b})$ is equivalent to $\psi(N)=N+O(N^b)$. [Proof](../3-formalized/the-largest-prime-factor-recovers-the-prime-error-exponent.md)

## Adjacent cutoffs

Can $E(N)$ and $E(pN)$ both be $O(N^{1/2+\varepsilon})$ along an unbounded sequence for each of $p=2,3$, allowing different sequences? A single quartet rotates by $\gamma\log p$ under dilation. The two rotations cannot both be multiples of $\pi$.

For a finite top, take a prime $p$ for which its nonzero frequencies give distinct phases $p^{i\gamma}\ne1$. Consecutive powers of $p$ have bounded first sums and linear second sums for the normalized top wave, uniformly in the initial phase. This suggests a one-sided test for AAL: can every fixed block $N,pN,\ldots,p^kN$ have all its errors below $N^{1/2+\varepsilon}$ at arbitrarily large $N$?

For arbitrarily large $t$, $p=2t+1$ is prime with $p\equiv7\pmod8$. Put $A_t(M)=C_{t,2t}(M)$. On $(t,2t]$ the cofactor is exactly $\mu$. Increasing $t$ by one changes three endpoints. At $t+1$ and $2t+2$ the Möbius value vanishes because four divides them. The sole change is $-1$ at $p$. Hence $A_{t+1}(pN)-A_t(pN)=N-\psi(N)$ for every $N$, including inside the first octave. [Formal recovery theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount.lean)

Under one quartet, this count recovers the averaged state on each confined rung to square-root accuracy after a positive rescaling and a log delay of at most half a period. The same pair of arithmetic cutoffs works for every rung. [Proof and Lean declarations](../3-formalized/adjacent-vaughan-octaves-and-the-quartet-wave.md)

The two rung amplitudes have independent phases. On their negative plane the on-line energy and confinement are nonnegative, so the real pairing of the right and reflected evaluations is negative definite. For $\delta=\Re\rho-1/2$ and multiplicity $m$, the common frequency gives a joint confinement bound $m((16-\delta^2)^{-1/2}-1/4)$. A contradiction would require an independent lower bound from the actual prime form. [Proof and Lean declarations](../3-formalized/quartet-rung-phase-and-confinement.md)

Completing the divisor row gives the original prime error with coefficient one after an explicit linear correction and error at most $50\sqrt{NV}$. Any saving for the restricted row must account for its complementary tail. [Exact decomposition](../5-failed/ecs-zcg-completing-the-divisor-row.md)

## Coincident products

For fixed distinct cofactors $d,e$, write $g=\gcd(d,e)$. At a common product $n=\operatorname{lcm}(d,e)k$ the two long prime weights are $\Lambda((e/g)k)$ and $\Lambda((d/g)k)$. For $k>1$ both can survive only when both reduced cofactors and $k$ are powers of the same prime. The resulting uncentred correlation above the first common product is at most $\log(\operatorname{lcm}(d,e))\log(N/\operatorname{lcm}(d,e))$. Squaring a cumulative count also introduces terms at unequal products. [Exact prime-power overlap](../3-formalized/coincident-products-of-ordinary-prime-weights.md)

Beyond $4V^2$, the square of the actual prime sum for a first octave is pointwise diagonal. After centering, coprime nonunit dilations give the row count up to an explicit logarithmic deficit. The nested ratio six instead gives $X-\psi(X)$ exactly, ruling out logarithmic bounds for all centered pairs. [Classification and obstruction](../5-failed/ecs-zcg-logarithmic-centered-cofactor-cross-terms.md)

At both paired widths the total absolute weight exceeds $cN$ for every $c<2\log 2$, first taking $V$ sufficiently large and then $N$ sufficiently large at fixed $V,W$. Prime multiples of the negative cofactors $V<p\le V^2$ and their complement supply opposite linear masses. [Prime multiples recover each cofactor](../5-failed/ecs-zcg-absolute-cofactor-counts.md)
