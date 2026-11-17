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

## Adjacent cutoffs

For arbitrarily large $t$, $p=2t+1$ is prime with $p\equiv7\pmod8$. Put $A_t(M)=C_{t,2t}(M)$. On $(t,2t]$ the cofactor is exactly $\mu$. Increasing $t$ by one changes three endpoints. At $t+1$ and $2t+2$ the Möbius value vanishes because four divides them. The sole change is $-1$ at $p$. Hence $A_{t+1}(pN)-A_t(pN)=N-\psi(N)$ for every $N$, including inside the first octave. [Formal recovery theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount.lean)

Under one quartet, the averaged state on each rung and this signed count each carry one conjugate pair. Their nonzero coefficients determine a positive amplitude and a fixed logarithmic delay. An independent estimate on the delayed counts that saves a power below the common frequency amplitude would exclude that quartet.
