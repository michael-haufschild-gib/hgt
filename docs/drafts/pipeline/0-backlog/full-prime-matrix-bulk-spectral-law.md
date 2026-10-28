# A bulk spectral law for the literal prime matrix

- **ID:** full-prime-matrix-bulk-spectral-law
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** finite-prime supported/unit factorization; actual prime kernel; non-Følner multiplicative Toeplitz spectra
- **Statement:** The empirical eigenvalue measures of the unshifted full prime matrices converge in Wasserstein distance of order two, with an explicit finite-prime block approximation.
- **Count:** uncounted; novelty and all exact proof obligations remain

## Target and significance gate

Let P_N be `weilPrimeKernel` on 1,...,N and let mu_N put mass 1/N at
each eigenvalue, counted with multiplicity. The conjecture is convergence of
mu_N in W_2 to a canonical arithmetic probability measure mu. Unlike the
fixed-conductor edge energies, this would describe a positive fraction of
the whole matrix spectrum. Establishing only a generic known Toeplitz limit
in new notation would not count. The singular all-prime specialization,
its precise applicability, and a nontrivial arithmetic characterization
must survive the novelty audit.

## Proposed mechanism, not a completed proof

For a nonempty finite prime set Q, delete all edges whose quotient is a
power of a prime outside Q. Write the resulting matrix as P_N^Q. Unique
supported/unit factorization decomposes it into blocks indexed by the
Q-coprime part u. The u block is the prime kernel on the Q-supported
integers d<=N/u.

Enumerate those integers as 1=d_1<d_2<... and write B_Q(d_j) for the
corresponding j-dimensional block. With delta_Q=product_(p in Q)(1-1/p),
the proposed finite-prime limiting measure is

`mu_Q = delta_Q * sum_(j>=1)(1/d_j-1/d_(j+1)) * sum_(lambda in spec B_Q(d_j)) delta_lambda`,

where the inner sum retains multiplicity. Its proposed total mass is one
by telescoping and `delta_Q*sum_j 1/d_j=1`. The empty prime set has limit
delta_0 and requires a separate definition. Counting Q-coprime integers
in each interval `(N/d_(j+1),N/d_j]` gives the finite-block frequencies.
The infinite block sum still needs a justified tail estimate.

The key all-prime tail identity should be

`N^(-1)*||P_N-P_N^Q||_HS^2`
` = (2/N)*sum_(p notin Q, k>=1, p^k<=N) (log p)^2*p^(-k)*floor(N/p^k)`
` <= 2*sum_(p notin Q)(log p)^2/(p^2-1)`.

The last series converges. A proved Hoffman--Wielandt bound would transfer
this to W_2 distance between the empirical laws. It should make mu_Q Cauchy
and then prove the full limit. The exact matrix identity, eigenvalue matching,
probability-measure construction, completeness, and all limiting exchanges
are still obligations, not hypotheses to insert into the final theorem.

The anticipated first two moments are zero and
`2*sum_p (log p)^2/(p^2-1)`. Closed prime-power triangles suggest the third
normalized trace tends to `6*sum_p (log p)^3/(p^2-1)^2`. W_2 convergence
alone does not identify the limiting third moment; higher integrability
must be proved before making that claim. No numerical experiment was used.

## Initial novelty audit

Corpus queries for empirical spectral distribution of the Weil prime matrix
and for multiplicative Toeplitz eigenvalue distributions returned other
prime trace constructions, conditional Weil Toeplitz norm bounds, and
constrained-prolate spectra. Their returned statements do not provide this
bulk law. This is an initial search, not a full audit of those sources.

[Guo--Li--Zhou, Theorem 1.11](https://arxiv.org/html/2305.07860v3) proves
empirical spectral convergence for bounded real multiplicative Toeplitz
symbols along natural truncations, with a countable atomic law for finite
coordinate symbols. The theorem and surrounding definitions were read.
That finite-prime result is baseline. Its full proof and extensions must
be checked before treating the proposed all-prime tail extension as new.

Section 4 has now been read through both main proofs. Its finite-coordinate
block formula is the formula above after grouping equal blocks. This is
established baseline. Its passage to infinitely many coordinates uses bounded
operator norms and Haar L2 approximation; the proposed weighted tail needs
its own applicability and novelty check.

The all-prime Fourier coefficients here have divergent unweighted square
sum, while the proposed arithmetic Hilbert--Schmidt bound includes an extra
prime-power reciprocal. That difference is a lead, not yet a proof that
existing Szegő results do not apply. The literal prime kernel and its
fixed-energy quasimodes must remain separate from bulk normalization.

## Gates

- [ ] Complete corpus and primary-literature novelty audit.
- [ ] Dependency-closed paper proof with an arithmetic characterization.
- [ ] Exact Lean statement and proof, direct checks, transitive axioms, umbrellas.
