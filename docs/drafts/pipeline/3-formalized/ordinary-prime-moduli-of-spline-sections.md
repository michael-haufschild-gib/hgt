# Ordinary primes suffice in the section-modulus test

For an effective spline divisor $a$ with $M=\sum_i a_i$, let $d$ be the integral modulus of all its prime-power contact rows. Let $d_1$ use only ordinary prime degrees. There is an absolute constant $C$ such that $0\le\log d-\log d_1\le C M^2$. Neither the number of conductors nor their sizes enter the constant.

**Proof.** A spline atom sampled at multiples $jk$ of one lower degree $j$ occupies a window of fixed multiplicative width in $k$. The Chebyshev estimate $\psi(x)-\theta(x)\ll\sqrt{x}$ bounds the sum of $\Lambda(k)/\sqrt{k}$ over the proper powers in that window by an absolute constant. The logarithmic mesh mass of the lower atom is also bounded independently of its center. Summing over ordered pairs of atoms costs $M^2$. Rounding nonnegative multiplicities down can only decrease the omitted contribution.

For $a_p=e_1+e_p$, RH is equivalent to the existence of $B$ such that every prime $p$ has arbitrarily large $m$ with $\log d_1(ma_p)\le A(ma_p)+Bm^2$. The proof uses the identity $Q(a_p)=2\operatorname{Re}S(0)+2\operatorname{Re}S(\log p)$ and the prime-degree one-sided trace criterion.

For arbitrary signed $a$, the absolute difference between the log rational generators is at most $C(\sum_i |a_i|)^2+\sum_{2\le k\le 3K_N}\Lambda(k)$. Taking absolute values in each sampled product reduces the estimate to the effective divisor $|a|$. Integer floors cost at most the displayed horizon term. For effective prime pairs, fitting the ordinary-prime modulus inside the original radius with zero allowance is also equivalent to RH.

**Lean.** `signed_generator_difference_bound`, `effective_modulus_difference_bound` and `riemannHypothesis_iff_ordinary_prime_modulus_fits`. [OrdinaryPrimeSectionModuli.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OrdinaryPrimeSectionModuli.lean)

**Unconditional allowance.** On $m(e_1+e_p)$ the absolute discrepancy between log radius and log full modulus is eventually less than $C p^{8999/24000}m^2$ for every positive $p$. The common constant follows by transferring the zero-width bound to the cubic spline orbit. Some prime and some choice of sign in $e_p\pm e_1$ give positive quadratic section growth. Otherwise the parallelogram identity bounds the prime trace below, which implies RH, and positivity would force the whole Gram to vanish. [PrimeSectionAllowanceAtTheStripEdge.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PrimeSectionAllowanceAtTheStripEdge.lean)
