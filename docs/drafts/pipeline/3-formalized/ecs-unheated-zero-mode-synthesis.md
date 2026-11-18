# Unheated zero modes of the state and ordinary-prime wave

Let $F$ be a confined critical state at its positive threshold, $a$ its confinement coefficient, $z=\rho-\tfrac12$ a centred zero and $c_z=\mathcal LF(z)$. Count zeros with multiplicity.

**State and wall.** Both series converge unconditionally in $L^2(0,\infty)$,
$$
-aF(-t)=\sum_z c_z e^{(z-8)t},\qquad
a e^{-t}F^+(t)=\sum_z c_z e^{(-z-1)t}.
$$
Removing the entire $\Re z>0$ subseries from the first formula leaves $R$ with $e^{(8-s)t}R\in L^2$ for every $0<s\le8$.

**Ordinary primes.** Let $H_-$ be the $\Re z<0$ subseries on the right of the wall formula. For every $0<s\le1$,
$$
e^{-st}\left(\sum_p\frac{\log p}{\sqrt p}\,F(t-\log p)
-e^{t/2}\mathcal LF(-1/2)+e^t H_-(t)\right)\in L^2(0,\infty).
$$
For any finite set $S$ of zero copies, the same bound holds with correction $\sum_{z\in S}c_z e^{-zt}$ whenever $-\Re z\le b<s$ outside $S$.

**Proof.** Apply the Poisson bound to $g(w)=\log(4+w)\mathcal LF(w-1)$ at $w=1+z$. Summing the Poisson kernels costs one boundary logarithm. The second and third reflected logarithmic moments give $\sum_z\log^2(4+|\Im z|)|c_z|^2<\infty$.

Pair each Laplace feature at $u$ with its reflected feature at $D-u$. At depths bounded away from both strip edges, the sum of the Gram entries at $u,v$ is
$$
\frac{1}{u+\bar v}+\frac{1}{2D-u-\bar v}
=\frac{2D}{(u+\bar v)(2D-u-\bar v)}.
$$
The modulus is bounded by a constant times $(1+|\Im u-\Im v|^2)^{-1}$. Its row sum over zeros costs one logarithm. The inequality $2|c_i c_j|\le |c_i|^2+|c_j|^2$ bounds every finite tail's squared norm by its weighted coefficient mass. Hence the exponential series converges on each separated damping line.

Pairing the Hilbert sums against Laplace features gives the state's Cauchy series on either side of the wall. Laplace injectivity identifies both sums. Additional exponential damping carries the complement of any removed layer to its contribution on the original line. The wall identity then gives the prime sum after polar subtraction. Proper powers have finite damped square mass for every positive exponent, leaving the ordinary primes.

The remaining arithmetic problem is independent cancellation of the ordinary-prime sum against its polar term before the left-zero contribution is removed.

**Lean declarations**

- `summable_log_sq_mul_norm_sq_laplace_centredZero` and `criticalState_summable_zeroRayFeature` prove weighted sampling and unconditional synthesis. [Sampling](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/LogarithmicallyWeightedZeroSamples.lean) · [Synthesis](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/UnheatedZeroModeSynthesis.lean)
- `criticalState_hasSum_unheated_zero_modes`, `criticalState_memLp_sub_right_zero_modes` and `criticalState_memLp_sub_finite_unheated_modes` give the state expansion and its remainders. [State expansion](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/TheUnheatedStateIsTheSumOfItsZeroModes.lean)
- `criticalState_memLp_damped_properPowerWave` removes the proper powers. [Proper-power wave](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheProperPrimePowersInThePrimeWave.lean)
- `criticalState_hasSum_unheated_beyondWall_modes`, `criticalState_memLp_ordinary_prime_remainder_after_left_zeros` and `criticalState_memLp_ordinary_prime_sum_sub_pole_add_finite_modes` give the wall expansion and ordinary-prime remainders. [Ordinary-prime wave](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Modes/UnheatedZeroModesBeyondTheWall.lean)
