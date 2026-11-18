# Shifted zero pairing on the full moment half-plane

Let $z=\rho-1/2$, $L=\mathcal LF$ for a confined critical state, and $a$ its confinement coefficient. Count zero copies with multiplicity. Put $\kappa=\Theta-1/2$.

**Claim.** On $\Re w<8-2\kappa$, the absolutely convergent unheated pairing satisfies
$$
\sum_z L(z)L(-z-w)=-a\int_{-\infty}^0 F(u)^2e^{-(8+w)u}\,du .
$$
This is the whole open half-plane of absolute square moments of the state.

**Proof.** At any $s>\kappa$, logarithmic sampling and the paired Gram estimate give unconditional convergence of $\sum_zL(z)e^{(z-s)t}$ in ray $L^2$. Reading the sum against a Laplace feature at $p$, $\Re p>0$, gives the state Cauchy formula at $p+s-8$. This identifies the sum with $-ae^{(8-s)t}F(-t)$ by Laplace injectivity; that function lies in $L^2$ by the sharp moment theorem.

Set $s=(8-\Re w)/2$ and test the expansion against $e^{(\bar w+s)t}F(-t)$. Both factors have finite square mass with weight $e^{(8+\Re w)t}$. The reading of the $z$-mode is $L(-z-w)$. A continuous linear functional carries an unconditional Hilbert sum to an absolutely convergent complex sum, giving the identity.

**Exact disk.** From any real centre $c<B=9-2\Theta$, the maximal radius of holomorphic continuation to a disk is $B-c$. The square transform is holomorphic on $\Re w<B$ by absolute convergence with a margin. Reflection $w=-8-\sigma$ identifies its real values, up to the nonzero factor $-a$, with the Laplace transform of the positive ray measure $F(-t)^2dt$. Its abscissa is $2\Theta-17$ by the strict convergence and divergence results for the square moment. A larger disk would continue this positive transform through its real abscissa, contradicting Landau's theorem. No boundary-integrability assumption enters.

**Lean.** [TheShiftedZeroPairingOnTheMomentHalfPlane](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Zeros/TheShiftedZeroPairingOnTheMomentHalfPlane.lean) proves `criticalState_hasSum_zero_modes_at_depth`, `criticalState_hasSum_shifted_zeroPairing_moment_halfPlane`, `criticalState_analyticOnNhd_shiftedZeroPairing`, and `criticalState_shiftedZeroPairing_exact_disk`.
