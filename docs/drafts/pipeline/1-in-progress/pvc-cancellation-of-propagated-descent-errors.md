# Cancellation of propagated descent errors

**PVC.** Write $E(x)=\psi(x)-x$ and $T_Df(x)=\sum_{1\le v\le x}g_D(v)f(\lfloor x/v\rfloor)$. The [fixed-width descent](../3-formalized/pvc-a-power-descent-for-the-actual-cofactor-count.md) controls one defect $(I-T_D)E$. Taking absolute values separately on the next level loses a power. Seek a square-root bound up to logarithms or $x^\epsilon$ for the *signed* second defect $(I-T_A)(I-T_D)E$, uniformly at logarithmic cutoffs.

If $c_R$ denotes the finite divisor coefficients of $I-T_R$, the double defect pairs $c_A*c_D$ with
$$
S_2(x)=\tfrac12\sum_{n\le x} d(n)\log n-\sum_{n\le x}d_3(n).
$$
The [complementary-divisor identity](../../../../formal/GaloisForLFunctions/RHTower/LogarithmicDivisorDilation.lean) gives $1*1*\Lambda=1*\log=d(n)\log(n)/2$. The quadratic logarithmic main terms cancel. The two zero reciprocal moments annihilate the remaining $x(P+Q\log x)$ after restoring real quotients, with rounding cost logarithmic per divisor pair. The unresolved estimate here is the sharp ternary divisor remainder $O_\epsilon(x^{1/2+\epsilon})$. The [fourth moment on the critical line](../../../../formal/GaloisForLFunctions/RHTower/MoebiusMollifiedCriticalMoment.lean) bounds a Gaussian-smoothed Perron integral for $\zeta^3$ there. Passing from that integral to sharp coefficients and controlling the moving truncations in the iterated descent remain open in this argument.
