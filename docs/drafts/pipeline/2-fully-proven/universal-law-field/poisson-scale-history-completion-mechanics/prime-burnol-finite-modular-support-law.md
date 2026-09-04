# Prime Burnol finite modular support law

- **ID:** ULF-PBFMS-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor source-formation theorem
- **Parents:** ULF-MCPT-001, P-G186, P-G194
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [NOT RH]
- **Lean:** formal/GaloisForLFunctions/RHTower/PrimeBurnolFiniteModularSupport.lean

## 1. Big-picture meaning

The modular cubic mechanism cannot start from a chosen pseudoinverse. It needs a canonical inverse
of every finite literal Euler covariance before theta completion. Define that covariance directly
from prime powers, their unsquared square-root Euler amplitudes, and the Burnol half-line columns.
Distinct prime-depth labels have distinct real decay rates, so their full complex-clock columns are
linearly independent for every ordinate assignment.

Thus every injective finite primitive packet has full modular support. Kernel reduction and phase
choice are absent. This discharges source formation only; it does not construct the cofinal theta
boundary.

## 2. Exact theorem

For a primitive cell `u=(p,e)` and real clock `kappa`, put

~~~text
lambda_u = log(p^(e+1)),
rho_u    = 1/2 + lambda_u + i kappa,
f_u(L)   = sqrt(Lambda(p^(e+1))/p^(e+1)) L exp(-(rho_u-1/2)L),  L>0.
~~~

Let `u_i`, `i< N`, be injectively labelled and let the clocks `kappa_i` be arbitrary. Then

~~~text
{f_(u_i)}_(i<N) is linearly independent in L2((0,infinity)),              (PBFMS.1)
det ( <f_(u_i),f_(u_j)> )_(i,j<N) != 0.                                  (PBFMS.2)
~~~

The Gram in (PBFMS.2) is the complete literal prime-mixed Burnol covariance, including its
unsquared Euler amplitudes and every cross-prime/depth entry. Its displayed columns agree with the
P-G186 base-Cauchy realization. Hence this source-native choice of every finite density `C_F` in
ULF-MCCED-001 is invertible and defines the canonical inner modular automorphism

~~~text
sigma_F(A)=C_F^(-1) A C_F.                                                (PBFMS.3)
~~~

## 3. Proof

Primitive logarithmic frequency is injective by unique prime-power factorization. Therefore

~~~text
beta_i = -(rho_(u_i)-1/2)
~~~

are distinct complex exponents, regardless of the clocks. Every Euler amplitude is nonzero.

Suppose a finite linear combination of the `L2` columns vanishes. Its representatives give,
almost everywhere on `(0,infinity)`,

~~~text
G(L)=sum_i c_i A_i L exp(beta_i L)=0.
~~~

`G(z)` is entire. Vanishing almost everywhere on any positive real interval forces `G` to vanish
identically. On the nonempty open set `z!=0`, divide by `z`; distinct-exponent independence gives
`c_i A_i=0` for every `i`. Since `A_i!=0`, all `c_i=0`. This proves (PBFMS.1).

Define the finite covariance to be this complete `L2` Gram. The standard Gram determinant criterion
then gives (PBFMS.2); no Route-P completion or Xi-labelled object enters its Lean proof.

## 4. Consequence and limit

ULF-MCCED-001 no longer needs a support-corner convention: finite modular actions are formed
canonically on the complete packet. The remaining obstruction is genuinely cofinal and
archimedean: prove that these finite modular actions define one theta-completion extension whose
cubic boundary is the same representative as the strict sub-unit Burnol pairing.

Finite invertibility is not selection, positivity, or RH. It supplies the source side of the
candidate mechanism and prevents a hidden pseudoinverse choice from manufacturing its index.
