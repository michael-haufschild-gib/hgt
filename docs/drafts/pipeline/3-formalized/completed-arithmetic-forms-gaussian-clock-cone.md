# The exact affine-Gamma cone of the nonlinear theta clock

**ID:** completed-arithmetic-forms-gaussian-clock-cone  
**Stage:** Formalised in Lean 4  
**Type:** Complete sign-cone classification and actual-source boundary

Let $\gamma_k=16^k(1/2)_k$ and define the odd-zero sequence
$s_{a,b}(2k)=a\gamma_k+b\gamma_{k+1}$.
Then every finite Hankel head of $s_{a,b}$ is positive semidefinite exactly when
$a\ge0$ and $b\ge0$. Every finite head is positive definite exactly when, in addition,
$a+b>0$.

Put $M=\int_{\mathbb R}e^{-y^2/16}\,dy>0$ and
$J_{a,b}(y)=(a+by^2)e^{-y^2/32}$. Relative to the positive Gaussian measure
$d\mu=e^{-y^2/32}dy$, the weighted moments satisfy
$$\int y^nJ_{a,b}(y)\,d\mu=M s_{a,b}(n).$$
Indeed, odd Gaussian moments vanish by reflection. Integration by parts gives
$I_{n+2}=8(n+1)I_n$ for $I_n=\int y^ne^{-y^2/16}dy$, hence
$I_{2k}=M\gamma_k$. All polynomial moments are integrable.
The density is continuous and bounded by $|a|+32|b|$, since
$e^{-y^2/32}\le1$ and $y^2e^{-y^2/32}\le32$.

The complete Hankel sign-cone law for a Gaussian measure identifies nonnegativity
of every head with pointwise nonnegativity of $J_{a,b}$. At zero this forces $a\ge0$.
If $b<0$, choose $y^2=(|a|+1)/(-b)$ to obtain
$a+by^2=a-|a|-1<0$. Thus $b\ge0$. Conversely the even and odd parity blocks
are nonnegative combinations of adjacent strict Gamma heads. A nonzero coefficient
gives strictness in every block. If both vanish the rank-one head vanishes.

For the literal inverse-hyperbolic first-atom clock, let
$q=\pi e^{2x}$, $B=(2q-3)^2$, and $C=4q^2e^{x-2q}>0$. Its exact profile is
$$\rho_x(t)=Ce^{-4t^2}(B-24t^2),$$
and its signed moment sequence is $C s_{B-3,3/8}$.
Consequently its complete Hankel cone is positive semidefinite exactly when
$B\ge3$, and this is also exactly its all-rank strictness region.
For $B<3$ some finite mixed head has a negative direction although every individual
signed even moment $C\gamma_k(B+6k)$ is nonnegative. The distinction is between
individual signed moments and the full mixed cone, within one exact source coordinate.

Together with the physical first atom's finite failing rank at every center, this
classifies the clock's positive cone and its nonlinear transport obstruction.

Lean: `GaloisForLFunctions/CompletedArithmeticForms/GaussianClockCone.lean`.
The capstones are `affineGamma_completeHankelCone_iff`,
`affineGamma_all_head_posSemidef_iff`, `affineGamma_all_head_posDef_iff`,
`firstAtomGaussianClock_all_head_posSemidef_iff`,
`firstAtomGaussianClock_all_head_posDef_iff`, and
`firstAtomGaussianClock_mixed_failure_of_shape_lt_three`.
Their transitive axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
