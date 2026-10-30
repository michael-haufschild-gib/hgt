# An exact positive Gaussian clock for the first theta atom

**ID:** completed-arithmetic-forms-hyperbolic-clock  
**Stage:** Formalized in Lean 4  
**Type:** Exact source coordinate change and boundary of positivity transport

Let $q=\pi e^{2x}>0$, $B=(2q-3)^2$, $C=4q^2e^{x-2q}>0$, and
$f_{1,x}(u)=f_1(x+u)f_1(x-u)$. The literal reflected first atom is
$$f_{1,x}(u)=C e^{-4q\sinh^2u}[B-24q\sinh^2u].$$
In the invertible real coordinate $u=\operatorname{arsinh}(t/\sqrt q)$, it is exactly
$$\rho_x(t)=f_{1,x}(\operatorname{arsinh}(t/\sqrt q))
=C e^{-4t^2}(B-24t^2).$$
The inverse coordinate is $t=\sqrt q\sinh u$.

For the entire rotated profile, put $G(z)=e^{4z^2}$. Since
$G''(z)=(8+64z^2)G(z)$,
$$\rho_x(iz)=C\big[(B-3)G(z)+\tfrac38G''(z)\big].$$
Here the left side denotes the entire continuation of the displayed Gaussian polynomial;
no global complex inverse-hyperbolic branch is asserted.
The exact signed even jets are therefore
$$
(-1)^k\rho_x^{(2k)}(0)
=C\big[(B-3)\gamma_k+\tfrac38\gamma_{k+1}\big]
=C\gamma_k(B+6k),\qquad \gamma_k=16^k(\tfrac12)_k.
$$
Every shifted clocked Hankel head is the exact positive combination
$$C\big[(B-3)G_{N,s}+\tfrac38G_{N,s+1}\big].$$
For $B\ge3$, the first summand is semidefinite and the second is definite. Thus every
shifted head and every full signed head of $\rho_x$ is positive definite, simultaneously
at that fixed center. This includes every $x\ge0$, since $q\ge\pi>3$.

At the same centers, the original physical-coordinate first atom has a finite failing
full signed rank $\kappa(x)$. Hence the exact nonlinear pullback
$$f_{1,x}(u)=\rho_x(\sqrt q\sinh u)$$
does not preserve the all-order signed Hankel cone. The positive Gaussian mixture is an
exact source comparison object; positivity transport requires control of this nonlinear
coordinate change. Its invertibility alone supplies no such control. No complete-theta
or integrated sign follows from the clocked first-atom cone.

Lean: `CompletedArithmeticForms/HyperbolicClock.lean`:
`firstAtomGaussianClockProfile_eq`, `firstAtomGaussianClockProfile_pullback`,
`firstAtomGaussianClockProfile_signed_even_jet`, `firstAtomGaussianClockHead_posDef`,
`firstAtomGaussianClock_all_rank_strict_of_nonneg`, and
`firstAtomGaussianClock_positive_pullback_fails`.
Their transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
