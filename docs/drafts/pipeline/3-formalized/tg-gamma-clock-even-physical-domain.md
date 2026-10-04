# TG C9.18b: literal physical Gamma kernel and maximal even domain

- **Stage:** 3-formalized
- **Route:** TG, physical Gamma functional calculus
- **Lean:** SoninGammaClockEvenDomain.lean, final audit and all ten foundation queries pass

For eps>0 form the intrinsic L1 positive clock kernel
p(u)=1_[eps,R](u) gamma(u)/u and its literal reflection p(-u).
Let k=p+reflect(p), and m=2 integral_[eps,R] gamma(u)/u du.
The existing integrated-scaling representation defines the bounded
physical even operator K=rho(k)-mI. Expanding its actual strong integral
and using Haar reflection gives
 Kf=integral_[eps,R] (gamma(u)/u)(D_exp(u)+D_exp(-u)-2I)f du.
No operator-norm integral or transform premise is used.

The exact corpus Mellin transport identifies rho(k) with multiplication
by the integral of k(u)exp(-i xi u). Haar reflection converts the second
term to the inverse character. Their sum minus 2 is exactly
2(cos(xi*u)-1). Hence the complete finite symbol after mI subtraction
is the literal S_(eps,R) from C9.18a, with all coefficients and clock
normalizations preserved. This proves actual finite intertwining before
any limit is taken.

Conjugate the self-adjoint maximal spectral Gamma operator by the actual
archimedean Mellin unitary. Its physical even domain consists exactly of
f whose Mellin image lies in the spectral maximal domain. Applying the
unitary and its inverse to the original cutoff convergence, the C9.18a
iff gives the full physical even iff: every nontrivial countably generated
cofinal cutoff family converges on f exactly on that domain, and the
limit is the conjugated operator's action. Self-adjointness follows from
the proved unitary conjugation theorem.

The next obligation retains both parity blocks of full Sonin L2.
The even result alone does not identify the full physical Gamma operator.
Arithmetic energy summability, Hardy compatibility and strict contraction
remain open. No RH conclusion is asserted.

Closed 2026-10-04. Required leaf audit: lake --old env lean
GaloisForLFunctions/RHTower/SoninGammaClockEvenDomain.lean -o its target olean;
exit0, empty diagnostics. All ten public declarations audited via /tmp
with only propext, Classical.choice and Quot.sound. Umbrella wired, index0
and ten names present. Global lint1: fourteen unrelated unreachable leaves,
no finding in this module (details /tmp/tg-c918b-lint.log).
